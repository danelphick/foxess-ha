"""Scheduler card support: static files, Lovelace resource and WebSocket API."""
from __future__ import annotations

import hashlib
import logging
from pathlib import Path
from typing import Any

import voluptuous as vol

from homeassistant.components import websocket_api
from homeassistant.components.http import StaticPathConfig
from homeassistant.components.lovelace.const import LOVELACE_DATA
from homeassistant.const import EVENT_HOMEASSISTANT_STARTED
from homeassistant.core import HomeAssistant
from homeassistant.helpers.storage import Store

from .const import DOMAIN, SCHEDULER_API_V3, FetchResult

_LOGGER = logging.getLogger(__name__)

_TEMPLATES_STORE_KEY = "foxess_templates_store"
_TEMPLATES_STORAGE_KEY = "foxess.templates"
_TEMPLATES_STORAGE_VERSION = 1
_CARD_SETUP_KEY = "foxess_scheduler_card_registered"
_CARD_STATIC_BASE = "/foxess_ha_static"
_CARD_JS_PREFIX = f"{_CARD_STATIC_BASE}/scheduler_card.js"


# Computed once at import time (blocking I/O is safe outside the event loop).
def _compute_card_url() -> str:
    card_file = Path(__file__).parent / "scheduler_card.js"
    try:
        digest = hashlib.md5(card_file.read_bytes()).hexdigest()[:8]
    except OSError:
        digest = "0"
    return f"{_CARD_JS_PREFIX}?v={digest}"


_CARD_URL = _compute_card_url()


def _is_remaining_group(g: dict) -> bool:
    """Return True if the group covers the full day (00:00–23:59)."""
    return (
        g.get("startHour") == 0
        and g.get("startMinute") == 0
        and g.get("endHour") == 23
        and g.get("endMinute") == 59
    )


def _result_message(result: FetchResult, resp: dict[str, Any] | None) -> str:
    """Return a user-facing message for a failed FoxESS Cloud call."""
    if resp is None:
        return "Network error — please try again."
    return resp.get("msg") or "FoxESS Cloud returned an error."


def _find_coordinator(hass: HomeAssistant, device_sn: str):
    """Return the coordinator for the FoxESS device with the given serial number."""
    for entry_info in hass.data.get(DOMAIN, {}).values():
        if not isinstance(entry_info, dict):
            continue
        coordinator = entry_info.get("coordinator")
        if getattr(coordinator, "devicesn", None) == device_sn:
            return coordinator
    return None


async def set_scheduler_flag(coordinator, enable: bool) -> tuple[FetchResult, str]:
    """Enable or disable the scheduler, updating the coordinator data on success."""
    result, resp, _ = await coordinator.client.async_set_scheduler_flag(
        coordinator.devicesn, coordinator.apiKey, enable
    )
    if result is not FetchResult.OK:
        _LOGGER.error("set_scheduler_flag: bad response %s", resp)
        return result, _result_message(result, resp)
    _LOGGER.debug("set_scheduler_flag: success, enable=%s", enable)
    coordinator.allData["schedulerEnabled"] = bool(enable)
    return FetchResult.OK, ""


async def set_scheduler_groups(coordinator, groups: list) -> tuple[FetchResult, str]:
    """Save the schedule to FoxESS Cloud using the device's scheduler API version."""
    if getattr(coordinator, "scheduler_api_version", None) == SCHEDULER_API_V3:
        return await _set_scheduler_groups_v3(coordinator, groups)
    return await _set_scheduler_groups_v2(coordinator, groups)


async def _set_scheduler_groups_v3(coordinator, groups: list) -> tuple[FetchResult, str]:
    """Save the schedule using the V3 API.

    All groups — including the 00:00–23:59 remaining slot — are sent directly to
    the V3 scheduler endpoint. V3 does not support per-group enable flags, and
    the remaining slot is a native first-class group in the API.
    """
    if not groups:
        return FetchResult.OK, ""
    result, resp, _ = await coordinator.client.async_set_scheduler_groups_v3(
        coordinator.devicesn, coordinator.apiKey, groups
    )
    if result is not FetchResult.OK:
        _LOGGER.error("set_scheduler_groups (V3): bad response %s", resp)
        return result, _result_message(result, resp)
    _LOGGER.debug("set_scheduler_groups (V3): success")
    return FetchResult.OK, ""


async def _set_scheduler_groups_v2(coordinator, groups: list) -> tuple[FetchResult, str]:
    """Save the schedule using the V2 API.

    The remaining time slot (00:00–23:59) is handled separately: its minSocOnGrid
    is written via the battery SoC settings and maxSoc via the MaxSoc device
    setting. It is NOT sent to the scheduler API, which does not handle it
    correctly.
    """
    client = coordinator.client
    devicesn = coordinator.devicesn
    api_key = coordinator.apiKey
    all_data = coordinator.allData

    remaining = next((g for g in groups if _is_remaining_group(g)), None)
    scheduled = [g for g in groups if not _is_remaining_group(g)]
    scheduler_was_enabled = bool(all_data.get("schedulerEnabled"))

    if remaining is not None:
        extra = remaining.get("extraParam", {})
        if scheduler_was_enabled:
            result, api_msg = await set_scheduler_flag(coordinator, False)
            if result is not FetchResult.OK:
                return result, api_msg

        current_min_soc = all_data.get("battery", {}).get("minSoc", 10)
        result, resp, _ = await client.async_set_battery_soc(
            devicesn,
            api_key,
            min_soc=current_min_soc,
            min_soc_on_grid=extra.get("minSocOnGrid", 10),
        )
        if result is not FetchResult.OK:
            return result, _result_message(result, resp)
        result, resp, _ = await client.async_set_device_setting(
            devicesn, api_key, "MaxSoc", str(extra.get("maxSoc", 100))
        )
        if result is not FetchResult.OK:
            return result, _result_message(result, resp)

    if not scheduled:
        if scheduler_was_enabled and remaining is not None:
            return await set_scheduler_flag(coordinator, True)
        return FetchResult.OK, ""

    result, resp, _ = await client.async_set_scheduler_groups(
        devicesn, api_key, scheduled
    )
    if result is not FetchResult.OK:
        _LOGGER.error("set_scheduler_groups: bad response %s", resp)
        return result, _result_message(result, resp)
    _LOGGER.debug("set_scheduler_groups: success")
    return FetchResult.OK, ""


def _send_failure(
    connection: websocket_api.ActiveConnection, msg: dict, result: FetchResult, api_msg: str
) -> None:
    if result is FetchResult.AUTH_FAILED:
        connection.send_error(msg["id"], websocket_api.ERR_UNAUTHORIZED, api_msg)
    else:
        connection.send_error(
            msg["id"],
            websocket_api.ERR_UNKNOWN_ERROR,
            "FoxESS Cloud returned an error: " + api_msg,
        )


@websocket_api.async_response
async def _ws_save_schedule(
    hass: HomeAssistant,
    connection: websocket_api.ActiveConnection,
    msg: dict,
) -> None:
    """Handle foxess/save_schedule WebSocket command — write groups to FoxESS Cloud."""
    device_sn = msg["deviceSN"]
    coordinator = _find_coordinator(hass, device_sn)
    if coordinator is None:
        connection.send_error(
            msg["id"], websocket_api.ERR_NOT_FOUND, f"No FoxESS device {device_sn}"
        )
        return
    result, api_msg = await set_scheduler_groups(coordinator, msg["groups"])
    if result is not FetchResult.OK:
        _send_failure(connection, msg, result, api_msg)
        return

    all_data = coordinator.allData
    all_data["schedulerGroups"] = msg["groups"]
    remaining = next((g for g in msg["groups"] if _is_remaining_group(g)), None)
    if remaining is not None:
        extra = remaining.get("extraParam", {})
        all_data["battery"]["minSocOnGrid"] = extra.get("minSocOnGrid")
    coordinator.async_set_updated_data(all_data)
    connection.send_result(msg["id"], {"ok": True})


@websocket_api.async_response
async def _ws_get_templates(
    hass: HomeAssistant,
    connection: websocket_api.ActiveConnection,
    msg: dict,
) -> None:
    """Handle foxess/get_templates WebSocket command — return saved schedule templates."""
    store = hass.data.get(_TEMPLATES_STORE_KEY)
    data = (await store.async_load()) or {}
    connection.send_result(msg["id"], {"templates": data.get(msg["deviceSN"], [])})


@websocket_api.async_response
async def _ws_save_template(
    hass: HomeAssistant,
    connection: websocket_api.ActiveConnection,
    msg: dict,
) -> None:
    """Handle foxess/save_template WebSocket command — persist a named schedule template."""
    store = hass.data.get(_TEMPLATES_STORE_KEY)
    data = (await store.async_load()) or {}
    templates = data.get(msg["deviceSN"], [])
    entry = {"name": msg["name"], "groups": msg["groups"]}
    idx = next((i for i, t in enumerate(templates) if t["name"] == msg["name"]), None)
    if idx is not None:
        templates[idx] = entry
    else:
        templates.append(entry)
    data[msg["deviceSN"]] = templates
    await store.async_save(data)
    connection.send_result(msg["id"], {"ok": True})


async def _register_lovelace_resource(hass: HomeAssistant) -> None:
    """Add or update the scheduler card JS as a Lovelace resource."""
    lovelace_data = hass.data.get(LOVELACE_DATA)
    if lovelace_data is None:
        return
    resources = lovelace_data.resources
    if not hasattr(resources, "async_create_item"):
        return  # YAML mode — resources are read-only

    target_url = _CARD_URL
    existing = next(
        (
            r
            for r in resources.async_items()
            if r.get("url", "").startswith(_CARD_JS_PREFIX)
        ),
        None,
    )
    try:
        if existing is None:
            await resources.async_create_item({"res_type": "module", "url": target_url})
            _LOGGER.debug("Registered FoxESS scheduler card as Lovelace resource")
        elif existing.get("url") != target_url:
            await resources.async_update_item(
                existing["id"], {"res_type": "module", "url": target_url}
            )
            _LOGGER.debug("Updated FoxESS scheduler card Lovelace resource URL")
    except Exception as err:  # noqa: BLE001
        _LOGGER.debug("Could not register/update Lovelace resource: %s", err)


async def async_setup_scheduler_card(hass: HomeAssistant) -> None:
    """Serve the scheduler card and register its WebSocket commands (once per HA run)."""
    if hass.data.get(_CARD_SETUP_KEY):
        return
    hass.data[_CARD_SETUP_KEY] = True

    if hass.http is not None:
        await hass.http.async_register_static_paths(
            [
                StaticPathConfig(
                    _CARD_STATIC_BASE,
                    str(Path(__file__).parent),
                    cache_headers=False,
                )
            ]
        )

    websocket_api.async_register_command(
        hass,
        "foxess/save_schedule",
        _ws_save_schedule,
        websocket_api.BASE_COMMAND_MESSAGE_SCHEMA.extend(
            {
                vol.Required("type"): "foxess/save_schedule",
                vol.Required("deviceSN"): str,
                vol.Required("groups"): list,
            }
        ),
    )
    websocket_api.async_register_command(
        hass,
        "foxess/get_templates",
        _ws_get_templates,
        websocket_api.BASE_COMMAND_MESSAGE_SCHEMA.extend(
            {
                vol.Required("type"): "foxess/get_templates",
                vol.Required("deviceSN"): str,
            }
        ),
    )
    websocket_api.async_register_command(
        hass,
        "foxess/save_template",
        _ws_save_template,
        websocket_api.BASE_COMMAND_MESSAGE_SCHEMA.extend(
            {
                vol.Required("type"): "foxess/save_template",
                vol.Required("deviceSN"): str,
                vol.Required("name"): str,
                vol.Required("groups"): list,
            }
        ),
    )

    hass.data[_TEMPLATES_STORE_KEY] = Store(
        hass, _TEMPLATES_STORAGE_VERSION, _TEMPLATES_STORAGE_KEY
    )

    if hass.is_running:
        await _register_lovelace_resource(hass)
    else:

        async def _on_ha_start(_event) -> None:
            await _register_lovelace_resource(hass)

        hass.bus.async_listen_once(EVENT_HOMEASSISTANT_STARTED, _on_ha_start)
