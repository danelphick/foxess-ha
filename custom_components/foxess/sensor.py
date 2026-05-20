"""Sensor platform for the FoxESS Home Assistant integration.

Fetches real-time inverter data, daily/monthly energy reports, and battery
settings from the FoxESS OpenAPI, and exposes them as Home Assistant sensor
entities.
"""

from __future__ import annotations

import asyncio
from datetime import datetime, timedelta
import enum
import hashlib
import json
import logging
from pathlib import Path
import time

import aiohttp
from dateutil import parser
import voluptuous as vol

from homeassistant.components import websocket_api
from homeassistant.components.http import StaticPathConfig
from homeassistant.components.lovelace.const import LOVELACE_DATA
from homeassistant.components.rest.data import RestData
from homeassistant.components.sensor import (
    PLATFORM_SCHEMA as SENSOR_PLATFORM_SCHEMA,
    SensorDeviceClass,
    SensorEntity,
    SensorStateClass,
)
from homeassistant.const import (
    CONF_NAME,
    CONF_PASSWORD,
    CONF_USERNAME,
    EVENT_HOMEASSISTANT_STARTED,
    PERCENTAGE,
    UnitOfElectricCurrent,
    UnitOfElectricPotential,
    UnitOfEnergy,
    UnitOfFrequency,
    UnitOfPower,
    UnitOfReactivePower,
    UnitOfTemperature,
)
from homeassistant.core import HomeAssistant
from homeassistant.exceptions import ConfigEntryAuthFailed
from homeassistant.helpers.aiohttp_client import async_get_clientsession
import homeassistant.helpers.config_validation as cv
from homeassistant.helpers.icon import icon_for_battery_level
from homeassistant.helpers.storage import Store
from homeassistant.helpers.update_coordinator import (
    CoordinatorEntity,
    DataUpdateCoordinator,
)
from homeassistant.util.ssl import SSLCipherList

_LOGGER = logging.getLogger(__name__)
_ENDPOINT_OA_DOMAIN = "https://www.foxesscloud.com"
_ENDPOINT_OA_BATTERY_SETTINGS = "/op/v0/device/battery/soc/get?sn="
_ENDPOINT_OA_REPORT = "/op/v0/device/report/query"
_ENDPOINT_OA_DEVICE_DETAIL = "/op/v0/device/detail"
_ENDPOINT_OA_DEVICE_DETAIL_V1 = "/op/v1/device/detail"
_ENDPOINT_OA_DEVICE_VARIABLES = "/op/v0/device/real/query"
_ENDPOINT_OA_DEVICE_VARIABLES_V1 = "/op/v1/device/real/query"
_ENDPOINT_OA_DAILY_GENERATION = "/op/v0/device/generation?sn="
_ENDPOINT_OA_SCHEDULER_SET_FLAG = "/op/v1/device/scheduler/set/flag"
_ENDPOINT_OA_SCHEDULER_SEGMENTS = "/op/v2/device/scheduler/get"
_ENDPOINT_OA_SCHEDULER_ENABLE = "/op/v2/device/scheduler/enable"
_ENDPOINT_OA_SCHEDULER_SEGMENTS_V3 = "/op/v3/device/scheduler/get"
_ENDPOINT_OA_SCHEDULER_ENABLE_V3 = "/op/v3/device/scheduler/enable"
_ENDPOINT_OA_DEVICE_SETTINGS_SET = "/op/v0/device/setting/set"
_ENDPOINT_OA_DEVICE_SETTINGS_GET = "/op/v0/device/setting/get"
_FOXESS_DEVICES_KEY = "foxess_devices"
_FOXESS_TEMPLATES_STORE_KEY = "foxess_templates_store"
_TEMPLATES_STORAGE_KEY = "foxess.templates"
_TEMPLATES_STORAGE_VERSION = 1
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

METHOD_POST = "POST"
METHOD_GET = "GET"
DEFAULT_ENCODING = "UTF-8"
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
DEFAULT_TIMEOUT = 75  # increase the size of inherited timeout, the API is a bit slow

ATTR_DEVICE_SN = "deviceSN"
ATTR_PLANTNAME = "plantName"
ATTR_MODULESN = "moduleSN"
ATTR_DEVICE_TYPE = "deviceType"
ATTR_MASTER = "masterVersion"
ATTR_MANAGER = "managerVersion"
ATTR_SLAVE = "slaveVersion"
ATTR_BATTERYLIST = "batteryList"
ATTR_LASTCLOUDSYNC = "lastCloudSync"

BATTERY_LEVELS = {"High": 80, "Medium": 50, "Low": 25, "Empty": 10}

CONF_APIKEY = "apiKey"
CONF_DEVICESN = "deviceSN"
CONF_DEVICEID = "deviceID"
CONF_SYSTEM_ID = "system_id"
CONF_EXTPV = "extendPV"
CONF_XTZONE = "xtZone"
CONF_GET_VARIABLES = "Restrict"
CONF_V1_API = "Use_V1_Api"
CONF_EVO = "Evo"
CONF_SCHEDULER_API_VERSION = "scheduler_api_version"
CONF_CAR_CHARGING_ENTITY = "car_charging_entity"

SCHEDULER_API_V2 = "v2"
SCHEDULER_API_V3 = "v3"
RETRY_NEXT_SLOT = -1
RETRY_IN_5_MINS = 25
_AUTH_ERRNO = {40256, 41808}  # Invalid/empty API key per FoxESS OpenAPI docs

# Key under hass.data where YAML-configured device info is stored so the
# config flow can detect conflicts and preserve the original deviceID.
YAML_CONFIGS_KEY = "foxess_yaml_configs"


class FetchResult(enum.Enum):
    """Result of a FoxESS Cloud API fetch call."""

    OK = "ok"
    ERROR = "error"
    AUTH_FAILED = "auth_failed"
    DNS_TIMEOUT = "dns_timeout"

    def __bool__(self) -> bool:
        """Return False for OK so callers can use `if not result:` for success."""
        return self is not FetchResult.OK


DEFAULT_NAME = "FoxESS"
DEFAULT_VERIFY_SSL = False  # True

SCAN_MINUTES = 1  # number of minutes betwen API requests
SCAN_INTERVAL = timedelta(minutes=SCAN_MINUTES)
_last_api: float = 0.0

PLATFORM_SCHEMA = SENSOR_PLATFORM_SCHEMA.extend(
    {
        vol.Optional(CONF_USERNAME): cv.string,
        vol.Optional(CONF_PASSWORD): cv.string,
        vol.Required(CONF_APIKEY): cv.string,
        vol.Required(CONF_DEVICESN): cv.string,
        vol.Required(CONF_DEVICEID): cv.string,
        vol.Optional(CONF_NAME, default=DEFAULT_NAME): cv.string,
        vol.Optional(CONF_EXTPV): cv.boolean,
        vol.Optional(CONF_XTZONE): cv.boolean,
        vol.Optional(CONF_GET_VARIABLES): cv.boolean,
        vol.Optional(CONF_V1_API): cv.boolean,
        vol.Optional(CONF_EVO): cv.boolean,
    }
)


async def async_setup_entry(hass, config_entry, async_add_entities):
    """Set up FoxESS sensors from a config entry."""
    await _async_setup_foxess(
        hass,
        config_entry.data,
        async_add_entities,
        config_entry,
    )


async def async_setup_platform(hass, config, async_add_entities, discovery_info=None):
    """Set up the FoxESS sensor."""
    # Advertise YAML config so the config flow can detect conflicts and
    # preserve the original deviceID (which may differ from deviceSN).
    yaml_configs = hass.data.setdefault(YAML_CONFIGS_KEY, {})
    yaml_configs[config[CONF_DEVICESN]] = {
        CONF_DEVICEID: config.get(CONF_DEVICEID),
        CONF_NAME: config.get(CONF_NAME, DEFAULT_NAME),
    }
    await _async_setup_foxess(hass, config, async_add_entities)


async def _fetch_device_detail(
    hass,
    allData: dict,
    devicesn: str,
    apiKey: str,
    Evo: bool,
    V1_Api: bool,
    config_entry,
) -> FetchResult:
    """Fetch device detail from FoxESS Cloud.

    Returns AUTH_FAILED (after logging) when the API key is rejected and
    config_entry is None (YAML config). Raises ConfigEntryAuthFailed when
    config_entry is set. Returns the FetchResult on success or other error.
    """
    if Evo:
        geterror = await getOADeviceList(hass, allData, devicesn, apiKey)
    else:
        geterror = await getOADeviceDetail(
            hass, allData, devicesn, apiKey, v1_api=V1_Api
        )
    if geterror is FetchResult.AUTH_FAILED:
        if config_entry is not None:
            raise ConfigEntryAuthFailed("FoxESS API key rejected")
        _LOGGER.error(
            "FoxESS API authentication failed. "
            "Update your apiKey in configuration.yaml and restart."
        )
        return geterror
    return geterror


async def _fetch_live_data(
    hass,
    allData: dict,
    devicesn: str,
    apiKey: str,
    V1_Api: bool,
    RestrictGetVar: bool,
    xtzone: bool,
    config_entry,
    statetest: int,
    tslice: int,
) -> tuple[FetchResult, int]:
    """Fetch raw sensor data and optional reports from FoxESS Cloud.

    Called when the inverter is online (statetest 1 or 2). Returns the final
    FetchResult and the (possibly adjusted) tslice. Returns AUTH_FAILED without
    raising on YAML config auth failure; raises ConfigEntryAuthFailed when
    config_entry is set.
    """
    allData["online"] = True
    if tslice == 0:
        # read in battery settings if fitted at startup, then every 60 mins
        await getOABatterySettings(hass, allData, devicesn, apiKey)
        await asyncio.sleep(1)  # OpenAPI demand
        sched_ver = (
            hass.data.get(_FOXESS_DEVICES_KEY, {})
            .get(devicesn, {})
            .get(CONF_SCHEDULER_API_VERSION, SCHEDULER_API_V2)
        )
        if sched_ver == SCHEDULER_API_V3:
            await getSchedulerSegmentsV3(hass, allData, devicesn, apiKey)
        else:
            await getSchedulerSegments(hass, allData, devicesn, apiKey)
        await asyncio.sleep(1)  # OpenAPI demand
    # main real time data fetch, followed by reports
    geterror = await getRaw(
        hass,
        allData,
        apiKey,
        devicesn,
        v1_api=V1_Api,
        restrict_get_var=RestrictGetVar,
        xtzone=xtzone,
    )
    if geterror is FetchResult.AUTH_FAILED:
        if config_entry is not None:
            raise ConfigEntryAuthFailed("FoxESS API key rejected")
        _LOGGER.error(
            "FoxESS API authentication failed. "
            "Update your apiKey in configuration.yaml and restart."
        )
        return geterror, tslice
    if not geterror:
        if tslice % 15 == 0:  # do at startup and every 15 minutes
            await asyncio.sleep(1)  # OpenAPI demand limit
            geterror = await getReport(hass, allData, apiKey, devicesn)
            if not geterror:
                if tslice == 0:
                    # get daily generation at startup, then every 60 minutes
                    await asyncio.sleep(1)  # OpenAPI demand
                    geterror = await getReportDailyGeneration(
                        hass, allData, apiKey, devicesn
                    )
                    if geterror:
                        _LOGGER.debug("getReportDailyGeneration False")
            else:
                _LOGGER.debug("getReport False")
            if geterror:
                geterror = FetchResult.OK
                allData["online"] = False
                tslice = RETRY_IN_5_MINS  # retry in 5 minutes
    else:
        _LOGGER.debug("get variables failed")
        if statetest == 2:
            # The inverter is in alarm, don't check every minute
            _LOGGER.debug(
                "Inverter in alarm, slowing retry response for SN: %s",
                devicesn,
            )
            allData["online"] = False
            tslice = RETRY_IN_5_MINS  # retry in 5 minutes
        elif geterror is FetchResult.DNS_TIMEOUT:
            _LOGGER.warning("Fox Cloud - DNS fail, retry in 1 minute")
            # retry in 1 minute
            if tslice != 0:
                tslice = tslice - 1
            else:
                tslice = RETRY_NEXT_SLOT
        else:
            # The get variables api call failed, leave it 5 minutes
            _LOGGER.debug("slowing retry response for SN: %s", devicesn)
            allData["online"] = False
            tslice = RETRY_IN_5_MINS  # retry in 5 minutes
        geterror = FetchResult.OK
    return geterror, tslice


async def _async_update_data(
    hass,
    allData: dict,
    devicesn: str,
    apiKey: str,
    Evo: bool,
    V1_Api: bool,
    RestrictGetVar: bool,
    xtzone: bool,
    config_entry,
    name: str,
    timeslice: dict,
) -> dict:
    """Fetch updated sensor data from FoxESS Cloud."""
    _LOGGER.debug("Updating data from https://www.foxesscloud.com/")
    hournow = datetime.now().strftime("%H")  # update hour now
    _LOGGER.debug("Time now: %s, last %s", hournow, timeslice["last_hour"])
    tslice = timeslice[devicesn] + 1  # increment current device time slice
    timeslice[devicesn] = tslice
    updated = False
    if tslice % 5 == 0:
        _LOGGER.debug("Main Poll, interval: %s, %s", devicesn, timeslice[devicesn])
        # try the openapi see if we get a response
        updated = True
        geterror = FetchResult.OK
        if tslice % 15 == 0:
            # get device detail at startup, then every 15 minutes to save api calls
            geterror = await _fetch_device_detail(
                hass, allData, devicesn, apiKey, Evo, V1_Api, config_entry
            )
            if geterror is FetchResult.AUTH_FAILED:
                return allData
            await asyncio.sleep(1)  # OpenAPI demand
        if not geterror:
            if allData["addressbook"]["status"] is not None:
                statetest = int(allData["addressbook"]["status"])
                if statetest == 3:
                    allData["raw"]["runningState"] = "164"  # off-grid
            else:
                statetest = 0
            _LOGGER.debug(" Statetest %s", statetest)
            if statetest in [1, 2]:
                geterror, tslice = await _fetch_live_data(
                    hass,
                    allData,
                    devicesn,
                    apiKey,
                    V1_Api,
                    RestrictGetVar,
                    xtzone,
                    config_entry,
                    statetest,
                    tslice,
                )
                if geterror is FetchResult.AUTH_FAILED:
                    return allData
            elif statetest == 3:
                # The inverter is off-line, no raw data polling, don't update entities
                # retry device detail call every 5 minutes until it comes back on-line
                allData["online"] = False
                tslice = RETRY_IN_5_MINS  # retry in 5 minutes
                _LOGGER.debug("Inverter off-line for SN: %s", devicesn)

            if not allData["online"]:
                if not geterror:
                    _LOGGER.warning("%s Inverter is off-line, waiting to retry", name)
                else:
                    _LOGGER.warning("%s Cloud timeout, retry in 1 minute", name)
        else:
            _LOGGER.warning(
                "%s Cloud timeout on Device Detail, retry in 1 minute.", name
            )

        if geterror is not FetchResult.OK:
            allData["online"] = False
            if tslice != 0:
                tslice = tslice - 1
                # failed to get specific detail so retry slot in 1 minute
            else:
                tslice = (
                    RETRY_NEXT_SLOT  # failed to get full data, try again in 1 minute
                )

    # actions here are every minute
    if tslice >= 59:
        tslice = RETRY_NEXT_SLOT  # reset timeslot, ready for full data fetch at 0
    _LOGGER.debug("Auxilliary timeslice %s, %s", devicesn, tslice)

    timeslice["last_hour"] = hournow
    timeslice[devicesn] = tslice

    if updated:
        _LOGGER.debug(allData)

    return allData


async def _register_lovelace_resource(hass) -> None:
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


@websocket_api.async_response
async def _ws_save_schedule(
    hass: HomeAssistant,
    connection: websocket_api.ActiveConnection,
    msg: dict,
) -> None:
    """Handle foxess/save_schedule WebSocket command — write groups to FoxESS Cloud."""
    device_sn = msg["deviceSN"]
    devices = hass.data.get(_FOXESS_DEVICES_KEY, {})
    if device_sn not in devices:
        connection.send_error(
            msg["id"], websocket_api.ERR_NOT_FOUND, f"No FoxESS device {device_sn}"
        )
        return
    device_info = devices[device_sn]
    sched_ver = device_info.get(CONF_SCHEDULER_API_VERSION, SCHEDULER_API_V2)
    if sched_ver == SCHEDULER_API_V3:
        result, api_msg = await setSchedulerSegmentsV3(
            hass, device_sn, device_info["apiKey"], msg["groups"]
        )
    else:
        result, api_msg = await setSchedulerSegments(
            hass, device_sn, device_info["apiKey"], msg["groups"]
        )
    if result is FetchResult.OK:
        device_data = devices[device_sn]
        all_data = device_data.get("allData")
        coord = device_data.get("coordinator")
        if all_data is not None and coord is not None:
            all_data["scheduler"]["groups"] = msg["groups"]
            remaining = next(
                (g for g in msg["groups"] if _is_remaining_group(g)), None
            )
            if remaining is not None:
                extra = remaining.get("extraParam", {})
                all_data["battery"]["minSocOnGrid"] = extra.get("minSocOnGrid")
            coord.async_set_updated_data(all_data)
        connection.send_result(msg["id"], {"ok": True})
    elif result is FetchResult.AUTH_FAILED:
        connection.send_error(msg["id"], websocket_api.ERR_UNAUTHORIZED, api_msg)
    else:
        connection.send_error(
            msg["id"],
            websocket_api.ERR_UNKNOWN_ERROR,
            "FoxESS Cloud returned an error: " + api_msg,
        )


@websocket_api.async_response
async def _ws_set_scheduler_flag(
    hass: HomeAssistant,
    connection: websocket_api.ActiveConnection,
    msg: dict,
) -> None:
    """Handle foxess/set_scheduler_flag WebSocket command — enable or disable the scheduler."""
    device_sn = msg["deviceSN"]
    devices = hass.data.get(_FOXESS_DEVICES_KEY, {})
    if device_sn not in devices:
        connection.send_error(
            msg["id"], websocket_api.ERR_NOT_FOUND, f"No FoxESS device {device_sn}"
        )
        return
    enable = msg["enable"]
    result, api_msg = await setSchedulerFlag(
        hass, device_sn, devices[device_sn]["apiKey"], enable
    )
    if result is FetchResult.OK:
        device_data = devices[device_sn]
        all_data = device_data.get("allData")
        coord = device_data.get("coordinator")
        if all_data is not None and coord is not None:
            all_data["scheduler"]["enabled"] = bool(enable)
            coord.async_set_updated_data(all_data)
        connection.send_result(msg["id"], {"ok": True})
    elif result is FetchResult.AUTH_FAILED:
        connection.send_error(msg["id"], websocket_api.ERR_UNAUTHORIZED, api_msg)
    else:
        connection.send_error(
            msg["id"],
            websocket_api.ERR_UNKNOWN_ERROR,
            "FoxESS Cloud returned an error: " + api_msg,
        )


@websocket_api.async_response
async def _ws_get_templates(
    hass: HomeAssistant,
    connection: websocket_api.ActiveConnection,
    msg: dict,
) -> None:
    """Handle foxess/get_templates WebSocket command — return saved schedule templates."""
    store = hass.data.get(_FOXESS_TEMPLATES_STORE_KEY)
    data = (await store.async_load()) or {}
    connection.send_result(msg["id"], {"templates": data.get(msg["deviceSN"], [])})


@websocket_api.async_response
async def _ws_save_template(
    hass: HomeAssistant,
    connection: websocket_api.ActiveConnection,
    msg: dict,
) -> None:
    """Handle foxess/save_template WebSocket command — persist a named schedule template."""
    store = hass.data.get(_FOXESS_TEMPLATES_STORE_KEY)
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


async def _async_setup_foxess(hass, config, async_add_entities, config_entry=None):
    """Shared setup logic for platform and config entry."""
    name = config.get(CONF_NAME)
    deviceID = config.get(CONF_DEVICEID)
    devicesn = config.get(CONF_DEVICESN)
    apiKey = config.get(CONF_APIKEY)
    ExtPV = config.get(CONF_EXTPV)
    xtzone = config.get(CONF_XTZONE)
    RestrictGetVar = config.get(CONF_GET_VARIABLES)
    V1_Api = config.get(CONF_V1_API)
    Evo = config.get(CONF_EVO)
    _LOGGER.debug("API Key: %s", apiKey)
    _LOGGER.debug("Device SN: %s", devicesn)
    _LOGGER.debug("Device ID: %s", deviceID)
    _LOGGER.debug("FoxESS Scan Interval: %s minutes", SCAN_MINUTES)
    _LOGGER.debug("Cross Time Zone: %s", xtzone)
    _LOGGER.debug("Restrict Variables: %s", RestrictGetVar)
    _LOGGER.debug("Extended PV: %s", ExtPV)
    _LOGGER.debug("v1 Api Calls: %s", V1_Api)
    _LOGGER.debug("EVO: %s", Evo)
    if V1_Api is not False:
        V1_Api = True
        _LOGGER.debug("v1 Api Calls Enabled")
    else:
        _LOGGER.warning("v1 Api Calls Disabled, using v0")
    if ExtPV is not True:
        ExtPV = False
        _LOGGER.debug("Extended PV Disabled")
    else:
        _LOGGER.warning("Extended PV 1-18 strings enabled")
    if RestrictGetVar is not True:
        RestrictGetVar = False
        _LOGGER.debug("Get Variables is full variable mode")
    else:
        _LOGGER.warning("Get Variables is in restricted mode")
    timeslice = {devicesn: RETRY_NEXT_SLOT, "last_hour": 0}
    allData = {
        "report": {},
        "reportDailyGeneration": {},
        "raw": {},
        "battery": {},
        "addressbook": {},
        "scheduler": {"enabled": None, "groups": []},
        "online": False,
    }
    allData["addressbook"]["hasBattery"] = False  # assume no battery is fitted for now
    allData["addressbook"]["status"] = "3"  # assume inverter is off-line for now

    scheduler_api_version = config.get(CONF_SCHEDULER_API_VERSION, SCHEDULER_API_V2)
    device_entry: dict = {
        "apiKey": apiKey,
        CONF_SCHEDULER_API_VERSION: scheduler_api_version,
    }
    hass.data.setdefault(_FOXESS_DEVICES_KEY, {})[devicesn] = device_entry

    async def _update_callback() -> dict:
        return await _async_update_data(
            hass,
            allData,
            devicesn,
            apiKey,
            Evo,
            V1_Api,
            RestrictGetVar,
            xtzone,
            config_entry,
            name,
            timeslice,
        )

    coordinator = DataUpdateCoordinator(
        hass,
        _LOGGER,
        name=DEFAULT_NAME,
        update_method=_update_callback,
        update_interval=SCAN_INTERVAL,
        config_entry=config_entry,
    )

    device_entry["allData"] = allData
    device_entry["coordinator"] = coordinator

    await coordinator.async_refresh()

    if not coordinator.last_update_success:
        _LOGGER.error(
            "FoxESS Cloud initialisation failed, Fatal Error - correct error and restart Home Assistant"
        )
        return False

    car_entity = config.get(CONF_CAR_CHARGING_ENTITY)
    if car_entity and config_entry is not None:
        from .car_charging import CarChargingManager  # noqa: PLC0415

        manager = CarChargingManager(hass, devicesn, apiKey, coordinator, allData)
        await manager.async_setup(car_entity)
        config_entry.async_on_unload(manager.async_teardown)

    def make(cls, *args):
        return cls(coordinator, name, deviceID, *args)

    async_add_entities(
        [
            *(
                entity
                for i in range(1, 7)
                for entity in (
                    make(
                        FoxESSCurrent,
                        f"PV{i} Current",
                        f"pv{i}-current",
                        f"pv{i}Current",
                    ),
                    make(FoxESSPower, f"PV{i} Power", f"pv{i}-power", f"pv{i}Power"),
                    make(FoxESSVolt, f"PV{i} Volt", f"pv{i}-volt", f"pv{i}Volt"),
                )
            ),
            make(FoxESSPower, "PV Power", "pv-power", "pvPower"),
            *(
                entity
                for phase in ("R", "S", "T")
                for entity in (
                    make(
                        FoxESSCurrent,
                        f"{phase} Current",
                        f"{phase.lower()}-current",
                        f"{phase}Current",
                    ),
                    make(
                        FoxESSFreq,
                        f"{phase} Freq",
                        f"{phase.lower()}-freq",
                        f"{phase}Freq",
                    ),
                    make(
                        FoxESSPower,
                        f"{phase} Power",
                        f"{phase.lower()}-power",
                        f"{phase}Power",
                    ),
                    make(
                        FoxESSVolt,
                        f"{phase} Volt",
                        f"{phase.lower()}-volt",
                        f"{phase}Volt",
                    ),
                )
            ),
            make(FoxESSPowerString, "Meter2 Power", "meter2-power", "meterPower2"),
            make(FoxESSReactivePower),
            make(FoxESSPowerFactor),
            make(FoxESSTemp, "Bat Temperature", "bat-temperature", "batTemperature"),
            make(
                FoxESSTemp, "Bat Temperature2", "bat-temperature2", "batTemperature_2"
            ),
            make(
                FoxESSTemp,
                "Ambient Temperature",
                "ambient-temperature",
                "ambientTemperation",
            ),
            make(
                FoxESSTemp, "Boost Temperature", "boost-temperature", "boostTemperation"
            ),
            make(FoxESSTemp, "Inv Temperature", "inv-temperature", "invTemperation"),
            make(FoxESSBatSoC, "Bat SoC", "bat-soc", "SoC"),
            make(FoxESSBatSoC, "Bat SoC1", "bat-soc1", "SoC_1"),
            make(FoxESSBatSoC, "Bat SoC2", "bat-soc2", "SoC_2"),
            make(FoxESSBatSoC, "Bat SoH", "bat-soh", "SOH"),
            make(FoxESSPower, "Inverter Bat Power", "inv-Bat-Power", "invBatPower"),
            make(FoxESSPower, "Inverter Bat Power2", "inv-Bat-Power2", "invBatPower_2"),
            make(FoxESSBatMinSoC),
            make(FoxESSBatMinSoConGrid),
            make(FoxESSSolarPower),
            make(FoxESSEnergyThroughput),
            make(FoxESSEnergySolar),
            make(FoxESSInverter),
            make(
                FoxESSPowerString,
                "Generation Power",
                "-generation-power",
                "generationPower",
            ),
            make(
                FoxESSPowerString,
                "Grid Consumption Power",
                "grid-consumption-power",
                "gridConsumptionPower",
            ),
            make(FoxESSPowerString, "FeedIn Power", "feedIn-power", "feedinPower"),
            make(
                FoxESSPowerString,
                "Bat Discharge Power",
                "bat-discharge-power",
                "batDischargePower",
            ),
            make(
                FoxESSPowerString,
                "Bat Charge Power",
                "bat-charge-power",
                "batChargePower",
            ),
            make(FoxESSPowerString, "Load Power", "load-power", "loadsPower"),
            make(
                FoxESSEnergyGenerated, "Energy Generated", "energy-generated", "value"
            ),
            make(
                FoxESSEnergyGenerated,
                "Energy Generated Month",
                "energy-generated-month",
                "month",
            ),
            make(
                FoxESSEnergyGenerated,
                "Energy Generated Cumulative",
                "energy-generated-cumulative",
                "cumulative",
            ),
            make(FoxESSEnergyGridConsumption),
            make(FoxESSEnergyFeedin),
            make(FoxESSEnergyBatCharge),
            make(FoxESSEnergyBatDischarge),
            make(FoxESSEnergyLoad),
            make(FoxESSPVEnergyTotal),
            make(FoxESSResidualEnergy),
            make(FoxESSResponseTime),
            make(FoxESSMaxBatChargeCurrent),
            make(FoxESSMaxBatDischargeCurrent),
            make(FoxESSRunningState, "Running State", "running-state", "runningState"),
            make(FoxESSSchedulerEnabled),
            make(FoxESSSchedulerGroups, devicesn, scheduler_api_version),
        ]
    )

    if ExtPV:
        async_add_entities(
            [
                entity
                for i in range(7, 19)
                for entity in (
                    make(
                        FoxESSCurrent,
                        f"PV{i} Current",
                        f"pv{i}-current",
                        f"pv{i}Current",
                    ),
                    make(FoxESSPower, f"PV{i} Power", f"pv{i}-power", f"pv{i}Power"),
                    make(FoxESSVolt, f"PV{i} Volt", f"pv{i}-volt", f"pv{i}Volt"),
                )
            ]
        )

    _registered_key = "foxess_card_static_registered"
    if not hass.data.get(_registered_key):
        await hass.http.async_register_static_paths(
            [
                StaticPathConfig(
                    _CARD_STATIC_BASE,
                    hass.config.path("custom_components/foxess"),
                    cache_headers=False,
                )
            ]
        )
        hass.data[_registered_key] = True

    _ws_key = "foxess_ws_registered"
    if not hass.data.get(_ws_key):
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
            "foxess/set_scheduler_flag",
            _ws_set_scheduler_flag,
            websocket_api.BASE_COMMAND_MESSAGE_SCHEMA.extend(
                {
                    vol.Required("type"): "foxess/set_scheduler_flag",
                    vol.Required("deviceSN"): str,
                    vol.Required("enable"): int,
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
        hass.data[_ws_key] = True

    if _FOXESS_TEMPLATES_STORE_KEY not in hass.data:
        hass.data[_FOXESS_TEMPLATES_STORE_KEY] = Store(
            hass, _TEMPLATES_STORAGE_VERSION, _TEMPLATES_STORAGE_KEY
        )

    if hass.is_running:
        await _register_lovelace_resource(hass)
    else:

        async def _on_ha_start(_event) -> None:
            await _register_lovelace_resource(hass)

        hass.bus.async_listen_once(EVENT_HOMEASSISTANT_STARTED, _on_ha_start)

    return None


class GetAuth:
    """Generates authentication headers for FoxESS Cloud API requests."""

    def get_signature(self, token, path, lang="en"):
        """Generate headers for FoxESS Cloud authentication.

        This function is used to generate a signature consisting of URL, token, and timestamp, and return a dictionary containing the signature and other information.
            :param token: your key
            :param path:  your request path
            :param lang: language, default is English.
            :return: with authentication header
        """
        timestamp = round(time.time() * 1000)
        signature = rf"{path}\r\n{token}\r\n{timestamp}"
        # or use user_agent_rotator.get_random_user_agent() for user-agent
        return {
            "token": token,
            "lang": lang,
            "timestamp": str(timestamp),
            "Content-Type": "application/json",
            "signature": self.md5c(text=signature),
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/117.0.0.0 Safari/537.36",
            "Connection": "close",
        }

    @staticmethod
    def md5c(text="", _type="lower"):
        """Return MD5 hash of text, lowercase by default or uppercase when _type is 'upper'."""
        res = hashlib.md5(text.encode(encoding="UTF-8")).hexdigest()
        if _type.__eq__("lower"):
            return res
        return res.upper()


async def waitforAPI():
    """Enforce the FoxESS API minimum 1-second interval between calls."""
    global _last_api  # noqa: PLW0603
    # wait for openAPI, there is a minimum of 1 second allowed between OpenAPI query calls
    # check if _last_api call was less than a second ago and if so delay the balance of 1 second
    now = time.time()
    last = _last_api
    diff = now - last if last != 0 else 1
    diff = round((diff + 0.2), 2)
    if diff < 1:
        await asyncio.sleep(diff)
        _LOGGER.debug("API enforced delay, wait: %s", diff)
    _last_api = time.time()
    return False


async def getOADeviceDetail(hass, allData, devicesn, apiKey, *, v1_api: bool):
    """Fetch device detail from FoxESS OpenAPI and populate allData['addressbook']."""
    await waitforAPI()

    if v1_api:
        path = _ENDPOINT_OA_DEVICE_DETAIL_V1
        _LOGGER.debug("Device Detail using V1 API")
    else:
        path = _ENDPOINT_OA_DEVICE_DETAIL

    headerData = GetAuth().get_signature(token=apiKey, path=path)

    path = _ENDPOINT_OA_DOMAIN + path + "?sn="
    _LOGGER.debug("OADevice Detail fetch %s%s", path, devicesn)
    timestamp = round(time.time() * 1000)

    restOADeviceDetail = RestData(
        hass,
        METHOD_GET,
        path + devicesn,
        DEFAULT_ENCODING,
        None,
        headerData,
        None,
        None,
        DEFAULT_VERIFY_SSL,
        SSLCipherList.PYTHON_DEFAULT,
        DEFAULT_TIMEOUT,
    )
    await restOADeviceDetail.async_update()

    if restOADeviceDetail.data is None or restOADeviceDetail.data == "":
        _LOGGER.debug("Unable to get OA Device Detail from FoxESS Cloud")
        return FetchResult.ERROR

    response = json.loads(restOADeviceDetail.data)
    if response["errno"] == 0 and (
        response["msg"] == "success" or response["msg"] == "Operation successful"
    ):
        allData["raw"]["ResponseTime"] = max(round(time.time() * 1000) - timestamp, 0)
        _LOGGER.debug("OA Device Detail Good Response: %s", response["result"])
        result = response["result"]
        allData["addressbook"] = result
        # manually poke this in as on the old cloud it was called plantname, need to keep in line with old entity name
        plantName = result["stationName"]
        allData["addressbook"]["plantName"] = plantName
        testBattery = result["hasBattery"]
        if testBattery:
            _LOGGER.debug("OA Device Detail System has Battery: %s", testBattery)
        else:
            _LOGGER.debug("OA Device Detail System has No Battery: %s", testBattery)
            allData["addressbook"][ATTR_BATTERYLIST] = "No Battery"
        return FetchResult.OK

    _LOGGER.error("OA Device Detail Bad Response: %s", response)
    return (
        FetchResult.AUTH_FAILED
        if response["errno"] in _AUTH_ERRNO
        else FetchResult.ERROR
    )


async def getOADeviceList(hass, allData, devicesn, apiKey):
    """Fetch the device list from FoxESS OpenAPI and populate allData['addressbook']."""
    await waitforAPI()

    path = "/op/v0/device/list"
    headerData = GetAuth().get_signature(token=apiKey, path=path)

    path = _ENDPOINT_OA_DOMAIN + "/op/v0/device/list"
    _LOGGER.debug("OADevice List fetch %s%s", path, devicesn)
    timestamp = round(time.time() * 1000)

    listData = '{ "currentPage": 1, "pageSize": 10}'

    restOADeviceList = RestData(
        hass,
        METHOD_POST,
        path,
        DEFAULT_ENCODING,
        None,
        headerData,
        None,
        listData,
        DEFAULT_VERIFY_SSL,
        SSLCipherList.PYTHON_DEFAULT,
        DEFAULT_TIMEOUT,
    )
    await restOADeviceList.async_update()

    if restOADeviceList.data is None or restOADeviceList.data == "":
        _LOGGER.debug("Unable to get OA Device List from FoxESS Cloud")
        return FetchResult.ERROR

    response = json.loads(restOADeviceList.data)
    if response["errno"] == 0 and (
        response["msg"] == "success" or response["msg"] == "Operation successful"
    ):
        allData["raw"]["ResponseTime"] = max(round(time.time() * 1000) - timestamp, 0)
        _LOGGER.debug("OA Device List Good Response: %s", response["result"])
        result = json.loads(restOADeviceList.data)["result"]["data"]
        for item in result:
            _LOGGER.debug("OA Device List item: %s", item)
            break
        allData["addressbook"] = item
        plantName = item["stationName"]
        allData["addressbook"]["plantName"] = plantName
        allData["addressbook"]["masterVersion"] = "not provided"
        allData["addressbook"]["managerVersion"] = "not provided"
        allData["addressbook"]["slaveVersion"] = "not provided"
        allData["addressbook"]["batteryList"] = "not provided"
        testBattery = item["hasBattery"]
        if testBattery:
            _LOGGER.debug("OA Device List System has Battery: %s", testBattery)
        else:
            _LOGGER.debug("OA Device List System has No Battery: %s", testBattery)
            allData["addressbook"][ATTR_BATTERYLIST] = "No Battery"

        return FetchResult.OK

    _LOGGER.error("OA Device List Bad Response: %s", response)
    return (
        FetchResult.AUTH_FAILED
        if response["errno"] in _AUTH_ERRNO
        else FetchResult.ERROR
    )


async def getOABatterySettings(hass, allData, devicesn, apiKey):
    """Fetch battery SoC settings from FoxESS OpenAPI and populate allData['battery']."""
    await waitforAPI()  # check for api delay

    path = "/op/v0/device/battery/soc/get"
    headerData = GetAuth().get_signature(token=apiKey, path=path)

    path = _ENDPOINT_OA_DOMAIN + _ENDPOINT_OA_BATTERY_SETTINGS
    if "hasBattery" not in allData["addressbook"]:
        hasBattery = False
    else:
        hasBattery = allData["addressbook"]["hasBattery"]

    if hasBattery:
        # only make this call if device detail reports battery fitted
        _LOGGER.debug("OABattery Settings fetch %s %s", path, devicesn)
        restOABatterySettings = RestData(
            hass,
            METHOD_GET,
            path + devicesn,
            DEFAULT_ENCODING,
            None,
            headerData,
            None,
            None,
            DEFAULT_VERIFY_SSL,
            SSLCipherList.PYTHON_DEFAULT,
            DEFAULT_TIMEOUT,
        )
        await restOABatterySettings.async_update()

        if restOABatterySettings.data is None:
            _LOGGER.debug("Unable to get OA Battery Settings from FoxESS Cloud")
            return FetchResult.ERROR

        response = json.loads(restOABatterySettings.data)
        if response["errno"] == 0 and (
            response["msg"] == "success" or response["msg"] == "Operation successful"
        ):
            _LOGGER.debug("OA Battery Settings Good Response: %s", response["result"])
            result = response["result"]
            minSoc = result["minSoc"]
            minSocOnGrid = result["minSocOnGrid"]
            allData["battery"]["minSoc"] = minSoc
            allData["battery"]["minSocOnGrid"] = minSocOnGrid
            _LOGGER.debug(
                "OA Battery Settings read MinSoc: %d, MinSocOnGrid: %d",
                minSoc,
                minSocOnGrid,
            )
            return FetchResult.OK

        _LOGGER.error("OA Battery Settings Bad Response: %s", response)
        return FetchResult.ERROR

    # device detail reports no battery fitted so reset these variables to show unknown
    allData["battery"]["minSoc"] = None
    allData["battery"]["minSocOnGrid"] = None
    return FetchResult.OK


async def getSchedulerSegments(hass, allData, devicesn, apiKey):
    """Fetch scheduler time segment groups from FoxESS OpenAPI and populate allData['scheduler']['groups']."""
    await waitforAPI()

    path = _ENDPOINT_OA_SCHEDULER_SEGMENTS
    headerData = GetAuth().get_signature(token=apiKey, path=path)

    _LOGGER.debug("getSchedulerSegments fetch %s", path)

    restSchedulerSegments = RestData(
        hass,
        METHOD_POST,
        _ENDPOINT_OA_DOMAIN + path,
        DEFAULT_ENCODING,
        None,
        headerData,
        None,
        '{"deviceSN":"' + devicesn + '"}',
        DEFAULT_VERIFY_SSL,
        SSLCipherList.PYTHON_DEFAULT,
        DEFAULT_TIMEOUT,
    )
    await restSchedulerSegments.async_update()

    if restSchedulerSegments.data is None or restSchedulerSegments.data == "":
        _LOGGER.debug("Unable to get scheduler segments from FoxESS Cloud")
        return FetchResult.ERROR

    response = json.loads(restSchedulerSegments.data)
    if response["errno"] == 0 and (
        response["msg"] == "success" or response["msg"] == "Operation successful"
    ):
        result = response["result"]
        if result is None:
            _LOGGER.debug(
                "Scheduler segments returned null — no cloud-side groups configured"
            )
            allData["scheduler"]["groups"] = []
        else:
            allData["scheduler"]["enabled"] = bool(int(result.get("enable", 0)))
            groups = result.get("groups", [])
            groups.sort(
                key=lambda g: (
                    g.get("endHour", 0) * 60 + g.get("endMinute", 0),
                    g.get("startHour", 0) * 60 + g.get("startMinute", 0),
                )
            )
            allData["scheduler"]["groups"] = groups
        return FetchResult.OK

    _LOGGER.debug("Scheduler segments bad response: %s", response)
    return (
        FetchResult.AUTH_FAILED
        if response["errno"] in _AUTH_ERRNO
        else FetchResult.ERROR
    )


def _is_remaining_group(g: dict) -> bool:
    """Return True if the group covers the full day (00:00–23:59)."""
    return (
        g.get("startHour") == 0
        and g.get("startMinute") == 0
        and g.get("endHour") == 23
        and g.get("endMinute") == 59
    )


async def _set_device_setting(
    hass: HomeAssistant,
    devicesn: str,
    apiKey: str,
    key: str,
    value: int | str,
) -> tuple[FetchResult, str]:
    """POST a single key/value pair to /op/v0/device/setting/set."""
    await waitforAPI()
    path = _ENDPOINT_OA_DEVICE_SETTINGS_SET
    headerData = GetAuth().get_signature(token=apiKey, path=path)
    session = async_get_clientsession(hass, verify_ssl=DEFAULT_VERIFY_SSL)
    try:
        timeout = aiohttp.ClientTimeout(total=DEFAULT_TIMEOUT)
        async with session.post(
            _ENDPOINT_OA_DOMAIN + path,
            headers=headerData,
            json={"sn": devicesn, "key": key, "value": str(value)},
            timeout=timeout,
        ) as resp:
            data = await resp.json(content_type=None)
    except Exception:
        _LOGGER.exception("_set_device_setting: network error (key=%s)", key)
        return FetchResult.ERROR, "Network error — please try again."

    if data.get("errno") == 0:
        _LOGGER.debug("_set_device_setting: success (key=%s)", key)
        return FetchResult.OK, ""

    _LOGGER.error("_set_device_setting: bad response (key=%s) %s", key, data)
    api_msg = data.get("msg") or "FoxESS Cloud returned an error."
    return (
        FetchResult.AUTH_FAILED if data.get("errno") in _AUTH_ERRNO else FetchResult.ERROR,
        api_msg,
    )


async def _get_device_setting(
    hass: HomeAssistant,
    devicesn: str,
    apiKey: str,
    key: str,
) -> tuple[FetchResult, str | None]:
    """GET /op/v0/device/setting/get for a single key; return (result, value_str)."""
    await waitforAPI()
    path = f"{_ENDPOINT_OA_DEVICE_SETTINGS_GET}?sn={devicesn}&key={key}"
    headerData = GetAuth().get_signature(token=apiKey, path=path)
    session = async_get_clientsession(hass, verify_ssl=DEFAULT_VERIFY_SSL)
    try:
        timeout = aiohttp.ClientTimeout(total=DEFAULT_TIMEOUT)
        async with session.get(
            _ENDPOINT_OA_DOMAIN + path, headers=headerData, timeout=timeout
        ) as resp:
            data = await resp.json(content_type=None)
    except Exception:
        _LOGGER.exception("_get_device_setting: network error (key=%s)", key)
        return FetchResult.ERROR, None
    if data.get("errno") == 0:
        return FetchResult.OK, data.get("result", {}).get("value")
    return (
        FetchResult.AUTH_FAILED if data.get("errno") in _AUTH_ERRNO else FetchResult.ERROR,
        None,
    )


async def _set_battery_soc(
    hass: HomeAssistant,
    devicesn: str,
    apiKey: str,
    min_soc: int,
    min_soc_on_grid: int,
) -> tuple[FetchResult, str]:
    """POST to /op/v0/device/battery/soc/set with minSoc and minSocOnGrid."""
    await waitforAPI()
    path = "/op/v0/device/battery/soc/set"
    headerData = GetAuth().get_signature(token=apiKey, path=path)
    session = async_get_clientsession(hass, verify_ssl=DEFAULT_VERIFY_SSL)
    try:
        timeout = aiohttp.ClientTimeout(total=DEFAULT_TIMEOUT)
        async with session.post(
            _ENDPOINT_OA_DOMAIN + path,
            headers=headerData,
            json={"sn": devicesn, "minSoc": min_soc, "minSocOnGrid": min_soc_on_grid},
            timeout=timeout,
        ) as resp:
            data = await resp.json(content_type=None)
    except Exception:
        _LOGGER.exception("_set_battery_soc: network error")
        return FetchResult.ERROR, "Network error — please try again."

    if data.get("errno") == 0:
        _LOGGER.debug("_set_battery_soc: success")
        return FetchResult.OK, ""

    _LOGGER.error("_set_battery_soc: bad response %s", data)
    api_msg = data.get("msg") or "FoxESS Cloud returned an error."
    return (
        FetchResult.AUTH_FAILED if data.get("errno") in _AUTH_ERRNO else FetchResult.ERROR,
        api_msg,
    )


async def setSchedulerSegments(
    hass: HomeAssistant, devicesn: str, apiKey: str, groups: list
) -> tuple[FetchResult, str]:
    """Save the schedule to FoxESS Cloud.

    The remaining time slot (00:00–23:59) is handled separately: its minSocOnGrid
    is written via /op/v0/device/battery/soc/set and maxSoc via /op/v0/device/setting/set.
    It is NOT sent to the scheduler API, which does not handle it correctly.
    """
    remaining = next((g for g in groups if _is_remaining_group(g)), None)
    scheduled = [g for g in groups if not _is_remaining_group(g)]

    devices_data = hass.data.get(_FOXESS_DEVICES_KEY, {})
    device_all_data = devices_data.get(devicesn, {}).get("allData", {})
    scheduler_was_enabled = bool(device_all_data.get("scheduler", {}).get("enabled"))

    if remaining is not None:
        extra = remaining.get("extraParam", {})
        if scheduler_was_enabled:
            result, api_msg = await setSchedulerFlag(hass, devicesn, apiKey, 0)
            if result is not FetchResult.OK:
                return result, api_msg

        current_min_soc = device_all_data.get("battery", {}).get("minSoc", 10)
        result, api_msg = await _set_battery_soc(
            hass, devicesn, apiKey,
            min_soc=current_min_soc,
            min_soc_on_grid=extra.get("minSocOnGrid", 10),
        )
        if result is not FetchResult.OK:
            return result, api_msg
        result, api_msg = await _set_device_setting(
            hass, devicesn, apiKey, "MaxSoc", extra.get("maxSoc", 100)
        )
        if result is not FetchResult.OK:
            return result, api_msg

    if not scheduled:
        if scheduler_was_enabled and remaining is not None:
            return await setSchedulerFlag(hass, devicesn, apiKey, 1)
        return FetchResult.OK, ""

    await waitforAPI()
    path = _ENDPOINT_OA_SCHEDULER_ENABLE
    headerData = GetAuth().get_signature(token=apiKey, path=path)
    session = async_get_clientsession(hass, verify_ssl=DEFAULT_VERIFY_SSL)
    try:
        timeout = aiohttp.ClientTimeout(total=DEFAULT_TIMEOUT)
        async with session.post(
            _ENDPOINT_OA_DOMAIN + path,
            headers=headerData,
            json={"deviceSN": devicesn, "groups": scheduled},
            timeout=timeout,
        ) as resp:
            data = await resp.json(content_type=None)
    except Exception:
        _LOGGER.exception("setSchedulerSegments: network error")
        return FetchResult.ERROR, "Network error — please try again."

    if data.get("errno") == 0:
        _LOGGER.debug("setSchedulerSegments: success")
        return FetchResult.OK, ""

    _LOGGER.error("setSchedulerSegments: bad response %s", data)
    api_msg = data.get("msg") or "FoxESS Cloud returned an error."
    return (
        FetchResult.AUTH_FAILED if data.get("errno") in _AUTH_ERRNO else FetchResult.ERROR,
        api_msg,
    )


async def setSchedulerFlag(
    hass: HomeAssistant, devicesn: str, apiKey: str, enable: int
) -> tuple[FetchResult, str]:
    """POST scheduler enable/disable flag to FoxESS Cloud /op/v1/device/scheduler/set/flag."""
    await waitforAPI()
    path = _ENDPOINT_OA_SCHEDULER_SET_FLAG
    headerData = GetAuth().get_signature(token=apiKey, path=path)
    session = async_get_clientsession(hass, verify_ssl=DEFAULT_VERIFY_SSL)
    try:
        timeout = aiohttp.ClientTimeout(total=DEFAULT_TIMEOUT)
        async with session.post(
            _ENDPOINT_OA_DOMAIN + path,
            headers=headerData,
            json={"deviceSN": devicesn, "enable": enable},
            timeout=timeout,
        ) as resp:
            data = await resp.json(content_type=None)
    except Exception:
        _LOGGER.exception("setSchedulerFlag: network error")
        return FetchResult.ERROR, "Network error — please try again."

    if data.get("errno") == 0:
        _LOGGER.debug("setSchedulerFlag: success, enable=%s", enable)
        return FetchResult.OK, ""

    _LOGGER.error("setSchedulerFlag: bad response %s", data)
    api_msg = data.get("msg") or "FoxESS Cloud returned an error."
    return (
        FetchResult.AUTH_FAILED if data.get("errno") in _AUTH_ERRNO else FetchResult.ERROR,
        api_msg,
    )


async def getSchedulerSegmentsV3(hass, allData, devicesn, apiKey):
    """Fetch scheduler time segment groups from FoxESS OpenAPI V3 and populate allData['scheduler']."""
    await waitforAPI()

    path = _ENDPOINT_OA_SCHEDULER_SEGMENTS_V3
    headerData = GetAuth().get_signature(token=apiKey, path=path)

    _LOGGER.debug("getSchedulerSegmentsV3 fetch %s", path)

    restSchedulerSegments = RestData(
        hass,
        METHOD_POST,
        _ENDPOINT_OA_DOMAIN + path,
        DEFAULT_ENCODING,
        None,
        headerData,
        None,
        '{"deviceSN":"' + devicesn + '"}',
        DEFAULT_VERIFY_SSL,
        SSLCipherList.PYTHON_DEFAULT,
        DEFAULT_TIMEOUT,
    )
    await restSchedulerSegments.async_update()

    if restSchedulerSegments.data is None or restSchedulerSegments.data == "":
        _LOGGER.debug("Unable to get scheduler segments (V3) from FoxESS Cloud")
        return FetchResult.ERROR

    response = json.loads(restSchedulerSegments.data)
    if response["errno"] == 0 and (
        response["msg"] == "success" or response["msg"] == "Operation successful"
    ):
        result = response["result"]
        if result is None:
            _LOGGER.debug(
                "Scheduler segments (V3) returned null — no cloud-side groups configured"
            )
            allData["scheduler"]["groups"] = []
        else:
            allData["scheduler"]["enabled"] = bool(int(result.get("enable", 0)))
            groups = result.get("groups", [])
            groups.sort(
                key=lambda g: (
                    g.get("endHour", 0) * 60 + g.get("endMinute", 0),
                    g.get("startHour", 0) * 60 + g.get("startMinute", 0),
                )
            )
            allData["scheduler"]["groups"] = groups
        return FetchResult.OK

    _LOGGER.debug("Scheduler segments (V3) bad response: %s", response)
    return (
        FetchResult.AUTH_FAILED
        if response["errno"] in _AUTH_ERRNO
        else FetchResult.ERROR
    )


async def setSchedulerSegmentsV3(
    hass: HomeAssistant, devicesn: str, apiKey: str, groups: list
) -> tuple[FetchResult, str]:
    """Save the schedule to FoxESS Cloud using the V3 API.

    All groups — including the 00:00–23:59 remaining slot — are sent directly to
    the V3 scheduler endpoint.  V3 does not support per-group enable flags, and
    the remaining slot is a native first-class group in the API.
    """
    if not groups:
        return FetchResult.OK, ""

    await waitforAPI()
    path = _ENDPOINT_OA_SCHEDULER_ENABLE_V3
    headerData = GetAuth().get_signature(token=apiKey, path=path)
    session = async_get_clientsession(hass, verify_ssl=DEFAULT_VERIFY_SSL)
    try:
        timeout = aiohttp.ClientTimeout(total=DEFAULT_TIMEOUT)
        async with session.post(
            _ENDPOINT_OA_DOMAIN + path,
            headers=headerData,
            json={"deviceSN": devicesn, "isDefault": False, "groups": groups},
            timeout=timeout,
        ) as resp:
            data = await resp.json(content_type=None)
    except Exception:
        _LOGGER.exception("setSchedulerSegmentsV3: network error")
        return FetchResult.ERROR, "Network error — please try again."

    if data.get("errno") == 0:
        _LOGGER.debug("setSchedulerSegmentsV3: success")
        return FetchResult.OK, ""

    _LOGGER.error("setSchedulerSegmentsV3: bad response %s", data)
    api_msg = data.get("msg") or "FoxESS Cloud returned an error."
    return (
        FetchResult.AUTH_FAILED if data.get("errno") in _AUTH_ERRNO else FetchResult.ERROR,
        api_msg,
    )


async def getReport(hass, allData, apiKey, devicesn):
    """Fetch monthly energy report data from FoxESS OpenAPI and populate allData['report']."""
    await waitforAPI()  # check for api delay

    path = _ENDPOINT_OA_REPORT
    headerData = GetAuth().get_signature(token=apiKey, path=path)

    path = _ENDPOINT_OA_DOMAIN + _ENDPOINT_OA_REPORT
    _LOGGER.debug("OA Report fetch %s ", path)

    now = datetime.now()
    month = str(datetime.now().month)  # now.strftime("%-m")

    reportData = (
        '{"sn":"'
        + devicesn
        + '","year":'
        + now.strftime("%Y")
        + ',"month":'
        + month
        + ',"dimension":"month","variables":["feedin","generation","gridConsumption","chargeEnergyToTal","dischargeEnergyToTal","loads","PVEnergyTotal"]}'
    )

    _LOGGER.debug("getReport OA request: %s", reportData)

    restOAReport = RestData(
        hass,
        METHOD_POST,
        path,
        DEFAULT_ENCODING,
        None,
        headerData,
        None,
        reportData,
        DEFAULT_VERIFY_SSL,
        SSLCipherList.PYTHON_DEFAULT,
        DEFAULT_TIMEOUT,
    )

    await restOAReport.async_update()

    if restOAReport.data is None or restOAReport.data == "":
        _LOGGER.debug("Unable to get OA Report from FoxESS Cloud")
        return FetchResult.ERROR

    # Openapi responded so process data
    response = json.loads(restOAReport.data)
    if response["errno"] == 0 and (
        response["msg"] == "success" or response["msg"] == "Operation successful"
    ):
        _LOGGER.debug(
            "OA Report Data fetched OK: %s %s ", response, restOAReport.data[:350]
        )
        result = json.loads(restOAReport.data)["result"]
        today = int(
            now.strftime("%d")
        )  # need today as an integer to locate in the monthly report index
        for item in result:
            variableName = item["variable"]
            # Daily reports break down the data hour by month for each day
            # so locate the current days index and use that as the sum
            index = 1
            cumulative_total = 0
            for dataItem in item["values"]:
                if today == index:  # we're only interested in the total for today
                    if dataItem is not None:
                        cumulative_total = dataItem
                    else:
                        _LOGGER.debug("Report month fetch, None received")
                    break
                index += 1
                # cumulative_total += dataItem
            allData["report"][variableName] = round(cumulative_total, 3)
            _LOGGER.debug(
                "OA Report Variable: %s, Total: %s", variableName, cumulative_total
            )
        return FetchResult.OK

    _LOGGER.debug("OA Report Bad Response: %s %s ", response, restOAReport.data)
    return FetchResult.ERROR


async def getReportDailyGeneration(hass, allData, apiKey, devicesn):
    """Fetch daily generation totals from FoxESS OpenAPI and populate allData['reportDailyGeneration']."""
    await waitforAPI()  # check for api delay

    path = "/op/v0/device/generation"
    headerData = GetAuth().get_signature(token=apiKey, path=path)

    path = _ENDPOINT_OA_DOMAIN + _ENDPOINT_OA_DAILY_GENERATION
    _LOGGER.debug("getReportDailyGeneration fetch %s ", path)

    generationData = '{"sn":"' + devicesn + '","dimension":"day"}'

    _LOGGER.debug("getReportDailyGeneration OA request: %s", generationData)

    restOAgen = RestData(
        hass,
        METHOD_GET,
        path + devicesn,
        DEFAULT_ENCODING,
        None,
        headerData,
        None,
        generationData,
        DEFAULT_VERIFY_SSL,
        SSLCipherList.PYTHON_DEFAULT,
        DEFAULT_TIMEOUT,
    )

    await restOAgen.async_update()

    if restOAgen.data is None or restOAgen.data == "":
        _LOGGER.debug("Unable to get OA Daily Generation Report from FoxESS Cloud")
        return FetchResult.ERROR

    response = json.loads(restOAgen.data)
    if response["errno"] == 0 and (
        response["msg"] == "success" or response["msg"] == "Operation successful"
    ):
        _LOGGER.debug(
            "OA Daily Generation Report Data fetched OK Response: %s",
            restOAgen.data[:500],
        )

        parsed = json.loads(restOAgen.data)["result"]
        for parsed_key, store_key in [
            ("today", "value"),
            ("month", "month"),
            ("cumulative", "cumulative"),
        ]:
            if parsed_key not in parsed:
                allData["reportDailyGeneration"][store_key] = 0
                _LOGGER.debug(
                    "OA Daily Generation Report data, %s has no value: %s set to 0",
                    parsed_key,
                    parsed,
                )
            else:
                allData["reportDailyGeneration"][store_key] = parsed[parsed_key]
                _LOGGER.debug(
                    "OA Daily Generation Report data: %s value %s",
                    parsed_key,
                    parsed[parsed_key],
                )
        return FetchResult.OK

    _LOGGER.debug(
        "OA Daily Generation Report Bad Response: %s %s ",
        response,
        restOAgen.data,
    )
    return FetchResult.ERROR


async def getRaw(
    hass, allData, apiKey, devicesn, *, v1_api: bool, restrict_get_var: bool, xtzone
):
    """Fetch real-time device variable data from FoxESS OpenAPI and populate allData['raw']."""
    await waitforAPI()  # check for api delay

    # "deviceSN" used for OpenAPI and it only fetches the real time data

    # build the devicesn string
    if v1_api:
        path = _ENDPOINT_OA_DEVICE_VARIABLES_V1
        _LOGGER.debug("Using V1 API")
        dsn = '{"sns":["' + devicesn + '"] '
    else:
        path = _ENDPOINT_OA_DEVICE_VARIABLES
        dsn = '{"sn":"' + devicesn + '" '

    if restrict_get_var:
        _LOGGER.debug("Getting Device Variable in restricted mode")

        dsn = (
            dsn
            + ',"variables":["ambientTemperation", "batChargePower", "batCurrent", "batCurrent_1", "batCurrent_2", "batDischargePower", "batTemperature", "batTemperature_1", "batTemperature_2", "batVolt", "batVolt_1", "batVolt_2", "boostTemperation", "chargeTemperature", "dspTemperature", "epsCurrentR", "epsCurrentS", "epsCurrentT", "epsPower", "epsPowerR", "epsPowerS", "epsPowerT", "epsVoltR", "epsVoltS", "epsVoltT", "feedinPower", "generationPower", "gridConsumptionPower", "input", "invBatCurrent", "invBatPower", "invBatVolt", "invTemperation", "loadsPower", "loadsPowerR", "loadsPowerS", "loadsPowerT", "meterPower", "meterPower2", "meterPowerR", "meterPowerS", "meterPowerT", "PowerFactor", "pv1Current", "pv1Power", "pv1Volt", "pv2Current", "pv2Power", "pv2Volt", "pv3Current", "pv3Power", "pv3Volt", "pv4Current", "pv4Power", "pv4Volt", "pvPower", "RCurrent", "ReactivePower", "RFreq", "RPower", "RVolt", "SCurrent", "SFreq", "SoC", "SPower", "SVolt", "TCurrent", "TFreq", "TPower", "TVolt", "SoC_1", "Soc_2", "ResidualEnergy", "energyThroughput", "runningState", "currentFaultCount"] }'
        )

    rawData = dsn + " }"

    _LOGGER.debug("getRaw OA request: %s", rawData)

    timestamp = round(time.time() * 1000)

    headerData = GetAuth().get_signature(token=apiKey, path=path)

    path = _ENDPOINT_OA_DOMAIN + path
    _LOGGER.debug("Path: %s", path)

    restOADeviceVariables = RestData(
        hass,
        METHOD_POST,
        path,
        DEFAULT_ENCODING,
        None,
        headerData,
        None,
        rawData,
        DEFAULT_VERIFY_SSL,
        SSLCipherList.PYTHON_DEFAULT,
        DEFAULT_TIMEOUT,
    )

    await restOADeviceVariables.async_update()
    if restOADeviceVariables.last_exception is not None:
        lastex = str(restOADeviceVariables.last_exception)
        _LOGGER.debug("Getvar exception: %s", lastex)
        if "Timeout while contacting DNS servers" in lastex:
            _LOGGER.debug("Getvar DNS exception: %s", lastex)
            return FetchResult.DNS_TIMEOUT
            # [Timeout while contacting DNS servers]

    if restOADeviceVariables.data is None or restOADeviceVariables.data == "":
        _LOGGER.debug("Unable to get OA Variables from FoxESS Cloud")
        return FetchResult.ERROR

    # Openapi responded correctly
    response = json.loads(restOADeviceVariables.data)
    if response["errno"] == 0 and (
        response["msg"] == "success" or response["msg"] == "Operation successful"
    ):
        allData["raw"]["ResponseTime"] = max(round(time.time() * 1000) - timestamp, 0)

        test = json.loads(restOADeviceVariables.data)["result"]

        timercv = test[0].get("time")
        tsrcv = parse_foxess_timestamp(xtzone, timercv)
        age = 0
        if tsrcv != 0:
            testd = datetime.now()
            tsnow = round(time.time())
            age = round(tsnow - tsrcv)
            _LOGGER.debug(
                "OA Variables time: %s vs %s timestamps r:%s now:%s, age: %s",
                timercv,
                testd,
                tsrcv,
                tsnow,
                age,
            )
            if age > 361:
                _LOGGER.debug(
                    "OA Variables invalid age: %s vs %s timestamps r:%s now:%s, age: %s",
                    timercv,
                    testd,
                    tsrcv,
                    tsnow,
                    age,
                )

        result = test[0].get("datas")
        _LOGGER.debug("OA Variables Good Response: %s", result)
        # allData['raw'] = {}
        for item in result:
            variableName = item["variable"]
            # If value exists
            if item.get("value") is not None:
                variableValue = item["value"]
            else:
                variableValue = 0
                _LOGGER.debug("Variable %s no value, set to zero", variableName)
            # fix for various battery and scale items
            if variableName == "SoC_1":
                variableName = "SoC_1"  # do nothing for the moment, future release might align this correctly to use SoC
            elif variableName == "batTemperature_1":
                variableName = "batTemperature"  # use entity for single battery systems
            elif variableName == "invBatPower_1":
                variableName = "invBatPower"  # use entity for single battery systems
            elif variableName == "ResidualEnergy":
                if item.get("unit") is not None:
                    scale = item["unit"]
                    if scale in ["1.0kWh", "kWh", None]:
                        variableValue = round((variableValue * 100), 2)
                        _LOGGER.debug(
                            "OA Variables ResidualEnergy Scale: *100 %s", scale
                        )
                    elif scale == "0.1kWh":
                        variableValue = round((variableValue * 10), 2)
                        _LOGGER.debug(
                            "OA Variables ResidualEnergy Scale: *10 %s", scale
                        )
                    else:
                        _LOGGER.debug("OA Variables ResidualEnergy Scale: %s", scale)

            allData["raw"][variableName] = variableValue
            _LOGGER.debug(
                "Var: %s, SN: %s set to %s",
                variableName,
                devicesn,
                allData["raw"][variableName],
            )

            if variableName == "runningState" and (
                "hasBattery" in allData["addressbook"]
            ):
                hasBat = allData["addressbook"]["hasBattery"]
                if not hasBat:
                    # solar only inverter
                    _LOGGER.debug(
                        "TestState: %s, hasBat: %s online: %s",
                        variableValue,
                        hasBat,
                        allData["online"],
                    )
                    if variableValue in ["161", "162"]:
                        # waiting and solar only so set off-line flag
                        if age < 361:
                            _LOGGER.debug(
                                "Waiting but data less than 5 minutes old - allow sample, RunningState: %s, hasBat: %s online: %s",
                                variableValue,
                                hasBat,
                                allData["online"],
                            )
                        else:
                            allData["online"] = False
                            _LOGGER.debug(
                                "Waiting so set off-line state, TestState: %s, hasBat: %s online: %s",
                                variableValue,
                                hasBat,
                                allData["online"],
                            )
                    elif variableValue == "163" and not allData["online"]:
                        # on-grid but showing off-line wait for it to be set on-line by OADeviceDetail
                        # allData["online"] = False
                        _LOGGER.debug(
                            "Inverter on-grid but off-line wait for OADevice to confirm, TestState: %s, hasBat: %s",
                            variableValue,
                            hasBat,
                        )

        return FetchResult.OK

    _LOGGER.debug("OA Device Variables Bad Response: %s", response)
    return (
        FetchResult.AUTH_FAILED
        if response["errno"] in _AUTH_ERRNO
        else FetchResult.ERROR
    )


def parse_foxess_timestamp(xtzone: bool, timercv: str) -> float:
    """Parse a FoxESS timestamp string into a UTC Unix timestamp.

    FoxESS returns timestamps in the format "2025-02-21 16:38:29 GMT+0000".
    Standard strptime fails on some locales, so the UTC offset is extracted
    manually and applied only when the device timezone differs from the local
    system timezone (controlled by the xtzone flag).

    Returns 0 on parse failure (ValueError, IndexError, OverflowError).
    """
    try:
        # format is "2025-02-21 16:38:29 GMT+0000" strptime is useless at international dates, so work out the offset
        # tsrcv = datetime.strptime(testt, "%Y-%m-%d %H:%M:%S %Z%z") fails on some countries
        _LOGGER.debug("OA Variables time: %s ", timercv)
        tzoffsetsign = timercv[23:24]
        tzoffsethr = int(timercv[24:26])
        tzoffsetmin = int(timercv[26:28])
        tzfull = str(timercv[23:28])
        _LOGGER.debug(
            "OA Variables tzoffsign: %s, hr: %s, min: %s, full: %s",
            tzoffsetsign,
            tzoffsethr,
            tzoffsetmin,
            tzfull,
        )
        tzoffset = tzoffsethr * 3600 + tzoffsetmin * 60
        if tzoffsetsign == "-":
            tzoffset = -tzoffset
        tsrcv = (parser.parse(timercv, ignoretz=True)).timestamp()
        zulu = datetime.now().astimezone().strftime("%z")
        if zulu != tzfull:
            if xtzone:
                _LOGGER.debug(
                    "OA Variables tsrcv applying offset: %s, offset: %s, zulu: %s",
                    tsrcv,
                    tzoffset,
                    zulu,
                )
                tsrcv = tsrcv - tzoffset
        else:
            _LOGGER.debug(
                "OA Variables tsrcv is local: %s, zulu: %s, offset: %s ",
                tsrcv,
                zulu,
                tzoffset,
            )
    except ValueError, IndexError, OverflowError:
        tsrcv = 0
    return tsrcv


def _get_float(d: dict, key: str) -> float:
    """Return float(d[key]) when key exists and value is not None, else 0.0."""
    val = d.get(key)
    return float(val) if val is not None else 0.0


class _RawDataSensor(CoordinatorEntity, SensorEntity):
    """Base class for reusable raw-data sensors configured at instantiation time.

    Use this when the same sensor class is instantiated multiple times with different
    names, unique IDs, and raw-data keys — for example, one class reused across all PV
    strings or grid phases. The name, unique ID, and key are passed as constructor
    arguments so each instance can be configured independently.
    """

    def __init__(self, coordinator, name, deviceID, nameValue, uniqueValue, keyValue):
        """Initialize the sensor entity."""
        super().__init__(coordinator=coordinator)
        self._nameValue = nameValue
        self._uniqueValue = uniqueValue
        self._keyValue = keyValue
        self._none_reported = False
        _LOGGER.debug("Initiating Entity - %s", self._nameValue)
        self._attr_name = f"{name} - {self._nameValue}"
        self._attr_unique_id = f"{deviceID}{self._uniqueValue}"

    @property
    def native_value(self) -> float | None:
        """Return value from raw data."""
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if self._keyValue not in self.coordinator.data["raw"]:
                if not self._none_reported:
                    _LOGGER.debug("%s None", self._keyValue)
                    self._none_reported = True
            else:
                return self.coordinator.data["raw"][self._keyValue]
        return None


class _FixedRawDataSensor(CoordinatorEntity, SensorEntity):
    """Base class for single-purpose raw-data sensors with identity baked into the class.

    Use this when the sensor class represents exactly one thing, so the name, unique ID,
    and raw-data key are fixed and declared as class attributes rather than passed at
    instantiation. Override _transform() to apply scaling or value correction without
    repeating the online/raw guard logic.
    """

    # These should be overridden in the base classes.
    _name_value: str
    _unique_value: str
    _key_value: str

    def __init__(self, coordinator, name, deviceID):
        """Initialize the sensor entity."""
        super().__init__(coordinator=coordinator)
        self._none_reported = False
        _LOGGER.debug("Initiating Entity - %s", self._name_value)
        self._attr_name = f"{name} - {self._name_value}"
        self._attr_unique_id = f"{deviceID}{self._unique_value}"

    def _transform(self, value: float) -> float:
        """Post-process the raw value. Override in subclasses to apply scaling or correction."""
        return value

    @property
    def native_value(self) -> float | None:
        """Return value from raw data, passed through _transform."""
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if self._key_value not in self.coordinator.data["raw"]:
                if not self._none_reported:
                    _LOGGER.debug("%s None", self._key_value)
                    self._none_reported = True
            else:
                return self._transform(self.coordinator.data["raw"][self._key_value])
        return None


class FoxESSPowerString(_RawDataSensor):
    """Sensor entity for string power measurements in kW."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.POWER
    _attr_native_unit_of_measurement = UnitOfPower.KILO_WATT


class FoxESSCurrent(_RawDataSensor):
    """Sensor entity for current measurements in amperes."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.CURRENT
    _attr_native_unit_of_measurement = UnitOfElectricCurrent.AMPERE


class FoxESSFreq(_RawDataSensor):
    """Sensor entity for grid frequency measurements in Hz."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.FREQUENCY
    _attr_native_unit_of_measurement = UnitOfFrequency.HERTZ


class FoxESSPower(_RawDataSensor):
    """Sensor entity for power measurements in kW."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.POWER
    _attr_native_unit_of_measurement = UnitOfPower.KILO_WATT


class FoxESSVolt(_RawDataSensor):
    """Sensor entity for voltage measurements in volts."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.VOLTAGE
    _attr_native_unit_of_measurement = UnitOfElectricPotential.VOLT


class FoxESSReactivePower(_FixedRawDataSensor):
    """Sensor entity for reactive power measurements."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.REACTIVE_POWER
    _attr_native_unit_of_measurement = UnitOfReactivePower.VOLT_AMPERE_REACTIVE
    _name_value = "Reactive Power"
    _unique_value = "reactive-power"
    _key_value = "ReactivePower"

    def _transform(self, value: float) -> float:
        """Scale kVAr to VAr."""
        return value * 1000


class FoxESSPowerFactor(_FixedRawDataSensor):
    """Sensor entity for power factor measurements."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.POWER_FACTOR
    _attr_native_unit_of_measurement = PERCENTAGE
    _name_value = "Power Factor"
    _unique_value = "power-factor"
    _key_value = "PowerFactor"


class FoxESSEnergyGenerated(CoordinatorEntity, SensorEntity):
    """Sensor entity for today's generated energy total in kWh."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(self, coordinator, name, deviceID, nameValue, uniqueValue, keyValue):
        """Initialize the sensor entity."""
        super().__init__(coordinator=coordinator)
        self._nameValue = nameValue
        self._uniqueValue = uniqueValue
        self._keyValue = keyValue
        self._none_reported = False
        _LOGGER.debug("Initiating Entity - %s", self._nameValue)
        self._attr_name = f"{name} - {self._nameValue}"
        self._attr_unique_id = f"{deviceID}{self._uniqueValue}"

    @property
    def native_value(self) -> float | None:
        """Return today's generated energy in kWh from the daily generation report."""
        value = self.coordinator.data["reportDailyGeneration"].get(self._keyValue)
        if value is None:
            if not self._none_reported:
                _LOGGER.debug("%s None", self._keyValue)
                self._none_reported = True
            return None
        return round(value, 3) if value > 0 else 0


class FoxESSEnergyThroughput(_FixedRawDataSensor):
    """Sensor entity for cumulative battery energy throughput in kWh."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR
    _name_value = "Energy Throughput"
    _unique_value = "energy-throughput"
    _key_value = "energyThroughput"

    def _transform(self, value: float) -> float:
        """Round to 3 decimal places; clamp negative values to zero."""
        return round(value, 3) if value > 0 else 0


class _ReportSensor(CoordinatorEntity, SensorEntity):
    """Base class for sensors that read a single keyed value from coordinator.data['report']."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR
    _round: bool = False

    # These should be overridden in the base classes.
    _name_value: str
    _unique_value: str
    _key_value: str

    def __init__(self, coordinator, name, deviceID):
        """Initialize the report sensor entity."""
        super().__init__(coordinator=coordinator)
        self._none_reported = False
        _LOGGER.debug("Initiating Entity - %s", self._name_value)
        self._attr_name = f"{name} - {self._name_value}"
        self._attr_unique_id = f"{deviceID}{self._unique_value}"

    @property
    def native_value(self) -> float | None:
        """Return value from report data."""
        if self._key_value not in self.coordinator.data["report"]:
            if not self._none_reported:
                _LOGGER.debug("%s None", self._key_value)
                self._none_reported = True
            return None
        value = self.coordinator.data["report"][self._key_value]
        return round(value, 3) if self._round else value


class FoxESSEnergyGridConsumption(_ReportSensor):
    """Sensor entity for today's grid consumption energy in kWh."""

    _name_value = "Grid Consumption"
    _unique_value = "grid-consumption"
    _key_value = "gridConsumption"


class FoxESSEnergyFeedin(_ReportSensor):
    """Sensor entity for today's feed-in energy in kWh."""

    _name_value = "FeedIn"
    _unique_value = "feedIn"
    _key_value = "feedin"


class FoxESSEnergyBatCharge(_ReportSensor):
    """Sensor entity for today's battery charge energy in kWh."""

    _name_value = "Bat Charge"
    _unique_value = "bat-charge"
    _key_value = "chargeEnergyToTal"


class FoxESSMaxBatChargeCurrent(_FixedRawDataSensor):
    """Sensor entity for maximum battery charge current in amperes."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.CURRENT
    _attr_native_unit_of_measurement = UnitOfElectricCurrent.AMPERE
    _name_value = "Max Bat Charge Current"
    _unique_value = "max-bat-charge-charge"
    _key_value = "maxChargeCurrent"


class FoxESSMaxBatDischargeCurrent(_FixedRawDataSensor):
    """Sensor entity for maximum battery discharge current in amperes."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.CURRENT
    _attr_native_unit_of_measurement = UnitOfElectricCurrent.AMPERE
    _name_value = "Max Bat Discharge Current"
    _unique_value = "max-bat-discharge-charge"
    _key_value = "maxDischargeCurrent"


class FoxESSEnergyBatDischarge(_ReportSensor):
    """Sensor entity for today's battery discharge energy in kWh."""

    _name_value = "Bat Discharge"
    _unique_value = "bat-discharge"
    _key_value = "dischargeEnergyToTal"


class FoxESSEnergyLoad(_ReportSensor):
    """Sensor entity for today's load energy in kWh."""

    _name_value = "Load"
    _unique_value = "load"
    _key_value = "loads"
    _round = True


class FoxESSPVEnergyTotal(_ReportSensor):
    """Sensor entity for today's total PV energy in kWh."""

    _name_value = "PVEnergyTotal"
    _unique_value = "PVEnergyTotal"
    _key_value = "PVEnergyTotal"
    _round = True


class FoxESSInverter(CoordinatorEntity, SensorEntity):
    """Sensor entity for inverter online/alarm/offline status."""

    def __init__(self, coordinator, name, deviceID):
        """Initialize the inverter status sensor entity."""
        super().__init__(coordinator=coordinator)
        self._none_reported = False
        _LOGGER.debug("Initiating Entity - Inverter")
        self._attr_name = name + " - Inverter"
        self._attr_unique_id = deviceID + "Inverter"
        self._attr_icon = "mdi:solar-power"

    @property
    def native_value(self) -> str | None:
        """Return inverter status as a string (on-line, in-alarm, or off-line)."""
        if self.coordinator.data["online"] or (
            not self.coordinator.data["online"]
            and int(self.coordinator.data["addressbook"]["status"]) in [1, 2, 3]
        ):
            if "status" not in self.coordinator.data["addressbook"]:
                if not self._none_reported:
                    _LOGGER.debug("addressbook status None")
                    self._none_reported = True
            elif int(self.coordinator.data["addressbook"]["status"]) == 1:
                return "on-line"
            elif int(self.coordinator.data["addressbook"]["status"]) == 2:
                return "in-alarm"
            else:
                return "off-line"
        return None

    @property
    def extra_state_attributes(self):
        """Return device details as extra state attributes."""
        if "status" not in self.coordinator.data["addressbook"]:
            _LOGGER.debug("addressbook status attributes None")
            return None
        return {
            ATTR_DEVICE_SN: self.coordinator.data["addressbook"][ATTR_DEVICE_SN],
            ATTR_PLANTNAME: self.coordinator.data["addressbook"][ATTR_PLANTNAME],
            ATTR_MODULESN: self.coordinator.data["addressbook"][ATTR_MODULESN],
            ATTR_DEVICE_TYPE: self.coordinator.data["addressbook"][ATTR_DEVICE_TYPE],
            ATTR_MASTER: self.coordinator.data["addressbook"][ATTR_MASTER],
            ATTR_MANAGER: self.coordinator.data["addressbook"][ATTR_MANAGER],
            ATTR_SLAVE: self.coordinator.data["addressbook"][ATTR_SLAVE],
            ATTR_BATTERYLIST: self.coordinator.data["addressbook"][ATTR_BATTERYLIST],
            ATTR_LASTCLOUDSYNC: datetime.now(),
        }


class FoxESSRunningState(_RawDataSensor):
    """Sensor entity for inverter running state with descriptive code labels."""

    _attr_icon = "mdi:state-machine"

    @property
    def native_value(self) -> str | None:
        """Return inverter running state code with a descriptive label."""
        if self.coordinator.data["raw"]:
            if self._keyValue not in self.coordinator.data["raw"]:
                if not self._none_reported:
                    _LOGGER.debug("%s None", self._keyValue)
                    self._none_reported = True
            else:
                res = self.coordinator.data["raw"][self._keyValue]
                if res == "160":
                    resText = f"{res}: self-test"
                elif res == "161":
                    resText = f"{res}: waiting"
                elif res == "162":
                    resText = f"{res}: checking"
                elif res == "163":
                    resText = f"{res}: on-grid"
                elif res == "164":
                    resText = f"{res}: off-grid"
                elif res == "165":
                    resText = f"{res}: fault"
                elif res == "166":
                    resText = f"{res}: permanent-fault"
                elif res == "167":
                    resText = f"{res}: standby"
                elif res == "168":
                    resText = f"{res}: upgrading"
                elif res == "169":
                    resText = f"{res}: fct"
                elif res == "170":
                    resText = f"{res}: illegal"
                else:
                    _LOGGER.debug("runcode %s", res)
                    resText = f"{res}: unknown code"
                return resText
        return None


class FoxESSEnergySolar(CoordinatorEntity, SensorEntity):
    """Sensor entity for estimated solar energy production in kWh, derived from report totals."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(self, coordinator, name, deviceID):
        """Initialize the solar energy sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Solar")
        self._attr_name = name + " - Solar"
        self._attr_unique_id = deviceID + "solar"

    @property
    def native_value(self) -> float | None:
        """Return estimated solar energy in kWh, derived from report totals."""
        report = self.coordinator.data["report"]
        loads = _get_float(report, "loads")
        charge = _get_float(report, "chargeEnergyToTal")
        feedIn = _get_float(report, "feedin")
        gridConsumption = _get_float(report, "gridConsumption")
        discharge = _get_float(report, "dischargeEnergyToTal")

        energysolar = round((loads + charge + feedIn - gridConsumption - discharge), 3)
        energysolar = max(energysolar, 0)
        return round(energysolar, 3)


class FoxESSSolarPower(CoordinatorEntity, SensorEntity):
    """Sensor entity for estimated real-time solar power in kW, derived from raw readings."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.POWER
    _attr_native_unit_of_measurement = UnitOfPower.KILO_WATT

    def __init__(self, coordinator, name, deviceID):
        """Initialize the solar power sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Solar Power")
        self._attr_name = name + " - Solar Power"
        self._attr_unique_id = deviceID + "solar-power"

    @property
    def native_value(self) -> float | None:
        """Return estimated solar power in kW, derived from raw power readings."""
        raw = self.coordinator.data["raw"]
        loads = _get_float(raw, "loadsPower")
        charge = _get_float(raw, "batChargePower")
        feedIn = _get_float(raw, "feedinPower")
        gridConsumption = _get_float(raw, "gridConsumptionPower")
        discharge = _get_float(raw, "batDischargePower")

        # check if what was returned (that some time was negative) is <0, so fix it
        total = loads + charge + feedIn - gridConsumption - discharge
        total = max(total, 0)
        return round(total, 3)


class FoxESSBatSoC(_RawDataSensor):
    """Sensor entity for battery state of charge percentage."""

    _attr_device_class = SensorDeviceClass.BATTERY
    _attr_native_unit_of_measurement = "%"

    @property
    def icon(self):
        """Return a battery icon for the current charge level."""
        return icon_for_battery_level(battery_level=self.native_value, charging=None)


class _BatterySettingsSensor(CoordinatorEntity, SensorEntity):
    """Base class for fixed-name sensors reading from coordinator.data['battery']."""

    _attr_device_class = SensorDeviceClass.BATTERY
    _attr_native_unit_of_measurement = "%"
    _name_value: str
    _unique_value: str
    _key_value: str

    def __init__(self, coordinator, name, deviceID):
        """Initialize the sensor entity."""
        super().__init__(coordinator=coordinator)
        self._none_reported = False
        _LOGGER.debug("Initiating Entity - %s", self._name_value)
        self._attr_name = f"{name} - {self._name_value}"
        self._attr_unique_id = f"{deviceID}{self._unique_value}"

    @property
    def native_value(self) -> float | None:
        """Return value from battery settings data."""
        if self.coordinator.data["online"] and self.coordinator.data["battery"]:
            if self._key_value not in self.coordinator.data["battery"]:
                if not self._none_reported:
                    _LOGGER.debug("%s None", self._key_value)
                    self._none_reported = True
            else:
                return self.coordinator.data["battery"][self._key_value]
        return None

    @property
    def icon(self):
        """Return a battery icon for the current level."""
        return icon_for_battery_level(battery_level=self.native_value, charging=None)


class FoxESSBatMinSoC(_BatterySettingsSensor):
    """Sensor entity for minimum allowed battery state of charge percentage."""

    _name_value = "Bat MinSoC"
    _unique_value = "bat-minsoc"
    _key_value = "minSoc"


class FoxESSBatMinSoConGrid(_BatterySettingsSensor):
    """Sensor entity for minimum battery state of charge when on grid."""

    _name_value = "Bat minSocOnGrid"
    _unique_value = "bat-minSocOnGrid"
    _key_value = "minSocOnGrid"


class FoxESSSchedulerEnabled(CoordinatorEntity, SensorEntity):
    """Sensor entity showing whether the FoxESS scheduler is enabled or disabled."""

    _attr_icon = "mdi:calendar-clock"

    def __init__(self, coordinator, name, deviceID):
        """Initialize the scheduler enabled sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Scheduler")
        self._attr_name = f"{name} - Scheduler"
        self._attr_unique_id = f"{deviceID}scheduler-enabled"

    @property
    def native_value(self) -> str | None:
        """Return 'enabled' or 'disabled' based on scheduler flag, or None if not yet fetched."""
        enabled = self.coordinator.data["scheduler"]["enabled"]
        if enabled is None:
            return None
        return "enabled" if enabled else "disabled"


class FoxESSSchedulerGroups(CoordinatorEntity, SensorEntity):
    """Sensor entity holding the full FoxESS scheduler group list."""

    _attr_icon = "mdi:calendar-clock"

    def __init__(
        self,
        coordinator,
        name,
        deviceID,
        device_sn: str = "",
        scheduler_api_version: str = SCHEDULER_API_V2,
    ):
        """Initialize the scheduler groups sensor entity."""
        super().__init__(coordinator=coordinator)
        self._device_sn = device_sn
        self._scheduler_api_version = scheduler_api_version
        _LOGGER.debug("Initiating Entity - Scheduler Groups")
        self._attr_name = f"{name} - Scheduler Groups"
        self._attr_unique_id = f"{deviceID}scheduler-groups"

    @property
    def native_value(self) -> int:
        """Return the number of configured scheduler groups."""
        return len(self.coordinator.data["scheduler"]["groups"])

    @property
    def extra_state_attributes(self) -> dict:
        """Return the full groups list, device SN and scheduler API version as attributes."""
        battery = self.coordinator.data.get("battery") or {}
        return {
            "groups": self.coordinator.data["scheduler"]["groups"],
            "device_sn": self._device_sn,
            "scheduler_api_version": self._scheduler_api_version,
            "min_soc": battery.get("minSoc"),
        }


class FoxESSTemp(_RawDataSensor):
    """Sensor entity for temperature measurements in degrees Celsius."""

    _attr_device_class = SensorDeviceClass.TEMPERATURE
    _attr_native_unit_of_measurement = UnitOfTemperature.CELSIUS


class FoxESSResidualEnergy(_FixedRawDataSensor):
    """Sensor entity for residual battery energy in kWh."""

    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR
    _name_value = "Residual Energy"
    _unique_value = "residual-energy"
    _key_value = "ResidualEnergy"

    def _transform(self, value: float) -> float:
        """Correct API scale bug: values > 50 are in Wh not kWh, divide by 100."""
        if value <= 0:
            return 0
        return value / 100 if value > 50 else value


class FoxESSResponseTime(CoordinatorEntity, SensorEntity):
    """Sensor entity for FoxESS API response time in milliseconds."""

    _attr_native_unit_of_measurement = "mS"

    def __init__(self, coordinator, name, deviceID):
        """Initialize the API response time sensor entity."""
        super().__init__(coordinator=coordinator)
        self._none_reported = False
        _LOGGER.debug("Initiating Entity - Response Time")
        self._attr_name = name + " - Response Time"
        self._attr_unique_id = deviceID + "response-time"

    @property
    def native_value(self) -> float | None:
        """Return the last FoxESS API response time in milliseconds."""
        if "ResponseTime" not in self.coordinator.data["raw"]:
            if not self._none_reported:
                _LOGGER.debug("ResponseTime None")
                self._none_reported = True
        else:
            return self.coordinator.data["raw"]["ResponseTime"]
        return None
