"""Car charging monitor for FoxESS Home Assistant integration.

Watches an external HA entity (e.g. Octopus Energy Intelligent Dispatching
binary sensor) and automatically switches the inverter to Backup mode when EV
charging is detected, then restores the previous work mode when it stops.

What to restore is persisted, so a restart of Home Assistant while the
inverter is held in Backup mode still restores it once charging ends.
"""

from __future__ import annotations

import asyncio
from datetime import datetime
import logging
from typing import Any

from homeassistant.const import STATE_UNAVAILABLE, STATE_UNKNOWN
from homeassistant.core import Event, HomeAssistant, State, callback
from homeassistant.helpers.event import async_track_state_change_event
from homeassistant.helpers.storage import Store

from .const import DOMAIN, SCHEDULER_API_V3, FetchResult

_LOGGER = logging.getLogger(__name__)

_PROTECTED_WORK_MODES = frozenset({"ForceCharge", "Backup"})
_DEFAULT_RESTORE_MODE = "SelfUse"
_STORAGE_VERSION = 1


class CarChargingManager:
    """Monitor an HA entity and protect the inverter battery while an EV charges."""

    def __init__(self, hass: HomeAssistant, coordinator) -> None:
        """Initialise the manager for the inverter behind the given coordinator."""
        self._hass = hass
        self._coordinator = coordinator
        self._allData = coordinator.allData
        self._car_is_charging: bool = False
        # Whether the scheduler and work mode have been read from FoxESS Cloud
        # since charging started; the coordinator only polls them hourly.
        self._state_fresh: bool = False
        self._managing: bool = False
        # A restore failed and should be retried on the next coordinator update.
        self._restore_pending: bool = False
        self._saved_state: dict[str, Any] | None = None
        self._store: Store = Store(
            hass, _STORAGE_VERSION, f"{DOMAIN}.car_charging.{coordinator.devicesn}"
        )
        self._unsubs: list = []
        self._lock = asyncio.Lock()

    async def async_setup(self, entity_id: str) -> None:
        """Resume any persisted state, then subscribe to state changes and coordinator updates."""
        stored = await self._store.async_load()
        if stored and isinstance(stored.get("saved_state"), dict):
            _LOGGER.info(
                "Resuming car charging management, will restore %s", stored["saved_state"]
            )
            self._saved_state = stored["saved_state"]
            self._managing = True

        # Listen for changes to the car charging binary sensor.
        self._unsubs.append(
            async_track_state_change_event(
                self._hass, entity_id, self._handle_charging_state_change
            )
        )

        # Listen for changes to scheduler state.
        self._unsubs.append(
            self._coordinator.async_add_listener(self._handle_coordinator_update)
        )

        # If the entity has no state yet (e.g. its integration is still
        # loading), wait for it to report one.
        state = self._hass.states.get(entity_id)
        if state is None or not self._is_known_state(state):
            return
        if self._is_charging_state(state):
            self._start_charging()
        elif self._managing:
            self._hass.async_create_task(self._restore_if_managed())

    @callback
    def async_teardown(self) -> None:
        """Unsubscribe all listeners."""
        for unsub in self._unsubs:
            unsub()
        self._unsubs.clear()

    @staticmethod
    def _is_charging_state(state: Any) -> bool:
        return state.state.lower() in {"on", "true", "charging", "active"}

    @staticmethod
    def _is_known_state(state: State) -> bool:
        return state.state not in (STATE_UNAVAILABLE, STATE_UNKNOWN)

    @callback
    def _start_charging(self) -> None:
        self._car_is_charging = True
        self._state_fresh = False
        # Charging again before a failed restore succeeded: keep managing with
        # the original saved state instead.
        self._restore_pending = False
        self._hass.async_create_task(self._evaluate_and_manage())

    @callback
    def _handle_charging_state_change(self, event: Event) -> None:
        new_state = event.data.get("new_state")
        old_state = event.data.get("old_state")

        new_charging = new_state is not None and self._is_charging_state(new_state)
        old_charging = old_state is not None and self._is_charging_state(old_state)

        # Managing while the car isn't known to be charging means the state
        # was resumed after a restart, so the first known non-charging state
        # ends the charge.
        resumed_and_stopped = (
            self._managing
            and new_state is not None
            and self._is_known_state(new_state)
        )
        if new_charging and not old_charging:
            _LOGGER.debug("Car charging started")
            self._start_charging()
        elif not new_charging and (old_charging or resumed_and_stopped):
            _LOGGER.debug("Car charging ended")
            self._car_is_charging = False
            self._hass.async_create_task(self._restore_if_managed())

    @callback
    def _handle_coordinator_update(self) -> None:
        if not self._car_is_charging:
            if self._restore_pending:
                self._hass.async_create_task(self._restore_if_managed())
            return

        if not self._managing:
            self._hass.async_create_task(self._evaluate_and_manage())
        elif self._saved_state is not None and self._allData["schedulerEnabled"]:
            # The scheduler is always off while managing (either it was already
            # off or we disabled it), so seeing it on means it was re-enabled
            # externally. Seeing it off tells us nothing, so must not overwrite
            # the saved flag, or the scheduler would never be restored.
            if not self._saved_state["scheduler_enabled"]:
                self._saved_state["scheduler_enabled"] = True
                self._hass.async_create_task(self._persist())

    def _get_active_work_mode(self) -> str | None:
        """Return the active work mode from scheduler groups, or None if not determinable."""
        if not self._allData["schedulerEnabled"]:
            return None

        now = datetime.now()
        now_minutes = now.hour * 60 + now.minute

        # Groups can overlap, e.g. an all-day SelfUse group with a ForceCharge
        # group on top of it, so the narrowest matching group wins.
        best_mode = None
        best_length = None
        for g in self._allData["schedulerGroups"]:
            if not g.get("enable", True):
                continue
            start = g.get("startHour", 0) * 60 + g.get("startMinute", 0)
            end = g.get("endHour", 0) * 60 + g.get("endMinute", 0)
            if start <= now_minutes <= end and (
                best_length is None or end - start < best_length
            ):
                best_mode = g.get("workMode")
                best_length = end - start

        return best_mode

    async def _evaluate_and_manage(self) -> None:
        """Switch the inverter to Backup mode if not already protected."""
        # Serialise with _restore_if_managed so overlapping runs can't save
        # the already-modified state, and a restore can't be skipped because
        # it ran before an in-flight switch to Backup had completed.
        async with self._lock:
            if self._car_is_charging:
                await self._evaluate_and_manage_locked()

    async def _evaluate_and_manage_locked(self) -> None:
        # Before saving what to restore, make sure it isn't stale. If it can't
        # be read, do nothing: the next coordinator update tries again.
        if not self._managing and not self._state_fresh:
            if not await self._refresh_inverter_state():
                return
            self._state_fresh = True

        if self._allData["schedulerEnabled"]:
            active_mode = self._get_active_work_mode()
        else:
            active_mode = self._allData.get("workMode")

        if active_mode in _PROTECTED_WORK_MODES:
            return

        if not self._managing:
            self._saved_state = {
                "scheduler_enabled": self._allData["schedulerEnabled"],
                "work_mode": active_mode or _DEFAULT_RESTORE_MODE,
            }

        if self._allData["schedulerEnabled"]:
            result = await self._set_scheduler_flag(False)
            if result is not FetchResult.OK:
                return
            self._allData["schedulerEnabled"] = False

        result = await self._set_work_mode("Backup")
        if result is FetchResult.OK:
            self._managing = True
            await self._persist()
            self._coordinator.async_set_updated_data(self._allData)

    async def _restore_if_managed(self) -> None:
        """Restore the previous work mode and scheduler state."""
        async with self._lock:
            await self._restore_if_managed_locked()

    async def _restore_if_managed_locked(self) -> None:
        if not self._managing or self._car_is_charging:
            return

        saved = self._saved_state
        result = await self._set_work_mode(
            saved.get("work_mode", _DEFAULT_RESTORE_MODE)
        )
        if result is FetchResult.OK and saved.get("scheduler_enabled"):
            result = await self._set_scheduler_flag(True)
            if result is FetchResult.OK:
                self._allData["schedulerEnabled"] = True

        if result is not FetchResult.OK:
            # Keep the saved state (including in storage) and retry on the
            # next coordinator update. Not notifying listeners here is what
            # stops the retry running straight away in a loop.
            _LOGGER.warning("Failed to restore %s, will retry", saved)
            self._restore_pending = True
            return

        self._restore_pending = False
        self._managing = False
        self._saved_state = None
        await self._store.async_remove()
        self._coordinator.async_set_updated_data(self._allData)

    async def _persist(self) -> None:
        """Save what to restore, so it survives a restart of Home Assistant."""
        if self._saved_state is not None:
            await self._store.async_save({"saved_state": self._saved_state})

    async def _refresh_inverter_state(self) -> bool:
        """Read the scheduler flag, and the groups or work mode, from FoxESS Cloud.

        Return False, leaving the coordinator data unchanged, if any read fails.
        """
        coordinator = self._coordinator
        result, resp, _ = await coordinator.client.async_get_scheduler_flag(
            coordinator.devicesn, coordinator.apiKey
        )
        enable = ((resp or {}).get("result") or {}).get("enable")
        if result is not FetchResult.OK or enable is None:
            _LOGGER.warning("Could not read the scheduler state, will retry: %s", resp)
            return False

        if enable:
            groups = await self._get_scheduler_groups()
            if groups is None:
                _LOGGER.warning("Could not read the scheduler groups, will retry")
                return False
            self._allData["schedulerGroups"] = groups
        else:
            work_mode = await self._get_work_mode()
            if work_mode is None:
                _LOGGER.warning("Could not read the work mode, will retry")
                return False
            self._allData["workMode"] = work_mode
        self._allData["schedulerEnabled"] = bool(enable)
        return True

    async def _get_scheduler_groups(self) -> list | None:
        """Read the scheduler groups from FoxESS Cloud."""
        coordinator = self._coordinator
        if getattr(coordinator, "scheduler_api_version", None) == SCHEDULER_API_V3:
            get_groups = coordinator.client.async_get_scheduler_groups_v3
        else:
            get_groups = coordinator.client.async_get_scheduler_groups
        result, resp, _ = await get_groups(coordinator.devicesn, coordinator.apiKey)
        groups = ((resp or {}).get("result") or {}).get("groups")
        if result is not FetchResult.OK or not isinstance(groups, list):
            return None
        return groups

    async def _get_work_mode(self) -> str | None:
        """Read the inverter's current work mode from FoxESS Cloud."""
        coordinator = self._coordinator
        result, resp, _ = await coordinator.client.async_get_work_mode(
            coordinator.devicesn, coordinator.apiKey
        )
        if result is not FetchResult.OK or not resp:
            return None
        res = resp.get("result") or {}
        values = res.get("values")
        return values.get("WorkMode") if isinstance(values, dict) else res.get("value")

    async def _set_work_mode(self, mode: str) -> FetchResult:
        """Set the inverter's work mode, recording it in the coordinator data."""
        coordinator = self._coordinator
        result, resp, _ = await coordinator.client.async_set_work_mode(
            coordinator.devicesn, coordinator.apiKey, mode
        )
        if result is FetchResult.OK:
            self._allData["workMode"] = mode
        else:
            _LOGGER.error("Failed to set work mode to %s: %s", mode, resp)
        return result

    async def _set_scheduler_flag(self, enable: bool) -> FetchResult:
        """Enable or disable the inverter's mode scheduler."""
        coordinator = self._coordinator
        result, resp, _ = await coordinator.client.async_set_scheduler_flag(
            coordinator.devicesn, coordinator.apiKey, enable
        )
        if result is not FetchResult.OK:
            _LOGGER.error("Failed to set scheduler flag to %s: %s", enable, resp)
        return result
