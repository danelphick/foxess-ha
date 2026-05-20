"""Car charging monitor for FoxESS Home Assistant integration.

Watches an external HA entity (e.g. Octopus Energy Intelligent Dispatching
binary sensor) and automatically switches the inverter to Backup mode when EV
charging is detected, then restores the previous work mode when it stops.
"""

from __future__ import annotations

from datetime import datetime
import logging
from typing import Any

from homeassistant.core import Event, HomeAssistant, callback
from homeassistant.helpers.event import async_track_state_change_event
from homeassistant.helpers.update_coordinator import DataUpdateCoordinator

from .sensor import (
    FetchResult,
    _get_device_setting,
    _set_device_setting,
    setSchedulerFlag,
)

_LOGGER = logging.getLogger(__name__)

_PROTECTED_WORK_MODES = frozenset({"ForceCharge", "Backup"})
_DEFAULT_RESTORE_MODE = "SelfUse"


class CarChargingManager:
    """Monitor an HA entity and protect the inverter battery while an EV charges."""

    def __init__(
        self,
        hass: HomeAssistant,
        devicesn: str,
        apiKey: str,
        coordinator: DataUpdateCoordinator,
        allData: dict[str, Any],
    ) -> None:
        """Initialise the manager with device credentials and shared data structures."""
        self._hass = hass
        self._devicesn = devicesn
        self._apiKey = apiKey
        self._coordinator = coordinator
        self._allData = allData
        self._car_is_charging: bool = False
        self._managing: bool = False
        self._saved_state: dict[str, Any] | None = None
        self._unsubs: list = []

    async def async_setup(self, entity_id: str) -> None:
        """Subscribe to state changes and coordinator updates."""
        # Listen for changes to the car charging binary sensor.
        self._unsubs.append(
            async_track_state_change_event(
                self._hass, entity_id, self._handle_charging_state_change
            )
        )

        # Listen for changes to scheduler state.
        self._unsubs.append(
            self._coordinator.async_add_listener(self._watch_for_scheduler_changes)
        )

        state = self._hass.states.get(entity_id)
        if state and self._is_charging_state(state):
            self._car_is_charging = True
            self._hass.async_create_task(self._evaluate_and_manage())

    @callback
    def async_teardown(self) -> None:
        """Unsubscribe all listeners."""
        for unsub in self._unsubs:
            unsub()
        self._unsubs.clear()

    @staticmethod
    def _is_charging_state(state: Any) -> bool:
        return state.state.lower() in {"on", "true", "charging", "active"}

    @callback
    def _handle_charging_state_change(self, event: Event) -> None:
        new_state = event.data.get("new_state")
        old_state = event.data.get("old_state")

        new_charging = new_state is not None and self._is_charging_state(new_state)
        old_charging = old_state is not None and self._is_charging_state(old_state)

        if new_charging and not old_charging:
            _LOGGER.debug("Car charging started")
            self._car_is_charging = True
            self._hass.async_create_task(self._evaluate_and_manage())
        elif not new_charging and old_charging:
            _LOGGER.debug("Car charging ended")
            self._car_is_charging = False
            self._hass.async_create_task(self._restore_if_managed())

    @callback
    def _watch_for_scheduler_changes(self) -> None:
        if not self._car_is_charging:
            return

        if not self._managing:
            self._hass.async_create_task(self._evaluate_and_manage())
        elif self._saved_state is not None:
            scheduler_enabled = self._allData["scheduler"]["enabled"]
            if scheduler_enabled != self._saved_state["scheduler_enabled"]:
                self._saved_state["scheduler_enabled"] = scheduler_enabled

    def _get_active_work_mode(self) -> str | None:
        """Return the active work mode from scheduler groups, or None if not determinable."""
        if not self._allData["scheduler"]["enabled"]:
            return None

        now = datetime.now()
        now_minutes = now.hour * 60 + now.minute

        for g in self._allData["scheduler"]["groups"]:
            if not g.get("enable", True):
                continue
            start = g.get("startHour", 0) * 60 + g.get("startMinute", 0)
            end = g.get("endHour", 0) * 60 + g.get("endMinute", 0)
            if start <= now_minutes <= end:
                return g.get("workMode")

        return None

    async def _evaluate_and_manage(self) -> None:
        """Switch the inverter to Backup mode if not already protected."""
        active_mode = self._get_active_work_mode()

        if active_mode is None and not self._allData["scheduler"]["enabled"]:
            _, active_mode = await _get_device_setting(
                self._hass, self._devicesn, self._apiKey, "WorkMode"
            )

        if active_mode in _PROTECTED_WORK_MODES:
            return

        if not self._managing:
            self._saved_state = {
                "scheduler_enabled": self._allData["scheduler"]["enabled"],
                "work_mode": active_mode or _DEFAULT_RESTORE_MODE,
            }

        if self._allData["scheduler"]["enabled"]:
            result, _ = await setSchedulerFlag(
                self._hass, self._devicesn, self._apiKey, 0
            )
            if result is not FetchResult.OK:
                return
            self._allData["scheduler"]["enabled"] = False

        result, _ = await _set_device_setting(
            self._hass, self._devicesn, self._apiKey, "WorkMode", "Backup"
        )
        if result is FetchResult.OK:
            self._managing = True
            self._coordinator.async_set_updated_data(self._allData)

    async def _restore_if_managed(self) -> None:
        """Restore the previous work mode and scheduler state."""
        if not self._managing:
            return

        saved = self._saved_state
        self._managing = False
        self._saved_state = None

        restore_mode = saved.get("work_mode", _DEFAULT_RESTORE_MODE)
        await _set_device_setting(
            self._hass, self._devicesn, self._apiKey, "WorkMode", restore_mode
        )

        if saved.get("scheduler_enabled"):
            await setSchedulerFlag(self._hass, self._devicesn, self._apiKey, 1)
            self._allData["scheduler"]["enabled"] = True

        self._coordinator.async_set_updated_data(self._allData)
