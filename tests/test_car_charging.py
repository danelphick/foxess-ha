"""Unit tests for CarChargingManager."""

from datetime import datetime
from unittest.mock import AsyncMock, MagicMock, patch

from custom_components.foxess.car_charging import (
    CarChargingManager,
    _DEFAULT_RESTORE_MODE,
)
from custom_components.foxess.sensor import FetchResult
import pytest


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_manager(scheduler_enabled: bool = False, groups: list | None = None) -> tuple[CarChargingManager, MagicMock, dict]:
    hass = MagicMock()
    hass.bus.async_listen = MagicMock(return_value=MagicMock())
    hass.states.get = MagicMock(return_value=None)
    hass.async_create_task = MagicMock(side_effect=lambda coro: coro.close())

    coordinator = MagicMock()
    coordinator.async_add_listener = MagicMock(return_value=MagicMock())
    coordinator.async_set_updated_data = MagicMock()

    all_data: dict = {
        "scheduler": {"enabled": scheduler_enabled, "groups": groups or []},
    }

    manager = CarChargingManager(hass, "SN123", "api-key", coordinator, all_data)
    return manager, hass, all_data


def _group(
    start_h: int,
    start_m: int,
    end_h: int,
    end_m: int,
    work_mode: str = "SelfUse",
    enable: bool = True,
) -> dict:
    return {
        "startHour": start_h,
        "startMinute": start_m,
        "endHour": end_h,
        "endMinute": end_m,
        "workMode": work_mode,
        "enable": enable,
    }


# ---------------------------------------------------------------------------
# TestIsChargingState
# ---------------------------------------------------------------------------


class TestIsChargingState:
    @pytest.mark.parametrize("state_str", ["on", "charging", "active", "true"])
    def test_charging_states(self, state_str: str) -> None:
        state = MagicMock()
        state.state = state_str
        assert CarChargingManager._is_charging_state(state) is True

    @pytest.mark.parametrize("state_str", ["off", "idle", "unavailable"])
    def test_non_charging_states(self, state_str: str) -> None:
        state = MagicMock()
        state.state = state_str
        assert CarChargingManager._is_charging_state(state) is False


# ---------------------------------------------------------------------------
# TestGetActiveWorkMode
# ---------------------------------------------------------------------------


class TestGetActiveWorkMode:
    def test_returns_none_when_scheduler_disabled(self) -> None:
        manager, _, _ = _make_manager(scheduler_enabled=False)
        assert manager._get_active_work_mode() is None

    def test_returns_matching_group_work_mode(self) -> None:
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, _ = _make_manager(
                scheduler_enabled=True,
                groups=[_group(14, 0, 15, 0, "ForceCharge")],
            )
            assert manager._get_active_work_mode() == "ForceCharge"

    def test_returns_none_when_no_group_matches(self) -> None:
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 20, 0)
            manager, _, _ = _make_manager(
                scheduler_enabled=True,
                groups=[_group(14, 0, 15, 0, "ForceCharge")],
            )
            assert manager._get_active_work_mode() is None

    def test_skips_disabled_groups(self) -> None:
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, _ = _make_manager(
                scheduler_enabled=True,
                groups=[_group(14, 0, 15, 0, "ForceCharge", enable=False)],
            )
            assert manager._get_active_work_mode() is None


# ---------------------------------------------------------------------------
# TestEvaluateAndManage
# ---------------------------------------------------------------------------


class TestEvaluateAndManage:
    @pytest.mark.asyncio
    async def test_no_op_when_already_backup(self) -> None:
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, _ = _make_manager(
                scheduler_enabled=True,
                groups=[_group(14, 0, 15, 0, "Backup")],
            )
            with patch("custom_components.foxess.car_charging._set_device_setting") as mock_set:
                await manager._evaluate_and_manage()
                mock_set.assert_not_called()

    @pytest.mark.asyncio
    async def test_no_op_when_force_charge(self) -> None:
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, _ = _make_manager(
                scheduler_enabled=True,
                groups=[_group(14, 0, 15, 0, "ForceCharge")],
            )
            with patch("custom_components.foxess.car_charging._set_device_setting") as mock_set:
                await manager._evaluate_and_manage()
                mock_set.assert_not_called()

    @pytest.mark.asyncio
    async def test_disables_scheduler_and_sets_backup_when_selfuse(self) -> None:
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, all_data = _make_manager(
                scheduler_enabled=True,
                groups=[_group(14, 0, 15, 0, "SelfUse")],
            )
            with (
                patch(
                    "custom_components.foxess.car_charging.setSchedulerFlag",
                    new_callable=AsyncMock,
                    return_value=(FetchResult.OK, ""),
                ) as mock_flag,
                patch(
                    "custom_components.foxess.car_charging._set_device_setting",
                    new_callable=AsyncMock,
                    return_value=(FetchResult.OK, ""),
                ) as mock_set,
            ):
                await manager._evaluate_and_manage()
                mock_flag.assert_called_once_with(manager._hass, "SN123", "api-key", 0)
                mock_set.assert_called_once_with(
                    manager._hass, "SN123", "api-key", "WorkMode", "Backup"
                )
                assert manager._managing is True

    @pytest.mark.asyncio
    async def test_sets_backup_when_scheduler_disabled_reads_mode_from_api(self) -> None:
        manager, _, _ = _make_manager(scheduler_enabled=False)
        with (
            patch(
                "custom_components.foxess.car_charging._get_device_setting",
                new_callable=AsyncMock,
                return_value=(FetchResult.OK, "SelfUse"),
            ) as mock_get,
            patch(
                "custom_components.foxess.car_charging._set_device_setting",
                new_callable=AsyncMock,
                return_value=(FetchResult.OK, ""),
            ),
        ):
            await manager._evaluate_and_manage()
            mock_get.assert_called_once_with(manager._hass, "SN123", "api-key", "WorkMode")
            assert manager._managing is True

    @pytest.mark.asyncio
    async def test_saves_state_before_switching(self) -> None:
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, all_data = _make_manager(
                scheduler_enabled=True,
                groups=[_group(14, 0, 15, 0, "SelfUse")],
            )
            with (
                patch(
                    "custom_components.foxess.car_charging.setSchedulerFlag",
                    new_callable=AsyncMock,
                    return_value=(FetchResult.OK, ""),
                ),
                patch(
                    "custom_components.foxess.car_charging._set_device_setting",
                    new_callable=AsyncMock,
                    return_value=(FetchResult.OK, ""),
                ),
            ):
                await manager._evaluate_and_manage()
                assert manager._saved_state == {
                    "scheduler_enabled": True,
                    "work_mode": "SelfUse",
                }

    @pytest.mark.asyncio
    async def test_does_not_overwrite_saved_state_when_already_managing(self) -> None:
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, _ = _make_manager(
                scheduler_enabled=False,
                groups=[],
            )
            manager._managing = True
            manager._saved_state = {"scheduler_enabled": True, "work_mode": "FeedInFirst"}

            with (
                patch(
                    "custom_components.foxess.car_charging._get_device_setting",
                    new_callable=AsyncMock,
                    return_value=(FetchResult.OK, "SelfUse"),
                ),
                patch(
                    "custom_components.foxess.car_charging._set_device_setting",
                    new_callable=AsyncMock,
                    return_value=(FetchResult.OK, ""),
                ),
            ):
                await manager._evaluate_and_manage()
                assert manager._saved_state["work_mode"] == "FeedInFirst"


# ---------------------------------------------------------------------------
# TestRestoreIfManaged
# ---------------------------------------------------------------------------


class TestRestoreIfManaged:
    @pytest.mark.asyncio
    async def test_restores_work_mode_and_reenables_scheduler(self) -> None:
        manager, _, all_data = _make_manager(scheduler_enabled=False)
        manager._managing = True
        manager._saved_state = {"scheduler_enabled": True, "work_mode": "SelfUse"}

        with (
            patch(
                "custom_components.foxess.car_charging._set_device_setting",
                new_callable=AsyncMock,
                return_value=(FetchResult.OK, ""),
            ) as mock_set,
            patch(
                "custom_components.foxess.car_charging.setSchedulerFlag",
                new_callable=AsyncMock,
                return_value=(FetchResult.OK, ""),
            ) as mock_flag,
        ):
            await manager._restore_if_managed()
            mock_set.assert_called_once_with(
                manager._hass, "SN123", "api-key", "WorkMode", "SelfUse"
            )
            mock_flag.assert_called_once_with(manager._hass, "SN123", "api-key", 1)
            assert all_data["scheduler"]["enabled"] is True
            assert manager._managing is False
            assert manager._saved_state is None

    @pytest.mark.asyncio
    async def test_restores_without_reenabling_when_was_disabled(self) -> None:
        manager, _, all_data = _make_manager(scheduler_enabled=False)
        manager._managing = True
        manager._saved_state = {"scheduler_enabled": False, "work_mode": "SelfUse"}

        with (
            patch(
                "custom_components.foxess.car_charging._set_device_setting",
                new_callable=AsyncMock,
                return_value=(FetchResult.OK, ""),
            ),
            patch(
                "custom_components.foxess.car_charging.setSchedulerFlag",
                new_callable=AsyncMock,
                return_value=(FetchResult.OK, ""),
            ) as mock_flag,
        ):
            await manager._restore_if_managed()
            mock_flag.assert_not_called()

    @pytest.mark.asyncio
    async def test_no_op_when_not_managing(self) -> None:
        manager, _, _ = _make_manager()
        with patch(
            "custom_components.foxess.car_charging._set_device_setting",
            new_callable=AsyncMock,
        ) as mock_set:
            await manager._restore_if_managed()
            mock_set.assert_not_called()


# ---------------------------------------------------------------------------
# TestScheduleChangeWhileCharging
# ---------------------------------------------------------------------------


class TestScheduleChangeWhileCharging:
    def test_updates_saved_scheduler_flag_on_external_change(self) -> None:
        manager, _, all_data = _make_manager(scheduler_enabled=False)
        manager._car_is_charging = True
        manager._managing = True
        manager._saved_state = {"scheduler_enabled": False, "work_mode": "SelfUse"}

        all_data["scheduler"]["enabled"] = True
        manager._handle_coordinator_update()

        assert manager._saved_state["scheduler_enabled"] is True

    def test_re_evaluates_when_not_managing_on_coordinator_update(self) -> None:
        manager, hass, _ = _make_manager()
        manager._car_is_charging = True
        manager._managing = False

        manager._handle_coordinator_update()

        hass.async_create_task.assert_called_once()


# ---------------------------------------------------------------------------
# Config flow tests live in test_config_flow.py (see TestReconfigureCarCharging)
# ---------------------------------------------------------------------------
