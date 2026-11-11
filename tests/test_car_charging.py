"""Unit tests for CarChargingManager."""

import asyncio
from datetime import datetime
from unittest.mock import AsyncMock, MagicMock, patch

from custom_components.foxess.car_charging import CarChargingManager
from custom_components.foxess.const import FetchResult
import pytest

_OK = (FetchResult.OK, {"errno": 0, "msg": "success"}, 10)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _flag_response(enabled: bool) -> tuple:
    return (FetchResult.OK, {"errno": 0, "result": {"enable": int(enabled)}}, 10)


def _groups_response(groups: list) -> tuple:
    return (FetchResult.OK, {"errno": 0, "result": {"groups": groups}}, 10)


_FAILED = (FetchResult.ERROR, {"errno": 40000, "msg": "error"}, 10)


def _make_manager(
    scheduler_enabled: bool = False,
    groups: list | None = None,
    car_is_charging: bool = True,
    stored: dict | None = None,
) -> tuple[CarChargingManager, MagicMock, dict]:
    """Return a manager whose cached state and FoxESS Cloud state both match the arguments."""
    hass = MagicMock()
    hass.bus.async_listen = MagicMock(return_value=MagicMock())
    hass.states.get = MagicMock(return_value=None)
    hass.async_create_task = MagicMock(side_effect=lambda coro: coro.close())

    coordinator = MagicMock()
    coordinator.devicesn = "SN123"
    coordinator.apiKey = "api-key"
    coordinator.scheduler_api_version = "v2"
    coordinator.async_add_listener = MagicMock(return_value=MagicMock())
    coordinator.async_set_updated_data = MagicMock()
    coordinator.client.async_set_scheduler_flag = AsyncMock(return_value=_OK)
    coordinator.client.async_set_work_mode = AsyncMock(return_value=_OK)
    coordinator.client.async_get_work_mode = AsyncMock(
        return_value=(FetchResult.OK, {"errno": 0, "result": {"value": "SelfUse"}}, 10)
    )
    coordinator.client.async_get_scheduler_flag = AsyncMock(
        return_value=_flag_response(scheduler_enabled)
    )
    coordinator.client.async_get_scheduler_groups = AsyncMock(
        return_value=_groups_response(groups or [])
    )

    all_data: dict = {
        "schedulerEnabled": scheduler_enabled,
        "schedulerGroups": groups or [],
        "workMode": None,
    }
    coordinator.allData = all_data

    store = MagicMock()
    store.async_load = AsyncMock(return_value=stored)
    store.async_save = AsyncMock()
    store.async_remove = AsyncMock()
    with patch("custom_components.foxess.car_charging.Store", return_value=store):
        manager = CarChargingManager(hass, coordinator)
    manager._car_is_charging = car_is_charging
    return manager, hass, all_data


def _state(value: str) -> MagicMock:
    state = MagicMock()
    state.state = value
    return state


def _state_event(old: str | None, new: str | None) -> MagicMock:
    event = MagicMock()
    event.data = {
        "old_state": None if old is None else _state(old),
        "new_state": None if new is None else _state(new),
    }
    return event


def _run_created_tasks(hass: MagicMock) -> list:
    """Make hass.async_create_task collect coroutines so a test can await them."""
    coros: list = []
    hass.async_create_task = MagicMock(side_effect=coros.append)
    return coros


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

    @pytest.mark.parametrize(
        ("hour", "minute", "expected"),
        [(23, 45, "ForceCharge"), (2, 0, "ForceCharge"), (21, 0, "SelfUse")],
    )
    def test_narrowest_overlapping_group_wins(
        self, hour: int, minute: int, expected: str
    ) -> None:
        # Groups sorted by end time, so the all-day group comes first.
        groups = [
            _group(0, 0, 4, 30, "ForceCharge"),
            _group(0, 0, 23, 59, "SelfUse"),
            _group(23, 30, 23, 59, "ForceCharge"),
        ]
        manager, _, _ = _make_manager(scheduler_enabled=True, groups=groups)
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, hour, minute)
            assert manager._get_active_work_mode() == expected

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
            await manager._evaluate_and_manage()
            manager._coordinator.client.async_set_work_mode.assert_not_called()

    @pytest.mark.asyncio
    async def test_no_op_when_force_charge(self) -> None:
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, _ = _make_manager(
                scheduler_enabled=True,
                groups=[_group(14, 0, 15, 0, "ForceCharge")],
            )
            await manager._evaluate_and_manage()
            manager._coordinator.client.async_set_work_mode.assert_not_called()

    @pytest.mark.asyncio
    async def test_disables_scheduler_and_sets_backup_when_selfuse(self) -> None:
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, all_data = _make_manager(
                scheduler_enabled=True,
                groups=[_group(14, 0, 15, 0, "SelfUse")],
            )
            client = manager._coordinator.client
            await manager._evaluate_and_manage()
            client.async_set_scheduler_flag.assert_called_once_with("SN123", "api-key", False)
            client.async_set_work_mode.assert_called_once_with("SN123", "api-key", "Backup")
            assert manager._managing is True
            assert all_data["schedulerEnabled"] is False
            assert all_data["workMode"] == "Backup"

    @pytest.mark.asyncio
    async def test_sets_backup_when_scheduler_disabled_reads_mode_from_api(self) -> None:
        manager, _, _ = _make_manager(scheduler_enabled=False)
        await manager._evaluate_and_manage()
        manager._coordinator.client.async_get_work_mode.assert_called_once_with(
            "SN123", "api-key"
        )
        assert manager._managing is True
        assert manager._saved_state["work_mode"] == "SelfUse"

    @pytest.mark.asyncio
    async def test_reads_work_mode_from_values_result(self) -> None:
        """The work mode is also read from the result's 'values' mapping."""
        manager, _, _ = _make_manager(scheduler_enabled=False)
        manager._coordinator.client.async_get_work_mode = AsyncMock(
            return_value=(
                FetchResult.OK,
                {"errno": 0, "result": {"values": {"WorkMode": "ForceCharge"}}},
                10,
            )
        )
        await manager._evaluate_and_manage()
        manager._coordinator.client.async_set_work_mode.assert_not_called()

    @pytest.mark.asyncio
    async def test_saves_state_before_switching(self) -> None:
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, all_data = _make_manager(
                scheduler_enabled=True,
                groups=[_group(14, 0, 15, 0, "SelfUse")],
            )
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

            await manager._evaluate_and_manage()
            assert manager._saved_state["work_mode"] == "FeedInFirst"


# ---------------------------------------------------------------------------
# TestRestoreIfManaged
# ---------------------------------------------------------------------------


class TestRestoreIfManaged:
    @pytest.mark.asyncio
    async def test_restores_work_mode_and_reenables_scheduler(self) -> None:
        manager, _, all_data = _make_manager(scheduler_enabled=False, car_is_charging=False)
        manager._managing = True
        manager._saved_state = {"scheduler_enabled": True, "work_mode": "SelfUse"}

        client = manager._coordinator.client
        await manager._restore_if_managed()
        client.async_set_work_mode.assert_called_once_with("SN123", "api-key", "SelfUse")
        client.async_set_scheduler_flag.assert_called_once_with("SN123", "api-key", True)
        assert all_data["schedulerEnabled"] is True
        assert manager._managing is False
        assert manager._saved_state is None

    @pytest.mark.asyncio
    async def test_restores_without_reenabling_when_was_disabled(self) -> None:
        manager, _, all_data = _make_manager(scheduler_enabled=False, car_is_charging=False)
        manager._managing = True
        manager._saved_state = {"scheduler_enabled": False, "work_mode": "SelfUse"}

        await manager._restore_if_managed()
        manager._coordinator.client.async_set_scheduler_flag.assert_not_called()

    @pytest.mark.asyncio
    async def test_no_op_when_not_managing(self) -> None:
        manager, _, _ = _make_manager(car_is_charging=False)
        await manager._restore_if_managed()
        manager._coordinator.client.async_set_work_mode.assert_not_called()

    @pytest.mark.asyncio
    async def test_no_op_when_charging_again(self) -> None:
        manager, _, _ = _make_manager(car_is_charging=True)
        manager._managing = True
        manager._saved_state = {"scheduler_enabled": True, "work_mode": "SelfUse"}
        await manager._restore_if_managed()
        manager._coordinator.client.async_set_work_mode.assert_not_called()
        assert manager._managing is True


# ---------------------------------------------------------------------------
# TestRestoreRetry
# ---------------------------------------------------------------------------

_SAVED = {"scheduler_enabled": True, "work_mode": "SelfUse"}


def _managing_manager() -> tuple[CarChargingManager, MagicMock, dict]:
    manager, hass, all_data = _make_manager(scheduler_enabled=False, car_is_charging=False)
    manager._managing = True
    manager._saved_state = dict(_SAVED)
    # Like DataUpdateCoordinator, notify listeners synchronously.
    manager._coordinator.async_set_updated_data.side_effect = (
        lambda _data: manager._handle_coordinator_update()
    )
    return manager, hass, all_data


class TestRestoreRetry:
    @pytest.mark.asyncio
    @pytest.mark.parametrize(
        "failing_call", ["async_set_work_mode", "async_set_scheduler_flag"]
    )
    async def test_failed_restore_keeps_saved_state_and_retries(
        self, failing_call: str
    ) -> None:
        manager, hass, all_data = _managing_manager()
        client = manager._coordinator.client
        getattr(client, failing_call).return_value = _FAILED

        await manager._restore_if_managed()

        assert manager._managing is True
        assert manager._saved_state == _SAVED
        assert all_data["schedulerEnabled"] is False
        manager._store.async_remove.assert_not_called()
        # No immediate retry loop.
        hass.async_create_task.assert_not_called()

        # The next coordinator update retries, and now succeeds.
        getattr(client, failing_call).return_value = _OK
        tasks = _run_created_tasks(hass)
        manager._handle_coordinator_update()
        assert len(tasks) == 1
        await tasks[0]

        assert client.async_set_work_mode.call_args.args[-1] == "SelfUse"
        assert client.async_set_scheduler_flag.call_args.args[-1] is True
        assert all_data["schedulerEnabled"] is True
        assert manager._managing is False
        manager._store.async_remove.assert_called_once()
        # Succeeding notifies listeners without scheduling another restore.
        assert len(tasks) == 1

    @pytest.mark.asyncio
    async def test_scheduler_not_reenabled_when_work_mode_restore_fails(self) -> None:
        manager, _, _ = _managing_manager()
        client = manager._coordinator.client
        client.async_set_work_mode.return_value = _FAILED
        await manager._restore_if_managed()
        client.async_set_scheduler_flag.assert_not_called()

    @pytest.mark.asyncio
    async def test_charging_again_cancels_retry_and_keeps_saved_state(self) -> None:
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, hass, _ = _managing_manager()
            client = manager._coordinator.client
            client.async_set_scheduler_flag.return_value = _FAILED
            await manager._restore_if_managed()
            assert manager._restore_pending is True

            client.async_set_scheduler_flag.return_value = _OK
            tasks = _run_created_tasks(hass)
            manager._start_charging()
            for coro in tasks:
                await coro
            assert manager._restore_pending is False
            assert manager._managing is True
            assert manager._saved_state == _SAVED
            client.async_get_scheduler_flag.assert_not_called()

            # A coordinator update while charging doesn't restore.
            tasks.clear()
            manager._handle_coordinator_update()
            assert tasks == []

    def test_coordinator_update_without_pending_restore_does_nothing(self) -> None:
        manager, hass, _ = _make_manager(car_is_charging=False)
        manager._managing = True
        manager._saved_state = dict(_SAVED)
        manager._handle_coordinator_update()
        hass.async_create_task.assert_not_called()


# ---------------------------------------------------------------------------
# TestScheduleChangeWhileCharging
# ---------------------------------------------------------------------------


class TestScheduleChangeWhileCharging:
    def test_updates_saved_scheduler_flag_on_external_change(self) -> None:
        manager, _, all_data = _make_manager(scheduler_enabled=False)
        manager._car_is_charging = True
        manager._managing = True
        manager._saved_state = {"scheduler_enabled": False, "work_mode": "SelfUse"}

        all_data["schedulerEnabled"] = True
        manager._handle_coordinator_update()

        assert manager._saved_state["scheduler_enabled"] is True
        # Persists the updated saved state.
        manager._hass.async_create_task.assert_called_once()

    def test_scheduler_seen_off_does_not_clear_saved_flag(self) -> None:
        """The scheduler is off because we disabled it; that must not be saved."""
        manager, _, all_data = _make_manager(scheduler_enabled=False)
        manager._managing = True
        manager._saved_state = {"scheduler_enabled": True, "work_mode": "SelfUse"}

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


# ---------------------------------------------------------------------------
# TestFullChargeCycle
# ---------------------------------------------------------------------------


class TestFullChargeCycle:
    @pytest.mark.asyncio
    async def test_scheduler_reenabled_after_charge(self) -> None:
        """Scheduler is restored even though coordinator updates report it disabled."""
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, all_data = _make_manager(
                scheduler_enabled=True,
                groups=[_group(14, 0, 15, 0, "SelfUse")],
            )
            # Like DataUpdateCoordinator, notify listeners synchronously.
            manager._coordinator.async_set_updated_data.side_effect = (
                lambda _data: manager._handle_coordinator_update()
            )
            client = manager._coordinator.client
            await manager._evaluate_and_manage()
            # A later poll of the cloud also reports the scheduler as disabled.
            all_data["schedulerEnabled"] = False
            manager._handle_coordinator_update()

            manager._car_is_charging = False
            await manager._restore_if_managed()

            assert client.async_set_scheduler_flag.call_args_list[-1].args[-1] is True
            assert client.async_set_work_mode.call_args_list[-1].args[-1] == "SelfUse"
            assert all_data["schedulerEnabled"] is True

    @pytest.mark.asyncio
    async def test_charge_ending_during_switch_still_restores(self) -> None:
        """A restore requested while switching to Backup runs after the switch."""
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, all_data = _make_manager(
                scheduler_enabled=True,
                groups=[_group(14, 0, 15, 0, "SelfUse")],
            )
            release = asyncio.Event()

            async def slow_flag(*_args):
                await release.wait()
                return _OK

            client = manager._coordinator.client
            client.async_set_scheduler_flag = AsyncMock(side_effect=slow_flag)
            evaluate = asyncio.ensure_future(manager._evaluate_and_manage())
            await asyncio.sleep(0)
            manager._car_is_charging = False
            restore = asyncio.ensure_future(manager._restore_if_managed())
            await asyncio.sleep(0)
            release.set()
            await asyncio.gather(evaluate, restore)

            assert manager._managing is False
            assert client.async_set_work_mode.call_args_list[-1].args[-1] == "SelfUse"
            assert client.async_set_scheduler_flag.call_args_list[-1].args[-1] is True
            assert all_data["schedulerEnabled"] is True

    @pytest.mark.asyncio
    async def test_no_switch_when_charge_already_ended(self) -> None:
        """A queued evaluation does nothing if the car has stopped charging."""
        manager, _, _ = _make_manager(car_is_charging=False)
        await manager._evaluate_and_manage()
        manager._coordinator.client.async_set_work_mode.assert_not_called()


# ---------------------------------------------------------------------------
# TestFreshStateAtChargeStart
# ---------------------------------------------------------------------------


class TestFreshStateAtChargeStart:
    @pytest.mark.asyncio
    async def test_stale_cache_scheduler_actually_on(self) -> None:
        """The cache says the scheduler is off, but FoxESS Cloud says it's on."""
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            groups = [_group(14, 0, 15, 0, "SelfUse")]
            manager, _, all_data = _make_manager(scheduler_enabled=True, groups=groups)
            all_data["schedulerEnabled"] = False
            all_data["schedulerGroups"] = []

            await manager._evaluate_and_manage()

            assert manager._saved_state == {"scheduler_enabled": True, "work_mode": "SelfUse"}
            client = manager._coordinator.client
            client.async_set_scheduler_flag.assert_called_once_with("SN123", "api-key", False)
            client.async_get_work_mode.assert_not_called()

    @pytest.mark.asyncio
    async def test_stale_cache_scheduler_actually_off(self) -> None:
        """The cache says a ForceCharge group is active, but the scheduler is off."""
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, all_data = _make_manager(scheduler_enabled=False)
            all_data["schedulerEnabled"] = True
            all_data["schedulerGroups"] = [_group(14, 0, 15, 0, "ForceCharge")]

            await manager._evaluate_and_manage()

            assert manager._saved_state == {"scheduler_enabled": False, "work_mode": "SelfUse"}
            manager._coordinator.client.async_set_work_mode.assert_called_once_with(
                "SN123", "api-key", "Backup"
            )

    @pytest.mark.asyncio
    @pytest.mark.parametrize(
        ("scheduler_enabled", "failing_call"),
        [
            (True, "async_get_scheduler_flag"),
            (True, "async_get_scheduler_groups"),
            (False, "async_get_work_mode"),
        ],
    )
    async def test_does_nothing_when_a_read_fails_then_retries(
        self, scheduler_enabled: bool, failing_call: str
    ) -> None:
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, all_data = _make_manager(
                scheduler_enabled=scheduler_enabled,
                groups=[_group(14, 0, 15, 0, "SelfUse")],
            )
            client = manager._coordinator.client
            working = getattr(client, failing_call).return_value
            getattr(client, failing_call).return_value = _FAILED

            await manager._evaluate_and_manage()

            client.async_set_scheduler_flag.assert_not_called()
            client.async_set_work_mode.assert_not_called()
            assert manager._managing is False
            assert all_data["schedulerEnabled"] is scheduler_enabled

            # The next coordinator update evaluates again, and now succeeds.
            getattr(client, failing_call).return_value = working
            await manager._evaluate_and_manage()
            assert manager._managing is True
            assert manager._saved_state["scheduler_enabled"] is scheduler_enabled

    @pytest.mark.asyncio
    async def test_reads_cloud_once_per_charge(self) -> None:
        """Re-evaluations during the same charge use the cache."""
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, _ = _make_manager(
                scheduler_enabled=True, groups=[_group(14, 0, 15, 0, "ForceCharge")]
            )
            await manager._evaluate_and_manage()
            await manager._evaluate_and_manage()
            client = manager._coordinator.client
            client.async_get_scheduler_flag.assert_called_once()
            client.async_get_scheduler_groups.assert_called_once()
            client.async_set_work_mode.assert_not_called()

            # A new charge reads it again.
            manager._start_charging()
            await manager._evaluate_and_manage()
            assert client.async_get_scheduler_flag.call_count == 2

    @pytest.mark.asyncio
    async def test_uses_v3_groups_endpoint(self) -> None:
        with patch("custom_components.foxess.car_charging.datetime") as mock_dt:
            mock_dt.now.return_value = datetime(2024, 1, 1, 14, 30)
            manager, _, all_data = _make_manager(scheduler_enabled=True)
            groups = [_group(14, 0, 15, 0, "ForceCharge")]
            coordinator = manager._coordinator
            coordinator.scheduler_api_version = "v3"
            coordinator.client.async_get_scheduler_groups_v3 = AsyncMock(
                return_value=_groups_response(groups)
            )

            await manager._evaluate_and_manage()

            coordinator.client.async_get_scheduler_groups.assert_not_called()
            assert all_data["schedulerGroups"] == groups


# ---------------------------------------------------------------------------
# TestPersistence
# ---------------------------------------------------------------------------


class TestPersistence:
    @pytest.mark.asyncio
    async def test_saved_state_persisted_and_removed(self) -> None:
        manager, _, _ = _make_manager(scheduler_enabled=False)
        store = manager._store

        await manager._evaluate_and_manage()
        store.async_save.assert_called_once_with(
            {"saved_state": {"scheduler_enabled": False, "work_mode": "SelfUse"}}
        )

        manager._car_is_charging = False
        await manager._restore_if_managed()
        store.async_remove.assert_called_once()

    @pytest.mark.asyncio
    async def test_nothing_persisted_when_switch_fails(self) -> None:
        manager, _, _ = _make_manager(scheduler_enabled=False)
        manager._coordinator.client.async_set_work_mode = AsyncMock(return_value=_FAILED)
        await manager._evaluate_and_manage()
        manager._store.async_save.assert_not_called()


# ---------------------------------------------------------------------------
# TestResumeAfterRestart
# ---------------------------------------------------------------------------

_STORED = {"saved_state": {"scheduler_enabled": True, "work_mode": "SelfUse"}}


class TestResumeAfterRestart:
    async def _setup(self, manager: CarChargingManager) -> None:
        with patch(
            "custom_components.foxess.car_charging.async_track_state_change_event"
        ):
            await manager.async_setup("binary_sensor.ev")

    @pytest.mark.asyncio
    async def test_restores_when_car_stopped_during_restart(self) -> None:
        manager, hass, all_data = _make_manager(car_is_charging=False, stored=_STORED)
        hass.states.get.return_value = _state("off")
        tasks = _run_created_tasks(hass)

        await self._setup(manager)
        assert manager._managing is True
        for coro in tasks:
            await coro

        client = manager._coordinator.client
        client.async_set_work_mode.assert_called_once_with("SN123", "api-key", "SelfUse")
        client.async_set_scheduler_flag.assert_called_once_with("SN123", "api-key", True)
        assert manager._managing is False
        manager._store.async_remove.assert_called_once()

    @pytest.mark.asyncio
    async def test_keeps_managing_when_car_still_charging(self) -> None:
        manager, hass, all_data = _make_manager(car_is_charging=False, stored=_STORED)
        all_data["workMode"] = "Backup"
        hass.states.get.return_value = _state("on")
        tasks = _run_created_tasks(hass)

        await self._setup(manager)
        for coro in tasks:
            await coro

        client = manager._coordinator.client
        client.async_get_scheduler_flag.assert_not_called()
        client.async_set_work_mode.assert_not_called()
        assert manager._managing is True
        assert manager._saved_state == _STORED["saved_state"]

        # Charging then ends normally.
        manager._handle_charging_state_change(_state_event("on", "off"))
        for coro in tasks[1:]:
            await coro
        client.async_set_scheduler_flag.assert_called_once_with("SN123", "api-key", True)

    @pytest.mark.asyncio
    async def test_waits_for_entity_state_before_restoring(self) -> None:
        manager, hass, _ = _make_manager(car_is_charging=False, stored=_STORED)
        hass.states.get.return_value = _state("unavailable")
        tasks = _run_created_tasks(hass)

        await self._setup(manager)
        assert tasks == []

        manager._handle_charging_state_change(_state_event("unavailable", "off"))
        for coro in tasks:
            await coro
        manager._coordinator.client.async_set_scheduler_flag.assert_called_once_with(
            "SN123", "api-key", True
        )
        assert manager._managing is False

    @pytest.mark.asyncio
    async def test_no_stored_state_does_nothing(self) -> None:
        manager, hass, _ = _make_manager(car_is_charging=False)
        hass.states.get.return_value = _state("off")
        tasks = _run_created_tasks(hass)

        await self._setup(manager)
        assert manager._managing is False
        assert tasks == []

    def test_entity_appearing_off_when_not_managing_does_nothing(self) -> None:
        manager, hass, _ = _make_manager(car_is_charging=False)
        manager._handle_charging_state_change(_state_event("unavailable", "off"))
        hass.async_create_task.assert_not_called()


@pytest.mark.asyncio
async def test_saved_state_round_trips_through_real_store(hass, hass_storage) -> None:
    """The saved state is written to HA storage and resumed by a new manager."""
    manager, _, _ = _make_manager(scheduler_enabled=False)
    coordinator = manager._coordinator
    manager = CarChargingManager(hass, coordinator)
    manager._car_is_charging = True

    await manager._evaluate_and_manage()
    key = "foxess.car_charging.SN123"
    assert hass_storage[key]["data"] == {
        "saved_state": {"scheduler_enabled": False, "work_mode": "SelfUse"}
    }

    resumed = CarChargingManager(hass, coordinator)
    with patch("custom_components.foxess.car_charging.async_track_state_change_event"):
        await resumed.async_setup("binary_sensor.ev")
    assert resumed._managing is True
    assert resumed._saved_state == {"scheduler_enabled": False, "work_mode": "SelfUse"}

    resumed._car_is_charging = False
    await resumed._restore_if_managed()
    await hass.async_block_till_done()
    assert key not in hass_storage
