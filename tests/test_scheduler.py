"""Tests for the FoxESS scheduler card backend."""

from unittest.mock import AsyncMock, MagicMock, patch

import pytest

from custom_components.foxess import scheduler
from custom_components.foxess.const import DOMAIN, FetchResult

_OK = (FetchResult.OK, {"errno": 0, "msg": "success"}, 10)


def _client(**overrides) -> MagicMock:
    """Return a mock FoxESSApiClient whose write calls succeed unless overridden."""
    client = MagicMock()
    for name in (
        "async_set_scheduler_flag",
        "async_set_scheduler_groups",
        "async_set_battery_soc",
        "async_set_device_setting",
    ):
        setattr(client, name, AsyncMock(return_value=overrides.get(name, _OK)))
    return client


def _coordinator(
    scheduler_enabled: bool = False, min_soc: int | None = 10, client=None
) -> MagicMock:
    coordinator = MagicMock()
    coordinator.devicesn = "SN1"
    coordinator.apiKey = "key"
    coordinator.client = client or _client()
    battery = {} if min_soc is None else {"minSoc": min_soc}
    coordinator.allData = {
        "schedulerEnabled": scheduler_enabled,
        "schedulerGroups": [],
        "battery": battery,
    }
    coordinator.data = coordinator.allData
    return coordinator


def _hass_with(coordinator) -> MagicMock:
    hass = MagicMock()
    hass.data = {DOMAIN: {"entry": {"coordinator": coordinator}}} if coordinator else {}
    return hass


def _connection() -> MagicMock:
    conn = MagicMock()
    conn.send_result = MagicMock()
    conn.send_error = MagicMock()
    return conn


_GROUP = {
    "enable": 1,
    "startHour": 0,
    "startMinute": 0,
    "endHour": 6,
    "endMinute": 0,
    "workMode": "SelfUse",
    "extraParam": {"minSocOnGrid": 10, "fdSoc": 90, "fdPwr": 0, "maxSoc": 100},
}


# ---------------------------------------------------------------------------
# set_scheduler_groups
# ---------------------------------------------------------------------------


@pytest.mark.asyncio
class TestSetSchedulerGroups:
    """Tests for set_scheduler_groups with ordinary time slots."""

    async def test_ok(self) -> None:
        """Returns OK and sends the groups when the API call succeeds."""
        coordinator = _coordinator()
        result, _ = await scheduler.set_scheduler_groups(coordinator, [_GROUP])
        assert result is FetchResult.OK
        coordinator.client.async_set_scheduler_groups.assert_called_once_with(
            "SN1", "key", [_GROUP]
        )

    async def test_auth_failed(self) -> None:
        """Returns AUTH_FAILED with the API message when the key is rejected."""
        client = _client(
            async_set_scheduler_groups=(
                FetchResult.AUTH_FAILED,
                {"errno": 41808, "msg": "auth error"},
                10,
            )
        )
        result, msg = await scheduler.set_scheduler_groups(
            _coordinator(client=client), [_GROUP]
        )
        assert result is FetchResult.AUTH_FAILED
        assert msg == "auth error"

    async def test_error(self) -> None:
        """Returns ERROR on a generic non-zero errno."""
        client = _client(
            async_set_scheduler_groups=(FetchResult.ERROR, {"errno": 40001}, 10)
        )
        result, msg = await scheduler.set_scheduler_groups(
            _coordinator(client=client), [_GROUP]
        )
        assert result is FetchResult.ERROR
        assert msg == "FoxESS Cloud returned an error."

    async def test_network_error(self) -> None:
        """Returns ERROR with a retry message when there is no response."""
        client = _client(async_set_scheduler_groups=(FetchResult.ERROR, None, 10))
        result, msg = await scheduler.set_scheduler_groups(
            _coordinator(client=client), [_GROUP]
        )
        assert result is FetchResult.ERROR
        assert msg == "Network error — please try again."


@pytest.mark.asyncio
class TestSetSchedulerGroupsRemainingGroup:
    """Tests for set_scheduler_groups remaining-group (00:00–23:59) handling."""

    _REMAINING = {
        "startHour": 0,
        "startMinute": 0,
        "endHour": 23,
        "endMinute": 59,
        "enable": 1,
        "workMode": "SelfUse",
        "extraParam": {"minSocOnGrid": 20, "fdSoc": 50, "fdPwr": 0, "maxSoc": 85},
    }
    _SCHEDULED = {
        "startHour": 6,
        "startMinute": 0,
        "endHour": 12,
        "endMinute": 0,
        "enable": 1,
        "workMode": "ForceCharge",
        "extraParam": {"minSocOnGrid": 10, "fdSoc": 50, "fdPwr": 2000, "maxSoc": 100},
    }

    async def test_writes_soc_settings_and_not_scheduler(self) -> None:
        """The remaining group is written as battery SoC and MaxSoc settings only."""
        coordinator = _coordinator(min_soc=15)
        client = coordinator.client
        result, _ = await scheduler.set_scheduler_groups(coordinator, [self._REMAINING])
        assert result is FetchResult.OK
        client.async_set_battery_soc.assert_called_once_with(
            "SN1", "key", min_soc=15, min_soc_on_grid=20
        )
        client.async_set_device_setting.assert_called_once_with(
            "SN1", "key", "MaxSoc", "85"
        )
        client.async_set_scheduler_groups.assert_not_called()

    async def test_scheduled_groups_sent_without_remaining_group(self) -> None:
        """Only the ordinary groups are sent to the scheduler API."""
        coordinator = _coordinator()
        await scheduler.set_scheduler_groups(
            coordinator, [self._SCHEDULED, self._REMAINING]
        )
        coordinator.client.async_set_scheduler_groups.assert_called_once_with(
            "SN1", "key", [self._SCHEDULED]
        )

    async def test_disables_and_reenables_scheduler_when_enabled(self) -> None:
        """The scheduler is turned off around the SoC writes and back on afterwards."""
        coordinator = _coordinator(scheduler_enabled=True)
        result, _ = await scheduler.set_scheduler_groups(coordinator, [self._REMAINING])
        assert result is FetchResult.OK
        calls = coordinator.client.async_set_scheduler_flag.call_args_list
        assert [c.args for c in calls] == [("SN1", "key", False), ("SN1", "key", True)]
        assert coordinator.allData["schedulerEnabled"] is True

    async def test_no_flag_calls_when_scheduler_not_enabled(self) -> None:
        """No flag calls are made at all when the scheduler was not active."""
        coordinator = _coordinator(scheduler_enabled=False)
        await scheduler.set_scheduler_groups(coordinator, [self._REMAINING])
        coordinator.client.async_set_scheduler_flag.assert_not_called()

    async def test_returns_error_when_disable_flag_fails(self) -> None:
        """Returns the error immediately when disabling the scheduler fails."""
        client = _client(
            async_set_scheduler_flag=(FetchResult.ERROR, {"msg": "flag error"}, 10)
        )
        coordinator = _coordinator(scheduler_enabled=True, client=client)
        result, msg = await scheduler.set_scheduler_groups(coordinator, [self._REMAINING])
        assert result is FetchResult.ERROR
        assert msg == "flag error"
        client.async_set_battery_soc.assert_not_called()

    async def test_returns_error_when_battery_soc_fails(self) -> None:
        """Returns the error immediately when writing the SoC settings fails."""
        client = _client(
            async_set_battery_soc=(FetchResult.ERROR, {"msg": "soc error"}, 10)
        )
        result, msg = await scheduler.set_scheduler_groups(
            _coordinator(client=client), [self._REMAINING]
        )
        assert result is FetchResult.ERROR
        assert msg == "soc error"
        client.async_set_device_setting.assert_not_called()

    async def test_returns_error_when_max_soc_setting_fails(self) -> None:
        """Returns the error when writing MaxSoc fails."""
        client = _client(
            async_set_device_setting=(FetchResult.ERROR, {"msg": "maxsoc error"}, 10)
        )
        result, msg = await scheduler.set_scheduler_groups(
            _coordinator(client=client), [self._REMAINING]
        )
        assert result is FetchResult.ERROR
        assert msg == "maxsoc error"

    async def test_defaults(self) -> None:
        """Falls back to minSoc=10 and maxSoc=100 when they are unknown."""
        remaining = {**self._REMAINING, "extraParam": {"minSocOnGrid": 20}}
        coordinator = _coordinator(min_soc=None)
        await scheduler.set_scheduler_groups(coordinator, [remaining])
        coordinator.client.async_set_battery_soc.assert_called_once_with(
            "SN1", "key", min_soc=10, min_soc_on_grid=20
        )
        coordinator.client.async_set_device_setting.assert_called_once_with(
            "SN1", "key", "MaxSoc", "100"
        )


# ---------------------------------------------------------------------------
# WebSocket handlers
# ---------------------------------------------------------------------------


@pytest.mark.asyncio
class TestWsSaveSchedule:
    """Tests for the foxess/save_schedule WebSocket handler."""

    def _msg(self, msg_id: int, device_sn: str = "SN1") -> dict:
        return {"id": msg_id, "type": "foxess/save_schedule", "deviceSN": device_sn, "groups": [_GROUP]}

    async def test_unknown_device_sends_not_found_error(self) -> None:
        """Handler sends ERR_NOT_FOUND when deviceSN is not configured."""
        conn = _connection()
        await scheduler._ws_save_schedule.__wrapped__(_hass_with(None), conn, self._msg(7, "UNKNOWN"))
        args = conn.send_error.call_args[0]
        assert args[0] == 7
        assert "not_found" in args[1]

    async def test_success_updates_coordinator_and_sends_result(self) -> None:
        """Handler stores the new groups and sends send_result on success."""
        coordinator = _coordinator()
        conn = _connection()
        await scheduler._ws_save_schedule.__wrapped__(_hass_with(coordinator), conn, self._msg(3))
        conn.send_result.assert_called_once_with(3, {"ok": True})
        conn.send_error.assert_not_called()
        assert coordinator.allData["schedulerGroups"] == [_GROUP]
        coordinator.async_set_updated_data.assert_called_once_with(coordinator.allData)

    @pytest.mark.parametrize(
        ("result", "error_code"),
        [(FetchResult.AUTH_FAILED, "unauthorized"), (FetchResult.ERROR, "unknown_error")],
    )
    async def test_failure_sends_error(self, result: FetchResult, error_code: str) -> None:
        """Handler maps auth failures and other errors to WebSocket error codes."""
        client = _client(async_set_scheduler_groups=(result, {"msg": "bad"}, 10))
        coordinator = _coordinator(client=client)
        conn = _connection()
        await scheduler._ws_save_schedule.__wrapped__(_hass_with(coordinator), conn, self._msg(5))
        args = conn.send_error.call_args[0]
        assert args[0] == 5
        assert error_code in args[1]
        coordinator.async_set_updated_data.assert_not_called()


@pytest.mark.asyncio
class TestWsTemplates:
    """Tests for the foxess/get_templates and foxess/save_template WebSocket handlers."""

    _GROUPS = [{"workMode": "ForceCharge", "startHour": 0, "startMinute": 0, "endHour": 6, "endMinute": 0}]

    def _hass(self, data: dict | None) -> MagicMock:
        store = MagicMock()
        store.async_load = AsyncMock(return_value=data)
        store.async_save = AsyncMock()
        hass = MagicMock()
        hass.data = {scheduler._TEMPLATES_STORE_KEY: store}
        return hass

    def _save_msg(self, name: str) -> dict:
        return {"id": 1, "type": "foxess/save_template", "deviceSN": "SN1", "name": name, "groups": self._GROUPS}

    @pytest.mark.parametrize("data", [None, {"OTHER_SN": [{"name": "t1", "groups": []}]}])
    async def test_get_returns_empty_list_without_templates(self, data) -> None:
        """Returns an empty list when nothing is stored for the device."""
        conn = _connection()
        msg = {"id": 1, "type": "foxess/get_templates", "deviceSN": "SN1"}
        await scheduler._ws_get_templates.__wrapped__(self._hass(data), conn, msg)
        conn.send_result.assert_called_once_with(1, {"templates": []})

    async def test_get_returns_saved_templates(self) -> None:
        """Returns the stored template list for the device."""
        templates = [{"name": "Morning", "groups": self._GROUPS}]
        conn = _connection()
        msg = {"id": 3, "type": "foxess/get_templates", "deviceSN": "SN1"}
        await scheduler._ws_get_templates.__wrapped__(self._hass({"SN1": templates}), conn, msg)
        conn.send_result.assert_called_once_with(3, {"templates": templates})

    async def test_save_new_template(self) -> None:
        """Saves a new template and keeps other devices' templates."""
        hass = self._hass({"OTHER": [{"name": "t", "groups": []}]})
        conn = _connection()
        await scheduler._ws_save_template.__wrapped__(hass, conn, self._save_msg("Morning"))
        conn.send_result.assert_called_once_with(1, {"ok": True})
        saved = hass.data[scheduler._TEMPLATES_STORE_KEY].async_save.call_args[0][0]
        assert saved == {
            "OTHER": [{"name": "t", "groups": []}],
            "SN1": [{"name": "Morning", "groups": self._GROUPS}],
        }

    async def test_save_overwrites_template_with_same_name(self) -> None:
        """Overwrites an existing template rather than creating a duplicate."""
        hass = self._hass({"SN1": [{"name": "Morning", "groups": []}]})
        await scheduler._ws_save_template.__wrapped__(hass, _connection(), self._save_msg("Morning"))
        saved = hass.data[scheduler._TEMPLATES_STORE_KEY].async_save.call_args[0][0]
        assert saved["SN1"] == [{"name": "Morning", "groups": self._GROUPS}]

    async def test_save_appends_template_with_new_name(self) -> None:
        """Appends a second template when the name is different."""
        hass = self._hass({"SN1": [{"name": "Morning", "groups": []}]})
        await scheduler._ws_save_template.__wrapped__(hass, _connection(), self._save_msg("Evening"))
        saved = hass.data[scheduler._TEMPLATES_STORE_KEY].async_save.call_args[0][0]
        assert [t["name"] for t in saved["SN1"]] == ["Morning", "Evening"]


# ---------------------------------------------------------------------------
# async_setup_scheduler_card
# ---------------------------------------------------------------------------


@pytest.mark.usefixtures("enable_custom_integrations")
async def test_setup_registers_commands_once(hass) -> None:
    """Setup registers the WebSocket commands and template store, and is idempotent."""
    with patch(
        "custom_components.foxess.scheduler.websocket_api.async_register_command"
    ) as register:
        await scheduler.async_setup_scheduler_card(hass)
        await scheduler.async_setup_scheduler_card(hass)

    commands = [call.args[1] for call in register.call_args_list]
    assert commands == [
        "foxess/save_schedule",
        "foxess/get_templates",
        "foxess/save_template",
    ]
    assert scheduler._TEMPLATES_STORE_KEY in hass.data


@pytest.mark.asyncio
class TestSetSchedulerGroupsV3:
    """Tests for set_scheduler_groups with the V3 scheduler API."""

    _REMAINING = {
        "startHour": 0,
        "startMinute": 0,
        "endHour": 23,
        "endMinute": 59,
        "workMode": "SelfUse",
        "extraParam": {"minSocOnGrid": 30, "maxSoc": 90},
    }

    def _coordinator(self, client=None) -> MagicMock:
        client = client or _client()
        client.async_set_scheduler_groups_v3 = AsyncMock(return_value=_OK)
        coordinator = _coordinator(scheduler_enabled=True, client=client)
        coordinator.scheduler_api_version = "v3"
        return coordinator

    async def test_sends_all_groups_including_remaining(self) -> None:
        """All groups, including the remaining slot, go to the V3 endpoint unchanged."""
        coordinator = self._coordinator()
        client = coordinator.client
        result, _ = await scheduler.set_scheduler_groups(coordinator, [_GROUP, self._REMAINING])
        assert result is FetchResult.OK
        client.async_set_scheduler_groups_v3.assert_called_once_with(
            "SN1", "key", [_GROUP, self._REMAINING]
        )
        client.async_set_scheduler_groups.assert_not_called()
        client.async_set_battery_soc.assert_not_called()
        client.async_set_device_setting.assert_not_called()
        client.async_set_scheduler_flag.assert_not_called()

    async def test_no_call_for_empty_schedule(self) -> None:
        """An empty schedule is not sent."""
        coordinator = self._coordinator()
        result, _ = await scheduler.set_scheduler_groups(coordinator, [])
        assert result is FetchResult.OK
        coordinator.client.async_set_scheduler_groups_v3.assert_not_called()

    async def test_error(self) -> None:
        """Returns the API error message on failure."""
        coordinator = self._coordinator()
        coordinator.client.async_set_scheduler_groups_v3 = AsyncMock(
            return_value=(FetchResult.AUTH_FAILED, {"msg": "bad key"}, 10)
        )
        result, msg = await scheduler.set_scheduler_groups(coordinator, [_GROUP])
        assert result is FetchResult.AUTH_FAILED
        assert msg == "bad key"
