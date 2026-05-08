"""Unit tests for FoxESS sensor entity native_value logic."""

import json
from unittest.mock import AsyncMock, MagicMock, patch

from custom_components.foxess.sensor import (
    _FOXESS_DEVICES_KEY,
    FetchResult,
    FoxESSBatMinSoC,
    FoxESSBatMinSoConGrid,
    FoxESSEnergyFeedin,
    FoxESSEnergyGenerated,
    FoxESSEnergyLoad,
    FoxESSEnergyThroughput,
    FoxESSPower,
    FoxESSPowerFactor,
    FoxESSReactivePower,
    FoxESSResidualEnergy,
    FoxESSRunningState,
    FoxESSSchedulerGroups,
    _ws_save_schedule,
    getReportDailyGeneration,
    setSchedulerSegments,
)
import pytest


def _coordinator(data: dict) -> MagicMock:
    mock = MagicMock()
    mock.data = data
    return mock


# ---------------------------------------------------------------------------
# FoxESSPower — representative of all parameterised raw-data sensors
# ---------------------------------------------------------------------------


class TestFoxESSPower:
    """Tests for FoxESSPower native_value."""

    def _make(self, data: dict) -> FoxESSPower:
        return FoxESSPower(
            _coordinator(data),
            "Inverter",
            "DEV01",
            "Grid Power",
            "gridPower",
            "meterPower",
        )

    def test_returns_value_when_online_and_key_present(self) -> None:
        """Returns the raw value when online and key exists."""
        assert (
            self._make({"online": True, "raw": {"meterPower": 3.5}}).native_value == 3.5
        )

    def test_returns_none_when_key_missing(self) -> None:
        """Returns None when the key is absent from raw data."""
        assert self._make({"online": True, "raw": {}}).native_value is None

    def test_returns_none_when_offline(self) -> None:
        """Returns None when the inverter is offline."""
        assert (
            self._make({"online": False, "raw": {"meterPower": 3.5}}).native_value
            is None
        )

    def test_returns_none_when_raw_falsy(self) -> None:
        """Returns None when raw data is None."""
        assert self._make({"online": True, "raw": None}).native_value is None


# ---------------------------------------------------------------------------
# FoxESSReactivePower — hardcoded key, value scaled × 1000 (kVAr → VAr)
# ---------------------------------------------------------------------------


class TestFoxESSReactivePower:
    """Tests for FoxESSReactivePower native_value."""

    def _make(self, data: dict) -> FoxESSReactivePower:
        return FoxESSReactivePower(_coordinator(data), "Inverter", "DEV01")

    def test_scales_value_by_1000(self) -> None:
        """Returns value multiplied by 1000 to convert kVAr to VAr."""
        assert (
            self._make({"online": True, "raw": {"ReactivePower": 2.5}}).native_value
            == 2500
        )

    def test_returns_none_when_key_missing(self) -> None:
        """Returns None when ReactivePower is absent from raw data."""
        assert self._make({"online": True, "raw": {}}).native_value is None

    def test_returns_none_when_offline(self) -> None:
        """Returns None when the inverter is offline."""
        assert (
            self._make({"online": False, "raw": {"ReactivePower": 2.5}}).native_value
            is None
        )


# ---------------------------------------------------------------------------
# FoxESSEnergyFeedin — reads from coordinator.data["report"]
# ---------------------------------------------------------------------------


class TestFoxESSEnergyFeedin:
    """Tests for FoxESSEnergyFeedin native_value."""

    def _make(self, data: dict) -> FoxESSEnergyFeedin:
        return FoxESSEnergyFeedin(_coordinator(data), "Inverter", "DEV01")

    def test_returns_value_when_present(self) -> None:
        """Returns the report value when the key exists."""
        assert self._make({"report": {"feedin": 12.5}}).native_value == 12.5

    def test_returns_zero_when_value_is_zero(self) -> None:
        """Returns 0 when the report value is zero."""
        assert self._make({"report": {"feedin": 0}}).native_value == 0

    def test_does_not_round_value(self) -> None:
        """Returns the value unrounded (_round=False for this subclass)."""
        assert self._make({"report": {"feedin": 12.12345}}).native_value == 12.12345

    def test_returns_none_when_key_missing(self) -> None:
        """Returns None when feedin key is absent from report."""
        assert self._make({"report": {}}).native_value is None


# ---------------------------------------------------------------------------
# FoxESSEnergyLoad — _round=True subclass of _ReportSensor
# ---------------------------------------------------------------------------


class TestFoxESSEnergyLoad:
    """Tests for FoxESSEnergyLoad native_value, which rounds to 3 decimal places."""

    def _make(self, data: dict) -> FoxESSEnergyLoad:
        """Create a FoxESSEnergyLoad sensor with the given coordinator data."""
        return FoxESSEnergyLoad(_coordinator(data), "Inverter", "DEV01")

    def test_rounds_value_to_3_decimal_places(self) -> None:
        """Returns value rounded to 3 decimal places."""
        assert self._make({"report": {"loads": 12.12345}}).native_value == 12.123

    def test_returns_zero_when_value_is_zero(self) -> None:
        """Returns 0 when the report value is zero."""
        assert self._make({"report": {"loads": 0}}).native_value == 0

    def test_returns_none_when_key_missing(self) -> None:
        """Returns None when loads key is absent from report."""
        assert self._make({"report": {}}).native_value is None


# ---------------------------------------------------------------------------
# FoxESSRunningState — maps numeric string codes to descriptive labels
# ---------------------------------------------------------------------------


class TestFoxESSRunningState:
    """Tests for FoxESSRunningState native_value."""

    def _make(self, data: dict) -> FoxESSRunningState:
        return FoxESSRunningState(
            _coordinator(data),
            "Inverter",
            "DEV01",
            "Running State",
            "runningState",
            "runningState",
        )

    @pytest.mark.parametrize(
        ("code", "label"),
        [
            ("160", "self-test"),
            ("161", "waiting"),
            ("162", "checking"),
            ("163", "on-grid"),
            ("164", "off-grid"),
            ("165", "fault"),
            ("166", "permanent-fault"),
            ("167", "standby"),
            ("168", "upgrading"),
            ("169", "fct"),
            ("170", "illegal"),
        ],
    )
    def test_known_code_returns_descriptive_label(self, code: str, label: str) -> None:
        """Returns a descriptive label for each known running state code."""
        sensor = self._make({"raw": {"runningState": code}})
        assert sensor.native_value == f"{code}: {label}"

    def test_unknown_code_returns_unknown_label(self) -> None:
        """Returns 'unknown code' suffix for unrecognised state codes."""
        assert (
            self._make({"raw": {"runningState": "999"}}).native_value
            == "999: unknown code"
        )

    def test_returns_none_when_key_missing(self) -> None:
        """Returns None when the state key is absent from raw data."""
        assert self._make({"raw": {}}).native_value is None

    def test_returns_none_when_no_raw_data(self) -> None:
        """Returns None when raw data is None."""
        assert self._make({"raw": None}).native_value is None


# ---------------------------------------------------------------------------
# FoxESSEnergyGenerated — reads from coordinator.data["reportDailyGeneration"]
# ---------------------------------------------------------------------------


class TestFoxESSEnergyGenerated:
    """Tests for FoxESSEnergyGenerated native_value."""

    def _make(self, data: dict) -> FoxESSEnergyGenerated:
        return FoxESSEnergyGenerated(
            _coordinator(data), "Inverter", "DEV01",
            "Energy Generated", "energy-generated", "value",
        )

    def test_returns_rounded_positive_value(self) -> None:
        """Returns value rounded to 3 decimal places when positive."""
        assert self._make({"reportDailyGeneration": {"value": 12.12345}}).native_value == 12.123

    def test_returns_zero_for_zero_value(self) -> None:
        """Returns 0 when the stored value is zero."""
        assert self._make({"reportDailyGeneration": {"value": 0}}).native_value == 0

    def test_returns_zero_for_negative_value(self) -> None:
        """Returns 0 when the stored value is negative."""
        assert self._make({"reportDailyGeneration": {"value": -5.0}}).native_value == 0

    def test_returns_none_when_key_missing(self) -> None:
        """Returns None when the key is absent from reportDailyGeneration."""
        assert self._make({"reportDailyGeneration": {}}).native_value is None


# ---------------------------------------------------------------------------
# FoxESSEnergyThroughput — reads from coordinator.data["raw"]
# ---------------------------------------------------------------------------


class TestFoxESSEnergyThroughput:
    """Tests for FoxESSEnergyThroughput native_value."""

    def _make(self, data: dict) -> FoxESSEnergyThroughput:
        return FoxESSEnergyThroughput(_coordinator(data), "Inverter", "DEV01")

    def test_returns_rounded_positive_value(self) -> None:
        """Returns value rounded to 3 decimal places when positive."""
        assert self._make({"online": True, "raw": {"energyThroughput": 5.6789}}).native_value == 5.679

    def test_returns_zero_for_zero_value(self) -> None:
        """Returns 0 when the stored value is zero."""
        assert self._make({"online": True, "raw": {"energyThroughput": 0}}).native_value == 0

    def test_returns_zero_for_negative_value(self) -> None:
        """Returns 0 when the stored value is negative."""
        assert self._make({"online": True, "raw": {"energyThroughput": -1.0}}).native_value == 0

    def test_returns_none_when_key_missing(self) -> None:
        """Returns None when energyThroughput is absent from raw data."""
        assert self._make({"online": True, "raw": {}}).native_value is None

    def test_returns_none_when_offline(self) -> None:
        """Returns None when the inverter is offline."""
        assert self._make({"online": False, "raw": {"energyThroughput": 5.0}}).native_value is None


# ---------------------------------------------------------------------------
# getReportDailyGeneration — parses today/month/cumulative from API response
# ---------------------------------------------------------------------------


def _make_response(result: dict, errno: int = 0, msg: str = "success") -> str:
    return json.dumps({"errno": errno, "msg": msg, "result": result})


def _rest_data_mock(response_json: str | None) -> MagicMock:
    mock = MagicMock()
    mock.async_update = AsyncMock()
    mock.last_exception = None
    mock.data = response_json
    return mock


@pytest.mark.asyncio
class TestGetReportDailyGeneration:
    """Tests for getReportDailyGeneration data parsing."""

    async def _call(self, response_json: str | None) -> dict:
        all_data = {"reportDailyGeneration": {}}
        with (
            patch("custom_components.foxess.sensor.waitforAPI", new_callable=AsyncMock),
            patch("custom_components.foxess.sensor.GetAuth"),
            patch(
                "custom_components.foxess.sensor.RestData",
                return_value=_rest_data_mock(response_json),
            ),
        ):
            result = await getReportDailyGeneration(MagicMock(), all_data, "key", "SN1")
        return result, all_data["reportDailyGeneration"]

    async def test_all_keys_present(self) -> None:
        """Stores today→value, month→month, cumulative→cumulative when all present."""
        payload = _make_response({"today": 1.5, "month": 30.0, "cumulative": 500.0})
        result, data = await self._call(payload)
        assert result is FetchResult.OK
        assert data == {"value": 1.5, "month": 30.0, "cumulative": 500.0}

    async def test_missing_today_defaults_to_zero(self) -> None:
        """Sets value to 0 when today is absent from the API result."""
        payload = _make_response({"month": 30.0, "cumulative": 500.0})
        _, data = await self._call(payload)
        assert data["value"] == 0

    async def test_missing_month_defaults_to_zero(self) -> None:
        """Sets month to 0 when month is absent from the API result."""
        payload = _make_response({"today": 1.5, "cumulative": 500.0})
        _, data = await self._call(payload)
        assert data["month"] == 0

    async def test_missing_cumulative_defaults_to_zero(self) -> None:
        """Sets cumulative to 0 when cumulative is absent from the API result."""
        payload = _make_response({"today": 1.5, "month": 30.0})
        _, data = await self._call(payload)
        assert data["cumulative"] == 0

    async def test_bad_errno_returns_error(self) -> None:
        """Returns ERROR when the API response errno is non-zero."""
        payload = _make_response({}, errno=40001, msg="error")
        result, _ = await self._call(payload)
        assert result is FetchResult.ERROR

    async def test_no_data_returns_error(self) -> None:
        """Returns ERROR when RestData yields no data."""
        result, _ = await self._call(None)
        assert result is FetchResult.ERROR


# ---------------------------------------------------------------------------
# FoxESSPowerFactor — pure _FixedRawDataSensor subclass (no native_value override)
# ---------------------------------------------------------------------------


class TestFoxESSPowerFactor:
    """Tests for FoxESSPowerFactor native_value via _FixedRawDataSensor base class."""

    def _make(self, data: dict) -> FoxESSPowerFactor:
        return FoxESSPowerFactor(_coordinator(data), "Inverter", "DEV01")

    def test_returns_value_when_online_and_key_present(self) -> None:
        """Returns the raw value when online and PowerFactor key exists."""
        assert self._make({"online": True, "raw": {"PowerFactor": 0.98}}).native_value == 0.98

    def test_returns_none_when_key_missing(self) -> None:
        """Returns None when PowerFactor is absent from raw data."""
        assert self._make({"online": True, "raw": {}}).native_value is None

    def test_returns_none_when_offline(self) -> None:
        """Returns None when the inverter is offline."""
        assert self._make({"online": False, "raw": {"PowerFactor": 0.98}}).native_value is None

    def test_returns_none_when_raw_falsy(self) -> None:
        """Returns None when raw data is None."""
        assert self._make({"online": True, "raw": None}).native_value is None


# ---------------------------------------------------------------------------
# FoxESSResidualEnergy — _FixedRawDataSensor subclass with scale-correction logic
# ---------------------------------------------------------------------------


class TestFoxESSResidualEnergy:
    """Tests for FoxESSResidualEnergy native_value scale-correction behaviour."""

    def _make(self, data: dict) -> FoxESSResidualEnergy:
        return FoxESSResidualEnergy(_coordinator(data), "Inverter", "DEV01")

    def test_returns_value_unchanged_when_in_normal_range(self) -> None:
        """Returns the raw value unmodified when 0 < value <= 50."""
        assert self._make({"online": True, "raw": {"ResidualEnergy": 10.0}}).native_value == 10.0

    def test_divides_by_100_when_value_exceeds_50(self) -> None:
        """Divides by 100 when value > 50, correcting the API scale bug."""
        assert self._make({"online": True, "raw": {"ResidualEnergy": 1500.0}}).native_value == 15.0

    def test_returns_zero_when_value_is_zero(self) -> None:
        """Returns 0 when ResidualEnergy is zero."""
        assert self._make({"online": True, "raw": {"ResidualEnergy": 0}}).native_value == 0

    def test_returns_none_when_key_missing(self) -> None:
        """Returns None when ResidualEnergy is absent from raw data."""
        assert self._make({"online": True, "raw": {}}).native_value is None

    def test_returns_none_when_offline(self) -> None:
        """Returns None when the inverter is offline."""
        assert self._make({"online": False, "raw": {"ResidualEnergy": 10.0}}).native_value is None


# ---------------------------------------------------------------------------
# FoxESSBatMinSoC / FoxESSBatMinSoConGrid — _BatterySettingsSensor subclasses
# ---------------------------------------------------------------------------


class TestFoxESSBatMinSoC:
    """Tests for FoxESSBatMinSoC native_value via _BatterySettingsSensor base class."""

    def _make(self, data: dict) -> FoxESSBatMinSoC:
        return FoxESSBatMinSoC(_coordinator(data), "Inverter", "DEV01")

    def test_returns_value_when_online_and_key_present(self) -> None:
        """Returns the battery minSoc value when online."""
        assert self._make({"online": True, "battery": {"minSoc": 10}}).native_value == 10

    def test_returns_none_when_key_missing(self) -> None:
        """Returns None when minSoc is absent from battery data."""
        assert self._make({"online": True, "battery": {}}).native_value is None

    def test_returns_none_when_offline(self) -> None:
        """Returns None when the inverter is offline."""
        assert self._make({"online": False, "battery": {"minSoc": 10}}).native_value is None

    def test_returns_none_when_battery_falsy(self) -> None:
        """Returns None when battery data is empty/falsy."""
        assert self._make({"online": True, "battery": None}).native_value is None


class TestFoxESSBatMinSoConGrid:
    """Tests for FoxESSBatMinSoConGrid native_value via _BatterySettingsSensor base class."""

    def _make(self, data: dict) -> FoxESSBatMinSoConGrid:
        return FoxESSBatMinSoConGrid(_coordinator(data), "Inverter", "DEV01")

    def test_returns_value_when_online_and_key_present(self) -> None:
        """Returns the battery minSocOnGrid value when online."""
        assert self._make({"online": True, "battery": {"minSocOnGrid": 20}}).native_value == 20

    def test_returns_none_when_key_missing(self) -> None:
        """Returns None when minSocOnGrid is absent from battery data."""
        assert self._make({"online": True, "battery": {}}).native_value is None

    def test_returns_none_when_offline(self) -> None:
        """Returns None when the inverter is offline."""
        assert self._make({"online": False, "battery": {"minSocOnGrid": 20}}).native_value is None


# ---------------------------------------------------------------------------
# FoxESSSchedulerGroups
# ---------------------------------------------------------------------------


class TestFoxESSSchedulerGroups:
    """Tests for FoxESSSchedulerGroups."""

    _GROUP = {"enable": 1, "startHour": 0, "startMinute": 0, "endHour": 1, "endMinute": 0,
              "workMode": "SelfUse", "minSocOnGrid": 10, "fdSoc": 90, "fdPwr": 0, "maxSoc": 100}

    def _make(self, groups: list, device_sn: str = "SN1") -> FoxESSSchedulerGroups:
        data = {"scheduler": {"groups": groups}}
        return FoxESSSchedulerGroups(_coordinator(data), "Inverter", "DEV01", device_sn)

    def test_native_value_is_group_count(self) -> None:
        """native_value returns the number of groups."""
        assert self._make([self._GROUP, self._GROUP]).native_value == 2

    def test_native_value_zero_when_empty(self) -> None:
        """native_value returns 0 when no groups are configured."""
        assert self._make([]).native_value == 0

    def test_groups_in_attributes(self) -> None:
        """extra_state_attributes includes the full groups list."""
        attrs = self._make([self._GROUP]).extra_state_attributes
        assert attrs["groups"] == [self._GROUP]

    def test_device_sn_in_attributes(self) -> None:
        """extra_state_attributes includes device_sn."""
        attrs = self._make([self._GROUP], device_sn="ABC123").extra_state_attributes
        assert attrs["device_sn"] == "ABC123"

    def test_device_sn_defaults_to_empty_string(self) -> None:
        """device_sn defaults to empty string when not provided."""
        data = {"scheduler": {"groups": [self._GROUP]}}
        entity = FoxESSSchedulerGroups(_coordinator(data), "Inv", "DEV")
        assert entity.extra_state_attributes["device_sn"] == ""


# ---------------------------------------------------------------------------
# setSchedulerSegments — write function
# ---------------------------------------------------------------------------


def _aio_session(response_data: dict) -> MagicMock:
    """Return a mock aiohttp session that yields the given JSON."""
    resp = MagicMock()
    resp.__aenter__ = AsyncMock(return_value=resp)
    resp.__aexit__ = AsyncMock(return_value=False)
    resp.json = AsyncMock(return_value=response_data)
    session = MagicMock()
    session.post = MagicMock(return_value=resp)
    return session


def _aio_session_raises(exc: Exception) -> MagicMock:
    """Return a mock aiohttp session whose post() raises the given exception."""
    session = MagicMock()
    session.post = MagicMock(side_effect=exc)
    return session


@pytest.mark.asyncio
class TestSetSchedulerSegments:
    """Tests for setSchedulerSegments."""

    _GROUPS = [{"enable": 1, "startHour": 0, "startMinute": 0, "endHour": 6, "endMinute": 0,
                "workMode": "SelfUse", "minSocOnGrid": 10, "fdSoc": 90, "fdPwr": 0, "maxSoc": 100}]

    async def _call(self, session: MagicMock) -> FetchResult:
        with (
            patch("custom_components.foxess.sensor.waitforAPI", new_callable=AsyncMock),
            patch("custom_components.foxess.sensor.GetAuth"),
            patch("custom_components.foxess.sensor.async_get_clientsession", return_value=session),
        ):
            return await setSchedulerSegments(MagicMock(), "SN1", "api-key", self._GROUPS)

    async def test_ok_on_errno_zero(self) -> None:
        """Returns OK when API responds with errno 0."""
        result = await self._call(_aio_session({"errno": 0, "msg": "success"}))
        assert result is FetchResult.OK

    async def test_auth_failed_on_errno_40256(self) -> None:
        """Returns AUTH_FAILED when API returns the invalid-key errno."""
        result = await self._call(_aio_session({"errno": 40256, "msg": "auth error"}))
        assert result is FetchResult.AUTH_FAILED

    async def test_error_on_non_zero_errno(self) -> None:
        """Returns ERROR on a generic non-zero errno."""
        result = await self._call(_aio_session({"errno": 40001, "msg": "error"}))
        assert result is FetchResult.ERROR

    async def test_error_on_network_exception(self) -> None:
        """Returns ERROR when the HTTP call raises an exception."""
        result = await self._call(_aio_session_raises(OSError("connection refused")))
        assert result is FetchResult.ERROR


# ---------------------------------------------------------------------------
# _ws_save_schedule — WebSocket handler
# ---------------------------------------------------------------------------


@pytest.mark.asyncio
class TestWsSaveSchedule:
    """Tests for the foxess/save_schedule WebSocket handler."""

    _GROUPS = [{"enable": 1, "startHour": 0, "startMinute": 0, "endHour": 6, "endMinute": 0,
                "workMode": "SelfUse", "minSocOnGrid": 10, "fdSoc": 90, "fdPwr": 0, "maxSoc": 100}]

    def _make_hass(self, device_sn: str | None = "SN1") -> MagicMock:
        hass = MagicMock()
        hass.data = (
            {_FOXESS_DEVICES_KEY: {device_sn: {"apiKey": "test-key"}}}
            if device_sn
            else {}
        )
        return hass

    def _make_connection(self) -> MagicMock:
        conn = MagicMock()
        conn.send_result = MagicMock()
        conn.send_error = MagicMock()
        return conn

    async def test_unknown_device_sends_not_found_error(self) -> None:
        """Handler sends ERR_NOT_FOUND when deviceSN is not registered."""
        hass = self._make_hass(device_sn=None)
        conn = self._make_connection()
        msg = {"id": 7, "type": "foxess/save_schedule", "deviceSN": "UNKNOWN", "groups": self._GROUPS}

        await _ws_save_schedule.__wrapped__(hass, conn, msg)

        conn.send_error.assert_called_once()
        args = conn.send_error.call_args[0]
        assert args[0] == 7
        assert "not_found" in args[1]

    async def test_success_sends_result(self) -> None:
        """Handler sends send_result when setSchedulerSegments returns OK."""
        hass = self._make_hass()
        conn = self._make_connection()
        msg = {"id": 3, "type": "foxess/save_schedule", "deviceSN": "SN1", "groups": self._GROUPS}

        with patch(
            "custom_components.foxess.sensor.setSchedulerSegments",
            new_callable=AsyncMock,
            return_value=FetchResult.OK,
        ):
            await _ws_save_schedule.__wrapped__(hass, conn, msg)

        conn.send_result.assert_called_once_with(3, {"ok": True})
        conn.send_error.assert_not_called()

    async def test_auth_failure_sends_unauthorized(self) -> None:
        """Handler sends ERR_UNAUTHORIZED when setSchedulerSegments returns AUTH_FAILED."""
        hass = self._make_hass()
        conn = self._make_connection()
        msg = {"id": 5, "type": "foxess/save_schedule", "deviceSN": "SN1", "groups": self._GROUPS}

        with patch(
            "custom_components.foxess.sensor.setSchedulerSegments",
            new_callable=AsyncMock,
            return_value=FetchResult.AUTH_FAILED,
        ):
            await _ws_save_schedule.__wrapped__(hass, conn, msg)

        conn.send_error.assert_called_once()
        args = conn.send_error.call_args[0]
        assert args[0] == 5
        assert "unauthorized" in args[1]

    async def test_error_sends_unknown_error(self) -> None:
        """Handler sends ERR_UNKNOWN_ERROR when setSchedulerSegments returns ERROR."""
        hass = self._make_hass()
        conn = self._make_connection()
        msg = {"id": 9, "type": "foxess/save_schedule", "deviceSN": "SN1", "groups": self._GROUPS}

        with patch(
            "custom_components.foxess.sensor.setSchedulerSegments",
            new_callable=AsyncMock,
            return_value=FetchResult.ERROR,
        ):
            await _ws_save_schedule.__wrapped__(hass, conn, msg)

        conn.send_error.assert_called_once()
        args = conn.send_error.call_args[0]
        assert args[0] == 9
        assert "unknown_error" in args[1]
