"""Unit tests for FoxESS sensor entity native_value logic."""

import json
from unittest.mock import AsyncMock, MagicMock, patch

from custom_components.foxess.sensor import (
    _FOXESS_DEVICES_KEY,
    _FOXESS_TEMPLATES_STORE_KEY,
    CONF_SCHEDULER_API_VERSION,
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
    _ws_get_templates,
    _ws_save_schedule,
    _ws_save_template,
    getReportDailyGeneration,
    setSchedulerSegments,
    setSchedulerSegmentsV3,
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

    def test_scheduler_api_version_in_attributes(self) -> None:
        """extra_state_attributes includes scheduler_api_version."""
        data = {"scheduler": {"groups": []}}
        entity = FoxESSSchedulerGroups(_coordinator(data), "Inv", "DEV01", "SN1", "v3")
        assert entity.extra_state_attributes["scheduler_api_version"] == "v3"

    def test_scheduler_api_version_defaults_to_v2(self) -> None:
        """scheduler_api_version defaults to 'v2' when not provided."""
        data = {"scheduler": {"groups": []}}
        entity = FoxESSSchedulerGroups(_coordinator(data), "Inv", "DEV01", "SN1")
        assert entity.extra_state_attributes["scheduler_api_version"] == "v2"


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
            result, _ = await setSchedulerSegments(MagicMock(), "SN1", "api-key", self._GROUPS)
            return result

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
            return_value=(FetchResult.OK, ""),
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
            return_value=(FetchResult.AUTH_FAILED, "auth error"),
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
            return_value=(FetchResult.ERROR, "error"),
        ):
            await _ws_save_schedule.__wrapped__(hass, conn, msg)

        conn.send_error.assert_called_once()
        args = conn.send_error.call_args[0]
        assert args[0] == 9
        assert "unknown_error" in args[1]


# ---------------------------------------------------------------------------
# _ws_get_templates — WebSocket handler
# ---------------------------------------------------------------------------


@pytest.mark.asyncio
class TestWsGetTemplates:
    """Tests for the foxess/get_templates WebSocket handler."""

    def _make_store(self, data: dict | None) -> MagicMock:
        store = MagicMock()
        store.async_load = AsyncMock(return_value=data)
        return store

    def _make_hass(self, store_data: dict | None = None) -> MagicMock:
        hass = MagicMock()
        hass.data = {_FOXESS_TEMPLATES_STORE_KEY: self._make_store(store_data)}
        return hass

    def _make_connection(self) -> MagicMock:
        conn = MagicMock()
        conn.send_result = MagicMock()
        conn.send_error = MagicMock()
        return conn

    async def test_returns_empty_list_when_store_is_empty(self) -> None:
        """Returns an empty templates list when the store has no data."""
        hass = self._make_hass(store_data=None)
        conn = self._make_connection()
        msg = {"id": 1, "type": "foxess/get_templates", "deviceSN": "SN1"}

        await _ws_get_templates.__wrapped__(hass, conn, msg)

        conn.send_result.assert_called_once_with(1, {"templates": []})

    async def test_returns_empty_list_when_no_entry_for_device(self) -> None:
        """Returns an empty templates list when the store has no entry for the device."""
        hass = self._make_hass(store_data={"OTHER_SN": [{"name": "t1", "groups": []}]})
        conn = self._make_connection()
        msg = {"id": 2, "type": "foxess/get_templates", "deviceSN": "SN1"}

        await _ws_get_templates.__wrapped__(hass, conn, msg)

        conn.send_result.assert_called_once_with(2, {"templates": []})

    async def test_returns_saved_templates_for_device(self) -> None:
        """Returns the stored template list for the given device."""
        templates = [{"name": "Morning", "groups": [{"workMode": "ForceCharge"}]}]
        hass = self._make_hass(store_data={"SN1": templates})
        conn = self._make_connection()
        msg = {"id": 3, "type": "foxess/get_templates", "deviceSN": "SN1"}

        await _ws_get_templates.__wrapped__(hass, conn, msg)

        conn.send_result.assert_called_once_with(3, {"templates": templates})


# ---------------------------------------------------------------------------
# _ws_save_template — WebSocket handler
# ---------------------------------------------------------------------------


@pytest.mark.asyncio
class TestWsSaveTemplate:
    """Tests for the foxess/save_template WebSocket handler."""

    _GROUPS = [{"workMode": "ForceCharge", "startHour": 0, "startMinute": 0,
                "endHour": 6, "endMinute": 0}]

    def _make_store(self, data: dict | None = None) -> MagicMock:
        store = MagicMock()
        store.async_load = AsyncMock(return_value=data)
        store.async_save = AsyncMock()
        return store

    def _make_hass(self, store: MagicMock) -> MagicMock:
        hass = MagicMock()
        hass.data = {_FOXESS_TEMPLATES_STORE_KEY: store}
        return hass

    def _make_connection(self) -> MagicMock:
        conn = MagicMock()
        conn.send_result = MagicMock()
        conn.send_error = MagicMock()
        return conn

    async def test_saves_new_template(self) -> None:
        """Saves a new template and calls send_result with ok."""
        store = self._make_store(data=None)
        hass = self._make_hass(store)
        conn = self._make_connection()
        msg = {"id": 1, "type": "foxess/save_template", "deviceSN": "SN1",
               "name": "Morning", "groups": self._GROUPS}

        await _ws_save_template.__wrapped__(hass, conn, msg)

        conn.send_result.assert_called_once_with(1, {"ok": True})
        saved = store.async_save.call_args[0][0]
        assert saved == {"SN1": [{"name": "Morning", "groups": self._GROUPS}]}

    async def test_overwrites_template_with_same_name(self) -> None:
        """Overwrites an existing template rather than creating a duplicate."""
        old_groups = [{"workMode": "SelfUse"}]
        store = self._make_store(data={"SN1": [{"name": "Morning", "groups": old_groups}]})
        hass = self._make_hass(store)
        conn = self._make_connection()
        msg = {"id": 2, "type": "foxess/save_template", "deviceSN": "SN1",
               "name": "Morning", "groups": self._GROUPS}

        await _ws_save_template.__wrapped__(hass, conn, msg)

        conn.send_result.assert_called_once_with(2, {"ok": True})
        saved = store.async_save.call_args[0][0]
        assert len(saved["SN1"]) == 1
        assert saved["SN1"][0]["groups"] == self._GROUPS

    async def test_appends_template_with_new_name(self) -> None:
        """Appends a second template when the name is different."""
        existing = [{"name": "Morning", "groups": self._GROUPS}]
        store = self._make_store(data={"SN1": existing})
        hass = self._make_hass(store)
        conn = self._make_connection()
        msg = {"id": 3, "type": "foxess/save_template", "deviceSN": "SN1",
               "name": "Evening", "groups": self._GROUPS}

        await _ws_save_template.__wrapped__(hass, conn, msg)

        saved = store.async_save.call_args[0][0]
        assert len(saved["SN1"]) == 2
        assert saved["SN1"][1]["name"] == "Evening"

    async def test_does_not_affect_other_devices(self) -> None:
        """Templates for other devices are preserved when saving."""
        store = self._make_store(data={"OTHER": [{"name": "t", "groups": []}]})
        hass = self._make_hass(store)
        conn = self._make_connection()
        msg = {"id": 4, "type": "foxess/save_template", "deviceSN": "SN1",
               "name": "Morning", "groups": self._GROUPS}

        await _ws_save_template.__wrapped__(hass, conn, msg)

        saved = store.async_save.call_args[0][0]
        assert "OTHER" in saved
        assert saved["OTHER"] == [{"name": "t", "groups": []}]


# ---------------------------------------------------------------------------
# setSchedulerSegments — remaining group handling
# ---------------------------------------------------------------------------


@pytest.mark.asyncio
class TestSetSchedulerSegmentsRemainingGroup:
    """Tests for setSchedulerSegments remaining-group (00:00–23:59) handling."""

    _REMAINING = {
        "startHour": 0, "startMinute": 0, "endHour": 23, "endMinute": 59,
        "enable": 1, "workMode": "SelfUse",
        "extraParam": {"minSocOnGrid": 20, "fdSoc": 50, "fdPwr": 0, "maxSoc": 85},
    }
    _SCHEDULED = {
        "startHour": 6, "startMinute": 0, "endHour": 12, "endMinute": 0,
        "enable": 1, "workMode": "ForceCharge",
        "extraParam": {"minSocOnGrid": 10, "fdSoc": 50, "fdPwr": 2000, "maxSoc": 100},
    }

    def _make_hass(self, scheduler_enabled: bool = False, min_soc: int = 10) -> MagicMock:
        hass = MagicMock()
        hass.data = {
            _FOXESS_DEVICES_KEY: {
                "SN1": {
                    "allData": {
                        "scheduler": {"enabled": scheduler_enabled},
                        "battery": {"minSoc": min_soc},
                    }
                }
            }
        }
        return hass

    async def test_calls_battery_soc_with_current_min_soc_from_all_data(self) -> None:
        """_set_battery_soc is called with the current minSoc read from allData."""
        hass = self._make_hass(min_soc=15)
        mock_battery = AsyncMock(return_value=(FetchResult.OK, ""))
        mock_device = AsyncMock(return_value=(FetchResult.OK, ""))
        with (
            patch("custom_components.foxess.sensor._set_battery_soc", mock_battery),
            patch("custom_components.foxess.sensor._set_device_setting", mock_device),
        ):
            result, _ = await setSchedulerSegments(hass, "SN1", "key", [self._REMAINING])
        assert result is FetchResult.OK
        mock_battery.assert_called_once_with(hass, "SN1", "key", min_soc=15, min_soc_on_grid=20)

    async def test_calls_device_setting_with_max_soc(self) -> None:
        """_set_device_setting is called with 'MaxSoc' and the group's maxSoc value."""
        hass = self._make_hass()
        mock_battery = AsyncMock(return_value=(FetchResult.OK, ""))
        mock_device = AsyncMock(return_value=(FetchResult.OK, ""))
        with (
            patch("custom_components.foxess.sensor._set_battery_soc", mock_battery),
            patch("custom_components.foxess.sensor._set_device_setting", mock_device),
        ):
            await setSchedulerSegments(hass, "SN1", "key", [self._REMAINING])
        mock_device.assert_called_once_with(hass, "SN1", "key", "MaxSoc", 85)

    async def test_disables_scheduler_when_enabled(self) -> None:
        """Calls setSchedulerFlag(0) when the scheduler is active before writing SoC settings."""
        hass = self._make_hass(scheduler_enabled=True)
        mock_flag = AsyncMock(return_value=(FetchResult.OK, ""))
        with (
            patch("custom_components.foxess.sensor.setSchedulerFlag", mock_flag),
            patch("custom_components.foxess.sensor._set_battery_soc", new_callable=AsyncMock, return_value=(FetchResult.OK, "")),
            patch("custom_components.foxess.sensor._set_device_setting", new_callable=AsyncMock, return_value=(FetchResult.OK, "")),
        ):
            await setSchedulerSegments(hass, "SN1", "key", [self._REMAINING])
        mock_flag.assert_any_call(hass, "SN1", "key", 0)

    async def test_returns_error_when_disable_flag_fails(self) -> None:
        """Returns ERROR immediately when setSchedulerFlag(0) fails, skipping battery SoC call."""
        hass = self._make_hass(scheduler_enabled=True)
        mock_battery = AsyncMock(return_value=(FetchResult.OK, ""))
        with (
            patch("custom_components.foxess.sensor.setSchedulerFlag", new_callable=AsyncMock, return_value=(FetchResult.ERROR, "flag error")),
            patch("custom_components.foxess.sensor._set_battery_soc", mock_battery),
            patch("custom_components.foxess.sensor._set_device_setting", new_callable=AsyncMock, return_value=(FetchResult.OK, "")),
        ):
            result, msg = await setSchedulerSegments(hass, "SN1", "key", [self._REMAINING])
        assert result is FetchResult.ERROR
        assert msg == "flag error"
        mock_battery.assert_not_called()

    async def test_skips_disable_when_scheduler_not_enabled(self) -> None:
        """The scheduler-disable flag call is skipped when the scheduler is already inactive."""
        hass = self._make_hass(scheduler_enabled=False)
        mock_flag = AsyncMock(return_value=(FetchResult.OK, ""))
        with (
            patch("custom_components.foxess.sensor.setSchedulerFlag", mock_flag),
            patch("custom_components.foxess.sensor._set_battery_soc", new_callable=AsyncMock, return_value=(FetchResult.OK, "")),
            patch("custom_components.foxess.sensor._set_device_setting", new_callable=AsyncMock, return_value=(FetchResult.OK, "")),
        ):
            await setSchedulerSegments(hass, "SN1", "key", [self._REMAINING])
        mock_flag.assert_not_called()

    async def test_reenables_scheduler_when_no_scheduled_groups_and_was_enabled(self) -> None:
        """setSchedulerFlag(1) is called after settings are written when no scheduled groups remain."""
        hass = self._make_hass(scheduler_enabled=True)
        mock_flag = AsyncMock(return_value=(FetchResult.OK, ""))
        with (
            patch("custom_components.foxess.sensor.setSchedulerFlag", mock_flag),
            patch("custom_components.foxess.sensor._set_battery_soc", new_callable=AsyncMock, return_value=(FetchResult.OK, "")),
            patch("custom_components.foxess.sensor._set_device_setting", new_callable=AsyncMock, return_value=(FetchResult.OK, "")),
        ):
            result, _ = await setSchedulerSegments(hass, "SN1", "key", [self._REMAINING])
        assert result is FetchResult.OK
        assert mock_flag.call_count == 2
        assert mock_flag.call_args_list[0][0] == (hass, "SN1", "key", 0)
        assert mock_flag.call_args_list[1][0] == (hass, "SN1", "key", 1)

    async def test_no_reenable_when_was_not_enabled(self) -> None:
        """No flag calls are made at all when the scheduler was not active."""
        hass = self._make_hass(scheduler_enabled=False)
        mock_flag = AsyncMock(return_value=(FetchResult.OK, ""))
        with (
            patch("custom_components.foxess.sensor.setSchedulerFlag", mock_flag),
            patch("custom_components.foxess.sensor._set_battery_soc", new_callable=AsyncMock, return_value=(FetchResult.OK, "")),
            patch("custom_components.foxess.sensor._set_device_setting", new_callable=AsyncMock, return_value=(FetchResult.OK, "")),
        ):
            result, _ = await setSchedulerSegments(hass, "SN1", "key", [self._REMAINING])
        assert result is FetchResult.OK
        mock_flag.assert_not_called()

    async def test_returns_error_when_battery_soc_fails(self) -> None:
        """Returns ERROR immediately when _set_battery_soc fails, skipping MaxSoc call."""
        hass = self._make_hass()
        mock_battery = AsyncMock(return_value=(FetchResult.ERROR, "soc error"))
        mock_device = AsyncMock(return_value=(FetchResult.OK, ""))
        with (
            patch("custom_components.foxess.sensor._set_battery_soc", mock_battery),
            patch("custom_components.foxess.sensor._set_device_setting", mock_device),
        ):
            result, msg = await setSchedulerSegments(hass, "SN1", "key", [self._REMAINING])
        assert result is FetchResult.ERROR
        assert msg == "soc error"
        mock_device.assert_not_called()

    async def test_returns_error_when_max_soc_setting_fails(self) -> None:
        """Returns ERROR immediately when _set_device_setting for MaxSoc fails."""
        hass = self._make_hass()
        mock_device = AsyncMock(return_value=(FetchResult.ERROR, "maxsoc error"))
        with (
            patch("custom_components.foxess.sensor._set_battery_soc", new_callable=AsyncMock, return_value=(FetchResult.OK, "")),
            patch("custom_components.foxess.sensor._set_device_setting", mock_device),
        ):
            result, msg = await setSchedulerSegments(hass, "SN1", "key", [self._REMAINING])
        assert result is FetchResult.ERROR
        assert msg == "maxsoc error"

    async def test_defaults_min_soc_to_10_when_missing_from_all_data(self) -> None:
        """Falls back to minSoc=10 when allData has no battery.minSoc entry."""
        hass = MagicMock()
        hass.data = {
            _FOXESS_DEVICES_KEY: {
                "SN1": {"allData": {"scheduler": {"enabled": False}, "battery": {}}}
            }
        }
        mock_battery = AsyncMock(return_value=(FetchResult.OK, ""))
        with (
            patch("custom_components.foxess.sensor._set_battery_soc", mock_battery),
            patch("custom_components.foxess.sensor._set_device_setting", new_callable=AsyncMock, return_value=(FetchResult.OK, "")),
        ):
            await setSchedulerSegments(hass, "SN1", "key", [self._REMAINING])
        mock_battery.assert_called_once_with(hass, "SN1", "key", min_soc=10, min_soc_on_grid=20)

    async def test_defaults_max_soc_to_100_when_missing_from_extra_param(self) -> None:
        """Falls back to maxSoc=100 when extraParam does not contain maxSoc."""
        remaining = {**self._REMAINING, "extraParam": {"minSocOnGrid": 20}}
        hass = self._make_hass()
        mock_device = AsyncMock(return_value=(FetchResult.OK, ""))
        with (
            patch("custom_components.foxess.sensor._set_battery_soc", new_callable=AsyncMock, return_value=(FetchResult.OK, "")),
            patch("custom_components.foxess.sensor._set_device_setting", mock_device),
        ):
            await setSchedulerSegments(hass, "SN1", "key", [remaining])
        mock_device.assert_called_once_with(hass, "SN1", "key", "MaxSoc", 100)


# ---------------------------------------------------------------------------
# setSchedulerSegmentsV3 — V3 scheduler API write function
# ---------------------------------------------------------------------------


@pytest.mark.asyncio
class TestSetSchedulerSegmentsV3:
    """Tests for setSchedulerSegmentsV3 — V3 scheduler API write function."""

    _SCHEDULED = {
        "startHour": 6, "startMinute": 0, "endHour": 12, "endMinute": 0,
        "enable": 1, "workMode": "ForceCharge",
        "extraParam": {"minSocOnGrid": 10, "fdSoc": 50, "fdPwr": 2000, "maxSoc": 100},
    }
    _REMAINING = {
        "startHour": 0, "startMinute": 0, "endHour": 23, "endMinute": 59,
        "enable": 1, "workMode": "SelfUse",
        "extraParam": {"minSocOnGrid": 30, "maxSoc": 90},
    }

    def _make_hass(self, scheduler_enabled: bool = False, min_soc: int = 10) -> MagicMock:
        hass = MagicMock()
        hass.data = {
            _FOXESS_DEVICES_KEY: {
                "SN1": {
                    "allData": {
                        "scheduler": {"enabled": scheduler_enabled},
                        "battery": {"minSoc": min_soc},
                    }
                }
            }
        }
        return hass

    async def _call(self, session: MagicMock, groups: list | None = None) -> tuple[FetchResult, str]:
        hass = self._make_hass()
        with (
            patch("custom_components.foxess.sensor.waitforAPI", new_callable=AsyncMock),
            patch("custom_components.foxess.sensor.GetAuth"),
            patch("custom_components.foxess.sensor.async_get_clientsession", return_value=session),
        ):
            return await setSchedulerSegmentsV3(hass, "SN1", "api-key", groups or [self._SCHEDULED])

    async def test_ok_on_errno_zero(self) -> None:
        """Returns OK when API responds with errno 0."""
        result, _ = await self._call(_aio_session({"errno": 0, "msg": "success"}))
        assert result is FetchResult.OK

    async def test_auth_failed_on_errno_40256(self) -> None:
        """Returns AUTH_FAILED when API returns the invalid-key errno."""
        result, _ = await self._call(_aio_session({"errno": 40256, "msg": "auth error"}))
        assert result is FetchResult.AUTH_FAILED

    async def test_error_on_non_zero_errno(self) -> None:
        """Returns ERROR on a generic non-zero errno."""
        result, _ = await self._call(_aio_session({"errno": 40001, "msg": "error"}))
        assert result is FetchResult.ERROR

    async def test_error_on_network_exception(self) -> None:
        """Returns ERROR when the HTTP call raises an exception."""
        result, _ = await self._call(_aio_session_raises(OSError("connection refused")))
        assert result is FetchResult.ERROR

    async def test_posts_to_v3_endpoint(self) -> None:
        """POSTs to the V3 scheduler endpoint URL."""
        session = _aio_session({"errno": 0, "msg": "success"})
        await self._call(session)
        url = session.post.call_args[0][0]
        assert "/op/v3/device/scheduler/enable" in url

    async def test_sends_is_default_false(self) -> None:
        """Sends isDefault=False in the request body."""
        session = _aio_session({"errno": 0, "msg": "success"})
        await self._call(session)
        payload = session.post.call_args[1]["json"]
        assert payload["isDefault"] is False

    async def test_remaining_group_is_sent_to_v3_endpoint(self) -> None:
        """The remaining 00:00–23:59 group is included in the V3 scheduler API call."""
        session = _aio_session({"errno": 0, "msg": "success"})
        result, _ = await self._call(session, groups=[self._REMAINING])
        assert result is FetchResult.OK
        payload = session.post.call_args[1]["json"]
        assert any(
            g["startHour"] == 0 and g["endHour"] == 23 and g["endMinute"] == 59
            for g in payload["groups"]
        )

    async def test_all_groups_sent_including_remaining(self) -> None:
        """When both scheduled and remaining groups are present, all are sent to V3."""
        session = _aio_session({"errno": 0, "msg": "success"})
        result, _ = await self._call(session, groups=[self._SCHEDULED, self._REMAINING])
        assert result is FetchResult.OK
        payload = session.post.call_args[1]["json"]
        assert len(payload["groups"]) == 2

    async def test_no_battery_soc_or_device_setting_calls_for_v3(self) -> None:
        """V3 does not call _set_battery_soc or _set_device_setting for the remaining group."""
        mock_battery = AsyncMock(return_value=(FetchResult.OK, ""))
        mock_device = AsyncMock(return_value=(FetchResult.OK, ""))
        session = _aio_session({"errno": 0, "msg": "success"})
        with (
            patch("custom_components.foxess.sensor._set_battery_soc", mock_battery),
            patch("custom_components.foxess.sensor._set_device_setting", mock_device),
            patch("custom_components.foxess.sensor.waitforAPI", new_callable=AsyncMock),
            patch("custom_components.foxess.sensor.GetAuth"),
            patch("custom_components.foxess.sensor.async_get_clientsession", return_value=session),
        ):
            await setSchedulerSegmentsV3(self._make_hass(), "SN1", "key", [self._REMAINING])
        mock_battery.assert_not_called()
        mock_device.assert_not_called()


# ---------------------------------------------------------------------------
# _ws_save_schedule — V2/V3 version routing
# ---------------------------------------------------------------------------


@pytest.mark.asyncio
class TestWsSaveScheduleVersionRouting:
    """Tests that _ws_save_schedule dispatches to V2 or V3 based on device config."""

    _GROUPS = [
        {
            "startHour": 6, "startMinute": 0, "endHour": 12, "endMinute": 0,
            "enable": 1, "workMode": "SelfUse",
            "extraParam": {"minSocOnGrid": 10, "fdSoc": 50, "fdPwr": 0, "maxSoc": 100},
        }
    ]

    def _make_hass(self, sched_ver: str | None) -> MagicMock:
        hass = MagicMock()
        entry: dict = {"apiKey": "test-key"}
        if sched_ver is not None:
            entry[CONF_SCHEDULER_API_VERSION] = sched_ver
        hass.data = {_FOXESS_DEVICES_KEY: {"SN1": entry}}
        return hass

    def _make_connection(self) -> MagicMock:
        conn = MagicMock()
        conn.send_result = MagicMock()
        conn.send_error = MagicMock()
        return conn

    async def test_uses_v2_by_default(self) -> None:
        """Calls setSchedulerSegments (V2) when no API version is configured."""
        hass = self._make_hass(sched_ver=None)
        msg = {"id": 1, "type": "foxess/save_schedule", "deviceSN": "SN1", "groups": self._GROUPS}
        with (
            patch("custom_components.foxess.sensor.setSchedulerSegments", new_callable=AsyncMock, return_value=(FetchResult.OK, "")) as mock_v2,
            patch("custom_components.foxess.sensor.setSchedulerSegmentsV3", new_callable=AsyncMock, return_value=(FetchResult.OK, "")) as mock_v3,
        ):
            await _ws_save_schedule.__wrapped__(hass, self._make_connection(), msg)
        mock_v2.assert_called_once()
        mock_v3.assert_not_called()

    async def test_uses_v2_when_explicitly_configured(self) -> None:
        """Calls setSchedulerSegments (V2) when version is explicitly "v2"."""
        hass = self._make_hass(sched_ver="v2")
        msg = {"id": 2, "type": "foxess/save_schedule", "deviceSN": "SN1", "groups": self._GROUPS}
        with (
            patch("custom_components.foxess.sensor.setSchedulerSegments", new_callable=AsyncMock, return_value=(FetchResult.OK, "")) as mock_v2,
            patch("custom_components.foxess.sensor.setSchedulerSegmentsV3", new_callable=AsyncMock, return_value=(FetchResult.OK, "")) as mock_v3,
        ):
            await _ws_save_schedule.__wrapped__(hass, self._make_connection(), msg)
        mock_v2.assert_called_once()
        mock_v3.assert_not_called()

    async def test_uses_v3_when_configured(self) -> None:
        """Calls setSchedulerSegmentsV3 when version is "v3"."""
        hass = self._make_hass(sched_ver="v3")
        msg = {"id": 3, "type": "foxess/save_schedule", "deviceSN": "SN1", "groups": self._GROUPS}
        with (
            patch("custom_components.foxess.sensor.setSchedulerSegments", new_callable=AsyncMock, return_value=(FetchResult.OK, "")) as mock_v2,
            patch("custom_components.foxess.sensor.setSchedulerSegmentsV3", new_callable=AsyncMock, return_value=(FetchResult.OK, "")) as mock_v3,
        ):
            await _ws_save_schedule.__wrapped__(hass, self._make_connection(), msg)
        mock_v3.assert_called_once()
        mock_v2.assert_not_called()

    async def test_v3_success_sends_result(self) -> None:
        """Handler sends send_result when setSchedulerSegmentsV3 returns OK."""
        hass = self._make_hass(sched_ver="v3")
        conn = self._make_connection()
        msg = {"id": 4, "type": "foxess/save_schedule", "deviceSN": "SN1", "groups": self._GROUPS}
        with patch(
            "custom_components.foxess.sensor.setSchedulerSegmentsV3",
            new_callable=AsyncMock,
            return_value=(FetchResult.OK, ""),
        ):
            await _ws_save_schedule.__wrapped__(hass, conn, msg)
        conn.send_result.assert_called_once_with(4, {"ok": True})
        conn.send_error.assert_not_called()

    async def test_v3_auth_failure_sends_unauthorized(self) -> None:
        """Handler sends ERR_UNAUTHORIZED when setSchedulerSegmentsV3 returns AUTH_FAILED."""
        hass = self._make_hass(sched_ver="v3")
        conn = self._make_connection()
        msg = {"id": 5, "type": "foxess/save_schedule", "deviceSN": "SN1", "groups": self._GROUPS}
        with patch(
            "custom_components.foxess.sensor.setSchedulerSegmentsV3",
            new_callable=AsyncMock,
            return_value=(FetchResult.AUTH_FAILED, "bad key"),
        ):
            await _ws_save_schedule.__wrapped__(hass, conn, msg)
        conn.send_error.assert_called_once()
        assert "unauthorized" in conn.send_error.call_args[0][1]
