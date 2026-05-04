"""Unit tests for FoxESS sensor entity native_value logic."""

import json
from unittest.mock import AsyncMock, MagicMock, patch

from custom_components.foxess.sensor import (
    FetchResult,
    FoxESSEnergyFeedin,
    FoxESSEnergyGenerated,
    FoxESSEnergyLoad,
    FoxESSEnergyThroughput,
    FoxESSPower,
    FoxESSReactivePower,
    FoxESSRunningState,
    getReportDailyGeneration,
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
        assert self._make({"raw": {"energyThroughput": 5.6789}}).native_value == 5.679

    def test_returns_zero_for_zero_value(self) -> None:
        """Returns 0 when the stored value is zero."""
        assert self._make({"raw": {"energyThroughput": 0}}).native_value == 0

    def test_returns_zero_for_negative_value(self) -> None:
        """Returns 0 when the stored value is negative."""
        assert self._make({"raw": {"energyThroughput": -1.0}}).native_value == 0

    def test_returns_none_when_key_missing(self) -> None:
        """Returns None when energyThroughput is absent from raw data."""
        assert self._make({"raw": {}}).native_value is None


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
