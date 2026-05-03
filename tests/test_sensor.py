"""Unit tests for FoxESS sensor entity native_value logic."""

from unittest.mock import MagicMock

from custom_components.foxess.sensor import (
    FoxESSEnergyFeedin,
    FoxESSPower,
    FoxESSReactivePower,
    FoxESSRunningState,
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

    def test_returns_none_when_key_missing(self) -> None:
        """Returns None when feedin key is absent from report."""
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
