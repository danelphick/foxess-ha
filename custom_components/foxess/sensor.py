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
import time

from dateutil import parser
import voluptuous as vol

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
    PERCENTAGE,
    UnitOfElectricCurrent,
    UnitOfElectricPotential,
    UnitOfEnergy,
    UnitOfFrequency,
    UnitOfPower,
    UnitOfReactivePower,
    UnitOfTemperature,
)
from homeassistant.exceptions import ConfigEntryAuthFailed
import homeassistant.helpers.config_validation as cv
from homeassistant.helpers.icon import icon_for_battery_level
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
    if tslice % 5 == 0:
        _LOGGER.debug("Main Poll, interval: %s, %s", devicesn, timeslice[devicesn])
        # try the openapi see if we get a response
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

    _LOGGER.debug(allData)

    return allData


async def _async_setup_foxess(hass, config, async_add_entities, config_entry=None):
    """Shared setup logic for platform and config entry."""
    Evo = False
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
        "online": False,
    }
    allData["addressbook"]["hasBattery"] = False  # assume no battery is fitted for now
    allData["addressbook"]["status"] = "3"  # assume inverter is off-line for now

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

    await coordinator.async_refresh()

    if not coordinator.last_update_success:
        _LOGGER.error(
            "FoxESS Cloud initialisation failed, Fatal Error - correct error and restart Home Assistant"
        )
        return False

    async_add_entities(
        [
            FoxESSCurrent(
                coordinator, name, deviceID, "PV1 Current", "pv1-current", "pv1Current"
            ),
            FoxESSPower(
                coordinator, name, deviceID, "PV1 Power", "pv1-power", "pv1Power"
            ),
            FoxESSVolt(coordinator, name, deviceID, "PV1 Volt", "pv1-volt", "pv1Volt"),
            FoxESSCurrent(
                coordinator, name, deviceID, "PV2 Current", "pv2-current", "pv2Current"
            ),
            FoxESSPower(
                coordinator, name, deviceID, "PV2 Power", "pv2-power", "pv2Power"
            ),
            FoxESSVolt(coordinator, name, deviceID, "PV2 Volt", "pv2-volt", "pv2Volt"),
            FoxESSCurrent(
                coordinator, name, deviceID, "PV3 Current", "pv3-current", "pv3Current"
            ),
            FoxESSPower(
                coordinator, name, deviceID, "PV3 Power", "pv3-power", "pv3Power"
            ),
            FoxESSVolt(coordinator, name, deviceID, "PV3 Volt", "pv3-volt", "pv3Volt"),
            FoxESSCurrent(
                coordinator, name, deviceID, "PV4 Current", "pv4-current", "pv4Current"
            ),
            FoxESSPower(
                coordinator, name, deviceID, "PV4 Power", "pv4-power", "pv4Power"
            ),
            FoxESSVolt(coordinator, name, deviceID, "PV4 Volt", "pv4-volt", "pv4Volt"),
            FoxESSCurrent(
                coordinator, name, deviceID, "PV5 Current", "pv5-current", "pv5Current"
            ),
            FoxESSPower(
                coordinator, name, deviceID, "PV5 Power", "pv5-power", "pv5Power"
            ),
            FoxESSVolt(coordinator, name, deviceID, "PV5 Volt", "pv5-volt", "pv5Volt"),
            FoxESSCurrent(
                coordinator, name, deviceID, "PV6 Current", "pv6-current", "pv6Current"
            ),
            FoxESSPower(
                coordinator, name, deviceID, "PV6 Power", "pv6-power", "pv6Power"
            ),
            FoxESSVolt(coordinator, name, deviceID, "PV6 Volt", "pv6-volt", "pv6Volt"),
            FoxESSPower(coordinator, name, deviceID, "PV Power", "pv-power", "pvPower"),
            FoxESSCurrent(
                coordinator, name, deviceID, "R Current", "r-current", "RCurrent"
            ),
            FoxESSFreq(coordinator, name, deviceID, "R Freq", "r-freq", "RFreq"),
            FoxESSPower(coordinator, name, deviceID, "R Power", "r-power", "RPower"),
            FoxESSPowerString(
                coordinator,
                name,
                deviceID,
                "Meter2 Power",
                "meter2-power",
                "meterPower2",
            ),
            FoxESSVolt(coordinator, name, deviceID, "R Volt", "r-volt", "RVolt"),
            FoxESSCurrent(
                coordinator, name, deviceID, "S Current", "s-current", "SCurrent"
            ),
            FoxESSFreq(coordinator, name, deviceID, "S Freq", "s-freq", "SFreq"),
            FoxESSPower(coordinator, name, deviceID, "S Power", "s-power", "SPower"),
            FoxESSVolt(coordinator, name, deviceID, "S Volt", "s-volt", "SVolt"),
            FoxESSCurrent(
                coordinator, name, deviceID, "T Current", "t-current", "TCurrent"
            ),
            FoxESSFreq(coordinator, name, deviceID, "T Freq", "t-freq", "TFreq"),
            FoxESSPower(coordinator, name, deviceID, "T Power", "t-power", "TPower"),
            FoxESSVolt(coordinator, name, deviceID, "T Volt", "t-volt", "TVolt"),
            FoxESSReactivePower(coordinator, name, deviceID),
            FoxESSPowerFactor(coordinator, name, deviceID),
            FoxESSTemp(
                coordinator,
                name,
                deviceID,
                "Bat Temperature",
                "bat-temperature",
                "batTemperature",
            ),
            FoxESSTemp(
                coordinator,
                name,
                deviceID,
                "Bat Temperature2",
                "bat-temperature2",
                "batTemperature_2",
            ),
            FoxESSTemp(
                coordinator,
                name,
                deviceID,
                "Ambient Temperature",
                "ambient-temperature",
                "ambientTemperation",
            ),
            FoxESSTemp(
                coordinator,
                name,
                deviceID,
                "Boost Temperature",
                "boost-temperature",
                "boostTemperation",
            ),
            FoxESSTemp(
                coordinator,
                name,
                deviceID,
                "Inv Temperature",
                "inv-temperature",
                "invTemperation",
            ),
            FoxESSBatSoC(coordinator, name, deviceID, "Bat SoC", "bat-soc", "SoC"),
            FoxESSBatSoC(coordinator, name, deviceID, "Bat SoC1", "bat-soc1", "SoC_1"),
            FoxESSBatSoC(coordinator, name, deviceID, "Bat SoC2", "bat-soc2", "SoC_2"),
            FoxESSBatSoC(coordinator, name, deviceID, "Bat SoH", "bat-soh", "SOH"),
            FoxESSPower(
                coordinator,
                name,
                deviceID,
                "Inverter Bat Power",
                "inv-Bat-Power",
                "invBatPower",
            ),
            FoxESSPower(
                coordinator,
                name,
                deviceID,
                "Inverter Bat Power2",
                "inv-Bat-Power2",
                "invBatPower_2",
            ),
            FoxESSBatMinSoC(coordinator, name, deviceID),
            FoxESSBatMinSoConGrid(coordinator, name, deviceID),
            FoxESSSolarPower(coordinator, name, deviceID),
            FoxESSEnergyThroughput(coordinator, name, deviceID),
            FoxESSEnergySolar(coordinator, name, deviceID),
            FoxESSInverter(coordinator, name, deviceID),
            FoxESSPowerString(
                coordinator,
                name,
                deviceID,
                "Generation Power",
                "-generation-power",
                "generationPower",
            ),
            FoxESSPowerString(
                coordinator,
                name,
                deviceID,
                "Grid Consumption Power",
                "grid-consumption-power",
                "gridConsumptionPower",
            ),
            FoxESSPowerString(
                coordinator,
                name,
                deviceID,
                "FeedIn Power",
                "feedIn-power",
                "feedinPower",
            ),
            FoxESSPowerString(
                coordinator,
                name,
                deviceID,
                "Bat Discharge Power",
                "bat-discharge-power",
                "batDischargePower",
            ),
            FoxESSPowerString(
                coordinator,
                name,
                deviceID,
                "Bat Charge Power",
                "bat-charge-power",
                "batChargePower",
            ),
            FoxESSPowerString(
                coordinator, name, deviceID, "Load Power", "load-power", "loadsPower"
            ),
            FoxESSEnergyGenerated(
                coordinator,
                name,
                deviceID,
                "Energy Generated",
                "energy-generated",
                "value",
            ),
            FoxESSEnergyGenerated(
                coordinator,
                name,
                deviceID,
                "Energy Generated Month",
                "energy-generated-month",
                "month",
            ),
            FoxESSEnergyGenerated(
                coordinator,
                name,
                deviceID,
                "Energy Generated Cumulative",
                "energy-generated-cumulative",
                "cumulative",
            ),
            FoxESSEnergyGridConsumption(coordinator, name, deviceID),
            FoxESSEnergyFeedin(coordinator, name, deviceID),
            FoxESSEnergyBatCharge(coordinator, name, deviceID),
            FoxESSEnergyBatDischarge(coordinator, name, deviceID),
            FoxESSEnergyLoad(coordinator, name, deviceID),
            FoxESSPVEnergyTotal(coordinator, name, deviceID),
            FoxESSResidualEnergy(coordinator, name, deviceID),
            FoxESSResponseTime(coordinator, name, deviceID),
            FoxESSMaxBatChargeCurrent(coordinator, name, deviceID),
            FoxESSMaxBatDischargeCurrent(coordinator, name, deviceID),
            FoxESSRunningState(
                coordinator,
                name,
                deviceID,
                "Running State",
                "running-state",
                "runningState",
            ),
        ]
    )

    if ExtPV:
        async_add_entities(
            [
                FoxESSCurrent(
                    coordinator,
                    name,
                    deviceID,
                    "PV7 Current",
                    "pv7-current",
                    "pv7Current",
                ),
                FoxESSPower(
                    coordinator, name, deviceID, "PV7 Power", "pv7-power", "pv7Power"
                ),
                FoxESSVolt(
                    coordinator, name, deviceID, "PV7 Volt", "pv7-volt", "pv7Volt"
                ),
                FoxESSCurrent(
                    coordinator,
                    name,
                    deviceID,
                    "PV8 Current",
                    "pv8-current",
                    "pv8Current",
                ),
                FoxESSPower(
                    coordinator, name, deviceID, "PV8 Power", "pv8-power", "pv8Power"
                ),
                FoxESSVolt(
                    coordinator, name, deviceID, "PV8 Volt", "pv8-volt", "pv8Volt"
                ),
                FoxESSCurrent(
                    coordinator,
                    name,
                    deviceID,
                    "PV9 Current",
                    "pv9-current",
                    "pv9Current",
                ),
                FoxESSPower(
                    coordinator, name, deviceID, "PV9 Power", "pv9-power", "pv9Power"
                ),
                FoxESSVolt(
                    coordinator, name, deviceID, "PV9 Volt", "pv9-volt", "pv9Volt"
                ),
                FoxESSCurrent(
                    coordinator,
                    name,
                    deviceID,
                    "PV10 Current",
                    "pv10-current",
                    "pv10Current",
                ),
                FoxESSPower(
                    coordinator, name, deviceID, "PV10 Power", "pv10-power", "pv10Power"
                ),
                FoxESSVolt(
                    coordinator, name, deviceID, "PV10 Volt", "pv10-volt", "pv10Volt"
                ),
                FoxESSCurrent(
                    coordinator,
                    name,
                    deviceID,
                    "PV11 Current",
                    "pv11-current",
                    "pv11Current",
                ),
                FoxESSPower(
                    coordinator, name, deviceID, "PV11 Power", "pv11-power", "pv11Power"
                ),
                FoxESSVolt(
                    coordinator, name, deviceID, "PV11 Volt", "pv11-volt", "pv11Volt"
                ),
                FoxESSCurrent(
                    coordinator,
                    name,
                    deviceID,
                    "PV12 Current",
                    "pv12-current",
                    "pv12Current",
                ),
                FoxESSPower(
                    coordinator, name, deviceID, "PV12 Power", "pv12-power", "pv12Power"
                ),
                FoxESSVolt(
                    coordinator, name, deviceID, "PV12 Volt", "pv12-volt", "pv12Volt"
                ),
                FoxESSCurrent(
                    coordinator,
                    name,
                    deviceID,
                    "PV13 Current",
                    "pv13-current",
                    "pv13Current",
                ),
                FoxESSPower(
                    coordinator, name, deviceID, "PV13 Power", "pv13-power", "pv13Power"
                ),
                FoxESSVolt(
                    coordinator, name, deviceID, "PV13 Volt", "pv13-volt", "pv13Volt"
                ),
                FoxESSCurrent(
                    coordinator,
                    name,
                    deviceID,
                    "PV14 Current",
                    "pv14-current",
                    "pv14Current",
                ),
                FoxESSPower(
                    coordinator, name, deviceID, "PV14 Power", "pv14-power", "pv14Power"
                ),
                FoxESSVolt(
                    coordinator, name, deviceID, "PV14 Volt", "pv14-volt", "pv14Volt"
                ),
                FoxESSCurrent(
                    coordinator,
                    name,
                    deviceID,
                    "PV15 Current",
                    "pv15-current",
                    "pv15Current",
                ),
                FoxESSPower(
                    coordinator, name, deviceID, "PV15 Power", "pv15-power", "pv15Power"
                ),
                FoxESSVolt(
                    coordinator, name, deviceID, "PV15 Volt", "pv15-volt", "pv15Volt"
                ),
                FoxESSCurrent(
                    coordinator,
                    name,
                    deviceID,
                    "PV16 Current",
                    "pv16-current",
                    "pv16Current",
                ),
                FoxESSPower(
                    coordinator, name, deviceID, "PV16 Power", "pv16-power", "pv16Power"
                ),
                FoxESSVolt(
                    coordinator, name, deviceID, "PV16 Volt", "pv16-volt", "pv16Volt"
                ),
                FoxESSCurrent(
                    coordinator,
                    name,
                    deviceID,
                    "PV17 Current",
                    "pv17-current",
                    "pv17Current",
                ),
                FoxESSPower(
                    coordinator, name, deviceID, "PV17 Power", "pv17-power", "pv17Power"
                ),
                FoxESSVolt(
                    coordinator, name, deviceID, "PV17 Volt", "pv17-volt", "pv17Volt"
                ),
                FoxESSCurrent(
                    coordinator,
                    name,
                    deviceID,
                    "PV18 Current",
                    "pv18-current",
                    "pv18Current",
                ),
                FoxESSPower(
                    coordinator, name, deviceID, "PV18 Power", "pv18-power", "pv18Power"
                ),
                FoxESSVolt(
                    coordinator, name, deviceID, "PV18 Volt", "pv18-volt", "pv18Volt"
                ),
            ]
        )

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
        ResponseTime = round(time.time() * 1000) - timestamp
        if ResponseTime > 0:
            allData["raw"]["ResponseTime"] = ResponseTime
        else:
            allData["raw"]["ResponseTime"] = 0
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
        ResponseTime = round(time.time() * 1000) - timestamp
        if ResponseTime > 0:
            allData["raw"]["ResponseTime"] = ResponseTime
        else:
            allData["raw"]["ResponseTime"] = 0
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
        if "today" not in parsed:
            allData["reportDailyGeneration"]["value"] = 0
            _LOGGER.debug(
                "OA Daily Generation Report data, today has no value: %s set to 0",
                parsed,
            )
        else:
            allData["reportDailyGeneration"]["value"] = parsed["today"]
            _LOGGER.debug(
                "OA Daily Generation Report data: todays value %s ", parsed["today"]
            )
        if "month" not in parsed:
            allData["reportDailyGeneration"]["month"] = 0
            _LOGGER.debug(
                "OA Daily Generation Report data, month has no value: %s set to 0",
                parsed,
            )
        else:
            allData["reportDailyGeneration"]["month"] = parsed["month"]
            _LOGGER.debug(
                "OA Daily Generation Report data: month value %s ", parsed["month"]
            )
        if "cumulative" not in parsed:
            allData["reportDailyGeneration"]["cumulative"] = 0
            _LOGGER.debug(
                "OA Daily Generation Report data, cumulative has no value: %s set to 0",
                parsed,
            )
        else:
            allData["reportDailyGeneration"]["cumulative"] = parsed["cumulative"]
            _LOGGER.debug(
                "OA Daily Generation Report data: cumulative value %s ",
                parsed["cumulative"],
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

        rawData = (
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
        ResponseTime = round(time.time() * 1000) - timestamp
        allData["raw"]["ResponseTime"] = max(ResponseTime, 0)

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
        for (
            item
        ) in result:  # json.loads(result): # restOADeviceVariables.data)['result']:
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
                    if variableValue is not None:
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
        if tzoffsetsign == "+":
            tzoffset = (tzoffsethr * 3600 + tzoffsetmin * 60) * 1
        else:
            tzoffset = (tzoffsethr * 3600 + tzoffsetmin * 60) * -1
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


class FoxESSPowerString(CoordinatorEntity, SensorEntity):
    """Sensor entity for string power measurements in kW."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.POWER
    _attr_native_unit_of_measurement = UnitOfPower.KILO_WATT

    def __init__(self, coordinator, name, deviceID, nameValue, uniqueValue, keyValue):
        """Initialize the power string sensor entity."""
        super().__init__(coordinator=coordinator)
        self._nameValue = nameValue
        self._uniqueValue = uniqueValue
        self._keyValue = keyValue
        _LOGGER.debug("Initiating Entity - %s", self._nameValue)
        self._attr_name = f"{name} - {self._nameValue}"
        self._attr_unique_id = f"{deviceID}{self._uniqueValue}"

    @property
    def native_value(self) -> str | None:
        """Return power string value in kW from raw data."""
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if self._keyValue not in self.coordinator.data["raw"]:
                _LOGGER.debug("%s None", self._keyValue)
            else:
                return self.coordinator.data["raw"][self._keyValue]
        return None


class FoxESSCurrent(CoordinatorEntity, SensorEntity):
    """Sensor entity for current measurements in amperes."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.CURRENT
    _attr_native_unit_of_measurement = UnitOfElectricCurrent.AMPERE

    def __init__(self, coordinator, name, deviceID, nameValue, uniqueValue, keyValue):
        """Initialize the current sensor entity."""
        super().__init__(coordinator=coordinator)
        self._nameValue = nameValue
        self._uniqueValue = uniqueValue
        self._keyValue = keyValue
        _LOGGER.debug("Initiating Entity - %s", self._nameValue)
        self._attr_name = f"{name} - {self._nameValue}"
        self._attr_unique_id = f"{deviceID}{self._uniqueValue}"

    @property
    def native_value(self) -> float | None:
        """Return current value in amperes from raw data."""
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if self._keyValue not in self.coordinator.data["raw"]:
                _LOGGER.debug("%s None", self._keyValue)
            else:
                return self.coordinator.data["raw"][self._keyValue]
        return None


class FoxESSFreq(CoordinatorEntity, SensorEntity):
    """Sensor entity for grid frequency measurements in Hz."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.FREQUENCY
    _attr_native_unit_of_measurement = UnitOfFrequency.HERTZ

    def __init__(self, coordinator, name, deviceID, nameValue, uniqueValue, keyValue):
        """Initialize the frequency sensor entity."""
        super().__init__(coordinator=coordinator)
        self._nameValue = nameValue
        self._uniqueValue = uniqueValue
        self._keyValue = keyValue
        _LOGGER.debug("Initiating Entity - %s", self._nameValue)
        self._attr_name = f"{name} - {self._nameValue}"
        self._attr_unique_id = f"{deviceID}{self._uniqueValue}"

    @property
    def native_value(self) -> float | None:
        """Return frequency value in Hz from raw data."""
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if self._keyValue not in self.coordinator.data["raw"]:
                _LOGGER.debug("%s None", self._keyValue)
            else:
                return self.coordinator.data["raw"][self._keyValue]
        return None


class FoxESSPower(CoordinatorEntity, SensorEntity):
    """Sensor entity for power measurements in kW."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.POWER
    _attr_native_unit_of_measurement = UnitOfPower.KILO_WATT

    def __init__(self, coordinator, name, deviceID, nameValue, uniqueValue, keyValue):
        """Initialize the power sensor entity."""
        super().__init__(coordinator=coordinator)
        self._nameValue = nameValue
        self._uniqueValue = uniqueValue
        self._keyValue = keyValue
        _LOGGER.debug("Initiating Entity - %s", self._nameValue)
        self._attr_name = f"{name} - {self._nameValue}"
        self._attr_unique_id = f"{deviceID}{self._uniqueValue}"

    @property
    def native_value(self) -> float | None:
        """Return power value in kW from raw data."""
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if self._keyValue not in self.coordinator.data["raw"]:
                _LOGGER.debug("%s None", self._keyValue)
            else:
                return self.coordinator.data["raw"][self._keyValue]
        return None


class FoxESSVolt(CoordinatorEntity, SensorEntity):
    """Sensor entity for voltage measurements in volts."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.VOLTAGE
    _attr_native_unit_of_measurement = UnitOfElectricPotential.VOLT

    def __init__(self, coordinator, name, deviceID, nameValue, uniqueValue, keyValue):
        """Initialize the voltage sensor entity."""
        super().__init__(coordinator=coordinator)
        self._nameValue = nameValue
        self._uniqueValue = uniqueValue
        self._keyValue = keyValue
        _LOGGER.debug("Initiating Entity - %s", self._nameValue)
        self._attr_name = f"{name} - {self._nameValue}"
        self._attr_unique_id = f"{deviceID}{self._uniqueValue}"

    @property
    def native_value(self) -> float | None:
        """Return voltage value in volts from raw data."""
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if self._keyValue not in self.coordinator.data["raw"]:
                _LOGGER.debug("%s None", self._keyValue)
            else:
                return self.coordinator.data["raw"][self._keyValue]
        return None


class FoxESSReactivePower(CoordinatorEntity, SensorEntity):
    """Sensor entity for reactive power measurements."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.REACTIVE_POWER
    _attr_native_unit_of_measurement = UnitOfReactivePower.VOLT_AMPERE_REACTIVE

    def __init__(self, coordinator, name, deviceID):
        """Initialize the reactive power sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Reactive Power")
        self._attr_name = name + " - Reactive Power"
        self._attr_unique_id = deviceID + "reactive-power"

    @property
    def native_value(self) -> float | None:
        """Return reactive power in VAr, scaled from kVAr."""
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if "ReactivePower" not in self.coordinator.data["raw"]:
                _LOGGER.debug("ReactivePower None")
            else:
                return self.coordinator.data["raw"]["ReactivePower"] * 1000
        return None


class FoxESSPowerFactor(CoordinatorEntity, SensorEntity):
    """Sensor entity for power factor measurements."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.POWER_FACTOR
    _attr_native_unit_of_measurement = PERCENTAGE

    def __init__(self, coordinator, name, deviceID):
        """Initialize the power factor sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Power Factor")
        self._attr_name = name + " - Power Factor"
        self._attr_unique_id = deviceID + "power-factor"

    @property
    def native_value(self) -> float | None:
        """Return power factor as a percentage from raw data."""
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if "PowerFactor" not in self.coordinator.data["raw"]:
                _LOGGER.debug("PowerFactor None")
            else:
                return self.coordinator.data["raw"]["PowerFactor"]
        return None


class FoxESSEnergyGenerated(CoordinatorEntity, SensorEntity):
    """Sensor entity for today's generated energy total in kWh."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(self, coordinator, name, deviceID, nameValue, uniqueValue, keyValue):
        """Initialize the energy generated sensor entity."""
        super().__init__(coordinator=coordinator)
        self._nameValue = nameValue
        self._uniqueValue = uniqueValue
        self._keyValue = keyValue
        _LOGGER.debug("Initiating Entity - %s", self._nameValue)
        self._attr_name = f"{name} - {self._nameValue}"
        self._attr_unique_id = f"{deviceID}{self._uniqueValue}"

    @property
    def native_value(self) -> float | None:
        """Return today's generated energy in kWh from the daily generation report."""
        if self._keyValue not in self.coordinator.data["reportDailyGeneration"]:
            _LOGGER.debug("%s None", self._keyValue)
        else:
            if self.coordinator.data["reportDailyGeneration"][self._keyValue] == 0:
                energygenerated = 0
            else:
                energygenerated = self.coordinator.data["reportDailyGeneration"][
                    self._keyValue
                ]
                if energygenerated > 0:
                    energygenerated = round(energygenerated, 3)
                else:
                    energygenerated = 0
            return energygenerated
        return None


class FoxESSEnergyThroughput(CoordinatorEntity, SensorEntity):
    """Sensor entity for cumulative battery energy throughput in kWh."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(self, coordinator, name, deviceID):
        """Initialize the energy throughput sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Energy Throughput")
        self._attr_name = name + " - Energy Throughput"
        self._attr_unique_id = deviceID + "energy-throughput"

    @property
    def native_value(self) -> str | None:
        """Return total energy throughput in kWh from raw data."""
        if "energyThroughput" not in self.coordinator.data["raw"]:
            _LOGGER.debug("raw Energy Throughput None")
        else:
            if self.coordinator.data["raw"]["energyThroughput"] == 0:
                energygenerated = 0
            else:
                energygenerated = self.coordinator.data["raw"]["energyThroughput"]
                if energygenerated > 0:
                    energygenerated = round(energygenerated, 3)
                else:
                    energygenerated = 0
            return energygenerated
        return None


class FoxESSEnergyGridConsumption(CoordinatorEntity, SensorEntity):
    """Sensor entity for today's grid consumption energy in kWh."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(self, coordinator, name, deviceID):
        """Initialize the grid consumption energy sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Grid Consumption")
        self._attr_name = name + " - Grid Consumption"
        self._attr_unique_id = deviceID + "grid-consumption"

    @property
    def native_value(self) -> str | None:
        """Return grid consumption energy in kWh from the monthly report."""
        if "gridConsumption" not in self.coordinator.data["report"]:
            _LOGGER.debug("report gridConsumption None")
        else:
            if self.coordinator.data["report"]["gridConsumption"] == 0:
                energygrid = 0
            else:
                energygrid = self.coordinator.data["report"]["gridConsumption"]
            return energygrid
        return None


class FoxESSEnergyFeedin(CoordinatorEntity, SensorEntity):
    """Sensor entity for today's feed-in energy in kWh."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(self, coordinator, name, deviceID):
        """Initialize the feed-in energy sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - FeedIn")
        self._attr_name = name + " - FeedIn"
        self._attr_unique_id = deviceID + "feedIn"

    @property
    def native_value(self) -> str | None:
        """Return feed-in energy in kWh from the monthly report."""
        if "feedin" not in self.coordinator.data["report"]:
            _LOGGER.debug("report feedin None")
        else:
            if self.coordinator.data["report"]["feedin"] == 0:
                energyfeedin = 0
            else:
                energyfeedin = self.coordinator.data["report"]["feedin"]
            return energyfeedin
        return None


class FoxESSEnergyBatCharge(CoordinatorEntity, SensorEntity):
    """Sensor entity for today's battery charge energy in kWh."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(self, coordinator, name, deviceID):
        """Initialize the battery charge energy sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Bat Charge")
        self._attr_name = name + " - Bat Charge"
        self._attr_unique_id = deviceID + "bat-charge"

    @property
    def native_value(self) -> str | None:
        """Return battery charge energy in kWh from the monthly report."""
        if "chargeEnergyToTal" not in self.coordinator.data["report"]:
            _LOGGER.debug("report chargeEnergyToTal None")
        else:
            if self.coordinator.data["report"]["chargeEnergyToTal"] == 0:
                energycharge = 0
            else:
                energycharge = self.coordinator.data["report"]["chargeEnergyToTal"]
            return energycharge
        return None


class FoxESSMaxBatChargeCurrent(CoordinatorEntity, SensorEntity):
    """Sensor entity for maximum battery charge current in amperes."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.CURRENT
    _attr_native_unit_of_measurement = UnitOfElectricCurrent.AMPERE

    def __init__(self, coordinator, name, deviceID):
        """Initialize the max battery charge current sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Max Bat Charge Current")
        self._attr_name = name + " - Max Bat Charge Current"
        self._attr_unique_id = deviceID + "max-bat-charge-charge"

    @property
    def native_value(self) -> str | None:
        """Return maximum battery charge current in amperes from raw data."""
        if "maxChargeCurrent" not in self.coordinator.data["raw"]:
            _LOGGER.debug("report maxChargeCurrent None")
        else:
            if self.coordinator.data["raw"]["maxChargeCurrent"] == 0:
                charge = 0
            else:
                charge = self.coordinator.data["raw"]["maxChargeCurrent"]
            return charge
        return None


class FoxESSMaxBatDischargeCurrent(CoordinatorEntity, SensorEntity):
    """Sensor entity for maximum battery discharge current in amperes."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.CURRENT
    _attr_native_unit_of_measurement = UnitOfElectricCurrent.AMPERE

    def __init__(self, coordinator, name, deviceID):
        """Initialize the max battery discharge current sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Max Bat Discharge Current")
        self._attr_name = name + " - Max Bat Discharge Current"
        self._attr_unique_id = deviceID + "max-bat-discharge-charge"

    @property
    def native_value(self) -> str | None:
        """Return maximum battery discharge current in amperes from raw data."""
        if "maxDischargeCurrent" not in self.coordinator.data["raw"]:
            _LOGGER.debug("report maxDischargeCurrent None")
        else:
            if self.coordinator.data["raw"]["maxDischargeCurrent"] == 0:
                charge = 0
            else:
                charge = self.coordinator.data["raw"]["maxDischargeCurrent"]
            return charge
        return None


class FoxESSEnergyBatDischarge(CoordinatorEntity, SensorEntity):
    """Sensor entity for today's battery discharge energy in kWh."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(self, coordinator, name, deviceID):
        """Initialize the battery discharge energy sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Bat Discharge")
        self._attr_name = name + " - Bat Discharge"
        self._attr_unique_id = deviceID + "bat-discharge"

    @property
    def native_value(self) -> str | None:
        """Return battery discharge energy in kWh from the monthly report."""
        if "dischargeEnergyToTal" not in self.coordinator.data["report"]:
            _LOGGER.debug("report dischargeEnergyToTal None")
        else:
            if self.coordinator.data["report"]["dischargeEnergyToTal"] == 0:
                energydischarge = 0
            else:
                energydischarge = self.coordinator.data["report"][
                    "dischargeEnergyToTal"
                ]
            return energydischarge
        return None


class FoxESSEnergyLoad(CoordinatorEntity, SensorEntity):
    """Sensor entity for today's load energy in kWh."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(self, coordinator, name, deviceID):
        """Initialize the load energy sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Load")
        self._attr_name = name + " - Load"
        self._attr_unique_id = deviceID + "load"

    @property
    def native_value(self) -> str | None:
        """Return load energy in kWh from the monthly report."""
        if "loads" not in self.coordinator.data["report"]:
            _LOGGER.debug("report loads None")
        else:
            if self.coordinator.data["report"]["loads"] == 0:
                energyload = 0
            else:
                energyload = self.coordinator.data["report"]["loads"]
            # round
            return round(energyload, 3)
        return None


class FoxESSPVEnergyTotal(CoordinatorEntity, SensorEntity):
    """Sensor entity for today's total PV energy in kWh."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(self, coordinator, name, deviceID):
        """Initialize the PV total energy sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - PV Energy Total")
        self._attr_name = name + " - PVEnergyTotal"
        self._attr_unique_id = deviceID + "PVEnergyTotal"

    @property
    def native_value(self) -> str | None:
        """Return total PV energy in kWh from the monthly report."""
        if "PVEnergyTotal" not in self.coordinator.data["report"]:
            _LOGGER.debug("report PVEnergyTotal None")
        else:
            if self.coordinator.data["report"]["PVEnergyTotal"] == 0:
                energyload = 0
            else:
                energyload = self.coordinator.data["report"]["PVEnergyTotal"]
            # round
            return round(energyload, 3)
        return None


class FoxESSInverter(CoordinatorEntity, SensorEntity):
    """Sensor entity for inverter online/alarm/offline status."""

    def __init__(self, coordinator, name, deviceID):
        """Initialize the inverter status sensor entity."""
        super().__init__(coordinator=coordinator)
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
                _LOGGER.debug("addressbook status None")
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


class FoxESSRunningState(CoordinatorEntity, SensorEntity):
    """Sensor entity for inverter running state with descriptive code labels."""

    def __init__(self, coordinator, name, deviceID, nameValue, uniqueValue, keyValue):
        """Initialize the running state sensor entity."""
        super().__init__(coordinator=coordinator)
        self._nameValue = nameValue
        self._uniqueValue = uniqueValue
        self._keyValue = keyValue
        _LOGGER.debug("Initiating Entity - %s", self._nameValue)
        self._attr_name = f"{name} - {self._nameValue}"
        self._attr_unique_id = f"{deviceID}{self._uniqueValue}"
        self._attr_icon = "mdi:state-machine"

    @property
    def native_value(self) -> str | None:
        """Return inverter running state code with a descriptive label."""
        if self.coordinator.data["raw"]:
            if self._keyValue not in self.coordinator.data["raw"]:
                _LOGGER.debug("%s None", self._keyValue)
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
        if "loads" not in self.coordinator.data["report"]:
            loads = 0
        else:
            loads = float(self.coordinator.data["report"]["loads"])

        if "chargeEnergyToTal" not in self.coordinator.data["report"]:
            charge = 0
        else:
            charge = float(self.coordinator.data["report"]["chargeEnergyToTal"])

        if "feedin" not in self.coordinator.data["report"]:
            feedIn = 0
        else:
            feedIn = float(self.coordinator.data["report"]["feedin"])

        if "gridConsumption" not in self.coordinator.data["report"]:
            gridConsumption = 0
        else:
            gridConsumption = float(self.coordinator.data["report"]["gridConsumption"])

        if "dischargeEnergyToTal" not in self.coordinator.data["report"]:
            discharge = 0
        else:
            discharge = float(self.coordinator.data["report"]["dischargeEnergyToTal"])

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
        if "loadsPower" not in self.coordinator.data["raw"]:
            loads = 0
        else:
            loads = float(self.coordinator.data["raw"]["loadsPower"])

        if (
            "batChargePower" not in self.coordinator.data["raw"]
            or self.coordinator.data["raw"]["batChargePower"] is None
        ):
            charge = 0
        else:
            charge = float(self.coordinator.data["raw"]["batChargePower"])

        if "feedinPower" not in self.coordinator.data["raw"]:
            feedIn = 0
        else:
            feedIn = float(self.coordinator.data["raw"]["feedinPower"])

        if "gridConsumptionPower" not in self.coordinator.data["raw"]:
            gridConsumption = 0
        else:
            gridConsumption = float(
                self.coordinator.data["raw"]["gridConsumptionPower"]
            )

        if (
            "batDischargePower" not in self.coordinator.data["raw"]
            or self.coordinator.data["raw"]["batDischargePower"] is None
        ):
            discharge = 0
        else:
            discharge = float(self.coordinator.data["raw"]["batDischargePower"])

        # check if what was returned (that some time was negative) is <0, so fix it
        total = loads + charge + feedIn - gridConsumption - discharge
        total = max(total, 0)
        return round(total, 3)


class FoxESSBatSoC(CoordinatorEntity, SensorEntity):
    """Sensor entity for battery state of charge percentage."""

    _attr_device_class = SensorDeviceClass.BATTERY
    _attr_native_unit_of_measurement = "%"

    def __init__(self, coordinator, name, deviceID, nameValue, uniqueValue, keyValue):
        """Initialize the battery state of charge sensor entity."""
        super().__init__(coordinator=coordinator)
        self._nameValue = nameValue
        self._uniqueValue = uniqueValue
        self._keyValue = keyValue
        _LOGGER.debug("Initiating Entity - %s", self._nameValue)
        self._attr_name = f"{name} - {self._nameValue}"
        self._attr_unique_id = f"{deviceID}{self._uniqueValue}"

    @property
    def native_value(self) -> float | None:
        """Return battery state of charge percentage from raw data."""
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if self._keyValue not in self.coordinator.data["raw"]:
                _LOGGER.debug("%s None", self._keyValue)
            else:
                return self.coordinator.data["raw"][self._keyValue]
        return None

    @property
    def icon(self):
        """Return a battery icon for the current charge level."""
        return icon_for_battery_level(battery_level=self.native_value, charging=None)


class FoxESSBatMinSoC(CoordinatorEntity, SensorEntity):
    """Sensor entity for minimum allowed battery state of charge percentage."""

    _attr_device_class = SensorDeviceClass.BATTERY
    _attr_native_unit_of_measurement = "%"

    def __init__(self, coordinator, name, deviceID):
        """Initialize the minimum battery SoC sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Bat MinSoC")
        self._attr_name = name + " - Bat MinSoC"
        self._attr_unique_id = deviceID + "bat-minsoc"

    @property
    def native_value(self) -> float | None:
        """Return minimum allowed battery SoC from battery settings."""
        if self.coordinator.data["online"] and self.coordinator.data["battery"]:
            if "minSoc" not in self.coordinator.data["battery"]:
                _LOGGER.debug("minSoc None")
            else:
                return self.coordinator.data["battery"]["minSoc"]
        return None

    @property
    def icon(self):
        """Return a battery icon for the minimum SoC level."""
        return icon_for_battery_level(battery_level=self.native_value, charging=None)


class FoxESSBatMinSoConGrid(CoordinatorEntity, SensorEntity):
    """Sensor entity for minimum battery state of charge when on grid."""

    _attr_device_class = SensorDeviceClass.BATTERY
    _attr_native_unit_of_measurement = "%"

    def __init__(self, coordinator, name, deviceID):
        """Initialize the minimum battery SoC on-grid sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Bat minSocOnGrid")
        self._attr_name = name + " - Bat minSocOnGrid"
        self._attr_unique_id = deviceID + "bat-minSocOnGrid"

    @property
    def native_value(self) -> float | None:
        """Return minimum battery SoC on-grid setting from battery settings."""
        if self.coordinator.data["online"] and self.coordinator.data["battery"]:
            if "minSocOnGrid" not in self.coordinator.data["battery"]:
                _LOGGER.debug("minSocOnGrid None")
            else:
                return self.coordinator.data["battery"]["minSocOnGrid"]
        return None

    @property
    def icon(self):
        """Return a battery icon for the minimum SoC on-grid level."""
        return icon_for_battery_level(battery_level=self.native_value, charging=None)


class FoxESSTemp(CoordinatorEntity, SensorEntity):
    """Sensor entity for temperature measurements in degrees Celsius."""

    _attr_device_class = SensorDeviceClass.TEMPERATURE
    _attr_native_unit_of_measurement = UnitOfTemperature.CELSIUS

    def __init__(self, coordinator, name, deviceID, nameValue, uniqueValue, keyValue):
        """Initialize the temperature sensor entity."""
        super().__init__(coordinator=coordinator)
        self._nameValue = nameValue
        self._uniqueValue = uniqueValue
        self._keyValue = keyValue
        _LOGGER.debug("Initiating Entity - %s", self._nameValue)
        self._attr_name = f"{name} - {self._nameValue}"
        self._attr_unique_id = f"{deviceID}{self._uniqueValue}"

    @property
    def native_value(self) -> float | None:
        """Return temperature value in degrees Celsius from raw data."""
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if self._keyValue not in self.coordinator.data["raw"]:
                _LOGGER.debug("%s None", self._keyValue)
            else:
                return self.coordinator.data["raw"][self._keyValue]
        return None


class FoxESSResidualEnergy(CoordinatorEntity, SensorEntity):
    """Sensor entity for residual battery energy in kWh."""

    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(self, coordinator, name, deviceID):
        """Initialize the residual energy sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Residual Energy")
        self._attr_name = name + " - Residual Energy"
        self._attr_unique_id = deviceID + "residual-energy"

    @property
    def native_value(self) -> float | None:
        """Return residual battery energy in kWh, correcting for API scale errors."""
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if "ResidualEnergy" not in self.coordinator.data["raw"]:
                _LOGGER.debug("ResidualEnergy None")
            else:
                re = self.coordinator.data["raw"]["ResidualEnergy"]
                if re > 0:
                    if re > 50:  # if openAPI scale is invalid (bug)
                        re = re / 100
                else:
                    re = 0
                return re
        return None


class FoxESSResponseTime(CoordinatorEntity, SensorEntity):
    """Sensor entity for FoxESS API response time in milliseconds."""

    _attr_native_unit_of_measurement = "mS"

    def __init__(self, coordinator, name, deviceID):
        """Initialize the API response time sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Response Time")
        self._attr_name = name + " - Response Time"
        self._attr_unique_id = deviceID + "response-time"

    @property
    def native_value(self) -> float | None:
        """Return the last FoxESS API response time in milliseconds."""
        if "ResponseTime" not in self.coordinator.data["raw"]:
            _LOGGER.debug("ResponseTime None")
        else:
            return self.coordinator.data["raw"]["ResponseTime"]
        return None
