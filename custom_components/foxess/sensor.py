from __future__ import annotations

from dataclasses import dataclass
from datetime import timedelta
from datetime import datetime
from dateutil import parser
import enum
import time
import logging
import json
import hashlib
import asyncio
import voluptuous as vol

from homeassistant.components.sensor import (
    SensorDeviceClass,
    SensorStateClass,
    PLATFORM_SCHEMA,
    SensorEntity,
)

from homeassistant.const import (
    CONF_PASSWORD,
    CONF_USERNAME,
    CONF_NAME,
    STATE_UNAVAILABLE,
    STATE_UNKNOWN,
    UnitOfPower,
    UnitOfTemperature,
    UnitOfEnergy,
    UnitOfElectricPotential,
    UnitOfElectricCurrent,
    UnitOfFrequency,
    UnitOfReactivePower,
    PERCENTAGE,
)
from homeassistant.config_entries import SOURCE_IMPORT, ConfigEntry
from homeassistant.exceptions import ConfigEntryAuthFailed, ConfigEntryNotReady
from homeassistant.helpers.device_registry import DeviceInfo
from homeassistant.helpers.update_coordinator import (
    CoordinatorEntity,
    DataUpdateCoordinator,
)
from homeassistant.helpers.restore_state import ExtraStoredData, RestoreEntity
from homeassistant.util.ssl import SSLCipherList
from homeassistant.helpers.icon import icon_for_battery_level
from homeassistant.util import dt as dt_util
import homeassistant.helpers.config_validation as cv

from .api import FoxESSApiClient, GetAuth, waitforAPI
from .const import (
    ATTR_BATTERYLIST,
    ATTR_DEVICE_SN,
    ATTR_DEVICE_TYPE,
    ATTR_LASTCLOUDSYNC,
    ATTR_MANAGER,
    ATTR_MASTER,
    ATTR_MODULESN,
    ATTR_PLANTNAME,
    ATTR_SLAVE,
    BATTERY_LEVELS,
    CONF_APIKEY,
    CONF_DEVICEID,
    CONF_DEVICESN,
    CONF_ENERGY_GENERATED_SANITY,
    CONF_EVO,
    CONF_EXTPV,
    CONF_GET_VARIABLES,
    CONF_NAME,
    CONF_REDUCE_API_CALLS,
    CONF_SCHEDULER_API_VERSION,
    CONF_SHOW_UNKNOWN_ZERO,
    CONF_SYSTEM_ID,
    CONF_V1_API,
    CONF_XTZONE,
    DEFAULT_ENERGY_GENERATED_SANITY,
    DEFAULT_NAME,
    DEFAULT_REDUCE_API_CALLS,
    DEFAULT_TIMEOUT,
    DOMAIN,
    FetchResult,
    RETRY_IN_5_MINS,
    RETRY_IN_10_MINS,
    RETRY_NEXT_SLOT,
    SCAN_INTERVAL,
    SCHEDULER_API_V2,
    SCHEDULER_API_V3,
    SCAN_MINUTES,
    YAML_CONFIGS_KEY,
    _AUTH_ERRNO,
    _ENDPOINT_OA_BATTERY_SETTINGS,
    _ENDPOINT_OA_DAILY_GENERATION,
    _ENDPOINT_OA_DEVICE_DETAIL,
    _ENDPOINT_OA_DEVICE_DETAIL_V1,
    _ENDPOINT_OA_DEVICE_LIST,
    _ENDPOINT_OA_DEVICE_VARIABLES,
    _ENDPOINT_OA_DEVICE_VARIABLES_V1,
    _ENDPOINT_OA_DOMAIN,
    _ENDPOINT_OA_REPORT,
)

_LOGGER = logging.getLogger(__name__)

METHOD_POST = "POST"
METHOD_GET = "GET"
DEFAULT_ENCODING = "UTF-8"
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
DEFAULT_VERIFY_SSL = False

PLATFORM_SCHEMA = PLATFORM_SCHEMA.extend(
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
        vol.Optional(
            CONF_ENERGY_GENERATED_SANITY, default=DEFAULT_ENERGY_GENERATED_SANITY
        ): cv.positive_float,
        vol.Optional(
            CONF_REDUCE_API_CALLS, default=DEFAULT_REDUCE_API_CALLS
        ): cv.boolean,
        vol.Optional(CONF_SHOW_UNKNOWN_ZERO, default=False): cv.boolean,
    }
)

token = None
timeslice = {}
last_api = 0
LastHour = 0
RestrictGetVar = False
xtzone = False
V1_Api = True
Evo = False


async def async_setup_entry(hass, config_entry, async_add_entities):
    """Set up FoxESS sensors from a config entry."""
    config = {**config_entry.data, **config_entry.options}
    coordinator = (
        hass.data.get(DOMAIN, {}).get(config_entry.entry_id, {}).get("coordinator")
    )
    await _async_setup_foxess(
        hass,
        config,
        async_add_entities,
        config_entry,
        coordinator=coordinator,
    )


async def async_setup_platform(hass, config, async_add_entities, discovery_info=None):
    """Set up the FoxESS sensor from YAML."""
    device_sn = config.get(CONF_DEVICESN)
    if not device_sn:
        return

    # Advertise YAML config so the config flow can detect conflicts and
    # preserve the original deviceID (which may differ from deviceSN).
    yaml_configs = hass.data.setdefault(YAML_CONFIGS_KEY, {})
    yaml_configs[device_sn] = {
        CONF_DEVICEID: config.get(CONF_DEVICEID),
        CONF_NAME: config.get(CONF_NAME, DEFAULT_NAME),
    }

    # Check if a ConfigEntry already exists for this deviceSN
    current_entries = hass.config_entries.async_entries(DOMAIN)
    if any(
        entry.unique_id == device_sn or entry.data.get(CONF_DEVICESN) == device_sn
        for entry in current_entries
    ):
        _LOGGER.debug(
            "FoxESS device %s is already configured in UI, skipping YAML setup",
            device_sn,
        )
        return

    # Trigger automatic import into UI
    _LOGGER.info(
        "Importing FoxESS device %s from configuration.yaml into UI", device_sn
    )
    hass.async_create_task(
        hass.config_entries.flow.async_init(
            DOMAIN,
            context={"source": SOURCE_IMPORT},
            data=config,
        )
    )


class FoxDataUpdateCoordinator(DataUpdateCoordinator):
    """DataUpdateCoordinator for FoxESS."""

    def __init__(
        self,
        hass: HomeAssistant,
        config: dict,
        config_entry: ConfigEntry | None = None,
        client: FoxESSApiClient | None = None,
    ) -> None:
        """Initialize FoxESS coordinator."""
        self.config = config
        self.client = client or FoxESSApiClient(hass)
        self.devicesn = config.get(CONF_DEVICESN)
        self.deviceID = config.get(CONF_DEVICEID) or self.devicesn
        self.inverter_name = config.get(CONF_NAME, DEFAULT_NAME)
        self.apiKey = config.get(CONF_APIKEY)
        self.ExtPV = bool(config.get(CONF_EXTPV, False))
        self.xtzone = bool(config.get(CONF_XTZONE, False))
        self.RestrictGetVar = bool(config.get(CONF_GET_VARIABLES, False))
        self.V1_Api = config.get(CONF_V1_API) is not False
        self.Evo = bool(config.get(CONF_EVO, False))
        self.energyGeneratedSanityCheck = float(
            config.get(CONF_ENERGY_GENERATED_SANITY, DEFAULT_ENERGY_GENERATED_SANITY)
            or DEFAULT_ENERGY_GENERATED_SANITY
        )
        self.reduce_api_calls = bool(
            config.get(CONF_REDUCE_API_CALLS, DEFAULT_REDUCE_API_CALLS)
        )
        self.scheduler_api_version = config.get(
            CONF_SCHEDULER_API_VERSION, SCHEDULER_API_V2
        )
        self.daily_gen_interval = 60 if self.reduce_api_calls else 15
        self.daily_gen_retry_interval = 10 if self.reduce_api_calls else 5
        self.daily_gen_timer = 0
        self.allData = {
            "report": {},
            "report_date": None,
            "reportDailyGeneration": {},
            "raw": {},
            "battery": {},
            "addressbook": {
                "hasBattery": config.get("has_battery", False),
                "status": "3",
            },
            "online": False,
            "workMode": None,
            "schedulerEnabled": False,
            "schedulerGroups": [],
        }

        if self.devicesn:
            timeslice[self.devicesn] = RETRY_NEXT_SLOT

        super().__init__(
            hass,
            _LOGGER,
            name=self.inverter_name or DEFAULT_NAME,
            update_method=self.async_update_data,
            update_interval=SCAN_INTERVAL,
            config_entry=config_entry,
        )
        self.data = self.allData

    async def async_config_entry_first_refresh(self) -> None:
        """Perform first refresh during config entry setup."""
        await self.async_refresh()
        if isinstance(self.last_exception, ConfigEntryAuthFailed):
            raise self.last_exception
        if not self.last_update_success:
            raise ConfigEntryNotReady(
                f"Failed to connect to FoxESS Cloud: {self.last_exception or 'initial refresh failed'}"
            )

    async def async_update_data(self) -> dict:
        """Fetch data from FoxESS Cloud."""
        global token, timeslice, LastHour, last_api, RestrictGetVar, xtzone, V1_Api, Evo
        Evo = self.Evo
        V1_Api = self.V1_Api
        RestrictGetVar = self.RestrictGetVar
        xtzone = self.xtzone
        devicesn = self.devicesn
        apiKey = self.apiKey
        name = self.inverter_name
        reduce_api_calls = self.reduce_api_calls
        allData = self.allData
        config_entry = self.config_entry

        _LOGGER.debug("Updating data from https://www.foxesscloud.com/")
        hournow = datetime.now().strftime("%H")  # update hour now
        _LOGGER.debug("Time now: %s, last %s", hournow, LastHour)
        tslice = timeslice.get(devicesn, RETRY_NEXT_SLOT) + 1  # increment current device time slice
        timeslice[devicesn] = tslice

        main_poll_due = (tslice % 10 == 0) if reduce_api_calls else (tslice % 5 == 0)
        detail_due = (tslice % 30 == 0) if reduce_api_calls else (tslice % 15 == 0)
        report_due = (tslice % 60 == 0) if reduce_api_calls else (tslice % 15 == 0)
        retry_slot = RETRY_IN_10_MINS if reduce_api_calls else RETRY_IN_5_MINS

        # Independent timer for daily generation report (#324)
        self.daily_gen_timer -= 1
        if self.daily_gen_timer <= 0:
            _LOGGER.debug(
                "Fetching OA Daily Generation Report on independent schedule for SN: %s",
                devicesn,
            )
            try:
                gen_error = await getReportDailyGeneration(
                    self.hass, allData, apiKey, devicesn
                )
                if gen_error is FetchResult.AUTH_FAILED:
                    if config_entry is not None:
                        raise ConfigEntryAuthFailed("FoxESS API key rejected")
                    _LOGGER.error(
                        "FoxESS API authentication failed in daily generation. "
                        "Update your apiKey in configuration.yaml and restart."
                    )
                elif gen_error:
                    _LOGGER.debug(
                        "getReportDailyGeneration failed for SN %s, retry in %s minutes",
                        devicesn,
                        self.daily_gen_retry_interval,
                    )
                    self.daily_gen_timer = self.daily_gen_retry_interval
                else:
                    self.daily_gen_timer = self.daily_gen_interval
            except ConfigEntryAuthFailed:
                raise
            except Exception as err:
                _LOGGER.warning(
                    "Unexpected error fetching daily generation for SN %s: %s, retry in %s minutes",
                    devicesn,
                    err,
                    self.daily_gen_retry_interval,
                )
                self.daily_gen_timer = self.daily_gen_retry_interval

        if main_poll_due:
            _LOGGER.debug("Main Poll, interval: %s, %s", devicesn, timeslice[devicesn])
            # try the openapi see if we get a response
            geterror = FetchResult.OK
            if detail_due:
                # get device detail at startup, then periodically to save api calls
                if Evo:
                    # Evo not currently in device detail, use list and fill partial blanks
                    geterror = await getOADeviceList(self.hass, allData, devicesn, apiKey)
                else:
                    geterror = await getOADeviceDetail(self.hass, allData, devicesn, apiKey)
                if geterror is FetchResult.AUTH_FAILED:
                    if config_entry is not None:
                        raise ConfigEntryAuthFailed("FoxESS API key rejected")
                    _LOGGER.error(
                        "FoxESS API authentication failed. "
                        "Update your apiKey in configuration.yaml and restart."
                    )
                    return allData
                await asyncio.sleep(1)  # OpenAPI demand
            if not geterror:
                if allData["addressbook"]["status"] is not None:
                    statetest = int(allData["addressbook"]["status"])
                    if statetest in [3]:
                        allData["raw"]["runningState"] = "164"  # off-grid
                else:
                    statetest = 0
                _LOGGER.debug(" Statetest %s", statetest)
                if statetest in [1, 2]:
                    allData["online"] = True
                    if tslice == 0:
                        # read in battery settings if fitted at startup, then every 60 mins
                        await getOABatterySettings(self.hass, allData, devicesn, apiKey)
                        await asyncio.sleep(1)  # OpenAPI demand
                        if allData.get("addressbook", {}).get("hasBattery"):
                            await getOAWorkModeAndScheduler(
                                self.hass,
                                allData,
                                devicesn,
                                apiKey,
                                scheduler_api_version=self.scheduler_api_version,
                            )
                    # main real time data fetch, followed by reports
                    geterror = await getRaw(
                        self.hass, allData, apiKey, devicesn, reduce_api_calls=reduce_api_calls
                    )
                    if geterror is FetchResult.AUTH_FAILED:
                        if config_entry is not None:
                            raise ConfigEntryAuthFailed("FoxESS API key rejected")
                        _LOGGER.error(
                            "FoxESS API authentication failed. "
                            "Update your apiKey in configuration.yaml and restart."
                        )
                        return allData
                    if not geterror:
                        if report_due:  # do at startup and periodically (every 15m or 60m)
                            await asyncio.sleep(1)  # OpenAPI demand limit
                            geterror = await getReport(self.hass, allData, apiKey, devicesn)
                            if geterror:
                                _LOGGER.debug("getReport False")
                                geterror = FetchResult.OK
                                allData["online"] = False
                                tslice = retry_slot  # retry in 5 or 10 minutes
                    else:
                        _LOGGER.debug("get variables failed")
                        if statetest == 2:
                            # The inverter is in alarm, don't check every minute
                            _LOGGER.debug(
                                "Inverter in alarm, slowing retry response for SN: %s",
                                devicesn,
                            )
                            allData["online"] = False
                            tslice = retry_slot  # retry in 5 or 10 minutes
                        else:
                            if geterror is FetchResult.DNS_TIMEOUT:
                                _LOGGER.warning("Fox Cloud - DNS fail, retry in 1 minute")
                                # retry in 1 minute
                                if tslice != 0:
                                    tslice = (tslice-1)
                                else:
                                    tslice = RETRY_NEXT_SLOT
                            else:
                                # The get variables api call failed, leave it 5 or 10 minutes
                                _LOGGER.debug("slowing retry response for SN: %s", devicesn)
                                allData["online"] = False
                                tslice = retry_slot  # retry in 5 or 10 minutes
                        geterror = FetchResult.OK
                else:
                    if statetest == 3:
                        # The inverter is off-line, no raw data polling, don't update entities
                        # retry device detail call periodically until it comes back on-line
                        allData["online"] = False
                        tslice = retry_slot  # retry in 5 or 10 minutes
                        _LOGGER.debug("Inverter off-line for SN: %s", devicesn)

                if not allData["online"]:
                    if not geterror:
                        _LOGGER.warning("%s Inverter is off-line, waiting to retry", name)
                    else:
                        _LOGGER.warning("%s Cloud timeout, retry in 1 minute", name)
            else:
                _LOGGER.warning("%s Cloud timeout on Device Detail, retry in 1 minute.", name)

            if geterror is not FetchResult.OK:
                allData["online"] = False
                if tslice != 0:
                    tslice = tslice-1
                    # failed to get specific detail so retry slot in 1 minute
                else:
                    tslice = RETRY_NEXT_SLOT  # failed to get full data, try again in 1 minute

        # actions here are every minute
        if tslice >= 59:
            tslice = RETRY_NEXT_SLOT  # reset timeslot, ready for full data fetch at 0
        _LOGGER.debug("Auxilliary timeslice %s, %s", devicesn, tslice)

        if LastHour != hournow:
            LastHour = hournow  # update the hour the last poll was run

        timeslice[devicesn] = tslice

        _LOGGER.debug(allData)

        return allData


async def _async_setup_foxess(
    hass,
    config,
    async_add_entities,
    config_entry=None,
    coordinator=None,
):
    """Shared setup logic for platform and config entry."""
    global LastHour, timeslice, last_api, RestrictGetVar, xtzone, V1_Api, Evo
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
    energyGeneratedSanityCheck = float(
        config.get(CONF_ENERGY_GENERATED_SANITY, DEFAULT_ENERGY_GENERATED_SANITY)
        or DEFAULT_ENERGY_GENERATED_SANITY
    )
    reduce_api_calls = bool(
        config.get(CONF_REDUCE_API_CALLS, DEFAULT_REDUCE_API_CALLS)
    )
    _LOGGER.debug("API Key: %s", f"...{apiKey[-4:]}" if apiKey else "(unset)")
    _LOGGER.debug("Device SN: %s", devicesn)
    _LOGGER.debug("Device ID: %s", deviceID)
    _LOGGER.debug("FoxESS Scan Interval: %s minutes", SCAN_MINUTES)
    _LOGGER.debug("Cross Time Zone: %s", xtzone)
    _LOGGER.debug("Restrict Variables: %s", RestrictGetVar)
    _LOGGER.debug("Extended PV: %s", ExtPV)
    _LOGGER.debug("v1 Api Calls: %s", V1_Api)
    _LOGGER.debug("EVO: %s", Evo)
    _LOGGER.debug("Energy Sanity Check: %s kWh", energyGeneratedSanityCheck)
    _LOGGER.debug("Reduced API Calls Mode: %s", reduce_api_calls)
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

    if devicesn and devicesn not in timeslice:
        timeslice[devicesn] = RETRY_NEXT_SLOT

    if coordinator is None:
        coordinator = FoxDataUpdateCoordinator(
            hass,
            config,
            config_entry=config_entry,
        )
        await coordinator.async_refresh()

        if not coordinator.last_update_success:
            _LOGGER.error(
                "FoxESS Cloud initialisation failed, Fatal Error - correct error and restart Home Assistant"
            )
            return False

    name = coordinator.inverter_name or name
    deviceID = coordinator.deviceID or deviceID
    if hasattr(coordinator, "ExtPV") and ExtPV is False:
        ExtPV = coordinator.ExtPV

    def make(cls, *args, **kwargs):
        return cls(coordinator, name, deviceID, *args, **kwargs)

    async_add_entities(
        [
            *(
                entity
                for i in range(1, 7)
                for entity in (
                    make(
                        FoxESSCurrent,
                        f"PV{i} Current",
                        f"pv{i}-current",
                        f"pv{i}Current",
                    ),
                    make(FoxESSPower, f"PV{i} Power", f"pv{i}-power", f"pv{i}Power"),
                    make(FoxESSVolt, f"PV{i} Volt", f"pv{i}-volt", f"pv{i}Volt"),
                )
            ),
            make(FoxESSPower, "PV Power", "pv-power", "pvPower"),
            *(
                entity
                for phase in ("R", "S", "T")
                for entity in (
                    make(
                        FoxESSCurrent,
                        f"{phase} Current",
                        f"{phase.lower()}-current",
                        f"{phase}Current",
                    ),
                    make(
                        FoxESSFreq,
                        f"{phase} Freq",
                        f"{phase.lower()}-freq",
                        f"{phase}Freq",
                    ),
                    make(
                        FoxESSPower,
                        f"{phase} Power",
                        f"{phase.lower()}-power",
                        f"{phase}Power",
                    ),
                    make(
                        FoxESSVolt,
                        f"{phase} Volt",
                        f"{phase.lower()}-volt",
                        f"{phase}Volt",
                    ),
                )
            ),
            make(FoxESSPowerString, "Meter2 Power", "meter2-power", "meterPower2"),
            make(FoxESSReactivePower),
            make(FoxESSPowerFactor),
            make(FoxESSTemp, "Bat Temperature", "bat-temperature", "batTemperature"),
            make(
                FoxESSTemp, "Bat Temperature2", "bat-temperature2", "batTemperature_2"
            ),
            make(
                FoxESSTemp,
                "Ambient Temperature",
                "ambient-temperature",
                "ambientTemperation",
            ),
            make(
                FoxESSTemp, "Boost Temperature", "boost-temperature", "boostTemperation"
            ),
            make(FoxESSTemp, "Inv Temperature", "inv-temperature", "invTemperation"),
            make(FoxESSBatSoC, "Bat SoC", "bat-soc", "SoC"),
            make(FoxESSBatSoC, "Bat SoC1", "bat-soc1", "SoC_1"),
            make(FoxESSBatSoC, "Bat SoC2", "bat-soc2", "SoC_2"),
            make(FoxESSBatSoC, "Bat SoH", "bat-soh", "SOH"),
            make(FoxESSPower, "Inverter Bat Power", "inv-Bat-Power", "invBatPower"),
            make(FoxESSPower, "Inverter Bat Power2", "inv-Bat-Power2", "invBatPower_2"),
            make(FoxESSBatMinSoC),
            make(FoxESSBatMinSoConGrid),
            make(FoxESSSolarPower),
            make(FoxESSNewSolarPower),
            make(FoxESSEnergyThroughput),
            make(FoxESSEnergySolar, max_value=energyGeneratedSanityCheck),
            make(FoxESSInverter),
            make(
                FoxESSPowerString,
                "Generation Power",
                "-generation-power",
                "generationPower",
            ),
            make(
                FoxESSPowerString,
                "Grid Consumption Power",
                "grid-consumption-power",
                "gridConsumptionPower",
            ),
            make(FoxESSPowerString, "FeedIn Power", "feedIn-power", "feedinPower"),
            make(
                FoxESSPowerString,
                "Bat Discharge Power",
                "bat-discharge-power",
                "batDischargePower",
            ),
            make(FoxESSNewBatDischargePower),
            make(
                FoxESSPowerString,
                "Bat Charge Power",
                "bat-charge-power",
                "batChargePower",
            ),
            make(FoxESSPowerString, "Load Power", "load-power", "loadsPower"),
            make(
                FoxESSEnergyGenerated,
                "Energy Generated",
                "energy-generated",
                "value",
                max_value=energyGeneratedSanityCheck,
            ),
            make(
                FoxESSEnergyGenerated,
                "Energy Generated Month",
                "energy-generated-month",
                "month",
            ),
            make(
                FoxESSEnergyGenerated,
                "Energy Generated Cumulative",
                "energy-generated-cumulative",
                "cumulative",
                max_daily_increase=energyGeneratedSanityCheck,
            ),
            make(FoxESSEnergyGridConsumption),
            make(FoxESSEnergyFeedin),
            make(FoxESSEnergyBatCharge),
            make(FoxESSEnergyBatDischarge),
            make(FoxESSEnergyLoad),
            make(FoxESSPVEnergyTotal),
            make(FoxESSResidualEnergy),
            make(FoxESSResponseTime),
            make(FoxESSMaxBatChargeCurrent),
            make(FoxESSMaxBatDischargeCurrent),
            make(FoxESSRunningState, "Running State", "running-state", "runningState"),
        ]
    )

    if ExtPV:
        async_add_entities(
            [
                entity
                for i in range(7, 19)
                for entity in (
                    make(
                        FoxESSCurrent,
                        f"PV{i} Current",
                        f"pv{i}-current",
                        f"pv{i}Current",
                    ),
                    make(FoxESSPower, f"PV{i} Power", f"pv{i}-power", f"pv{i}Power"),
                    make(FoxESSVolt, f"PV{i} Volt", f"pv{i}-volt", f"pv{i}Volt"),
                )
            ]
        )


def _is_ok(response: dict) -> bool:
    """Return True when a FoxESS OpenAPI response reports success.

    Relies on ``errno == 0`` only; the ``msg`` changes occasionaly
    so it's not a reliable signal.
    """
    return response.get("errno") == 0


async def getOADeviceDetail(hass, allData, devicesn, apiKey):
    client = FoxESSApiClient(hass)
    res, response, elapsed_ms = await client.async_get_device_detail(
        devicesn, apiKey, v1_api=V1_Api
    )
    if res is not FetchResult.OK or not response:
        _LOGGER.debug("Unable to get OA Device Detail from FoxESS Cloud")
        return res

    if _is_ok(response):
        allData["raw"]["ResponseTime"] = max(0, elapsed_ms)
        _LOGGER.debug("OA Device Detail Good Response: %s", response.get("result"))
        result = response["result"]
        allData["addressbook"] = result
        # manually poke this in as on the old cloud it was called plantname, need to keep in line with old entity name
        plantName = result.get("stationName")
        allData["addressbook"]["plantName"] = plantName
        testBattery = result.get("hasBattery")
        if testBattery:
            _LOGGER.debug("OA Device Detail System has Battery: %s", testBattery)
        else:
            _LOGGER.debug("OA Device Detail System has No Battery: %s", testBattery)
            allData["addressbook"][ATTR_BATTERYLIST] = "No Battery"
        return FetchResult.OK
    else:
        _LOGGER.error("OA Device Detail Bad Response: %s", response)
        return (
            FetchResult.AUTH_FAILED
            if response.get("errno") in _AUTH_ERRNO
            else FetchResult.ERROR
        )


async def getOADeviceList(hass, allData, devicesn, apiKey):
    client = FoxESSApiClient(hass)
    res, response, elapsed_ms = await client.async_get_device_list(
        apiKey, page=1, page_size=10
    )
    if res is not FetchResult.OK or not response:
        _LOGGER.debug("Unable to get OA Device List from FoxESS Cloud")
        return res

    if _is_ok(response):
        allData["raw"]["ResponseTime"] = max(0, elapsed_ms)
        _LOGGER.debug("OA Device List Good Response: %s", response.get("result"))
        result_data = response.get("result", {}).get("data", [])
        item = {}
        for d in result_data:
            if d.get("deviceSN") == devicesn:
                item = d
                break
        if not item and result_data:
            item = result_data[0]
        allData["addressbook"] = item
        plantName = item.get("stationName")
        allData["addressbook"]["plantName"] = plantName
        allData["addressbook"]["masterVersion"] = "not provided"
        allData["addressbook"]["managerVersion"] = "not provided"
        allData["addressbook"]["slaveVersion"] = "not provided"
        allData["addressbook"]["batteryList"] = "not provided"
        testBattery = item.get("hasBattery")
        if testBattery:
            _LOGGER.debug("OA Device List System has Battery: %s", testBattery)
        else:
            _LOGGER.debug("OA Device List System has No Battery: %s", testBattery)
            allData["addressbook"][ATTR_BATTERYLIST] = "No Battery"
        return FetchResult.OK
    else:
        _LOGGER.error("OA Device List Bad Response: %s", response)
        return (
            FetchResult.AUTH_FAILED
            if response.get("errno") in _AUTH_ERRNO
            else FetchResult.ERROR
        )


async def getOABatterySettings(hass, allData, devicesn, apiKey):
    if "hasBattery" not in allData.get("addressbook", {}):
        hasBattery = False
    else:
        hasBattery = allData["addressbook"]["hasBattery"]

    if hasBattery:
        # only make this call if device detail reports battery fitted
        _LOGGER.debug("OABattery Settings fetch for SN: %s", devicesn)
        client = FoxESSApiClient(hass)
        res, response, elapsed_ms = await client.async_get_battery_settings(devicesn, apiKey)
        if res is not FetchResult.OK or not response:
            _LOGGER.debug("Unable to get OA Battery Settings from FoxESS Cloud")
            return res

        if _is_ok(response):
            _LOGGER.debug(
                "OA Battery Settings Good Response: %s", response.get("result")
            )
            result = response.get("result", {})
            minSoc = result.get("minSoc")
            minSocOnGrid = result.get("minSocOnGrid")
            allData["battery"]["minSoc"] = minSoc
            allData["battery"]["minSocOnGrid"] = minSocOnGrid
            _LOGGER.debug(
                "OA Battery Settings read MinSoc: %s, MinSocOnGrid: %s",
                minSoc,
                minSocOnGrid,
            )
            return FetchResult.OK
        else:
            _LOGGER.error("OA Battery Settings Bad Response: %s", response)
            return (
                FetchResult.AUTH_FAILED
                if response.get("errno") in _AUTH_ERRNO
                else FetchResult.ERROR
            )
    else:
        # device detail reports no battery fitted so reset these variables to show unknown
        allData["battery"]["minSoc"] = None
        allData["battery"]["minSocOnGrid"] = None
        return FetchResult.OK


async def getOAWorkModeAndScheduler(
    hass, allData, devicesn, apiKey, scheduler_api_version=SCHEDULER_API_V2
):
    """Fetch Work Mode and Scheduler flag/groups from FoxESS Cloud."""
    client = FoxESSApiClient(hass)
    try:
        res, resp, _ = await client.async_get_work_mode(devicesn, apiKey)
        if res is FetchResult.OK and resp and resp.get("errno") == 0:
            result = resp.get("result", {})
            work_mode = (
                result.get("values", {}).get("WorkMode")
                if isinstance(result.get("values"), dict)
                else result.get("value")
            )
            if work_mode:
                allData["workMode"] = work_mode
        await asyncio.sleep(1)

        res_flag, resp_flag, _ = await client.async_get_scheduler_flag(devicesn, apiKey)
        if res_flag is FetchResult.OK and resp_flag and resp_flag.get("errno") == 0:
            result_flag = resp_flag.get("result", {})
            enable = result_flag.get("enable")
            if enable is not None:
                allData["schedulerEnabled"] = bool(enable)
        await asyncio.sleep(1)

        if scheduler_api_version == SCHEDULER_API_V3:
            get_groups = client.async_get_scheduler_groups_v3
        else:
            get_groups = client.async_get_scheduler_groups
        res_grp, resp_grp, _ = await get_groups(devicesn, apiKey)
        if res_grp is FetchResult.OK and resp_grp and resp_grp.get("errno") == 0:
            result_grp = resp_grp.get("result", {})
            groups = result_grp.get("groups")
            if isinstance(groups, list):
                allData["schedulerGroups"] = groups
        await asyncio.sleep(1)

        res_fct, resp_fct, _ = await client.async_get_force_charge_times(devicesn, apiKey)
        if res_fct is FetchResult.OK and resp_fct and resp_fct.get("errno") == 0:
            result_fct = resp_fct.get("result", {})
            if isinstance(result_fct, list) and result_fct:
                result_fct = result_fct[0]
            if isinstance(result_fct, dict):
                allData["forceChargeTimes"] = result_fct
    except Exception as err:
        _LOGGER.debug("Error fetching work mode or scheduler settings: %s", err)


async def getReport(hass, allData, apiKey, devicesn):
    client = FoxESSApiClient(hass)
    _LOGGER.debug("OA Report fetch for SN %s", devicesn)

    now = datetime.now()
    variables = [
        "feedin",
        "generation",
        "gridConsumption",
        "chargeEnergyToTal",
        "dischargeEnergyToTal",
        "loads",
        "PVEnergyTotal",
    ]

    res, response, elapsed_ms = await client.async_get_report(
        devicesn=devicesn,
        token=apiKey,
        year=now.year,
        month=now.month,
        variables=variables,
    )

    if res is not FetchResult.OK or not response:
        _LOGGER.debug("Unable to get OA Report from FoxESS Cloud")
        return res

    if _is_ok(response):
        _LOGGER.debug("OA Report Data fetched OK: %s", response)
        result = response.get("result", [])
        today = now.day
        for item in result:
            variableName = item.get("variable")
            if not variableName:
                continue
            index = 1
            cumulative_total = 0
            for dataItem in item.get("values", []):
                if today == index:
                    if dataItem is not None:
                        cumulative_total = dataItem
                    else:
                        _LOGGER.debug("Report month fetch, None received")
                    break
                index += 1
            allData["report"][variableName] = round(cumulative_total, 3)
            _LOGGER.debug(
                "OA Report Variable: %s, Total: %s", variableName, cumulative_total
            )
        allData["report_date"] = now.date()
        return FetchResult.OK
    else:
        _LOGGER.debug("OA Report Bad Response: %s", response)
        return (
            FetchResult.AUTH_FAILED
            if response.get("errno") in _AUTH_ERRNO
            else FetchResult.ERROR
        )


async def getReportDailyGeneration(hass, allData, apiKey, devicesn):
    client = FoxESSApiClient(hass)
    _LOGGER.debug("getReportDailyGeneration fetch for SN %s", devicesn)

    res, response, elapsed_ms = await client.async_get_daily_generation(devicesn, apiKey)
    if res is not FetchResult.OK or not response:
        _LOGGER.debug("Unable to get OA Daily Generation Report from FoxESS Cloud")
        return res

    if _is_ok(response):
        _LOGGER.debug("OA Daily Generation Report Data fetched OK Response: %s", response)

        result_data = response.get("result")
        if not isinstance(result_data, dict):
            _LOGGER.debug(
                "OA Daily Generation Report result is not a dict: %s", result_data
            )
            return FetchResult.ERROR

        parsed = result_data
        if "today" in parsed and parsed["today"] is not None:
            allData["reportDailyGeneration"]["value"] = parsed["today"]
            _LOGGER.debug(
                "OA Daily Generation Report data: todays value %s ", parsed["today"]
            )
        else:
            _LOGGER.debug(
                "OA Daily Generation Report data, today has no value in %s, retaining previous: %s",
                parsed,
                allData["reportDailyGeneration"].get("value"),
            )

        if "month" in parsed and parsed["month"] is not None:
            allData["reportDailyGeneration"]["month"] = parsed["month"]
            _LOGGER.debug(
                "OA Daily Generation Report data: month value %s ", parsed["month"]
            )
        else:
            _LOGGER.debug(
                "OA Daily Generation Report data, month has no value in %s, retaining previous: %s",
                parsed,
                allData["reportDailyGeneration"].get("month"),
            )

        if "cumulative" in parsed and parsed["cumulative"] is not None:
            allData["reportDailyGeneration"]["cumulative"] = parsed["cumulative"]
            _LOGGER.debug(
                "OA Daily Generation Report data: cumulative value %s ",
                parsed["cumulative"],
            )
        else:
            _LOGGER.debug(
                "OA Daily Generation Report data, cumulative has no value in %s, retaining previous: %s",
                parsed,
                allData["reportDailyGeneration"].get("cumulative"),
            )

        return FetchResult.OK
    else:
        _LOGGER.debug("OA Daily Generation Report Bad Response: %s", response)
        return (
            FetchResult.AUTH_FAILED
            if response.get("errno") in _AUTH_ERRNO
            else FetchResult.ERROR
        )


async def getRaw(hass, allData, apiKey, devicesn, reduce_api_calls: bool = False):
    client = FoxESSApiClient(hass)
    raw_vars = None
    if RestrictGetVar:
        _LOGGER.debug("Getting Device Variable in restricted mode")
        raw_vars = [
            "ambientTemperation",
            "batChargePower",
            "batCurrent",
            "batCurrent_1",
            "batCurrent_2",
            "batDischargePower",
            "batTemperature",
            "batTemperature_1",
            "batTemperature_2",
            "batVolt",
            "batVolt_1",
            "batVolt_2",
            "boostTemperation",
            "chargeTemperature",
            "dspTemperature",
            "epsCurrentR",
            "epsCurrentS",
            "epsCurrentT",
            "epsPower",
            "epsPowerR",
            "epsPowerS",
            "epsPowerT",
            "epsVoltR",
            "epsVoltS",
            "epsVoltT",
            "feedinPower",
            "generationPower",
            "gridConsumptionPower",
            "input",
            "invBatCurrent",
            "invBatPower",
            "invBatVolt",
            "invTemperation",
            "loadsPower",
            "loadsPowerR",
            "loadsPowerS",
            "loadsPowerT",
            "meterPower",
            "meterPower2",
            "meterPowerR",
            "meterPowerS",
            "meterPowerT",
            "PowerFactor",
            "pv1Current",
            "pv1Power",
            "pv1Volt",
            "pv2Current",
            "pv2Power",
            "pv2Volt",
            "pv3Current",
            "pv3Power",
            "pv3Volt",
            "pv4Current",
            "pv4Power",
            "pv4Volt",
            "pvPower",
            "RCurrent",
            "ReactivePower",
            "RFreq",
            "RPower",
            "RVolt",
            "SCurrent",
            "SFreq",
            "SoC",
            "SPower",
            "SVolt",
            "TCurrent",
            "TFreq",
            "TPower",
            "TVolt",
            "SoC_1",
            "Soc_2",
            "ResidualEnergy",
            "energyThroughput",
            "runningState",
            "currentFaultCount",
        ]

    res, response, elapsed_ms = await client.async_get_real_data(
        devicesn=devicesn,
        token=apiKey,
        variables=raw_vars,
        v1_api=V1_Api,
    )

    if res is not FetchResult.OK or not response:
        _LOGGER.debug("Unable to get OA Variables from FoxESS Cloud")
        return res

    if _is_ok(response):
        allData["raw"]["ResponseTime"] = max(0, elapsed_ms)
        test = response.get("result")
        if not test or not isinstance(test, list):
            _LOGGER.debug("OA Variables empty result in response")
            return FetchResult.ERROR

        timercv = test[0].get("time")
        try:
            # format is "2025-02-21 16:38:29 GMT+0000" strptime is useless at international dates, so work out the offset
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
            if tzoffsetsign in ["+"]:
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
        except:
            tsrcv = 0
        age = 0
        max_age = 661 if reduce_api_calls else 361
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
            if age > max_age:
                _LOGGER.debug(
                    "OA Variables invalid age: %s vs %s timestamps r:%s now:%s, age: %s (max: %s)",
                    timercv,
                    testd,
                    tsrcv,
                    tsnow,
                    age,
                    max_age,
                )

        result = test[0].get("datas", [])
        _LOGGER.debug("OA Variables Good Response: %s", result)
        for item in result:
            variableName = item.get("variable")
            if not variableName:
                continue
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
                # OpenAPI may return:
                # - hundredths of kWh with unit '0.01kWh' (e.g. 1933.0 for 19.33 kWh) -> divide by 100
                # - tenths of kWh with unit '0.1kWh' (e.g. 235.0 for 23.5 kWh) -> divide by 10
                # - directly in kWh with unit '0.01kWh', 'kWh', '1.0kWh', or None (e.g. 20.2 or 23.5)
                if variableValue is not None:
                    scale = item.get("unit")
                    if scale == "0.1kWh":
                        if variableValue > 100.0:
                            variableValue = round(variableValue / 10.0, 2)
                            _LOGGER.debug("OA Variables ResidualEnergy Scale (0.1kWh): /10 to %s", variableValue)
                        else:
                            variableValue = round(float(variableValue), 2)
                    elif variableValue > 100.0:
                        variableValue = round(variableValue / 100.0, 2)
                        _LOGGER.debug("OA Variables ResidualEnergy Scale (>100): /100 to %s", variableValue)
                    else:
                        variableValue = round(float(variableValue), 2)
                        _LOGGER.debug("OA Variables ResidualEnergy: %s (scale: %s)", variableValue, scale)

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
                        if variableValue == "161" or variableValue == "162":
                            # waiting and solar only so set off-line flag
                            if age < max_age:
                                _LOGGER.debug(
                                    "Waiting but data less than %s minutes old - allow sample, RunningState: %s, hasBat: %s online: %s",
                                    round(max_age / 60),
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
    else:
        _LOGGER.debug("OA Device Variables Bad Response: %s", response)
        return (
            FetchResult.AUTH_FAILED
            if response.get("errno") in _AUTH_ERRNO
            else FetchResult.ERROR
        )


def _get_float(d: dict, key: str) -> float:
    """Return float(d[key]) when key exists and value is not None, else 0.0."""
    val = d.get(key)
    return float(val) if val is not None else 0.0


class FoxESSEntity(CoordinatorEntity, SensorEntity):
    """Base class for FoxESS sensor entities with DeviceInfo."""

    @property
    def _show_unknown_zero(self) -> bool:
        """Return True if offline zeroing is enabled in config."""
        config = getattr(self.coordinator, "config", None)
        if isinstance(config, dict):
            return bool(config.get(CONF_SHOW_UNKNOWN_ZERO, False))
        return False

    @property
    def device_info(self) -> DeviceInfo | None:
        """Return device information to group all entities under one device."""
        devicesn = getattr(self.coordinator, "devicesn", None) or getattr(
            self, "_deviceID", None
        )
        if not devicesn:
            return None
        inverter_name = getattr(self.coordinator, "inverter_name", None) or devicesn
        data = getattr(self.coordinator, "data", {}) or {}
        addressbook = data.get("addressbook", {}) if isinstance(data, dict) else {}
        return DeviceInfo(
            identifiers={(DOMAIN, devicesn)},
            name=inverter_name,
            manufacturer="FoxESS",
            model=addressbook.get(ATTR_DEVICE_TYPE),
            sw_version=addressbook.get(ATTR_MASTER),
            serial_number=devicesn,
            configuration_url=_ENDPOINT_OA_DOMAIN,
        )


class _RawDataSensor(FoxESSEntity):
    """Base class for reusable raw-data sensors configured at instantiation time.

    Use this when the same sensor class is instantiated multiple times with different
    names, unique IDs, and raw-data keys — for example, one class reused across all PV
    strings or grid phases. The name, unique ID, and key are passed as constructor
    arguments so each instance can be configured independently.
    """

    # Value reported instead of unknown when the show_unknown_zero option is on.
    # None means the option does not apply to this sensor.
    _unknown_zero_value: float | str | None = None

    def __init__(self, coordinator, name, deviceID, nameValue, uniqueValue, keyValue):
        """Initialize the sensor entity."""
        super().__init__(coordinator=coordinator)
        self._nameValue = nameValue
        self._uniqueValue = uniqueValue
        self._keyValue = keyValue
        self._none_reported = False
        _LOGGER.debug("Initiating Entity - %s", self._nameValue)
        self._attr_name = f"{name} - {self._nameValue}"
        self._attr_unique_id = f"{deviceID}{self._uniqueValue}"

    @property
    def native_value(self) -> float | None:
        """Return value from raw data."""
        if self.coordinator.data.get("online") and self.coordinator.data.get("raw"):
            if self._keyValue in self.coordinator.data["raw"]:
                return self.coordinator.data["raw"][self._keyValue]
            if not self._none_reported:
                _LOGGER.debug("%s None", self._keyValue)
                self._none_reported = True
        return self._unknown_zero_value if self._show_unknown_zero else None


class _FixedRawDataSensor(FoxESSEntity):
    """Base class for single-purpose raw-data sensors with identity baked into the class.

    Use this when the sensor class represents exactly one thing, so the name, unique ID,
    and raw-data key are fixed and declared as class attributes rather than passed at
    instantiation. Override _transform() to apply scaling or value correction without
    repeating the online/raw guard logic.
    """

    # These should be overridden in the subclasses.
    _name_value: str
    _unique_value: str
    _key_value: str
    # Set to False for values that are reported even while the inverter is offline.
    _requires_online: bool = True

    def __init__(self, coordinator, name, deviceID):
        """Initialize the sensor entity."""
        super().__init__(coordinator=coordinator)
        self._none_reported = False
        _LOGGER.debug("Initiating Entity - %s", self._name_value)
        self._attr_name = f"{name} - {self._name_value}"
        self._attr_unique_id = f"{deviceID}{self._unique_value}"

    def _transform(self, value):
        """Post-process the raw value. Override in subclasses to apply scaling or correction."""
        return value

    @property
    def native_value(self) -> float | None:
        """Return value from raw data, passed through _transform."""
        data = self.coordinator.data
        if self._requires_online and not (data.get("online") and data.get("raw")):
            return None
        raw = data.get("raw") or {}
        if self._key_value not in raw:
            if not self._none_reported:
                _LOGGER.debug("%s None", self._key_value)
                self._none_reported = True
            return None
        return self._transform(raw[self._key_value])


class FoxESSPowerString(_RawDataSensor):
    """Sensor entity for string power measurements in kW."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.POWER
    _attr_native_unit_of_measurement = UnitOfPower.KILO_WATT
    _unknown_zero_value = "0"


class FoxESSCurrent(_RawDataSensor):
    """Sensor entity for current measurements in amperes."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.CURRENT
    _attr_native_unit_of_measurement = UnitOfElectricCurrent.AMPERE
    _unknown_zero_value = 0.0


class FoxESSFreq(_RawDataSensor):
    """Sensor entity for grid frequency measurements in Hz."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.FREQUENCY
    _attr_native_unit_of_measurement = UnitOfFrequency.HERTZ


class FoxESSPower(_RawDataSensor):
    """Sensor entity for power measurements in kW."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.POWER
    _attr_native_unit_of_measurement = UnitOfPower.KILO_WATT
    _unknown_zero_value = 0.0


class FoxESSVolt(_RawDataSensor):
    """Sensor entity for voltage measurements in volts."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.VOLTAGE
    _attr_native_unit_of_measurement = UnitOfElectricPotential.VOLT
    _unknown_zero_value = 0.0


class FoxESSReactivePower(_FixedRawDataSensor):
    """Sensor entity for reactive power measurements."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.REACTIVE_POWER
    _attr_native_unit_of_measurement = UnitOfReactivePower.VOLT_AMPERE_REACTIVE
    _name_value = "Reactive Power"
    _unique_value = "reactive-power"
    _key_value = "ReactivePower"

    def _transform(self, value: float) -> float:
        """Scale kVAr to VAr."""
        return value * 1000


class FoxESSPowerFactor(_FixedRawDataSensor):
    """Sensor entity for power factor measurements."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.POWER_FACTOR
    _attr_native_unit_of_measurement = PERCENTAGE
    _name_value = "Power Factor"
    _unique_value = "power-factor"
    _key_value = "PowerFactor"


CUMULATIVE_REGRESSION_ACCEPT_AFTER = timedelta(hours=24)


@dataclass
class CumulativeGuardData(ExtraStoredData):
    """Last accepted lifetime cumulative value, kept across restarts."""

    last_valid: float
    last_valid_at: datetime | None

    def as_dict(self) -> dict:
        return {
            "last_valid": self.last_valid,
            "last_valid_at": (
                self.last_valid_at.isoformat() if self.last_valid_at else None
            ),
        }

    @classmethod
    def from_dict(cls, data: dict) -> CumulativeGuardData | None:
        try:
            last_valid = float(data["last_valid"])
            at = data.get("last_valid_at")
            return cls(last_valid, dt_util.parse_datetime(at) if at else None)
        except (KeyError, TypeError, ValueError):
            return None


class FoxESSEnergyGenerated(FoxESSEntity, RestoreEntity):
    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(
        self,
        coordinator,
        name,
        deviceID,
        nameValue,
        uniqueValue,
        keyValue,
        max_value=None,
        max_daily_increase=None,
    ):
        super().__init__(coordinator=coordinator)
        self._nameValue = nameValue
        self._uniqueValue = uniqueValue
        self._keyValue = keyValue
        self._max_value = max_value
        self._max_daily_increase = max_daily_increase
        self._last_known_value = None
        self._last_valid_cumulative = None
        self._last_valid_cumulative_at = None
        self._regression_since = None
        _LOGGER.debug("Initiating Entity - %s", self._nameValue)
        self._attr_name = f"{name} - {self._nameValue}"
        self._attr_unique_id = f"{deviceID}{self._uniqueValue}"

    @property
    def native_value(self) -> float | None:
        show_zero = self._show_unknown_zero
        if self._keyValue not in self.coordinator.data.get("reportDailyGeneration", {}):
            _LOGGER.debug("%s None", self._keyValue)
            return self._last_known_value if show_zero else None

        val = self.coordinator.data["reportDailyGeneration"][self._keyValue]
        if val is None:
            return self._last_known_value if show_zero else None

        if val == 0:
            energygenerated = 0.0
        else:
            if val > 0:
                energygenerated = round(float(val), 3)
            else:
                energygenerated = 0.0

        if (
            self._max_value is not None
            and energygenerated is not None
            and energygenerated > self._max_value
        ):
            _LOGGER.warning(
                "%s value %s exceeds sanity check threshold %s kWh, ignoring",
                self._nameValue,
                energygenerated,
                self._max_value,
            )
            return self._last_known_value if show_zero else None

        if self._keyValue == "cumulative" and not self._cumulative_guard_accepts(
            energygenerated
        ):
            return self._last_known_value if show_zero else None

        self._last_known_value = energygenerated
        return energygenerated

    def _cumulative_guard_accepts(self, value: float) -> bool:
        """Return True if a lifetime cumulative reading may be published.

        The cloud sometimes returns a far too low cumulative value (e.g. 0 or 0.3
        kWh) for a single report. TOTAL_INCREASING treats any decrease as a meter
        reset and counts the whole lifetime total again when the real value
        returns (#404). Readings below the last accepted value are rejected; a
        decrease that persists for CUMULATIVE_REGRESSION_ACCEPT_AFTER is accepted
        as a genuine reset. Increases larger than the daily sanity threshold per
        elapsed day (at least one day) are rejected as spikes.
        """
        now = dt_util.utcnow()
        last = self._last_valid_cumulative
        if last is None:
            self._accept_cumulative(value, now)
            return True

        if value < last:
            if self._regression_since is None:
                self._regression_since = now
                _LOGGER.warning(
                    "%s value %s is lower than last accepted value %s kWh, ignoring",
                    self._nameValue,
                    value,
                    last,
                )
            if now - self._regression_since < CUMULATIVE_REGRESSION_ACCEPT_AFTER:
                return False
            _LOGGER.warning(
                "%s value %s has stayed below %s kWh since %s, accepting as reset",
                self._nameValue,
                value,
                last,
                self._regression_since,
            )
            self._accept_cumulative(value, now)
            return True

        if (
            self._max_daily_increase is not None
            and self._last_valid_cumulative_at is not None
        ):
            elapsed_days = max(
                (now - self._last_valid_cumulative_at).total_seconds() / 86400, 1.0
            )
            limit = self._max_daily_increase * elapsed_days
            if value - last > limit:
                _LOGGER.warning(
                    "%s increase from %s to %s kWh exceeds %s kWh, ignoring",
                    self._nameValue,
                    last,
                    value,
                    round(limit, 3),
                )
                return False

        self._accept_cumulative(value, now)
        return True

    def _accept_cumulative(self, value: float, now: datetime) -> None:
        self._last_valid_cumulative = value
        self._last_valid_cumulative_at = now
        self._regression_since = None

    @property
    def extra_restore_state_data(self) -> CumulativeGuardData | None:
        if self._keyValue != "cumulative" or self._last_valid_cumulative is None:
            return None
        return CumulativeGuardData(
            self._last_valid_cumulative, self._last_valid_cumulative_at
        )

    async def async_added_to_hass(self) -> None:
        await super().async_added_to_hass()
        if self._keyValue != "cumulative":
            return
        extra = await self.async_get_last_extra_data()
        restored = CumulativeGuardData.from_dict(extra.as_dict()) if extra else None
        if restored is not None and self._last_valid_cumulative is None:
            self._last_valid_cumulative = restored.last_valid
            self._last_valid_cumulative_at = restored.last_valid_at
            self._last_known_value = restored.last_valid
        elif self._last_valid_cumulative is None:
            # Fallback for initial upgrade from releases prior to CumulativeGuardData
            prev_state = await self.async_get_last_state()
            if prev_state and prev_state.state not in (
                STATE_UNKNOWN,
                STATE_UNAVAILABLE,
            ):
                try:
                    self._last_valid_cumulative = float(prev_state.state)
                    self._last_valid_cumulative_at = prev_state.last_updated
                    self._last_known_value = self._last_valid_cumulative
                except (ValueError, TypeError):
                    pass


class FoxESSEnergyThroughput(_FixedRawDataSensor):
    """Sensor entity for cumulative battery energy throughput in kWh."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR
    _name_value = "Energy Throughput"
    _unique_value = "energy-throughput"
    _key_value = "energyThroughput"
    _requires_online = False

    def _transform(self, value: float) -> float:
        """Round to 3 decimal places; clamp negative values to zero."""
        return round(value, 3) if value > 0 else 0


class _ReportSensor(FoxESSEntity):
    """Base class for sensors that read a single keyed value from coordinator.data['report']."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR
    _round: bool = False

    # These should be overridden in the subclasses.
    _name_value: str
    _unique_value: str
    _key_value: str

    def __init__(self, coordinator, name, deviceID):
        """Initialize the report sensor entity."""
        super().__init__(coordinator=coordinator)
        self._none_reported = False
        _LOGGER.debug("Initiating Entity - %s", self._name_value)
        self._attr_name = f"{name} - {self._name_value}"
        self._attr_unique_id = f"{deviceID}{self._unique_value}"

    @property
    def native_value(self) -> float | None:
        """Return value from report data."""
        if self._key_value not in self.coordinator.data["report"]:
            if not self._none_reported:
                _LOGGER.debug("%s None", self._key_value)
                self._none_reported = True
            return None
        value = self.coordinator.data["report"][self._key_value]
        return round(value, 3) if self._round else value


class FoxESSEnergyGridConsumption(_ReportSensor):
    """Sensor entity for today's grid consumption energy in kWh."""

    _name_value = "Grid Consumption"
    _unique_value = "grid-consumption"
    _key_value = "gridConsumption"


class FoxESSEnergyFeedin(_ReportSensor):
    """Sensor entity for today's feed-in energy in kWh."""

    _name_value = "FeedIn"
    _unique_value = "feedIn"
    _key_value = "feedin"


class FoxESSEnergyBatCharge(_ReportSensor):
    """Sensor entity for today's battery charge energy in kWh."""

    _name_value = "Bat Charge"
    _unique_value = "bat-charge"
    _key_value = "chargeEnergyToTal"


class FoxESSMaxBatChargeCurrent(_FixedRawDataSensor):
    """Sensor entity for maximum battery charge current in amperes."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.CURRENT
    _attr_native_unit_of_measurement = UnitOfElectricCurrent.AMPERE
    _name_value = "Max Bat Charge Current"
    _unique_value = "max-bat-charge-charge"
    _key_value = "maxChargeCurrent"
    _requires_online = False


class FoxESSMaxBatDischargeCurrent(_FixedRawDataSensor):
    """Sensor entity for maximum battery discharge current in amperes."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.CURRENT
    _attr_native_unit_of_measurement = UnitOfElectricCurrent.AMPERE
    _name_value = "Max Bat Discharge Current"
    _unique_value = "max-bat-discharge-charge"
    _key_value = "maxDischargeCurrent"
    _requires_online = False


class FoxESSEnergyBatDischarge(_ReportSensor):
    """Sensor entity for today's battery discharge energy in kWh."""

    _name_value = "Bat Discharge"
    _unique_value = "bat-discharge"
    _key_value = "dischargeEnergyToTal"


class FoxESSEnergyLoad(_ReportSensor):
    """Sensor entity for today's load energy in kWh."""

    _name_value = "Load"
    _unique_value = "load"
    _key_value = "loads"
    _round = True


class FoxESSPVEnergyTotal(FoxESSEntity):
    """Sensor entity for today's total PV energy in kWh."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(self, coordinator, name, deviceID):
        """Initialize the PV energy total sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - PV Energy Total")
        self._attr_name = name + " - PVEnergyTotal"
        self._attr_unique_id = deviceID + "PVEnergyTotal"
        self._last_known_value = None

    @property
    def native_value(self) -> float | None:
        """Return today's PV energy, or the last known value when show_unknown_zero is on."""
        show_zero = self._show_unknown_zero
        val = self.coordinator.data.get("report", {}).get("PVEnergyTotal")
        if val is None:
            return self._last_known_value if show_zero else None
        self._last_known_value = round(float(val), 3)
        return self._last_known_value


class FoxESSInverter(FoxESSEntity):
    """Sensor entity for inverter online/alarm/offline status."""

    _attr_icon = "mdi:solar-power"

    def __init__(self, coordinator, name, deviceID):
        """Initialize the inverter status sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Inverter")
        self._attr_name = name + " - Inverter"
        self._attr_unique_id = deviceID + "Inverter"

    @property
    def native_value(self) -> str | None:
        """Return the inverter status: on-line, in-alarm, or off-line."""
        data = self.coordinator.data or {}
        addressbook = data.get("addressbook", {}) if isinstance(data, dict) else {}
        status = addressbook.get("status")
        try:
            status_int = int(status) if status is not None else None
        except (ValueError, TypeError):
            status_int = None

        if status_int in _INVERTER_STATUS:
            return _INVERTER_STATUS[status_int]
        if data.get("online"):
            _LOGGER.debug("addressbook status None or unknown: %s", status)
        return None

    @property
    def extra_state_attributes(self):
        """Return device detail attributes from the address book."""
        data = self.coordinator.data or {}
        addressbook = data.get("addressbook", {}) if isinstance(data, dict) else {}
        if not addressbook or ATTR_DEVICE_SN not in addressbook:
            _LOGGER.debug("addressbook device detail not yet available")
            return None
        return {
            ATTR_DEVICE_SN: addressbook.get(ATTR_DEVICE_SN),
            ATTR_PLANTNAME: addressbook.get(ATTR_PLANTNAME),
            ATTR_MODULESN: addressbook.get(ATTR_MODULESN),
            ATTR_DEVICE_TYPE: addressbook.get(ATTR_DEVICE_TYPE),
            ATTR_MASTER: addressbook.get(ATTR_MASTER),
            ATTR_MANAGER: addressbook.get(ATTR_MANAGER),
            ATTR_SLAVE: addressbook.get(ATTR_SLAVE),
            ATTR_BATTERYLIST: addressbook.get(ATTR_BATTERYLIST),
            ATTR_LASTCLOUDSYNC: datetime.now(),
        }


_INVERTER_STATUS = {1: "on-line", 2: "in-alarm", 3: "off-line"}

_RUNNING_STATES = {
    "160": "self-test",
    "161": "waiting",
    "162": "checking",
    "163": "on-grid",
    "164": "off-grid",
    "165": "fault",
    "166": "permanent-fault",
    "167": "standby",
    "168": "upgrading",
    "169": "fct",
    "170": "illegal",
}


class FoxESSRunningState(_RawDataSensor):
    """Sensor entity for inverter running state with descriptive code labels."""

    _attr_icon = "mdi:state-machine"

    @property
    def native_value(self) -> str | None:
        """Return the running state code with its descriptive label."""
        raw = self.coordinator.data["raw"]
        if not raw:
            return None
        if self._keyValue not in raw:
            if not self._none_reported:
                _LOGGER.debug("%s None", self._keyValue)
                self._none_reported = True
            return None
        res = raw[self._keyValue]
        if res not in _RUNNING_STATES:
            _LOGGER.debug("runcode %s", res)
        return f"{res}: {_RUNNING_STATES.get(res, 'unknown code')}"


class FoxESSEnergySolar(FoxESSEntity):
    """Sensor entity for estimated solar energy production in kWh, derived from report totals."""

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(self, coordinator, name, deviceID, max_value=None):
        """Initialize the solar energy sensor entity."""
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Solar")
        self._attr_name = name + " - Solar"
        self._attr_unique_id = deviceID + "solar"
        self._max_value = max_value
        self._last_day = None
        self._max_today = 0.0

    @property
    def native_value(self) -> float | None:
        """Return estimated solar energy in kWh, derived from report totals."""
        today = dt_util.now().date()
        if self._last_day != today:
            self._last_day = today
            self._max_today = 0.0

        # The report is cached and only refetched every 15 (or 60) minutes, so
        # just after midnight it still holds yesterday's totals. Using them
        # would seed the ratchet with yesterday's value and pin the sensor
        # there for the whole day.
        report_date = self.coordinator.data.get("report_date")
        if report_date is not None and report_date != today:
            return round(self._max_today, 3)

        report = self.coordinator.data["report"]
        loads = _get_float(report, "loads")
        charge = _get_float(report, "chargeEnergyToTal")
        feedIn = _get_float(report, "feedin")
        gridConsumption = _get_float(report, "gridConsumption")
        discharge = _get_float(report, "dischargeEnergyToTal")

        energysolar = round((loads + charge + feedIn - gridConsumption - discharge), 3)
        energysolar = max(energysolar, 0)

        # Sanity check: ignore spikes exceeding max_value
        if self._max_value is not None and energysolar > self._max_value:
            _LOGGER.warning(
                "%s value %s exceeds sanity check threshold %s kWh, ignoring",
                self._attr_name,
                energysolar,
                self._max_value,
            )
            return round(self._max_today, 3) if self._max_today > 0 else None

        # Monotonic ratchet: prevent evening drops from creating negative stats deltas
        if energysolar > self._max_today:
            self._max_today = energysolar

        return round(self._max_today, 3)


class FoxESSSolarPower(FoxESSEntity):
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
        raw = self.coordinator.data["raw"]
        loads = _get_float(raw, "loadsPower")
        charge = _get_float(raw, "batChargePower")
        feedIn = _get_float(raw, "feedinPower")
        gridConsumption = _get_float(raw, "gridConsumptionPower")
        discharge = _get_float(raw, "batDischargePower")

        # check if what was returned (that some time was negative) is <0, so fix it
        total = loads + charge + feedIn - gridConsumption - discharge
        return round(max(total, 0), 3)


class FoxESSNewSolarPower(FoxESSEntity):
    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.POWER
    _attr_native_unit_of_measurement = UnitOfPower.KILO_WATT

    def __init__(self, coordinator, name, deviceID):
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - New Solar Power")
        self._attr_name = name + " - New Solar Power"
        self._attr_unique_id = deviceID + "new-solar-power"

    @property
    def native_value(self) -> float | None:
        if not self.coordinator.data["online"] or not self.coordinator.data["raw"]:
            return None
        raw = self.coordinator.data["raw"]
        loads = _get_float(raw, "loadsPower")
        charge = _get_float(raw, "batChargePower")
        feedIn = _get_float(raw, "feedinPower")
        gridConsumption = _get_float(raw, "gridConsumptionPower")
        discharge = _get_float(raw, "batDischargePower")
        secondInverter = _get_float(raw, "meterPower2")
        inverterOutput = _get_float(raw, "generationPower")
        pv = _get_float(raw, "pvPower")

        _LOGGER.debug("New Solar Power:\n")
        _LOGGER.debug("  loads:           %.3f", loads)
        _LOGGER.debug("  charge:          %.3f", charge)
        _LOGGER.debug("  feedIn:          %.3f", feedIn)
        _LOGGER.debug("  gridConsumption: %.3f", gridConsumption)
        _LOGGER.debug("  discharge:       %.3f", discharge)
        _LOGGER.debug("  secondInverter:  %.3f", secondInverter)
        _LOGGER.debug("  inverterOutput:  %.3f", inverterOutput)
        _LOGGER.debug("  pv:              %.3f", pv)

        # The second inverter always reports a negative value indicating that it's generating, 0 or
        # sometimes a tiny positive number.
        secondInverter = -secondInverter
        # The second inverter can consume power when not generating. For now, we set it to 0 in
        # these cases, but ideally we'd create a new category called inverter loss and put it there
        # or add it directly to the load.
        secondInverter = max(0, secondInverter)

        if inverterOutput >= 0:
            if pv + discharge > 0:
                pvRatio = pv / (pv + discharge)
                return round(pvRatio * inverterOutput + secondInverter + charge, 3)
            return 0

        # check if what was returned (that some time was negative) is <0, so fix it
        total = loads + charge + feedIn - gridConsumption - discharge
        if total < 0:
            total = 0
        return round(total, 3)


class FoxESSNewBatDischargePower(FoxESSEntity):
    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.POWER
    _attr_native_unit_of_measurement = UnitOfPower.KILO_WATT

    def __init__(self, coordinator, name, deviceID):
        super().__init__(coordinator=coordinator)
        _LOGGER.debug(f"Initiating Entity - New Bat Discharge Power")
        self._attr_name = f"{name} - New Bat Discharge Power"
        self._attr_unique_id = f"{deviceID}new-bat-discharge-power"

    @property
    def native_value(self) -> float | None:
        if not self.coordinator.data["online"] or not self.coordinator.data["raw"]:
            return None
        raw = self.coordinator.data["raw"]
        discharge = _get_float(raw, "batDischargePower")
        inverterOutput = _get_float(raw, "generationPower")
        pv = _get_float(raw, "pvPower")

        _LOGGER.debug("New Discharge Power:\n")
        _LOGGER.debug("  discharge:       %.3f", discharge)
        _LOGGER.debug("  inverterOutput:  %.3f", inverterOutput)
        _LOGGER.debug("  pv:              %.3f", pv)

        if inverterOutput >= 0:
            if pv + discharge > 0:
                dischargeRatio = discharge / (pv + discharge)
                return round(dischargeRatio * inverterOutput, 3)
            return 0
        else:
            # Battery cannot be discharging as there is power feeding into the inverter either from
            # the second inverter or the grid.
            return 0


class FoxESSBatSoC(_RawDataSensor):
    """Sensor entity for battery state of charge percentage."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.BATTERY
    _attr_native_unit_of_measurement = "%"

    @property
    def icon(self):
        """Return a battery icon for the current charge level."""
        return icon_for_battery_level(battery_level=self.native_value, charging=None)


class _BatterySettingsSensor(FoxESSEntity):
    """Base class for fixed-name sensors reading from coordinator.data['battery']."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.BATTERY
    _attr_native_unit_of_measurement = "%"

    # These should be overridden in the subclasses.
    _name_value: str
    _unique_value: str
    _key_value: str

    def __init__(self, coordinator, name, deviceID):
        """Initialize the sensor entity."""
        super().__init__(coordinator=coordinator)
        self._none_reported = False
        _LOGGER.debug("Initiating Entity - %s", self._name_value)
        self._attr_name = f"{name} - {self._name_value}"
        self._attr_unique_id = f"{deviceID}{self._unique_value}"

    @property
    def native_value(self) -> float | None:
        """Return value from battery settings data."""
        if self.coordinator.data["online"] and self.coordinator.data["battery"]:
            if self._key_value in self.coordinator.data["battery"]:
                return self.coordinator.data["battery"][self._key_value]
            if not self._none_reported:
                _LOGGER.debug("%s None", self._key_value)
                self._none_reported = True
        return None

    @property
    def icon(self):
        """Return a battery icon for the current level."""
        return icon_for_battery_level(battery_level=self.native_value, charging=None)


class FoxESSBatMinSoC(_BatterySettingsSensor):
    """Sensor entity for minimum allowed battery state of charge percentage."""

    _name_value = "Bat MinSoC"
    _unique_value = "bat-minsoc"
    _key_value = "minSoc"


class FoxESSBatMinSoConGrid(_BatterySettingsSensor):
    """Sensor entity for minimum battery state of charge when on grid."""

    _name_value = "Bat minSocOnGrid"
    _unique_value = "bat-minSocOnGrid"
    _key_value = "minSocOnGrid"


class FoxESSTemp(_RawDataSensor):
    """Sensor entity for temperature measurements in degrees Celsius."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = SensorDeviceClass.TEMPERATURE
    _attr_native_unit_of_measurement = UnitOfTemperature.CELSIUS


class FoxESSResidualEnergy(_FixedRawDataSensor):
    """Sensor entity for residual battery energy in kWh."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_device_class = getattr(SensorDeviceClass, "ENERGY_STORAGE", None)
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR
    _name_value = "Residual Energy"
    _unique_value = "residual-energy"
    _key_value = "ResidualEnergy"

    def _transform(self, value) -> float | None:
        """Correct the API scale bug (values > 100 are in units of 10 Wh) and clamp at zero."""
        if value is None:
            return None
        try:
            value = float(value)
        except (ValueError, TypeError):
            return None
        if value > 100.0:
            value = value / 100.0
        elif value < 0:
            value = 0.0
        return round(value, 2)


class FoxESSResponseTime(_FixedRawDataSensor):
    """Sensor entity for FoxESS API response time in milliseconds."""

    _attr_state_class: SensorStateClass = SensorStateClass.MEASUREMENT
    _attr_native_unit_of_measurement = "mS"
    _name_value = "Response Time"
    _unique_value = "response-time"
    _key_value = "ResponseTime"
    _requires_online = False
