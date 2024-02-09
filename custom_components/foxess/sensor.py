from __future__ import annotations

from collections import namedtuple
from datetime import timedelta
from datetime import datetime
import time
import logging
import json
import hashlib
import asyncio
import voluptuous as vol

from homeassistant.components.rest.data import RestData
from homeassistant.exceptions import ConfigEntryNotReady
from homeassistant.components.sensor import (
    SensorDeviceClass,
    SensorStateClass,
    PLATFORM_SCHEMA,
    SensorEntity,
)


from homeassistant.const import (
    ATTR_DATE,
    ATTR_TEMPERATURE,
    ATTR_TIME,
    ATTR_VOLTAGE,
    CONF_PASSWORD,
    CONF_USERNAME,
    CONF_NAME,
    UnitOfEnergy,
    UnitOfPower,
    UnitOfTemperature,
    UnitOfEnergy,
    UnitOfElectricPotential,
    UnitOfElectricCurrent,
    UnitOfFrequency,
    POWER_VOLT_AMPERE_REACTIVE,
)
from homeassistant.helpers.update_coordinator import (
    CoordinatorEntity,
    DataUpdateCoordinator,
    UpdateFailed,
)
from homeassistant.util.ssl import SSLCipherList
from homeassistant.helpers.icon import icon_for_battery_level
from homeassistant.core import callback
import homeassistant.helpers.config_validation as cv

from random_user_agent.user_agent import UserAgent
from random_user_agent.params import SoftwareName, OperatingSystem

software_names = [SoftwareName.CHROME.value]
operating_systems = [OperatingSystem.WINDOWS.value, OperatingSystem.LINUX.value]
user_agent_rotator = UserAgent(software_names=software_names, operating_systems=operating_systems, limit=100)


_LOGGER = logging.getLogger(__name__)
_ENDPOINT_OA_DOMAIN = "https://www.foxesscloud.com"
_ENDPOINT_OA_BATTERY_SETTINGS = "/op/v0/device/battery/soc/get?sn="
_ENDPOINT_OA_REPORT = "/op/v0/device/report/query"
_ENDPOINT_OA_DEVICE_DETAIL = "/op/v0/device/detail?sn="
_ENDPOINT_OA_DEVICE_VARIABLES = "/op/v0/device/real/query"
_ENDPOINT_OA_DAILY_GENERATION = "/op/v0/device/generation?sn="

METHOD_POST = "POST"
METHOD_GET = "GET"
DEFAULT_ENCODING = "UTF-8"
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
DEFAULT_TIMEOUT = 75 # increase the size of inherited timeout, the API is a bit slow

ATTR_DEVICE_SN = "deviceSN"
ATTR_PLANTNAME = "plantName"
ATTR_MODULESN = "moduleSN"
ATTR_DEVICE_TYPE = "deviceType"
ATTR_STATUS = "status"
ATTR_COUNTRY = "country"
ATTR_COUNTRYCODE = "countryCode"
ATTR_CITY = "city"
ATTR_ADDRESS = "address"
ATTR_FEEDINDATE = "feedinDate"
ATTR_LASTCLOUDSYNC = "lastCloudSync"

BATTERY_LEVELS = {"High": 80, "Medium": 50, "Low": 25, "Empty": 10}

CONF_APIKEY = "apiKey"
CONF_DEVICESN = "deviceSN"
CONF_DEVICEID = "deviceID"
CONF_SYSTEM_ID = "system_id"
RETRY_NEXT_SLOT = -1

DEFAULT_NAME = "FoxESS"
DEFAULT_VERIFY_SSL = False # True

SCAN_MINUTES = 1 # number of minutes betwen API requests
SCAN_INTERVAL = timedelta(minutes=SCAN_MINUTES)

PLATFORM_SCHEMA = PLATFORM_SCHEMA.extend(
    {
        vol.Optional(CONF_USERNAME): cv.string,
        vol.Optional(CONF_PASSWORD): cv.string,
        vol.Required(CONF_APIKEY): cv.string,
        vol.Required(CONF_DEVICESN): cv.string,
        vol.Required(CONF_DEVICEID): cv.string,
        vol.Optional(CONF_NAME, default=DEFAULT_NAME): cv.string,
    }
)

token = None

async def async_setup_platform(hass, config, async_add_entities, discovery_info=None):
    """Set up the FoxESS sensor."""
    global LastHour, TimeSlice, last_api
    name = config.get(CONF_NAME)
    deviceID = config.get(CONF_DEVICEID)
    deviceSN = config.get(CONF_DEVICESN)
    apiKey = config.get(CONF_APIKEY)
    _LOGGER.debug("API Key:" + apiKey)
    _LOGGER.debug("Device SN:" + deviceSN)
    _LOGGER.debug("Device ID:" + deviceID)
    _LOGGER.debug( f"FoxESS Scan Interval: {SCAN_MINUTES} minutes" )
    TimeSlice = {}
    TimeSlice[deviceSN] = RETRY_NEXT_SLOT
    last_api = 0
    LastHour = 0
    allData = {
        "report":{},
        "reportDailyGeneration": {},
        "raw":{},
        "battery":{},
        "addressbook":{},
        "online":False
    }
    allData['addressbook']['hasBattery'] = False

    async def async_update_data():
        _LOGGER.debug("Updating data from https://www.foxesscloud.com/")
        global token, TimeSlice, LastHour
        hournow = datetime.now().strftime("%_H") # update hour now
        _LOGGER.debug(f"Time now: {hournow}, last {LastHour}")
        TSlice = TimeSlice[deviceSN] + 1 # get the time slice for the current device and increment it
        TimeSlice[deviceSN] = TSlice
        if (TSlice % 5 == 0):
            _LOGGER.debug(f"TimeSlice Main Poll, interval: {deviceSN}, {TimeSlice[deviceSN]}")

            # try the openapi see if we get a response
            if TSlice==0: # get device detail at startup, then every 30 minutes to save api calls
                addfail = await getOADeviceDetail(hass, allData, deviceSN, apiKey)
            else:
                addfail = 0

            if addfail == 0:
                if allData["addressbook"]["status"] is not None:
                    statetest = int(allData["addressbook"]["status"])
                else:
                    statetest = 0
                _LOGGER.debug(f" Statetest {statetest}")

                if statetest in [1,2,3]:
                    allData["online"] = True
                    if TSlice==0:
                        # do this at startup and then every 30 minutes
                        addfail = await getOABatterySettings(hass, allData, deviceSN, apiKey) # read in battery settings where fitted, poll every 15 mins
                    # main real time data fetch, followed by reports
                    getError = await getRaw(hass, allData, apiKey, deviceSN, deviceID)
                    if getError == False:
                        if TSlice==0 or TSlice==15: # do this at startup, every 15 minutes and on the hour change
                            getError = await getReport(hass, allData, apiKey, deviceSN, deviceID)
                            if getError == False:
                                if TSlice==0:
                                    # do this at startup, then every 30 minutes
                                    getError = await getReportDailyGeneration(hass, allData, apiKey, deviceSN, deviceID)
                                    if getError == True:
                                        allData["online"] = False
                                        TSlice=RETRY_NEXT_SLOT # failed to get data so try again in 1 minute
                                        _LOGGER.debug("getReportDailyGeneration False")
                            else:
                                allData["online"] = False
                                TSlice=RETRY_NEXT_SLOT # failed to get data so try again in 1 minute
                                _LOGGER.debug("getReport False")

                    else:
                        allData["online"] = False
                        TSlice=RETRY_NEXT_SLOT # failed to get data so try again in 1 minute
                        _LOGGER.debug("getRaw False")

                if allData["online"] == False:
                    _LOGGER.warning(f"{name} has Cloud timeout or the Inverter is off-line, connection will be retried in 1 minute")
            else:
                _LOGGER.warning(f"{name} has Cloud timeout or the Inverter is off-line, connection will be retried in 1 minute.")
                TSlice=RETRY_NEXT_SLOT # failed to get data so try again in a minute

        # actions here are every minute
        if TSlice==30:
            TSlice=RETRY_NEXT_SLOT # reset timeslice and start again from 0
        _LOGGER.debug(f"Auxilliary TimeSlice {deviceSN}, {TSlice}")

        if LastHour != hournow:
            LastHour = hournow # update the hour the last poll was run

        TimeSlice[deviceSN] = TSlice

        _LOGGER.debug(allData)

        return allData


    coordinator = DataUpdateCoordinator(
        hass,
        _LOGGER,
        # Name of the data. For logging purposes.
        name=DEFAULT_NAME,
        update_method=async_update_data,
        # Polling interval. Will only be polled if there are subscribers.
        update_interval=SCAN_INTERVAL,
    )

    await coordinator.async_refresh()

    if not coordinator.last_update_success:
        _LOGGER.error(
            "FoxESS Cloud initialisation failed, Fatal Error - correct error and restart Home Assistant")
        return False

    async_add_entities([
        FoxESSCurrent(coordinator, name, deviceID, prefix="PV1", value_field="pv1Current"),
        FoxESSPower(coordinator, name, deviceID, prefix="PV1", value_field="pv1Power"),
        FoxESSVolt(coordinator, name, deviceID, prefix="PV1", value_field="pv1Volt"),
        FoxESSCurrent(coordinator, name, deviceID, prefix="PV2", value_field="pv2Current"),
        FoxESSPower(coordinator, name, deviceID, prefix="PV2", value_field="pv2Power"),
        FoxESSVolt(coordinator, name, deviceID, prefix="PV2", value_field="pv2Volt"),
        FoxESSCurrent(coordinator, name, deviceID, prefix="PV3", value_field="pv3Current"),
        FoxESSPower(coordinator, name, deviceID, prefix="PV3", value_field="pv3Power"),
        FoxESSVolt(coordinator, name, deviceID, prefix="PV3", value_field="pv3Volt"),
        FoxESSCurrent(coordinator, name, deviceID, prefix="PV4", value_field="pv4Current"),
        FoxESSPower(coordinator, name, deviceID, prefix="PV4", value_field="pv4Power"),
        FoxESSVolt(coordinator, name, deviceID, prefix="PV4", value_field="pv4Volt"),
        FoxESSPower(coordinator, name, deviceID, prefix="PV", value_field="pvPower"),
        FoxESSCurrent(coordinator, name, deviceID, prefix="R"),
        FoxESSFrequency(coordinator, name, deviceID, prefix="R"),
        FoxESSPower(coordinator, name, deviceID, prefix="R"),
        FoxESSPower(coordinator, name, deviceID, prefix="Meter2", value_field="meterPower2"),
        FoxESSVolt(coordinator, name, deviceID, prefix="R"),
        FoxESSCurrent(coordinator, name, deviceID, prefix="S"),
        FoxESSFrequency(coordinator, name, deviceID, prefix="S"),
        FoxESSPower(coordinator, name, deviceID, prefix="S"),
        FoxESSVolt(coordinator, name, deviceID, prefix="S"),
        FoxESSCurrent(coordinator, name, deviceID, prefix="T"),
        FoxESSFrequency(coordinator, name, deviceID, prefix="T"),
        FoxESSPower(coordinator, name, deviceID, prefix="T"),
        FoxESSVolt(coordinator, name, deviceID, prefix="T"),
        FoxESSReactivePower(coordinator, name, deviceID),
        FoxESSTemperature(coordinator, name, deviceID, prefix="bat"),
        FoxESSTemperature(coordinator, name, deviceID, prefix="ambient", value_field="ambientTemperation"),
        FoxESSTemperature(coordinator, name, deviceID, prefix="boost", value_field="boostTemperation"),
        FoxESSTemperature(coordinator, name, deviceID, prefix="inv", value_field="invTemperation"),
        FoxESSBatSoC(coordinator, name, deviceID),
        FoxESSBatMinSoC(coordinator, name, deviceID),
        FoxESSBatMinSoConGrid(coordinator, name, deviceID),
        FoxESSSolarPower(coordinator, name, deviceID),
        FoxESSEnergySolar(coordinator, name, deviceID),
        FoxESSInverter(coordinator, name, deviceID),
        FoxESSPower(coordinator, name, deviceID, prefix="Generation", value_field="generationPower",
             # This unique name is specified directly to force the "-" at the beginning which is
             # different to every other sensor's unique name.
            unique_name="-generation-power",
        ),
        FoxESSPower(coordinator, name, deviceID, prefix="Grid Consumption", value_field="gridConsumptionPower"),
        FoxESSPower(coordinator, name, deviceID, prefix="FeedIn", unique_name="feedIn-power", value_field="feedinPower"),
        FoxESSPower(coordinator, name, deviceID, prefix="Bat Discharge", value_field="batDischargePower"),
        FoxESSPower(coordinator, name, deviceID, prefix="Bat Charge", value_field="batChargePower"),
        FoxESSPower(coordinator, name, deviceID, prefix="Load", value_field="loadsPower"),
        FoxESSEnergy(coordinator, name, deviceID, entity_type="Energy Generated", report_field="reportDailyGeneration", value_field="value"),
        FoxESSEnergy(coordinator, name, deviceID, entity_type="Grid Consumption", report_field="report", value_field="gridConsumption"),
        FoxESSEnergy(coordinator, name, deviceID, entity_type="FeedIn", unique_name="feedIn", report_field="report", value_field="feedin"),
        FoxESSEnergy(coordinator, name, deviceID, entity_type="Bat Charge", report_field="report", value_field="chargeEnergyToTal"),
        FoxESSEnergy(coordinator, name, deviceID, entity_type="Bat Discharge", report_field="report", value_field="dischargeEnergyToTal"),
        FoxESSEnergyLoad(coordinator, name, deviceID),
        FoxESSResidualEnergy(coordinator, name, deviceID)
    ])


class GetAuth:

    def get_signature(self, token, path, lang='en'):
        """
        This function is used to generate a signature consisting of URL, token, and timestamp, and return a dictionary containing the signature and other information.
            :param token: your key
            :param path:  your request path
            :param lang: language, default is English.
            :return: with authentication header
        """
        timestamp = round(time.time() * 1000)
        signature = fr'{path}\r\n{token}\r\n{timestamp}'
        # or use user_agent_rotator.get_random_user_agent() for user-agent
        result = {
            'token': token,
            'lang': lang,
            'timestamp': str(timestamp),
            'Content-Type': 'application/json',
            'signature': self.md5c(text=signature),
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) '
                          'Chrome/117.0.0.0 Safari/537.36',
            'Connection': 'close'
        }
        return result

    @staticmethod
    def md5c(text="", _type="lower"):
        res = hashlib.md5(text.encode(encoding='UTF-8')).hexdigest()
        if _type.__eq__("lower"):
            return res
        else:
            return res.upper()


async def waitforAPI():
    global last_api
    # wait for openAPI, there is a minimum of 1 second allowed between OpenAPI query calls
    # check if last_api call was less than a second ago and if so delay the balance of 1 second
    now = time.time()
    last = last_api
    diff = now - last if last != 0 else 1
    diff = round( (diff+0.2) ,2)
    if diff < 1:
        await asyncio.sleep(diff)
        _LOGGER.debug(f"API enforced delay, wait: {diff}")
    now = time.time()
    last_api = now
    return False

async def getOADeviceDetail(hass, allData, deviceSN, apiKey):

    await waitforAPI()

    path = "/op/v0/device/detail"
    headerData = GetAuth().get_signature(token=apiKey, path=path)

    path = _ENDPOINT_OA_DOMAIN + _ENDPOINT_OA_DEVICE_DETAIL
    _LOGGER.debug("OADevice Detail fetch " + path + deviceSN)

    restOADeviceDetail = RestData(hass, METHOD_GET, path + deviceSN, DEFAULT_ENCODING,  None, headerData, None, None, DEFAULT_VERIFY_SSL, SSLCipherList.PYTHON_DEFAULT, DEFAULT_TIMEOUT)
    await restOADeviceDetail.async_update()

    if restOADeviceDetail.data is None or restOADeviceDetail.data == '':
        _LOGGER.debug("Unable to get OA Device Detail from FoxESS Cloud")
        return True
    else:
        response = json.loads(restOADeviceDetail.data)
        if response["errno"] == 0 and response["msg"] == 'success' :
            _LOGGER.debug(f"OA Device Detail Good Response: {response['result']}")
            result = response['result']
            allData['addressbook'] = result
            # manually poke this in as on the old cloud it was called plantname, need to keep in line with old entity name
            plantName = result['stationName']
            allData['addressbook']['plantName'] = plantName
            testBattery = result['hasBattery']
            if testBattery:
                _LOGGER.debug(f"OA Device Detail System has Battery: {testBattery}")
            else:
                _LOGGER.debug(f"OA Device Detail System has No Battery: {testBattery}")
            return False
        else:
            _LOGGER.debug(f"OA Device Detail Bad Response: {response}")
            return True

async def getOABatterySettings(hass, allData, deviceSN, apiKey):

    await waitforAPI() # check for api delay

    path = "/op/v0/device/battery/soc/get"
    headerData = GetAuth().get_signature(token=apiKey, path=path)

    path = _ENDPOINT_OA_DOMAIN + _ENDPOINT_OA_BATTERY_SETTINGS
    if "hasBattery" not in allData["addressbook"]:
        hasBattery = False
    else:
        hasBattery = allData['addressbook']['hasBattery']

    if hasBattery:
        # only make this call if device detail reports battery fitted
        _LOGGER.debug("OABattery Settings fetch " + path + deviceSN)
        restOABatterySettings = RestData(hass, METHOD_GET, path + deviceSN, DEFAULT_ENCODING,  None, headerData, None, None, DEFAULT_VERIFY_SSL, SSLCipherList.PYTHON_DEFAULT, DEFAULT_TIMEOUT)
        await restOABatterySettings.async_update()

        if restOABatterySettings.data is None:
            _LOGGER.debug("Unable to get OA Battery Settings from FoxESS Cloud")
            return True
        else:
            response = json.loads(restOABatterySettings.data)
            if response["errno"] == 0 and response["msg"] == 'success' :
                _LOGGER.debug(f"OA Battery Settings Good Response: {response['result']}")
                result = response['result']
                minSoc = result['minSoc']
                minSocOnGrid = result['minSocOnGrid']
                allData["battery"]["minSoc"] = minSoc
                allData["battery"]["minSocOnGrid"] = minSocOnGrid
                _LOGGER.debug(f"OA Battery Settings read MinSoc: {minSoc}, MinSocOnGrid: {minSocOnGrid}")
                return False
            else:
                _LOGGER.debug(f"OA Battery Settings Bad Response: {response}")
                return True
    else:
        # device detail reports no battery fitted so reset these variables to show unknown
        allData["battery"]["minSoc"] = None
        allData["battery"]["minSocOnGrid"] = None
        return False


async def getReport(hass, allData, apiKey, deviceSN, deviceID):

    await waitforAPI() # check for api delay

    path = _ENDPOINT_OA_REPORT
    headerData = GetAuth().get_signature(token=apiKey, path=path)

    path = _ENDPOINT_OA_DOMAIN + _ENDPOINT_OA_REPORT
    _LOGGER.debug("OA Report fetch " + path )

    now = datetime.now()

    reportData = '{"sn":"'+deviceSN+'","year":'+now.strftime("%Y")+',"month":'+now.strftime("%_m")+',"dimension":"month","variables":["feedin","generation","gridConsumption","chargeEnergyToTal","dischargeEnergyToTal","loads"]}'
    _LOGGER.debug("getReport OA request:" + reportData)

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
        DEFAULT_TIMEOUT
    )

    await restOAReport.async_update()

    if restOAReport.data is None or restOAReport.data == '':
        _LOGGER.debug("Unable to get OA Report from FoxESS Cloud")
        return True
    else:
        # Openapi responded so process data
        response = json.loads(restOAReport.data)
        if response["errno"] == 0 and response["msg"] == 'success' :
            _LOGGER.debug(f"OA Report Data fetched OK: {response} "+ restOAReport.data[:350])
            result = json.loads(restOAReport.data)['result']
            today = int(now.strftime("%_d")) # need today as an integer to locate in the monthly report index
            for item in result:
                variableName = item['variable']
                # Daily reports break down the data hour by month for each day
                # so locate the current days index and use that as the sum
                index = 1
                cumulative_total = 0
                for dataItem in item['values']:
                    if today==index: # we're only interested in the total for today
                        if dataItem != None:
                            cumulative_total = dataItem
                        else:
                            _LOGGER.warn(f"Report month fetch, None received")
                        break
                    index+=1
                    #cumulative_total += dataItem
                allData['report'][variableName] = round(cumulative_total,3)
                _LOGGER.debug(f"OA Report Variable: {variableName}, Total: {cumulative_total}")
            return False
        else:
            _LOGGER.debug(f"OA Report Bad Response: {response} "+ restOAReport.data)
            return True


async def getReportDailyGeneration(hass, allData, apiKey, deviceSN, deviceID):

    await waitforAPI() # check for api delay

    now = datetime.now()
    path = "/op/v0/device/generation"
    headerData = GetAuth().get_signature(token=apiKey, path=path)

    path = _ENDPOINT_OA_DOMAIN + _ENDPOINT_OA_DAILY_GENERATION
    _LOGGER.debug("getReportDailyGeneration fetch " + path )

    generationData = '{"sn":"'+deviceSN+'","dimension":"day"}'

    _LOGGER.debug("getReportDailyGeneration OA request:" + generationData)

    restOAgen = RestData(
        hass,
        METHOD_GET,
        path + deviceSN,
        DEFAULT_ENCODING,
        None,
        headerData,
        None,
        generationData,
        DEFAULT_VERIFY_SSL,
        SSLCipherList.PYTHON_DEFAULT,
        DEFAULT_TIMEOUT
    )

    await restOAgen.async_update()

    if restOAgen.data is None or restOAgen.data == '':
        _LOGGER.debug("Unable to get OA Daily Generation Report from FoxESS Cloud")
        return True
    else:
        response = json.loads(restOAgen.data)
        if response["errno"] == 0 and response["msg"] == 'success' :
            _LOGGER.debug("OA Daily Generation Report Data fetched OK Response:"+ restOAgen.data[:500])

            parsed = json.loads(restOAgen.data)["result"]
            if "today" not in parsed:
                allData["reportDailyGeneration"]["value"] = 0
                _LOGGER.debug(f"OA Daily Generation Report data, today has no value: {parsed} set to 0")
            else:
                allData["reportDailyGeneration"]["value"] = parsed['today']
                _LOGGER.debug(f"OA Daily Generation Report data: {parsed} and todays value {parsed['today']} ")
            return False
        else:
            _LOGGER.debug(f"OA Daily Generation Report Bad Response: {response} "+ restOAgen.data)
            return True


async def getRaw(hass, allData, apiKey, deviceSN, deviceID):

    await waitforAPI() # check for api delay

    path = _ENDPOINT_OA_DEVICE_VARIABLES
    headerData = GetAuth().get_signature(token=apiKey, path=path)

    # "deviceSN" used for OpenAPI and it only fetches the real time data
    rawData =  '{"sn":"'+deviceSN+'","variables":["ambientTemperation", \
                                    "batChargePower","batCurrent","batDischargePower","batTemperature","batVolt", \
                                    "boostTemperation", "chargeTemperature", "dspTemperature", \
                                    "epsCurrentR","epsCurrentS","epsCurrentT","epsPower","epsPowerR","epsPowerS","epsPowerT","epsVoltR","epsVoltS","epsVoltT", \
                                    "feedinPower", "generationPower","gridConsumptionPower", \
                                    "input","invBatCurrent","invBatPower","invBatVolt","invTemperation", \
                                    "loadsPower","loadsPowerR","loadsPowerS","loadsPowerT", \
                                    "meterPower","meterPower2","meterPowerR","meterPowerS","meterPowerT","PowerFactor", \
                                    "pv1Current","pv1Power","pv1Volt","pv2Current","pv2Power","pv2Volt", \
                                    "pv3Current","pv3Power","pv3Volt","pv4Current","pv4Power","pv4Volt","pvPower", \
                                    "RCurrent","ReactivePower","RFreq","RPower","RVolt", \
                                    "SCurrent","SFreq","SoC","SPower","SVolt", \
                                    "TCurrent","TFreq","TPower","TVolt", \
                                    "ResidualEnergy", "todayYield"] }'

    _LOGGER.debug("getRaw OA request:" +rawData)

    path = _ENDPOINT_OA_DOMAIN + _ENDPOINT_OA_DEVICE_VARIABLES
    _LOGGER.debug("OADevice Variables fetch " + path )

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
        DEFAULT_TIMEOUT
    )

    await restOADeviceVariables.async_update()

    if restOADeviceVariables.data is None or restOADeviceVariables.data == '':
        _LOGGER.debug("Unable to get OA Device Variables from FoxESS Cloud")
        return True
    else:
        # Openapi responded correctly
        response = json.loads(restOADeviceVariables.data)
        if response["errno"] == 0 and response["msg"] == 'success' :
            test = json.loads(restOADeviceVariables.data)['result']
            result = test[0].get('datas')
            _LOGGER.debug(f"OA Device Variables Good Response: {result}")
            # allData['raw'] = {}
            for item in result: # json.loads(result): # restOADeviceVariables.data)['result']:
                variableName = item['variable']
                # If value exists
                if item.get('value') is not None:
                    variableValue = item['value']
                else:
                    variableValue = 0
                    _LOGGER.debug( f"Variable {variableName} no value, set to zero" )

                allData['raw'][variableName] = variableValue
                _LOGGER.debug( f"Variable: {variableName} being set to {allData['raw'][variableName]}" )
            return False
        else:
            _LOGGER.debug(f"OA Device Variables Bad Response: {response}")
            return True


class FoxESSSimpleSensor(CoordinatorEntity, SensorEntity):
    def __init__(
        self,
        coordinator,
        name,
        deviceID,
        device_class,
        sensor_state_class,
        unit_of_measurement,
        entity_type,
        unique_name=None,
        report_field=None,
        value_field=None
    ):
        """Creates a simple sensor that retrieves its data from the coordinator.

        Args:
            coordinator (DataUpdateCoordinator): Coordinator from which the sensor gets its data.
            name (str): Name given in the original configuration by the user.
            deviceID (str): DeviceID given in the original configuration by the user.
            device_class (SensorDeviceClass): Device class for the sensor.
            sensor_state_class (SensorStateClass): State class for the sensor.
            unit_of_measurement (any): Unit of measurement.
            entity_type (str): A description of the sensor. E.g. "Load", "Reactive Power".
            unique_name (str, optional): The unique name to provided to HA. If not provided then it
            will be generated from the entity type.
            report_field (str): Name of the report entry within the coordinator's data.
            value_field (str): Name of the value entry within the report field (within the
            coordinator's data).
        """
        _LOGGER.debug("Initiating Entity - %s", entity_type)
        super().__init__(coordinator=coordinator)
        self._attr_name = name+" - "+entity_type
        if not unique_name:
            unique_name = entity_type.lower().replace(" ", "-")
        self._attr_unique_id = deviceID+unique_name

        self.status = namedtuple(
            "status",
            [
                ATTR_DATE,
                ATTR_TIME,
            ],
        )
        self._attr_device_class = device_class
        self._attr_state_class = sensor_state_class
        self._attr_native_unit_of_measurement = unit_of_measurement
        self.report_field = report_field
        self.value_field = value_field

    @property
    def native_value(self) -> str | None:
        if self.coordinator.data["online"] and self.coordinator.data[self.report_field]:
            if self.value_field not in self.coordinator.data[self.report_field]:
                _LOGGER.debug("%s None", self.value_field)
            else:
                return self.coordinator.data[self.report_field][self.value_field]
        return None


class FoxESSRawSensor(FoxESSSimpleSensor):
    def __init__(
        self,
        coordinator,
        name,
        deviceID,
        device_class,
        unit_of_measurement,
        entity_type,
        unique_name=None,
        value_field=None
    ):
        """Creates a simple sensor that retrieves its data from the coordinator's raw report.

        Args:
            coordinator (DataUpdateCoordinator): Coordinator from which the sensor gets its data.
            name (str): Name given in the original configuration by the user.
            deviceID (str): DeviceID given in the original configuration by the user.
            device_class (SensorDeviceClass): Device class for the sensor.
            unit_of_measurement (any): Unit of measurement.
            entity_type (str): A description of the sensor. E.g. "Load", "Reactive Power".
            unique_name (str, optional): The unique name to provided to HA. If not provided then it
            will be generated from the entity type.
            value_field (str): Name of the value entry within the report field (within the
            coordinator's data).
        """
        super().__init__(
            coordinator=coordinator,
            name=name,
            deviceID=deviceID,
            device_class=device_class,
            sensor_state_class=SensorStateClass.MEASUREMENT,
            unit_of_measurement=unit_of_measurement,
            entity_type=entity_type,
            unique_name=unique_name,
            report_field="raw",
            value_field=value_field,
        )


class FoxESSCurrent(FoxESSRawSensor):
    def __init__(self, coordinator, name, deviceID, prefix, value_field=None):
        if value_field is None:
            value_field = prefix + "Current"
        super().__init__(
            coordinator=coordinator,
            name=name,
            deviceID=deviceID,
            device_class=SensorDeviceClass.CURRENT,
            unit_of_measurement=UnitOfElectricCurrent.AMPERE,
            entity_type=prefix + " Current",
            value_field=value_field
            )


class FoxESSPower(FoxESSRawSensor):
    def __init__(
        self, coordinator, name, deviceID, prefix, unique_name=None, value_field=None
    ):
        if value_field is None:
            value_field = prefix + "Power"
        super().__init__(
            coordinator=coordinator,
            name=name,
            deviceID=deviceID,
            device_class=SensorDeviceClass.POWER,
            unit_of_measurement=UnitOfPower.KILO_WATT,
            entity_type=prefix + " Power",
            unique_name=unique_name,
            value_field=value_field
            )


class FoxESSVolt(FoxESSRawSensor):
    def __init__(self, coordinator, name, deviceID, prefix, value_field=None):
        if value_field is None:
            value_field = prefix + "Volt"
        super().__init__(
            coordinator=coordinator,
            name=name,
            deviceID=deviceID,
            device_class=SensorDeviceClass.VOLTAGE,
            unit_of_measurement=UnitOfElectricPotential.VOLT,
            entity_type=prefix + " Volt",
            value_field=value_field
            )


class FoxESSFrequency(FoxESSRawSensor):
    def __init__(self, coordinator, name, deviceID, prefix):
        super().__init__(
            coordinator=coordinator,
            name=name,
            deviceID=deviceID,
            device_class=SensorDeviceClass.FREQUENCY,
            unit_of_measurement=UnitOfFrequency.HERTZ,
            entity_type=prefix + " Freq",
            value_field=prefix + "Freq"
            )

class FoxESSTemperature(FoxESSRawSensor):
    def __init__(self, coordinator, name, deviceID, prefix, value_field=None):
        if value_field is None:
            value_field = prefix + "Temperature"
        super().__init__(
            coordinator=coordinator,
            name=name,
            deviceID=deviceID,
            device_class=SensorDeviceClass.TEMPERATURE,
            unit_of_measurement=UnitOfTemperature.CELSIUS,
            entity_type=prefix + " Temperature",
            value_field=value_field
            )


class FoxESSEnergy(FoxESSSimpleSensor):
    def __init__(
        self,
        coordinator,
        name,
        deviceID,
        entity_type=None,
        unique_name=None,
        report_field=None,
        value_field=None,
    ):
        super().__init__(
            coordinator=coordinator,
            name=name,
            deviceID=deviceID,
            device_class=SensorDeviceClass.ENERGY,
            sensor_state_class=SensorStateClass.TOTAL_INCREASING,
            unit_of_measurement=UnitOfEnergy.WATT_HOUR,
            entity_type=entity_type,
            unique_name=unique_name,
            report_field=report_field,
            value_field=value_field,
        )

    @property
    def native_value(self) -> str | None:
        energy = super().native_value
        return energy if energy != 0 else None


class FoxESSReactivePower(FoxESSRawSensor):
    def __init__(self, coordinator, name, deviceID):
        super().__init__(
            coordinator=coordinator,
            name=name,
            deviceID=deviceID,
            device_class=SensorDeviceClass.REACTIVE_POWER,
            unit_of_measurement=POWER_VOLT_AMPERE_REACTIVE,
            entity_type="Reactive Power",
            value_field="ReactivePower")

    @property
    def native_value(self) -> float | None:
        reactive_power = super().native_value
        if reactive_power is not None:
            reactive_power *= 1000
        return reactive_power


class FoxESSEnergyLoad(FoxESSEnergy):
    def __init__(self, coordinator, name, deviceID):
        super().__init__(
            coordinator=coordinator,
            name=name,
            deviceID=deviceID,
            entity_type="Load",
            report_field="report",
            value_field="loads",
        )

    @property
    def native_value(self) -> str | None:
        energyload = super().native_value
        if energyload is not None:
            # was getting an error on round() when load was None, changed it to 0
            return round(energyload,3)
        return None


class FoxESSInverter(CoordinatorEntity, SensorEntity):

    def __init__(self, coordinator, name, deviceID):
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Inverter")
        self._attr_name = name+" - Inverter"
        self._attr_unique_id = deviceID+"Inverter"
        self._attr_icon = "mdi:solar-power"
        self.status = namedtuple(
            "status",
            [
                ATTR_DATE,
                ATTR_TIME,
                ATTR_DEVICE_SN,
                ATTR_PLANTNAME,
                ATTR_MODULESN,
                ATTR_DEVICE_TYPE,
                ATTR_STATUS,
                ATTR_COUNTRY,
                ATTR_COUNTRYCODE,
                ATTR_CITY,
                ATTR_ADDRESS,
                ATTR_FEEDINDATE,
                ATTR_LASTCLOUDSYNC
            ],
        )

    @property
    def native_value(self) -> str | None:
        if self.coordinator.data["online"]:
            if "status" not in self.coordinator.data["addressbook"]:
                _LOGGER.debug("addressbook status None")
            else:
                if int(self.coordinator.data["addressbook"]["status"]) == 1:
                    return "on-line"
                else:
                    if int(self.coordinator.data["addressbook"]["status"]) == 2:
                        return "in-alarm"
                    else:
                        return "off-line"
        return None

    @property
    def extra_state_attributes(self):
        if self.coordinator.data["online"]:
            if "status" not in self.coordinator.data["addressbook"]:
                _LOGGER.debug("addressbook status attributes None")
            else:
                return {
                    ATTR_DEVICE_SN: self.coordinator.data["addressbook"][ATTR_DEVICE_SN],
                    ATTR_PLANTNAME: self.coordinator.data["addressbook"][ATTR_PLANTNAME],
                    ATTR_MODULESN: self.coordinator.data["addressbook"][ATTR_MODULESN],
                    ATTR_DEVICE_TYPE: self.coordinator.data["addressbook"][ATTR_DEVICE_TYPE],
                    #ATTR_COUNTRY: self.coordinator.data["addressbook"]["result"][ATTR_COUNTRY],
                    #ATTR_COUNTRYCODE: self.coordinator.data["addressbook"]["result"][ATTR_COUNTRYCODE],
                    #ATTR_CITY: self.coordinator.data["addressbook"]["result"][ATTR_CITY],
                    #ATTR_ADDRESS: self.coordinator.data["addressbook"]["result"][ATTR_ADDRESS],
                    #ATTR_FEEDINDATE: self.coordinator.data["addressbook"]["result"][ATTR_FEEDINDATE],
                    ATTR_LASTCLOUDSYNC: datetime.now()
                }
        return None


class FoxESSEnergySolar(FoxESSEnergy):

    _attr_state_class: SensorStateClass = SensorStateClass.TOTAL_INCREASING
    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(self, coordinator, name, deviceID):
        super().__init__(coordinator=coordinator, name=name, deviceID=deviceID, entity_type="Solar")

    @property
    def native_value(self) -> float | None:
        if self.coordinator.data["online"]:
            if "loads" not in self.coordinator.data["report"]:
                loads = 0
            else:
                loads = float(self.coordinator.data["report"]["loads"])

            if "chargeEnergyToTal" not in self.coordinator.data["report"]:
                charge = 0
            else:
                charge = float(self.coordinator.data["report"]["chargeEnergyToTal"])

            if "feedin" not in self.coordinator.data["report"]:
                feedin = 0
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

            energysolar = round((loads + charge + feedIn - gridConsumption - discharge),3)
            if energysolar<0:
                energysolar=0
            return round(energysolar,3)
        return None

def getValueFromCoordinator(coordinator, report_field, value_field):
    value = coordinator.data[report_field].get(value_field)
    return float(value) if value is not None else 0

def getValuesFromCoordinator(coordinator, report_field, value_fields):
    return (
        getValueFromCoordinator(coordinator, report_field, field)
        for field in value_fields
    )

class FoxESSSolarPower(FoxESSPower):
    def __init__(self, coordinator, name, deviceID):
        super().__init__(
            coordinator=coordinator, name=name, deviceID=deviceID, prefix="Solar"
        )

    @property
    def native_value(self) -> float | None:
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            loads, charge, feedIn, gridConsumption, discharge = (
                getValuesFromCoordinator(
                    self.coordinator,
                    "raw",
                    [
                        "loadsPower",
                        "batChargePower",
                        "feedinPower",
                        "gridConsumptionPower",
                        "batDischargePower",
                    ],
                )
            )

            #check if what was returned (that some time was negative) is <0, so fix it
            total = (loads + charge + feedIn - gridConsumption - discharge)
            if total<0:
                total=0
            return round(total,3)
        return None

class FoxESSBatState(FoxESSSimpleSensor):
    def __init__(self, coordinator, name, deviceID, entity_type, report_field, value_field):
        super().__init__(
            coordinator=coordinator,
            name=name,
            deviceID=deviceID,
            device_class=SensorDeviceClass.BATTERY,
            sensor_state_class=SensorStateClass.MEASUREMENT,
            unit_of_measurement="%",
            entity_type=entity_type,
            report_field=report_field,
            value_field=value_field,
        )

    @property
    def icon(self):
        return icon_for_battery_level(battery_level=self.native_value, charging=None)


class FoxESSBatSoC(FoxESSBatState):
    def __init__(self, coordinator, name, deviceID):
        super().__init__(
            coordinator=coordinator,
            name=name,
            deviceID=deviceID,
            entity_type="Bat SoC",
            report_field="raw",
            value_field="SoC",
        )


class FoxESSBatMinSoC(FoxESSBatState):
    def __init__(self, coordinator, name, deviceID):
        super().__init__(
            coordinator=coordinator,
            name=name,
            deviceID=deviceID,
            entity_type="Bat MinSoC",
            report_field="battery",
            value_field="minSoc",
        )


class FoxESSBatMinSoConGrid(FoxESSBatState):
    def __init__(self, coordinator, name, deviceID):
        super().__init__(
            coordinator=coordinator,
            name=name,
            deviceID=deviceID,
            entity_type="Bat minSocOnGrid",
            report_field="battery",
            value_field="minSocOnGrid",
        )


class FoxESSBatTemp(CoordinatorEntity, SensorEntity):

    _attr_device_class = SensorDeviceClass.TEMPERATURE
    _attr_native_unit_of_measurement = UnitOfTemperature.CELSIUS

    def __init__(self, coordinator, name, deviceID):
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Bat Temperature")
        self._attr_name = name+" - Bat Temperature"
        self._attr_unique_id = deviceID+"bat-temperature"
        self.status = namedtuple(
            "status",
            [
                ATTR_DATE,
                ATTR_TIME,
            ],
        )

    @property
    def native_value(self) -> float | None:
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if "batTemperature" not in self.coordinator.data["raw"]:
                _LOGGER.debug("batTemperature None")
            else:
                return self.coordinator.data["raw"]["batTemperature"]
        return None


class FoxESSAmbientTemp(CoordinatorEntity, SensorEntity):

    _attr_device_class = SensorDeviceClass.TEMPERATURE
    _attr_native_unit_of_measurement = UnitOfTemperature.CELSIUS

    def __init__(self, coordinator, name, deviceID):
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Ambient Temperature")
        self._attr_name = name+" - Ambient Temperature"
        self._attr_unique_id = deviceID+"ambient-temperature"
        self.status = namedtuple(
            "status",
            [
                ATTR_DATE,
                ATTR_TIME,
            ],
        )

    @property
    def native_value(self) -> float | None:
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if "ambientTemperation" not in self.coordinator.data["raw"]:
                _LOGGER.debug("ambientTemperation None")
            else:
                return self.coordinator.data["raw"]["ambientTemperation"]
        return None


class FoxESSBoostTemp(CoordinatorEntity, SensorEntity):

    _attr_device_class = SensorDeviceClass.TEMPERATURE
    _attr_native_unit_of_measurement = UnitOfTemperature.CELSIUS

    def __init__(self, coordinator, name, deviceID):
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Boost Temperature")
        self._attr_name = name+" - Boost Temperature"
        self._attr_unique_id = deviceID+"boost-temperature"
        self.status = namedtuple(
            "status",
            [
                ATTR_DATE,
                ATTR_TIME,
            ],
        )

    @property
    def native_value(self) -> float | None:
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if "boostTemperation" not in self.coordinator.data["raw"]:
                _LOGGER.debug("boostTemperation None")
            else:
                return self.coordinator.data["raw"]["boostTemperation"]
        return None


class FoxESSInvTemp(CoordinatorEntity, SensorEntity):

    _attr_device_class = SensorDeviceClass.TEMPERATURE
    _attr_native_unit_of_measurement = UnitOfTemperature.CELSIUS

    def __init__(self, coordinator, name, deviceID):
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Inv Temperature")
        self._attr_name = name+" - Inv Temperature"
        self._attr_unique_id = deviceID+"inv-temperature"
        self.status = namedtuple(
            "status",
            [
                ATTR_DATE,
                ATTR_TIME,
            ],
        )

    @property
    def native_value(self) -> float | None:
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if "invTemperation" not in self.coordinator.data["raw"]:
                _LOGGER.debug("invTemperation None")
            else:
                return self.coordinator.data["raw"]["invTemperation"]
        return None


class FoxESSResidualEnergy(CoordinatorEntity, SensorEntity):

    _attr_device_class = SensorDeviceClass.ENERGY
    _attr_native_unit_of_measurement = UnitOfEnergy.KILO_WATT_HOUR

    def __init__(self, coordinator, name, deviceID):
        super().__init__(coordinator=coordinator)
        _LOGGER.debug("Initiating Entity - Residual Energy")
        self._attr_name = name+" - Residual Energy"
        self._attr_unique_id = deviceID+"residual-energy"
        self.status = namedtuple(
            "status",
            [
                ATTR_DATE,
                ATTR_TIME,
            ],
        )

    @property
    def native_value(self) -> float | None:
        if self.coordinator.data["online"] and self.coordinator.data["raw"]:
            if "ResidualEnergy" not in self.coordinator.data["raw"]:
                _LOGGER.debug("ResidualEnergy None")
            else:
                re = self.coordinator.data["raw"]["ResidualEnergy"]
                if re > 0:
                    re = re / 100
                else:
                    re = 0
                return re
        return None
