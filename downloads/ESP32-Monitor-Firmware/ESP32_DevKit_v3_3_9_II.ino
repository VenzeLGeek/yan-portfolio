/* 
 *  ESP32 Monitor v3.3.9_dualbroadcast_safe
*/
#include <Wire.h>
#include "SensirionI2cSht3x.h"
#include <Sensirion_UPT_Core.h>
#include <Sensirion_Gadget_BLE.h>
#include <NimBLEDevice.h>
#include "time.h"
#include "FS.h"
#include "LittleFS.h"
#include <Preferences.h>
#include "esp_sleep.h"
#include "esp_mac.h"
#include "esp_pm.h"
#include "esp_wifi.h"
#include "esp_bt.h"
#include <vector>
#include <WiFi.h>
#include <WiFiClient.h>
#include <WiFiClientSecure.h>

using namespace sensirion::upt::core;

// ─── Constants ───────────────────────────────────────────────────────────────
#define WEB_SERVICE_UUID   "0000fff0-0000-1000-8000-00805f9b34fb"
#define DATA_CHAR_UUID     "0000fff1-0000-1000-8000-00805f9b34fb"
#define FILE_CHAR_UUID     "0000fff2-0000-1000-8000-00805f9b34fb"

// Board variant — set per file
#define DEFAULT_SOIL_PIN   34
#define DEFAULT_SDA_PIN    25
#define DEFAULT_SCL_PIN    26
#define DEFAULT_I2C_ADDR   0x45
#define DEFAULT_NAME       "S"

#define ADC_DRY_VALUE      2400
#define ADC_WET_VALUE      1000
#define ADC_NUM_SAMPLES    10

#define NORMAL_NOTIFY_S    5
#define BOOT_CPU_MHZ       80
#define ACTIVE_CPU_MHZ     240

// Recovery window after RESET when DS-recording was active (sec).
#define NORMAL_WINDOW_S    180

// DS-cycle broadcast duration. Long enough that a scanner running
// at 1 Hz reliably catches at least one packet during the wake.
#define DS_ADV_DURATION_MS 4000

// SMART-WAKE: broadcast duration before Wi-Fi/SMTP window when alert is firing.
// Must be ≥ baseline DS_ADV_DURATION_MS (4 s) — macOS CoreBluetooth and bleak
// passive-scan need at least one full duty cycle (~1.28 s) to surface a new
// manufacturer-data packet, and the alert path then takes the radio away for
// Wi-Fi/SMTP. Anything shorter than 4 s and PC misses the broadcast.
#define SMART_ALERT_PRE_ADV_MS 4000

// DUAL-BROADCAST (v3.3.8): each phase duration. Total wake window = 2*PHASE.
// 3 s per phase is empirically the minimum for Android MyAmbience and
// macOS bleak scanners to reliably catch one advertisement during their
// passive-scan duty cycle (~1.28 s @ 50% duty).
#define DUAL_PHASE_MS 3000  // legacy back-compat
#define DUAL_PHASE_SENS_MS  2000   // v3.3.9: Sensirion phase (shorter for current safety)
#define DUAL_PHASE_CUST_MS  3000   // v3.3.9: custom 0xFFFF phase
#define DUAL_INTER_GAP_MS    500   // v3.3.9: LDO recovery between phases

// SMART-WAKE: per-channel email cooldown in seconds.
// Persisted across Deep Sleep in RTC_DATA_ATTR lastAlertEpoch[6].
#define SMART_ALERT_COOLDOWN_S 300

// Persistent operating mode.
#define OPMODE_NORMAL   0
#define OPMODE_LIGHT    1
#define OPMODE_DS       2

// CPU clock per mode.
#define CPU_NORMAL_MHZ  240
#define CPU_LIGHT_MHZ    80

// ─── Global objects ──────────────────────────────────────────────────────────
SensirionI2cSht3x      sht35;
NimBLELibraryWrapper   bleLib;
DataProvider           dataProvider(bleLib, DataType::T_RH_HCHO);
NimBLECharacteristic*  pDataChar = nullptr;
NimBLECharacteristic*  pFileChar = nullptr;
Preferences            prefs;

// ─── Configuration ───────────────────────────────────────────────────────────
struct Config {
  String   bleName       = DEFAULT_NAME;
  uint8_t  soilPin       = DEFAULT_SOIL_PIN;
  uint8_t  sdaPin        = DEFAULT_SDA_PIN;
  uint8_t  sclPin        = DEFAULT_SCL_PIN;
  uint8_t  sht35Addr     = DEFAULT_I2C_ADDR;

  uint32_t measureInterval = 10;   // also = DS sleep duration in seconds
  uint32_t notifyInterval  = 5;

  // recording state — survives any reboot
  bool     wantsLogging   = false;
  String   currentLogFile = "";

  // persistent operating mode (NVS-backed)
  uint8_t  opMode         = OPMODE_NORMAL;

  // Wi-Fi / SMTP / alerts
  String   wifiSsid = "";
  String   wifiPass = "";
  String   emailTo   = "";
  String   emailFrom = "";
  String   smtpHost  = "";
  uint16_t smtpPort  = 465;
  String   smtpUser  = "";
  String   smtpPass  = "";
  float    t_low  = -100, t_high = -100;
  float    h_low  = -100, h_high = -100;
  float    s_low  = -100, s_high = -100;
  // SMART-WAKE: gates the smart-wake path on DS-cycle. When false the plate
  // takes the original silent runDsWakePath (lowest possible drain).
  // When true the plate takes runSmartDsWakePath: silent Stage 1 + conditional
  // Stage 2 (Wi-Fi/SMTP only on alert). Set via BLE command EMAIL_EN:0|1.
  bool     emailEnabled = false;
} cfg;

// ─── Runtime state machine ───────────────────────────────────────────────────
enum PlateState {
  STATE_BOOT_WINDOW,
  STATE_NORMAL,
  STATE_DS_COUNTDOWN,
  STATE_DS_WAKE
};

PlateState plateState = STATE_BOOT_WINDOW;

// Boot-window countdown
uint32_t   bootWindowDeadlineMs = 0;
uint32_t   bootWindowLastTickMs = 0;

// DS-countdown (user-triggered Sleep)
uint8_t    dsCountdownSec    = 0;
uint32_t   dsCountdownStepMs = 0;

// Last good measurement (cached for status-adv broadcast)
static float g_lastTemp = 0.0f;
static float g_lastHum  = 0.0f;
static float g_lastSoil = 0.0f;
static bool  g_lastValid = false;

// Recording / runtime
int      desktopClients = 0;
bool     timeSynced     = false;
bool     isLogging      = false;
String   currentLogFile = "";
String   lastLogFile    = "";
File     logFile;
unsigned long lastMeasureMs = 0;
unsigned long lastNotifyMs  = 0;

// alert email cooldown for Normal-mode loop (volatile, in-RAM)
unsigned long lastEmailMs[6] = {0,0,0,0,0,0};
#define ALERT_COOLDOWN_MS 300000UL

// ─── v3: NimBLE init tracker ─────────────────────────────────────────────────
// NimBLE-Arduino 1.x doesn't expose getInitialized(), so we track whether
// the BT stack has been brought up ourselves.  Set true in two places:
// (a) after dataProvider.begin() in runColdBootPath() (Sensirion's lib
// inits NimBLE internally), and (b) inside broadcastStatusAdv() right
// after NimBLEDevice::init().  Checked in enterDeepSleep() so we only
// run the BLE-side teardown when there's actually something to tear down.
static bool g_nimbleInited = false;

// ─── SMART-WAKE: RTC-persistent per-channel cooldown ─────────────────────────
// Survives Deep Sleep. Six entries map to channels:
//   0=T_LOW  1=T_HIGH  2=H_LOW  3=H_HIGH  4=S_LOW  5=S_HIGH
// Each holds the unix-epoch time of the LAST email sent for that channel.
// A new alert email may fire only after SMART_ALERT_COOLDOWN_S has elapsed.
RTC_DATA_ATTR int64_t lastAlertEpoch[6] = {0, 0, 0, 0, 0, 0};

// ─── System log (firmware event log stored on LittleFS) ──────────────────────
#define SYSLOG_PATH      "/syslog.txt"
#define SYSLOG_MAX_BYTES 32768

void syslog(const char* level, const char* msg) {
  Serial.printf("[SYSLOG][%s] %s\n", level, msg);
  File f = LittleFS.open(SYSLOG_PATH, "a");
  if (!f) return;
  if ((int)f.size() > SYSLOG_MAX_BYTES) {
    f.close();
    LittleFS.remove(SYSLOG_PATH);
    f = LittleFS.open(SYSLOG_PATH, "w");
    if (!f) return;
    f.println("--- syslog rotated ---");
  }
  struct tm ti;
  if (getLocalTime(&ti)) {
    char ts[24];
    snprintf(ts, sizeof(ts), "%02d.%02d.%04d %02d:%02d:%02d",
             ti.tm_mday, ti.tm_mon + 1, ti.tm_year + 1900,
             ti.tm_hour, ti.tm_min, ti.tm_sec);
    f.printf("[%s][%s] %s\n", ts, level, msg);
  } else {
    f.printf("[--.--.---- --:--:--][%s] %s\n", level, msg);
  }
  f.flush();
  f.close();
}

#define SYSLOG_I(msg) syslog("INFO",  msg)
#define SYSLOG_W(msg) syslog("WARN",  msg)
#define SYSLOG_E(msg) syslog("ERROR", msg)

// ─── Forward declarations ────────────────────────────────────────────────────
void enterDeepSleep(uint32_t seconds);
void broadcastSensirionAdv(float t, float h, float s, uint32_t durMs);
void broadcastStatusAdv(float t, float h, float s,
                        bool logging, bool inDsCycle,
                        uint32_t intervalSec, uint32_t durMs);
bool sendEmail(const String& subj, const String& body);
bool wifiConnect(uint32_t timeoutMs);
void wifiOff();

// ─── Command queue (FIFO) ────────────────────────────────────────────────────
std::vector<String> cmdQueue;
portMUX_TYPE        cmdMux = portMUX_INITIALIZER_UNLOCKED;

inline void cmdEnqueue(const String& s) {
  portENTER_CRITICAL(&cmdMux);
  cmdQueue.push_back(s);
  portEXIT_CRITICAL(&cmdMux);
}
inline bool cmdDequeue(String& out) {
  bool ok = false;
  portENTER_CRITICAL(&cmdMux);
  if (!cmdQueue.empty()) {
    out = cmdQueue.front();
    cmdQueue.erase(cmdQueue.begin());
    ok = true;
  }
  portEXIT_CRITICAL(&cmdMux);
  return ok;
}

// ─── BLE callbacks ───────────────────────────────────────────────────────────
class ServerCB : public NimBLEServerCallbacks {
  void onConnect(NimBLEServer*, NimBLEConnInfo&) override {
    desktopClients++;
    Serial.printf("[BLE] Connected (clients=%d)\n", desktopClients);
    if (plateState == STATE_BOOT_WINDOW) {
      plateState = STATE_NORMAL;
      Serial.println("[STATE] BOOT_WINDOW -> NORMAL (client connected)");
    } else if (plateState == STATE_DS_COUNTDOWN) {
      plateState = STATE_NORMAL;
      Serial.println("[STATE] DS_COUNTDOWN -> NORMAL (client connected)");
    }
  }
  void onDisconnect(NimBLEServer*, NimBLEConnInfo&, int) override {
    desktopClients = max(0, desktopClients - 1);
    Serial.printf("[BLE] Disconnected (clients=%d)\n", desktopClients);
    NimBLEDevice::startAdvertising();
    if (plateState == STATE_NORMAL && desktopClients == 0) {
      uint32_t now = millis();
      if (bootWindowDeadlineMs == 0 || now >= bootWindowDeadlineMs) {
        bootWindowDeadlineMs = now + (uint32_t)NORMAL_WINDOW_S * 1000UL;
      }
      bootWindowLastTickMs = now;
      plateState = STATE_BOOT_WINDOW;
      Serial.println("[STATE] NORMAL -> BOOT_WINDOW (client disconnected, waiting for timer)");
    }
  }
};

class DataCharCB : public NimBLECharacteristicCallbacks {
  void onWrite(NimBLECharacteristic* pChar, NimBLEConnInfo&) override {
    std::string raw = pChar->getValue();
    if (raw.empty()) return;
    String s(raw.c_str()); s.trim();
    if (s.length() == 0) return;
    cmdEnqueue(s);
    Serial.printf("[CMD-Q] %s (queue size=%d)\n", s.c_str(), (int)cmdQueue.size());
  }
};

// ─── NVS settings ────────────────────────────────────────────────────────────
void loadCfg() {
  prefs.begin("cfg", true);
  cfg.bleName        = prefs.getString("name", DEFAULT_NAME);
  cfg.soilPin   = DEFAULT_SOIL_PIN;
  cfg.sdaPin    = DEFAULT_SDA_PIN;
  cfg.sclPin    = DEFAULT_SCL_PIN;
  cfg.sht35Addr = DEFAULT_I2C_ADDR;
  cfg.measureInterval = prefs.getUInt("interval", 10);
  cfg.notifyInterval  = prefs.getUInt("nfyIv",    NORMAL_NOTIFY_S);
  cfg.wantsLogging    = prefs.getBool("rec",      false);
  cfg.currentLogFile  = prefs.getString("recFile", "");
  cfg.opMode          = prefs.getUChar("opmode",  OPMODE_NORMAL);
  lastLogFile         = prefs.getString("lastlog", "");
  cfg.wifiSsid  = prefs.getString("wssid", "");
  cfg.wifiPass  = prefs.getString("wpass", "");
  cfg.emailTo   = prefs.getString("eto",   "");
  cfg.emailFrom = prefs.getString("efrom", "");
  cfg.smtpHost  = prefs.getString("shost", "");
  cfg.smtpPort  = prefs.getUShort("sport", 465);
  cfg.smtpUser  = prefs.getString("suser", "");
  cfg.smtpPass  = prefs.getString("spass", "");
  cfg.t_low  = prefs.getFloat("tlo", -100); cfg.t_high = prefs.getFloat("thi", -100);
  cfg.h_low  = prefs.getFloat("hlo", -100); cfg.h_high = prefs.getFloat("hhi", -100);
  cfg.s_low  = prefs.getFloat("slo", -100); cfg.s_high = prefs.getFloat("shi", -100);
  cfg.emailEnabled = prefs.getBool("em_en", false);  // SMART-WAKE gate
  prefs.end();
}
void saveCfg() {
  prefs.begin("cfg", false);
  prefs.putString("name",     cfg.bleName);
  prefs.putUInt  ("interval", cfg.measureInterval);
  prefs.putUInt  ("nfyIv",    cfg.notifyInterval);
  prefs.putBool  ("rec",      cfg.wantsLogging);
  prefs.putString("recFile",  cfg.currentLogFile);
  prefs.putUChar ("opmode",   cfg.opMode);
  prefs.putString("lastlog",  lastLogFile);
  prefs.putString("wssid", cfg.wifiSsid); prefs.putString("wpass", cfg.wifiPass);
  prefs.putString("eto",   cfg.emailTo);  prefs.putString("efrom", cfg.emailFrom);
  prefs.putString("shost", cfg.smtpHost); prefs.putUShort("sport", cfg.smtpPort);
  prefs.putString("suser", cfg.smtpUser); prefs.putString("spass", cfg.smtpPass);
  prefs.putFloat("tlo", cfg.t_low ); prefs.putFloat("thi", cfg.t_high);
  prefs.putFloat("hlo", cfg.h_low ); prefs.putFloat("hhi", cfg.h_high);
  prefs.putFloat("slo", cfg.s_low ); prefs.putFloat("shi", cfg.s_high);
  prefs.putBool ("em_en", cfg.emailEnabled);  // SMART-WAKE gate
  prefs.end();
}

// ─── Helpers ─────────────────────────────────────────────────────────────────
String getTimestamp() {
  struct tm ti;
  if (getLocalTime(&ti)) {
    char buf[24];
    snprintf(buf, sizeof(buf), "%02d.%02d.%04d %02d:%02d:%02d",
             ti.tm_mday, ti.tm_mon + 1, ti.tm_year + 1900,
             ti.tm_hour, ti.tm_min, ti.tm_sec);
    return String(buf);
  }
  unsigned long s = millis() / 1000;
  char buf[16];
  snprintf(buf, sizeof(buf), "T+%02lu:%02lu:%02lu", s / 3600, (s % 3600) / 60, s % 60);
  return String(buf);
}
bool isTimeValid() {
  struct tm ti;
  if (!getLocalTime(&ti)) return false;
  return (ti.tm_year + 1900) >= 2024;
}
float readSoilMoisture() {
  long sum = 0;
  for (int i = 0; i < ADC_NUM_SAMPLES; i++) {
    sum += analogRead(cfg.soilPin);
    delay(2);
  }
  int raw = sum / ADC_NUM_SAMPLES;
  return constrain((float)map(raw, ADC_DRY_VALUE, ADC_WET_VALUE, 0, 100), 0.0f, 100.0f);
}

// ─── Deep Sleep entry ────────────────────────────────────────────────────────
// v3: CLEAN radio teardown before esp_deep_sleep_start().
//
// Prior versions called esp_deep_sleep_start() while NimBLE and/or WiFi were
// still active.  On ESP32-WROOM the PMU sometimes brownout-resets ~1 s after
// the sleep call when the radio analog blocks weren't gracefully released,
// causing an infinite "cold-boot 180s window -> DS -> 1 s reboot -> cold-boot"
// loop where SMART-WAKE only fires once and the broadcast never reaches the
// PC scanner (because plate is in cold-boot GATT mode, not DS-cycle).
//
// The teardown order matters:
//   1. Close logFile (flush LittleFS journal)
//   2. Disconnect any BLE clients politely so they don't keep advertising
//      the connection in their cache
//   3. NimBLEDevice::deinit(true) — releases the BT controller
//   4. WiFi.disconnect(true, true) + WiFi.mode(WIFI_OFF) + esp_wifi_stop()
//      + esp_wifi_deinit() — releases the WiFi PHY
//   5. esp_bt_controller_disable() + esp_bt_controller_deinit() — fully
//      releases the Bluetooth controller's analog block
//   6. Short delay so the LDO has time to recover the 3.3 V rail
//   7. Lower CPU clock, then esp_deep_sleep_start()
void enterDeepSleep(uint32_t seconds) {
  char buf[96];
  snprintf(buf, sizeof(buf), "DEEP-ENTRY sleeping=%us state=%d wantsLog=%d isLogging=%d",
           seconds, plateState, cfg.wantsLogging, isLogging);
  Serial.printf("[DEEP-ENTRY] sleeping %us | state=%d wantsLog=%d isLogging=%d\n",
                seconds, plateState, cfg.wantsLogging, isLogging);
  SYSLOG_I(buf);
  long curEpoch = (long)time(nullptr);
  prefs.begin("cfg", false);
  prefs.putBool  ("rec",     isLogging);
  prefs.putString("recFile", currentLogFile);
  prefs.putLong  ("epoch",   curEpoch);
  prefs.putUInt  ("sleepS",  seconds);
  prefs.end();
  if (logFile) logFile.close();

  // ── Clean radio teardown ──────────────────────────────────────────────────
  // Step 1: disconnect BLE clients politely so they release the link.
  // Guard with our own g_nimbleInited flag (NimBLE-Arduino 1.x has no
  // getInitialized()).  Only valid GATT-server paths set g_nimbleInited
  // via runColdBootPath() or broadcastStatusAdv().
  if (g_nimbleInited) {
    // pDataChar is only non-null when runColdBootPath has built the GATT
    // server.  Skip the disconnect call in the silent runDsWakePath case
    // (NimBLE was inited for adv-only — no service, no clients possible).
    if (pDataChar) {
      NimBLEServer* pSrv = NimBLEDevice::getServer();
      if (pSrv && pSrv->getConnectedCount() > 0) {
        Serial.println("[DEEP] disconnecting BLE clients before sleep");
        pSrv->disconnect(0);
        delay(150);
      }
    }
    // Step 2: stop advertising, then deinit NimBLE (releases controller).
    // v3.3.9: extended delays — Sensirion DataProvider leaves heavier
    // NimBLE state than v3.3.7 baseline, so we give BT stack more time
    // to fully release resources before controller disable.
    NimBLEAdvertising* pAdv = NimBLEDevice::getAdvertising();
    if (pAdv) pAdv->stop();
    delay(100);  // v3.3.9: was 20 ms
    NimBLEDevice::deinit(true);
    g_nimbleInited = false;
    delay(100);  // v3.3.9: was 20 ms
  }

  // Step 3: WiFi teardown (no-op if WiFi was never started).
  WiFi.disconnect(true, true);
  WiFi.mode(WIFI_OFF);
  esp_wifi_stop();
  esp_wifi_deinit();
  delay(20);

  // Step 4: fully disable Bluetooth controller — releases the analog
  // block so the LDO doesn't see a residual 60-80 mA load when the
  // digital domain is already in DS.  Safe even if controller was
  // never enabled — both calls are idempotent.
  esp_bt_controller_disable();
  esp_bt_controller_deinit();

  // Step 5: let the 3.3 V rail recover (capacitor charge) before the
  // PMU starts pulling current down for sleep.
  // v3.3.9: extended to 300 ms — v3.3.8 lab logs showed brownout reset
  // with 100 ms after new dual-broadcast workflow.
  delay(300);

  snprintf(buf, sizeof(buf), "DEEP sleeping=%us epoch=%ld", seconds, curEpoch);
  SYSLOG_I(buf);
  Serial.printf("[DEEP] Sleeping %us (epoch=%ld)\n", seconds, curEpoch);
  Serial.flush();
  setCpuFrequencyMhz(BOOT_CPU_MHZ);
  esp_sleep_enable_timer_wakeup((uint64_t)seconds * 1000000ULL);
  esp_deep_sleep_start();
}

// ─── Logging ─────────────────────────────────────────────────────────────────
void startLogging(const String& filename, bool append) {
  if (isLogging) { logFile.close(); isLogging = false; }
  if (!isTimeValid()) {
    Serial.println("[LOG] ERROR: time not synced — recording aborted");
    if (pDataChar) {
      pDataChar->setValue("LOG_ERR:time_not_synced"); pDataChar->notify();
    }
    return;
  }
  String path = filename.startsWith("/") ? filename : "/" + filename;
  bool exists = LittleFS.exists(path);
  logFile = LittleFS.open(path, (append && exists) ? "a" : "w");
  if (!logFile) {
    if (pDataChar) { pDataChar->setValue("LOG_ERR:open_failed"); pDataChar->notify(); }
    return;
  }
  if (!exists || !append) {
    logFile.println("DateTime; Temp; Air Humidity; Soil Humidity; Device");
    logFile.flush();
  }
  isLogging       = true;
  currentLogFile  = path;
  cfg.wantsLogging   = true;
  cfg.currentLogFile = path;
  saveCfg();
  Serial.printf("[LOG] %s %s\n", append ? "Appending to" : "New file", path.c_str());
  if (pDataChar) {
    char buf[80];
    snprintf(buf, sizeof(buf), "LOG_STARTED:%s", path.c_str());
    pDataChar->setValue((uint8_t*)buf, strlen(buf)); pDataChar->notify();
  }
}
void stopLogging() {
  if (!isLogging) return;
  String stopped = currentLogFile;
  logFile.close();
  isLogging = false;
  lastLogFile = stopped;
  cfg.wantsLogging   = false;
  cfg.currentLogFile = "";
  cfg.opMode = OPMODE_NORMAL;
  plateState = STATE_NORMAL;
  bootWindowDeadlineMs = 0;
  saveCfg();
  SYSLOG_I("LOG stopped opMode=NORMAL persisted");
  Serial.printf("[LOG] Stopped: %s\n", stopped.c_str());
  if (pDataChar) {
    char buf[80];
    snprintf(buf, sizeof(buf), "LOG_STOPPED:%s", stopped.c_str());
    pDataChar->setValue((uint8_t*)buf, strlen(buf)); pDataChar->notify();
  }
  currentLogFile = "";
}

// ─── BLE: file index & transfer ──────────────────────────────────────────────
void sendFileList() {
  if (!pFileChar) return;
  File root = LittleFS.open("/");
  if (!root || !root.isDirectory()) {
    pFileChar->setValue("NO_FILES"); pFileChar->notify(); return;
  }
  pFileChar->setValue("LIST_START"); pFileChar->notify(); delay(40);
  File f = root.openNextFile();
  while (f) {
    time_t t = f.getLastWrite();
    char d[20] = "unknown";
    if (t > 1000000000L) {
      struct tm* ti = localtime(&t);
      snprintf(d, sizeof(d), "%02d.%02d.%04d %02d:%02d",
               ti->tm_mday, ti->tm_mon + 1, ti->tm_year + 1900, ti->tm_hour, ti->tm_min);
    }
    char line[128];
    snprintf(line, sizeof(line), "FILE:%s|%d|%s", f.name(), (int)f.size(), d);
    pFileChar->setValue((uint8_t*)line, strlen(line));
    pFileChar->notify(); delay(25);
    f = root.openNextFile();
  }
  pFileChar->setValue("LIST_END"); pFileChar->notify();
}
void sendFile(const String& filename) {
  if (!pFileChar) return;
  String path = filename.startsWith("/") ? filename : "/" + filename;
  if (!LittleFS.exists(path)) {
    pFileChar->setValue("FILE_NOT_FOUND"); pFileChar->notify(); return;
  }
  File f = LittleFS.open(path, "r");
  if (!f) { pFileChar->setValue("FILE_ERR"); pFileChar->notify(); return; }
  char header[80];
  snprintf(header, sizeof(header), "FILE_START:%s|%d", f.name(), (int)f.size());
  pFileChar->setValue((uint8_t*)header, strlen(header));
  pFileChar->notify(); delay(60);
  String line = "";
  while (f.available()) {
    char c = f.read();
    if (c == '\n') {
      if (line.length() > 0) {
        pFileChar->setValue((uint8_t*)line.c_str(), line.length());
        pFileChar->notify(); delay(12); line = "";
      }
    } else if (c != '\r') {
      line += c;
      if (line.length() >= 160) {
        pFileChar->setValue((uint8_t*)line.c_str(), line.length());
        pFileChar->notify(); delay(12); line = "";
      }
    }
  }
  if (line.length() > 0) {
    pFileChar->setValue((uint8_t*)line.c_str(), line.length());
    pFileChar->notify(); delay(12);
  }
  f.close(); delay(40);
  pFileChar->setValue("FILE_END"); pFileChar->notify();
}
void sendAllFiles() {
  if (!pFileChar) return;
  pFileChar->setValue("ALL_FILES_START"); pFileChar->notify(); delay(60);
  File root = LittleFS.open("/");
  if (!root || !root.isDirectory()) {
    pFileChar->setValue("ALL_FILES_END"); pFileChar->notify(); return;
  }
  File f = root.openNextFile();
  while (f) {
    String n(f.name()); f.close();
    sendFile(n); delay(80);
    f = root.openNextFile();
  }
  pFileChar->setValue("ALL_FILES_END"); pFileChar->notify();
}
void sendFileAsLog(const String& filename) {
  if (!pFileChar) return;
  String path = filename.startsWith("/") ? filename : "/" + filename;
  if (!LittleFS.exists(path)) {
    pFileChar->setValue("NO_LOG"); pFileChar->notify(); return;
  }
  File f = LittleFS.open(path, "r");
  if (!f) { pFileChar->setValue("NO_LOG"); pFileChar->notify(); return; }
  pFileChar->setValue("LOG_START"); pFileChar->notify(); delay(60);
  String line = "";
  while (f.available()) {
    char c = f.read();
    if (c == '\n') {
      if (line.length() > 0) {
        pFileChar->setValue((uint8_t*)line.c_str(), line.length());
        pFileChar->notify(); delay(12); line = "";
      }
    } else if (c != '\r') {
      line += c;
      if (line.length() >= 160) {
        pFileChar->setValue((uint8_t*)line.c_str(), line.length());
        pFileChar->notify(); delay(12); line = "";
      }
    }
  }
  if (line.length() > 0) {
    pFileChar->setValue((uint8_t*)line.c_str(), line.length());
    pFileChar->notify(); delay(12);
  }
  f.close(); delay(40);
  pFileChar->setValue("LOG_END"); pFileChar->notify();
}

// ─── STATUS ──────────────────────────────────────────────────────────────────
void sendStatus() {
  if (!pDataChar) return;
  int filesN = 0; size_t total = 0;
  File root = LittleFS.open("/");
  if (root && root.isDirectory()) {
    File f = root.openNextFile();
    while (f) { filesN++; total += f.size(); f = root.openNextFile(); }
  }
  bool hasWifi  = cfg.wifiSsid.length() > 0;
  bool hasEmail = cfg.emailTo.length() > 0 && cfg.smtpHost.length() > 0;
  uint8_t psave = (plateState == STATE_DS_COUNTDOWN ||
                   plateState == STATE_DS_WAKE) ? 2 : 0;
  char buf[320];
  snprintf(buf, sizeof(buf),
    "STATUS:interval=%u,nfyIv=%u,psave=%u,files=%d,used=%u,total=%u,"
    "logging=%d,file=%s,lastfile=%s,timesynced=%d,wifi=%d,email=%d,state=%d",
    cfg.measureInterval, cfg.notifyInterval, psave,
    filesN, (unsigned)total, (unsigned)LittleFS.totalBytes(),
    isLogging ? 1 : 0,
    isLogging ? currentLogFile.c_str() : "none",
    lastLogFile.length() > 0 ? lastLogFile.c_str() : "none",
    timeSynced ? 1 : 0,
    hasWifi ? 1 : 0, hasEmail ? 1 : 0,
    (int)plateState
  );
  pDataChar->setValue((uint8_t*)buf, strlen(buf));
  pDataChar->notify();
  Serial.printf("[STATUS] %s\n", buf);
}

// ─── Wi-Fi / SMTP / Email helpers ────────────────────────────────────────────
bool wifiConnect(uint32_t timeoutMs = 12000) {
  if (cfg.wifiSsid.length() == 0) {
    Serial.println("[WIFI] connect skipped — no SSID configured");
    return false;
  }
  if (WiFi.status() == WL_CONNECTED) return true;
  Serial.printf("[WIFI] connect SSID=%s …\n", cfg.wifiSsid.c_str());
  WiFi.mode(WIFI_STA);
  // SMART-WAKE: reduce TX power to 8.5 dBm (~7 mW) before associate.
  // Default 19.5 dBm pulls 240-300 mA at TX peak; 8.5 dBm pulls ~170 mA.
  // Indoor range to a typical router is still >15 m, so coverage is fine.
  WiFi.setTxPower(WIFI_POWER_8_5dBm);
  WiFi.begin(cfg.wifiSsid.c_str(), cfg.wifiPass.c_str());
  uint32_t t0 = millis();
  while (WiFi.status() != WL_CONNECTED && millis() - t0 < timeoutMs) delay(200);
  if (WiFi.status() == WL_CONNECTED) {
    Serial.printf("[WIFI] OK RSSI=%d IP=%s TXP=8.5dBm\n",
                  (int)WiFi.RSSI(), WiFi.localIP().toString().c_str());
    return true;
  }
  Serial.printf("[WIFI] FAIL status=%d\n", (int)WiFi.status());
  return false;
}
void wifiOff() { WiFi.disconnect(true); WiFi.mode(WIFI_OFF); }

String b64encode(const String& in) {
  static const char* tbl =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  String out; int i = 0, n = in.length();
  while (i < n) {
    int b1 = (uint8_t)in[i++];
    int b2 = (i < n) ? (uint8_t)in[i++] : -1;
    int b3 = (i < n) ? (uint8_t)in[i++] : -1;
    out += tbl[b1 >> 2];
    out += tbl[((b1 & 3) << 4) | (b2 >= 0 ? (b2 >> 4) : 0)];
    out += (b2 >= 0) ? tbl[((b2 & 15) << 2) | (b3 >= 0 ? (b3 >> 6) : 0)] : '=';
    out += (b3 >= 0) ? tbl[b3 & 63] : '=';
  }
  return out;
}
bool sendEmail(const String& subj, const String& body) {
  if (cfg.smtpHost.length() == 0 || cfg.emailTo.length() == 0) {
    Serial.println("[EMAIL] not configured"); return false;
  }
  if (!wifiConnect()) return false;
  WiFiClientSecure client;
  client.setInsecure();
  if (!client.connect(cfg.smtpHost.c_str(), cfg.smtpPort)) {
    Serial.printf("[SMTP] connect FAIL\n"); return false;
  }
  auto wait = [&](const char* tag)->bool{
    String resp;
    String curLine;
    String finalLine;
    uint32_t t0 = millis();
    bool done = false;
    while (millis() - t0 < 5000 && !done) {
      if (client.available()) {
        char c = (char)client.read();
        resp += c;
        if (c == '\n') {
          if (curLine.length() >= 4) {
            char sep = curLine.charAt(3);
            if (sep == ' ') {
              finalLine = curLine;
              done = true;
            }
          } else {
            finalLine = curLine;
            done = true;
          }
          curLine = "";
        } else if (c != '\r') {
          curLine += c;
        }
      } else {
        delay(5);
      }
    }
    Serial.printf("[SMTP %s] %s", tag, resp.c_str());
    if (!resp.endsWith("\n")) Serial.println();
    if (finalLine.length() == 0) return false;
    return finalLine[0] == '2' || finalLine[0] == '3';
  };
  bool ok = true;
  if (!wait("HELLO"))                                      ok = false;
  if (ok) { client.print("EHLO esp32\r\n");                if (!wait("EHLO"))   ok = false; }
  if (ok) { client.print("AUTH LOGIN\r\n");                if (!wait("AUTH"))   ok = false; }
  if (ok) { client.print(b64encode(cfg.smtpUser) + "\r\n");if (!wait("USER"))   ok = false; }
  if (ok) { client.print(b64encode(cfg.smtpPass) + "\r\n");if (!wait("PASS"))   ok = false; }
  if (ok) { client.print("MAIL FROM:<" + cfg.emailFrom + ">\r\n"); if (!wait("FROM")) ok = false; }
  if (ok) { client.print("RCPT TO:<"   + cfg.emailTo   + ">\r\n"); if (!wait("TO"))   ok = false; }
  if (ok) { client.print("DATA\r\n");                      if (!wait("DATA"))   ok = false; }
  if (ok) {
    client.print("Subject: " + subj + "\r\n");
    client.print("From: ESP32 Monitor <" + cfg.emailFrom + ">\r\n");
    client.print("To: " + cfg.emailTo + "\r\n\r\n");
    client.print(body); client.print("\r\n.\r\n");
    if (!wait("BODY")) ok = false;
  }
  client.print("QUIT\r\n"); wait("QUIT");
  client.stop();
  Serial.printf("[EMAIL] \"%s\" -> %s\n", subj.c_str(), ok ? "OK" : "FAIL");
  return ok;
}
void checkAlerts(float t, float h, float s) {
  bool anyEnabled = (cfg.t_low  > -100 || cfg.t_high > -100 ||
                     cfg.h_low  > -100 || cfg.h_high > -100 ||
                     cfg.s_low  > -100 || cfg.s_high > -100);
  if (!anyEnabled) return;
  if (cfg.emailTo.length() == 0) return;
  uint32_t now = millis();
  auto trigger = [&](int idx, const char* what, float val, float thr, const char* op){
    if (now - lastEmailMs[idx] < ALERT_COOLDOWN_MS) return;
    lastEmailMs[idx] = now;
    Serial.printf("[ALERT] %s: %.1f %s %.1f\n", what, val, op, thr);
    const char* desc = idx==0?"Temperature too LOW":idx==1?"Temperature too HIGH":
                       idx==2?"Air humidity too LOW":idx==3?"Air humidity too HIGH":
                       idx==4?"Soil moisture too LOW":"Soil moisture too HIGH";
    String unit = (idx < 2) ? "C" : "%";
    String subj = String("[ESP32 ") + cfg.bleName + "] ALERT: " + desc + " (" + String(val,1) + " " + unit + ")";
    String body = String("ALERT from ESP32 \"") + cfg.bleName + "\"\n\n" +
                  desc + ": " + String(val,1) + " " + unit +
                  "  (threshold " + op + " " + String(thr,1) + " " + unit + ")\n\n" +
                  "Current readings:\n" +
                  "  Temperature:   " + String(t,1) + " C\n" +
                  "  Air humidity:  " + String(h,1) + " %\n" +
                  "  Soil moisture: " + String(s,1) + " %\n\n" +
                  "Device: " + cfg.bleName + "\n" +
                  "MAC:    " + NimBLEDevice::getAddress().toString().c_str() + "\n" +
                  "Time:   " + getTimestamp();
    sendEmail(subj, body);
  };
  if (cfg.t_low  > -100 && t < cfg.t_low ) trigger(0, "TEMP_LOW",  t, cfg.t_low,  "<");
  if (cfg.t_high > -100 && t > cfg.t_high) trigger(1, "TEMP_HIGH", t, cfg.t_high, ">");
  if (cfg.h_low  > -100 && h < cfg.h_low ) trigger(2, "HUM_LOW",   h, cfg.h_low,  "<");
  if (cfg.h_high > -100 && h > cfg.h_high) trigger(3, "HUM_HIGH",  h, cfg.h_high, ">");
  if (cfg.s_low  > -100 && s < cfg.s_low ) trigger(4, "SOIL_LOW",  s, cfg.s_low,  "<");
  if (cfg.s_high > -100 && s > cfg.s_high) trigger(5, "SOIL_HIGH", s, cfg.s_high, ">");
}

// ─── SMART-WAKE: alert-pending check (RTC-persistent cooldown) ───────────────
// Returns true if any configured channel is currently crossing its threshold
// AND that channel's per-channel cooldown (5 min, in unix-epoch seconds)
// has elapsed. nowEpoch must be a valid unix time (>= 1e9) for the check to
// run; otherwise we conservatively return false to avoid hammering SMTP on
// boots where time hasn't been restored.
bool checkAlertsPending(float t, float h, float soil, int64_t nowEpoch) {
  if (nowEpoch < 1000000000LL) return false;
  if (cfg.emailTo.length() == 0 || cfg.smtpHost.length() == 0) return false;
  bool anyEnabled = (cfg.t_low  > -100 || cfg.t_high > -100 ||
                     cfg.h_low  > -100 || cfg.h_high > -100 ||
                     cfg.s_low  > -100 || cfg.s_high > -100);
  if (!anyEnabled) return false;

  auto cross_and_due = [&](int idx, bool cross) -> bool {
    if (!cross) return false;
    return (nowEpoch - lastAlertEpoch[idx]) >= (int64_t)SMART_ALERT_COOLDOWN_S;
  };

  if (cross_and_due(0, cfg.t_low  > -100 && t < cfg.t_low ))      return true;
  if (cross_and_due(1, cfg.t_high > -100 && t > cfg.t_high))      return true;
  if (cross_and_due(2, cfg.h_low  > -100 && h < cfg.h_low ))      return true;
  if (cross_and_due(3, cfg.h_high > -100 && h > cfg.h_high))      return true;
  if (cross_and_due(4, cfg.s_low  > -100 && soil < cfg.s_low ))   return true;
  if (cross_and_due(5, cfg.s_high > -100 && soil > cfg.s_high))   return true;
  return false;
}

// ─── SMART-WAKE: fire emails for each crossed channel, update RTC cooldown ──
// Called only when checkAlertsPending() returned true and WiFi is already up
// (or about to be brought up by sendEmail -> wifiConnect).
void sendAlertEmailsAndUpdateCooldown(float t, float h, float soil,
                                      int64_t nowEpoch) {
  uint8_t mac[6];
  esp_read_mac(mac, ESP_MAC_BT);
  char macStr[20];
  snprintf(macStr, sizeof(macStr), "%02X:%02X:%02X:%02X:%02X:%02X",
           mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);

  auto trigger = [&](int idx, const char* what, float val, float thr, const char* op) {
    if ((nowEpoch - lastAlertEpoch[idx]) < (int64_t)SMART_ALERT_COOLDOWN_S) return;
    Serial.printf("[SMART-ALERT] %s: %.1f %s %.1f\n", what, val, op, thr);
    char slbuf[80];
    snprintf(slbuf, sizeof(slbuf), "SMART-ALERT %s val=%.1f thr=%.1f", what, val, thr);
    SYSLOG_I(slbuf);
    const char* desc = idx==0?"Temperature too LOW":idx==1?"Temperature too HIGH":
                       idx==2?"Air humidity too LOW":idx==3?"Air humidity too HIGH":
                       idx==4?"Soil moisture too LOW":"Soil moisture too HIGH";
    String unit = (idx < 2) ? "C" : "%";
    String subj = String("[ESP32 ") + cfg.bleName + "] ALERT: " + desc + " (" + String(val,1) + " " + unit + ")";
    String body = String("ALERT from ESP32 \"") + cfg.bleName + "\"\n\n" +
                  desc + ": " + String(val,1) + " " + unit +
                  "  (threshold " + op + " " + String(thr,1) + " " + unit + ")\n\n" +
                  "Current readings:\n" +
                  "  Temperature:   " + String(t,1) + " C\n" +
                  "  Air humidity:  " + String(h,1) + " %\n" +
                  "  Soil moisture: " + String(soil,1) + " %\n\n" +
                  "Device: " + cfg.bleName + "\n" +
                  "MAC:    " + macStr + "\n" +
                  "Time:   " + getTimestamp();
    if (sendEmail(subj, body)) {
      lastAlertEpoch[idx] = nowEpoch;  // RTC-persistent — survives DS
    }
  };

  if (cfg.t_low  > -100 && t < cfg.t_low )     trigger(0, "TEMP_LOW",  t, cfg.t_low,  "<");
  if (cfg.t_high > -100 && t > cfg.t_high)     trigger(1, "TEMP_HIGH", t, cfg.t_high, ">");
  if (cfg.h_low  > -100 && h < cfg.h_low )     trigger(2, "HUM_LOW",   h, cfg.h_low,  "<");
  if (cfg.h_high > -100 && h > cfg.h_high)     trigger(3, "HUM_HIGH",  h, cfg.h_high, ">");
  if (cfg.s_low  > -100 && soil < cfg.s_low )  trigger(4, "SOIL_LOW",  soil, cfg.s_low,  "<");
  if (cfg.s_high > -100 && soil > cfg.s_high)  trigger(5, "SOIL_HIGH", soil, cfg.s_high, ">");
}

// ─── Sensirion Gadget BLE broadcast (v3.3.8 dual-broadcast Phase A) ──────────
// Initializes Sensirion DataProvider (which sets up NimBLE advertising in
// Sensirion's 0x06D5 manufacturer-data format), writes current sensor values
// as a sample, commits it (publishes to BLE stack), then waits durMs while
// the library advertises. After the wait, advertising is stopped so the
// caller can replace the advertisement payload with another format.
//
// Used in runSmartDsWakePath() before broadcastStatusAdv() to deliver live
// T/H/Soil readings to the Sensirion MyAmbience smartphone app during the
// Deep Sleep wake window.
void broadcastSensirionAdv(float t, float h, float s, uint32_t durMs) {
  // v3.3.9 BROWNOUT FIX: lower CPU clock during heavy BLE stack init
  // to cut peak current. Reverted at end.
  uint32_t cpuSaved = getCpuFrequencyMhz();
  setCpuFrequencyMhz(80);
  delay(10);  // let PLL settle

  if (!g_nimbleInited) {
    // dataProvider.begin() allocates GATT server + advertising (Sensirion 0x06D5).
    // Heavy: ~80-120 mA peak. Mark flag so subsequent broadcastStatusAdv()
    // does NOT re-init NimBLE.
    dataProvider.begin();
    g_nimbleInited = true;
    Serial.println("[ADV-S] dataProvider.begin() done — Sensirion advertising up");
    delay(50);  // v3.3.9: extra settle after heavy init
  }
  dataProvider.writeValueToCurrentSample(t, SignalType::TEMPERATURE_DEGREES_CELSIUS);
  dataProvider.writeValueToCurrentSample(h, SignalType::RELATIVE_HUMIDITY_PERCENTAGE);
  dataProvider.writeValueToCurrentSample(s, SignalType::HCHO_PARTS_PER_BILLION);
  dataProvider.commitSample();
  Serial.printf("[ADV-S] Sensirion broadcast t=%.1f h=%.1f s=%.1f dur=%ums\n",
                t, h, s, (unsigned)durMs);
  if (durMs > 0) delay(durMs);
  // Stop advertising so caller can install a different mfg-data payload.
  NimBLEAdvertising* pAdv = NimBLEDevice::getAdvertising();
  if (pAdv) pAdv->stop();
  delay(50);  // v3.3.9: was 20 ms

  // v3.3.9: settling gap before next phase. Gives LDO + decoupling caps
  // time to recover from BLE init surge before next adv swap.
  delay(DUAL_INTER_GAP_MS);

  // Restore CPU clock.
  setCpuFrequencyMhz(cpuSaved);
  delay(10);
}

// ─── Status broadcast (no GATT, ~durMs) ──────────────────────────────────────
void broadcastStatusAdv(float t, float h, float s,
                        bool logging, bool inDsCycle,
                        uint32_t intervalSec, uint32_t durMs) {
  if (!g_nimbleInited) {
    NimBLEDevice::init(cfg.bleName.c_str());
    g_nimbleInited = true;
    Serial.printf("[ADV] NimBLE init for status broadcast (name=%s)\n",
                  cfg.bleName.c_str());
  }
  int16_t  tr = (int16_t)(t * 100.0f);
  uint16_t hr = (uint16_t)(h * 100.0f);
  uint16_t sr = (uint16_t)(s * 100.0f);
  uint8_t flags = 0;
  if (logging)                                   flags |= 0x01;
  if (inDsCycle)                                 flags |= 0x02;
  if (cfg.wifiSsid.length() > 0)                 flags |= 0x04;
  if (cfg.emailTo.length() > 0 &&
      cfg.smtpHost.length() > 0)                 flags |= 0x08;
  uint32_t ivMin = intervalSec / 60UL;
  if (ivMin > 255UL) ivMin = 255UL;
  uint8_t payload[10];
  payload[0] = 0xFF; payload[1] = 0xFF;
  payload[2] = (uint8_t)(tr        & 0xFF);
  payload[3] = (uint8_t)((tr >> 8) & 0xFF);
  payload[4] = (uint8_t)(hr        & 0xFF);
  payload[5] = (uint8_t)((hr >> 8) & 0xFF);
  payload[6] = (uint8_t)(sr        & 0xFF);
  payload[7] = (uint8_t)((sr >> 8) & 0xFF);
  payload[8] = flags;
  payload[9] = (uint8_t)ivMin;
  NimBLEAdvertising* pAdv = NimBLEDevice::getAdvertising();
  if (!pAdv) return;
  pAdv->setMinInterval(0x20);
  pAdv->setMaxInterval(0x40);
  NimBLEAdvertisementData advData;
  advData.setName(cfg.bleName.c_str());
  std::string mfg((const char*)payload, sizeof(payload));
  advData.setManufacturerData(mfg);
  pAdv->setAdvertisementData(advData);
  pAdv->start();
  Serial.printf("[ADV] broadcast t=%.1f h=%.1f s=%.1f flags=0x%02X ivMin=%u dur=%ums\n",
                t, h, s, flags, (unsigned)ivMin, (unsigned)durMs);
  if (durMs > 0) { delay(durMs); pAdv->stop(); }
}

// ─── Command handler ─────────────────────────────────────────────────────────
void handleCommand(const String& cmd) {
  Serial.printf("[CMD t=%lums] %s | state=%d clients=%d isLogging=%d\n",
                millis(), cmd.c_str(), (int)plateState, desktopClients, isLogging);

  if (cmd.startsWith("TIME:")) {
    long t = cmd.substring(5).toInt();
    if (t > 1000000000L) {
      struct timeval tv = { (time_t)t, 0 };
      settimeofday(&tv, nullptr);
      timeSynced = true;
      prefs.begin("cfg", false);
      prefs.putLong("epoch",  t);
      prefs.putUInt("sleepS", 0);
      prefs.end();
      Serial.printf("[TIME] Synced %ld\n", t);
      if (cfg.wantsLogging && !isLogging && cfg.currentLogFile.length() > 0) {
        startLogging(cfg.currentLogFile, true);
      }
    }
    return;
  }
  if (cmd.startsWith("INTERVAL:")) {
    long v = cmd.substring(9).toInt();
    if (v >= 1 && v <= 86400) { cfg.measureInterval = v; saveCfg(); }
    return;
  }
  if (cmd.startsWith("NOTIFY_INTERVAL:")) {
    long v = cmd.substring(16).toInt();
    if (v >= 1 && v <= 3600) { cfg.notifyInterval = v; saveCfg(); }
    return;
  }
  if (cmd == "GET_STATUS")     { sendStatus();    return; }
  if (cmd == "LIST_FILES")     { sendFileList();  return; }
  if (cmd == "GET_ALL_FILES")  { sendAllFiles();  return; }
  if (cmd.startsWith("GET_FILE:")) { sendFile(cmd.substring(9)); return; }

  if (cmd == "STAY_NORMAL") {
    plateState = STATE_NORMAL;
    bootWindowDeadlineMs = 0;
    dsCountdownSec = 0;
    cfg.opMode = OPMODE_NORMAL;
    saveCfg();
    Serial.println("[STATE] -> NORMAL (STAY_NORMAL latched, opMode=NORMAL persisted)");
    SYSLOG_I("STAY_NORMAL opMode=NORMAL persisted");
    if (pDataChar) { pDataChar->setValue("STAY_NORMAL_OK"); pDataChar->notify(); }
    return;
  }

  if (cmd == "MODE:NORMAL") {
    cfg.opMode = OPMODE_NORMAL;
    saveCfg();
    plateState = STATE_NORMAL;
    bootWindowDeadlineMs = 0;
    Serial.println("[STATE] -> NORMAL (MODE:NORMAL persisted)");
    SYSLOG_I("MODE:NORMAL persisted forever-on");
    if (pDataChar) { pDataChar->setValue("MODE_NORMAL_OK"); pDataChar->notify(); }
    return;
  }
  if (cmd == "MODE:DS") {
    cfg.opMode = OPMODE_DS;
    saveCfg();
    Serial.println("[CFG] opMode=DS persisted (DS entry via START_DS_COUNTDOWN)");
    SYSLOG_I("MODE:DS opMode persisted");
    if (pDataChar) { pDataChar->setValue("MODE_DS_OK"); pDataChar->notify(); }
    return;
  }
  if (cmd == "MODE:LIGHT_SLEEP" || cmd == "MODE:LIGHT") {
    cfg.opMode = OPMODE_LIGHT;
    saveCfg();
    plateState = STATE_NORMAL;
    bootWindowDeadlineMs = 0;
    setCpuFrequencyMhz(CPU_LIGHT_MHZ);
    Serial.println("[STATE] -> LIGHT_SLEEP (CPU 80MHz)");
    SYSLOG_I("MODE:LIGHT_SLEEP persisted");
    if (pDataChar) { pDataChar->setValue("MODE_LIGHT_OK"); pDataChar->notify(); }
    return;
  }

  if (cmd.startsWith("START_DS_COUNTDOWN:")) {
    if (plateState == STATE_DS_COUNTDOWN) {
      Serial.println("[CMD] START_DS_COUNTDOWN — already counting, ignored");
      return;
    }
    long n = cmd.substring(19).toInt();
    if (n < 1 || n > 60) n = 10;
    cfg.opMode = OPMODE_DS;
    saveCfg();
    SYSLOG_I("START_DS_COUNTDOWN opMode=DS persisted");
    plateState = STATE_DS_COUNTDOWN;
    dsCountdownSec    = (uint8_t)n;
    dsCountdownStepMs = millis();
    Serial.printf("[STATE] -> DS_COUNTDOWN (%lds)\n", n);
    char buf[24];
    snprintf(buf, sizeof(buf), "DS_COUNTDOWN:%u", dsCountdownSec);
    if (pDataChar) { pDataChar->setValue((uint8_t*)buf, strlen(buf)); pDataChar->notify(); }
    return;
  }

  if (cmd == "LOG:STOP" || cmd == "STOP_LOG") { stopLogging(); return; }
  if (cmd == "START_LOG") {
    if (pDataChar) { pDataChar->setValue("LOG_ERR:no_filename"); pDataChar->notify(); }
    return;
  }
  if (cmd.startsWith("LOG:START:"))  { startLogging(cmd.substring(10), false); return; }
  if (cmd.startsWith("LOG:APPEND:")) { startLogging(cmd.substring(11), true);  return; }

  if (cmd == "GET_LOG") {
    if (isLogging && currentLogFile.length() > 0)               { sendFileAsLog(currentLogFile); return; }
    if (lastLogFile.length() > 0 && LittleFS.exists(lastLogFile)) { sendFileAsLog(lastLogFile);    return; }
    File root = LittleFS.open("/");
    String found = "";
    if (root && root.isDirectory()) {
      File f = root.openNextFile();
      while (f) { String n(f.name()); if (n > found) found = n; f = root.openNextFile(); }
    }
    if (found.length() > 0) sendFileAsLog(found);
    else if (pFileChar)     { pFileChar->setValue("NO_LOG"); pFileChar->notify(); }
    return;
  }
  if (cmd.startsWith("DEL_FILE:")) {
    String p = cmd.substring(9);
    if (!p.startsWith("/")) p = "/" + p;
    if (isLogging && currentLogFile == p) {
      if (pDataChar) { pDataChar->setValue("DEL_ERR:active"); pDataChar->notify(); }
      return;
    }
    bool ok = LittleFS.remove(p);
    if (ok && lastLogFile == p) { lastLogFile = ""; saveCfg(); }
    if (pDataChar) {
      String r = ok ? "DEL_OK:" + p : "DEL_ERR:" + p;
      pDataChar->setValue((uint8_t*)r.c_str(), r.length()); pDataChar->notify();
    }
    return;
  }
  if (cmd == "CLEAR_LOG") {
    if (isLogging) { logFile.close(); isLogging = false; }
    File root = LittleFS.open("/");
    if (root && root.isDirectory()) {
      File f = root.openNextFile();
      while (f) { String n = "/" + String(f.name()); LittleFS.remove(n); f = root.openNextFile(); }
    }
    lastLogFile = ""; cfg.wantsLogging = false; cfg.currentLogFile = "";
    saveCfg();
    if (pDataChar) { pDataChar->setValue("CLEAR_OK"); pDataChar->notify(); }
    return;
  }

  if (cmd == "GET_SYSLOG") { sendFile(SYSLOG_PATH); return; }
  if (cmd == "CLEAR_SYSLOG") {
    LittleFS.remove(SYSLOG_PATH);
    SYSLOG_I("syslog cleared via BLE");
    if (pDataChar) { pDataChar->setValue("SYSLOG_CLEAR_OK"); pDataChar->notify(); }
    return;
  }

  if (cmd.startsWith("SETNAME:")) {
    cfg.bleName = cmd.substring(8); cfg.bleName.trim();
    saveCfg();
    if (pDataChar) { pDataChar->setValue("OK_REBOOT"); pDataChar->notify(); }
    return;
  }

  if (cmd == "WIFI:CLEAR") {
    cfg.wifiSsid = ""; cfg.wifiPass = ""; saveCfg();
    if (pDataChar) { pDataChar->setValue("WIFI_CLEARED"); pDataChar->notify(); }
    return;
  }
  if (cmd.startsWith("WIFI:")) {
    String body = cmd.substring(5);
    int p = body.indexOf(':'); if (p < 0) return;
    cfg.wifiSsid = body.substring(0, p);
    cfg.wifiPass = body.substring(p + 1);
    saveCfg();
    if (pDataChar) { pDataChar->setValue("WIFI_OK"); pDataChar->notify(); }
    return;
  }
  if (cmd == "EMAIL:CLEAR") {
    cfg.emailTo = cfg.emailFrom = cfg.smtpHost = cfg.smtpUser = cfg.smtpPass = "";
    cfg.smtpPort = 465; saveCfg();
    if (pDataChar) { pDataChar->setValue("EMAIL_CLEARED"); pDataChar->notify(); }
    return;
  }
  // SMART-WAKE: enable/disable feature gate (app pushes from wizard checkbox).
  if (cmd == "EMAIL_EN:1" || cmd == "EMAIL_EN:0") {
    cfg.emailEnabled = (cmd == "EMAIL_EN:1");
    saveCfg();
    if (pDataChar) {
      pDataChar->setValue(cfg.emailEnabled ? "EMAIL_EN_ON" : "EMAIL_EN_OFF");
      pDataChar->notify();
    }
    return;
  }
  if (cmd == "EMAIL:TEST") {
    bool ok = sendEmail("ESP32 test", "This is a test email from your ESP32 sensor.");
    if (pDataChar) {
      pDataChar->setValue(ok ? "EMAIL_TEST_OK" : "EMAIL_TEST_FAIL");
      pDataChar->notify();
    }
    return;
  }
  if (cmd.startsWith("EMAIL:")) {
    String body = cmd.substring(6);
    String parts[6]; int i = 0, start = 0;
    for (int idx = 0; idx < (int)body.length() && i < 6; idx++) {
      if (body[idx] == ':') { parts[i++] = body.substring(start, idx); start = idx + 1; }
    }
    if (i < 6) parts[i++] = body.substring(start);
    if (i < 6) return;
    cfg.emailTo   = parts[0]; cfg.emailFrom = parts[1]; cfg.smtpHost = parts[2];
    cfg.smtpPort  = parts[3].toInt(); if (cfg.smtpPort == 0) cfg.smtpPort = 465;
    cfg.smtpUser  = parts[4]; cfg.smtpPass = parts[5];
    saveCfg();
    if (pDataChar) { pDataChar->setValue("EMAIL_OK"); pDataChar->notify(); }
    return;
  }
  if (cmd == "ALERT:CLEAR") {
    cfg.t_low = cfg.t_high = cfg.h_low = cfg.h_high = cfg.s_low = cfg.s_high = -100;
    saveCfg();
    if (pDataChar) { pDataChar->setValue("ALERTS_CLEARED"); pDataChar->notify(); }
    return;
  }
  if (cmd.startsWith("ALERT:")) {
    String body = cmd.substring(6);
    int p = body.indexOf(':'); if (p < 0) return;
    String key = body.substring(0, p); float v = body.substring(p + 1).toFloat();
    if      (key == "T_LOW")  cfg.t_low  = v;
    else if (key == "T_HIGH") cfg.t_high = v;
    else if (key == "H_LOW")  cfg.h_low  = v;
    else if (key == "H_HIGH") cfg.h_high = v;
    else if (key == "S_LOW")  cfg.s_low  = v;
    else if (key == "S_HIGH") cfg.s_high = v;
    else return;
    saveCfg();
    if (pDataChar) { pDataChar->setValue("ALERT_OK"); pDataChar->notify(); }
    return;
  }

  if (cmd == "REBOOT") {
    Serial.println("[REBOOT] in 500ms…"); delay(500); ESP.restart();
  }
}

// ─── DS-WAKE silent measurement path (BASELINE — emailEnabled=false) ─────────
void runDsWakePath() {
  analogReadResolution(12);
  analogSetAttenuation(ADC_11db);
  pinMode(cfg.soilPin, INPUT);
  Wire.begin(cfg.sdaPin, cfg.sclPin);
  sht35.begin(Wire, cfg.sht35Addr);
  delay(50);

  configTime(0, 0, "");
  if (!LittleFS.begin(true)) {
    Serial.println("[DS-WAKE] LittleFS FAILED");
    SYSLOG_E("DS-WAKE LittleFS FAILED");
    enterDeepSleep(cfg.measureInterval);
    return;
  }

  prefs.begin("cfg", true);
  long savedEpoch = prefs.getLong("epoch", 0);
  uint32_t sleptS  = prefs.getUInt("sleepS", 0);
  prefs.end();
  if (savedEpoch > 1000000000L) {
    time_t restored = (time_t)savedEpoch + sleptS;
    struct timeval tv = { restored, 0 };
    settimeofday(&tv, nullptr);
    timeSynced = true;
    Serial.printf("[DS-WAKE] time restored %ld\n", (long)restored);
  }

  if (cfg.wantsLogging && cfg.currentLogFile.length() > 0 && isTimeValid()) {
    String path = cfg.currentLogFile;
    if (!path.startsWith("/")) path = "/" + path;
    bool exists = LittleFS.exists(path);
    logFile = LittleFS.open(path, exists ? "a" : "w");
    if (logFile) {
      if (!exists) {
        logFile.println("DateTime; Temp; Air Humidity; Soil Humidity; Device");
      }
      isLogging = true;
      currentLogFile = path;
    }
  }

  uint32_t next_sleep_s = cfg.measureInterval;

  float t = NAN, h = NAN;
  int16_t err = sht35.measureSingleShot(REPEATABILITY_HIGH, true, t, h);
  float s = readSoilMoisture();
  if (err == 0) {
    g_lastTemp = t; g_lastHum = h; g_lastSoil = s; g_lastValid = true;
    Serial.printf("[DS-WAKE] %s; %.1f°C; %.1f%%; soil %.1f%%\n",
                  getTimestamp().c_str(), t, h, s);
    char slbuf[80];
    snprintf(slbuf, sizeof(slbuf), "DS-WAKE %.1fC %.1f%% soil=%.1f%% logging=%d",
             t, h, s, isLogging);
    SYSLOG_I(slbuf);
    if (isLogging && logFile) {
      struct tm ti;
      if (getLocalTime(&ti) && isTimeValid()) {
        char db[12], tb[10];
        snprintf(db, sizeof(db), "%02d.%02d.%04d", ti.tm_mday, ti.tm_mon + 1, ti.tm_year + 1900);
        snprintf(tb, sizeof(tb), "%02d:%02d:%02d", ti.tm_hour, ti.tm_min, ti.tm_sec);
        uint8_t _mac[6];
        esp_read_mac(_mac, ESP_MAC_BT);
        char macShort[10];
        snprintf(macShort, sizeof(macShort), "%02X%02X%02X%02X",
                 _mac[2], _mac[3], _mac[4], _mac[5]);
        char line[100];
        snprintf(line, sizeof(line), "%s %s; %.1f; %.1f; %.1f; %s",
                 db, tb, t, h, s, macShort);
        logFile.println(line); logFile.flush();
      }
    }
    checkAlerts(t, h, s);
  } else {
    char slbuf[40];
    snprintf(slbuf, sizeof(slbuf), "DS-WAKE sensor err=%d", err);
    Serial.printf("[DS-WAKE] sensor err=%d\n", err);
    SYSLOG_E(slbuf);
  }
  if (logFile) logFile.close();

  if (g_lastValid) {
    plateState = STATE_DS_WAKE;
    broadcastStatusAdv(g_lastTemp, g_lastHum, g_lastSoil,
                       isLogging, /*inDsCycle=*/true,
                       cfg.measureInterval, DS_ADV_DURATION_MS);
  } else {
    Serial.println("[DS-WAKE] no valid measurement — skip adv");
  }

  long curEpoch = (long)time(nullptr);
  prefs.begin("cfg", false);
  prefs.putLong("epoch",  curEpoch);
  prefs.putUInt("sleepS", 0);
  prefs.end();

  enterDeepSleep(next_sleep_s);
}

// ─── SMART-WAKE path (emailEnabled=true) ─────────────────────────────────────
// Stage 1 (~4 s, same drain as baseline DS-wake):
//   SHT35 + LittleFS init -> measure -> CSV -> 0xFFFF broadcast.
// Stage 2 (only when checkAlertsPending=true):
//   stop adv -> WiFi.setTxPower(8.5dBm) -> sendEmail per crossed channel ->
//   wifiOff. RTC_DATA_ATTR lastAlertEpoch[6] tracks per-channel cooldown
//   across Deep Sleep, so an unchanging alert state fires once every 5 min
//   instead of every measurement cycle.
//
// When no thresholds cross, this path is identical in time/current to the
// baseline silent path — so battery autonomy equals email-OFF baseline.
void runSmartDsWakePath() {
  // Step 1: bare-metal init (no Sensirion BLE library, no GATT)
  analogReadResolution(12);
  analogSetAttenuation(ADC_11db);
  pinMode(cfg.soilPin, INPUT);
  Wire.begin(cfg.sdaPin, cfg.sclPin);
  sht35.begin(Wire, cfg.sht35Addr);
  delay(50);

  configTime(0, 0, "");
  if (!LittleFS.begin(true)) {
    Serial.println("[SMART-WAKE] LittleFS FAILED");
    SYSLOG_E("SMART-WAKE LittleFS FAILED");
    enterDeepSleep(cfg.measureInterval);
    return;
  }

  // Step 2: time + logging state restore
  prefs.begin("cfg", true);
  long savedEpoch = prefs.getLong("epoch", 0);
  uint32_t sleptS  = prefs.getUInt("sleepS", 0);
  prefs.end();
  if (savedEpoch > 1000000000L) {
    time_t restored = (time_t)savedEpoch + sleptS;
    struct timeval tv = { restored, 0 };
    settimeofday(&tv, nullptr);
    timeSynced = true;
    Serial.printf("[SMART-WAKE] time restored %ld\n", (long)restored);
  }

  if (cfg.wantsLogging && cfg.currentLogFile.length() > 0 && isTimeValid()) {
    String path = cfg.currentLogFile;
    if (!path.startsWith("/")) path = "/" + path;
    bool exists = LittleFS.exists(path);
    logFile = LittleFS.open(path, exists ? "a" : "w");
    if (logFile) {
      if (!exists) logFile.println("DateTime; Temp; Air Humidity; Soil Humidity; Device");
      isLogging = true;
      currentLogFile = path;
    }
  }

  // Step 3: measure
  float t = NAN, h = NAN;
  int16_t err = sht35.measureSingleShot(REPEATABILITY_HIGH, true, t, h);
  float soil = readSoilMoisture();

  // Step 4: write CSV (always, regardless of alert path)
  if (err == 0) {
    g_lastTemp = t; g_lastHum = h; g_lastSoil = soil; g_lastValid = true;
    Serial.printf("[SMART-WAKE] %s; %.1f°C; %.1f%%; soil %.1f%%\n",
                  getTimestamp().c_str(), t, h, soil);
    char slbuf[96];
    snprintf(slbuf, sizeof(slbuf),
             "SMART-WAKE %.1fC %.1f%% soil=%.1f%% logging=%d",
             t, h, soil, isLogging);
    SYSLOG_I(slbuf);
    if (isLogging && logFile) {
      struct tm ti;
      if (getLocalTime(&ti) && isTimeValid()) {
        char db[12], tb[10];
        snprintf(db, sizeof(db), "%02d.%02d.%04d", ti.tm_mday, ti.tm_mon + 1, ti.tm_year + 1900);
        snprintf(tb, sizeof(tb), "%02d:%02d:%02d", ti.tm_hour, ti.tm_min, ti.tm_sec);
        uint8_t _mac[6];
        esp_read_mac(_mac, ESP_MAC_BT);
        char macShort[10];
        snprintf(macShort, sizeof(macShort), "%02X%02X%02X%02X",
                 _mac[2], _mac[3], _mac[4], _mac[5]);
        char line[100];
        snprintf(line, sizeof(line), "%s %s; %.1f; %.1f; %.1f; %s",
                 db, tb, t, h, soil, macShort);
        logFile.println(line); logFile.flush();
      }
    }
  } else {
    char slbuf[40];
    snprintf(slbuf, sizeof(slbuf), "SMART-WAKE sensor err=%d", err);
    Serial.printf("[SMART-WAKE] sensor err=%d\n", err);
    SYSLOG_E(slbuf);
  }
  if (logFile) logFile.close();

  // Step 5: decide whether to fire Stage 2 (WiFi+email)
  int64_t nowEpoch = (int64_t)time(nullptr);
  bool alertPending = (err == 0) &&
                      checkAlertsPending(t, h, soil, nowEpoch);

  plateState = STATE_DS_WAKE;

  if (alertPending) {
    SYSLOG_I("SMART-WAKE alert pending — opening WiFi+email window");
    Serial.println("[SMART-WAKE] ALERT_PENDING — stage 2 (WiFi+email)");

    // v3.3.8 DUAL-BROADCAST: Sensirion (MyAmbience) THEN custom 0xFFFF (PC app).
    // Both broadcasts run during the Stage 1 silent window so MyAmbience
    // receives live readings even on alert cycles where Wi-Fi will follow.
    if (g_lastValid) {
      broadcastSensirionAdv(g_lastTemp, g_lastHum, g_lastSoil, DUAL_PHASE_SENS_MS);
      broadcastStatusAdv(g_lastTemp, g_lastHum, g_lastSoil,
                         isLogging, /*inDsCycle=*/true,
                         cfg.measureInterval,
                         DUAL_PHASE_CUST_MS);
    }
    NimBLEAdvertising* pAdv = NimBLEDevice::getAdvertising();
    if (pAdv) pAdv->stop();

    // Fire emails — sendEmail() will bring up Wi-Fi at 8.5 dBm via
    // wifiConnect(), do the SMTP transaction, then we wifiOff explicitly.
    sendAlertEmailsAndUpdateCooldown(t, h, soil, nowEpoch);
    wifiOff();
    SYSLOG_I("SMART-WAKE email window done");
  } else {
    // No alert -> v3.3.8 DUAL-BROADCAST: Sensirion (3 s) + custom 0xFFFF (3 s).
    // Total wake window ≈ 6 s. MyAmbience receives live readings via
    // Phase A; ESP32 Monitor desktop app receives them via Phase B.
    if (g_lastValid) {
      broadcastSensirionAdv(g_lastTemp, g_lastHum, g_lastSoil, DUAL_PHASE_SENS_MS);
      broadcastStatusAdv(g_lastTemp, g_lastHum, g_lastSoil,
                         isLogging, /*inDsCycle=*/true,
                         cfg.measureInterval, DUAL_PHASE_CUST_MS);
    } else {
      Serial.println("[SMART-WAKE] no valid measurement — skip adv");
    }
  }

  // Step 6: persist epoch and Deep Sleep again for cfg.measureInterval
  long curEpoch = (long)time(nullptr);
  prefs.begin("cfg", false);
  prefs.putLong("epoch",  curEpoch);
  prefs.putUInt("sleepS", 0);
  prefs.end();

  enterDeepSleep(cfg.measureInterval);
}

// ─── COLD-BOOT / RESET path (UNCHANGED vs baseline v3.3.7) ───────────────────
void runColdBootPath() {
  Serial.println("[BOOT] Sensirion BLE library init …");
  InitSampleConfigurationMapping();
  dataProvider.begin();   // Sensirion's lib inits NimBLE internally
  g_nimbleInited = true;
  delay(200);

  Serial.println("[BOOT] NimBLE GATT init …");
  NimBLEDevice::setDeviceName(cfg.bleName.c_str());
  Serial.printf("[BLE] GAP Device Name set to: %s\n", cfg.bleName.c_str());
  NimBLEServer* pServer = NimBLEDevice::getServer();
  pServer->setCallbacks(new ServerCB());
  NimBLEService* pSvc = pServer->createService(WEB_SERVICE_UUID);
  pDataChar = pSvc->createCharacteristic(DATA_CHAR_UUID,
                NIMBLE_PROPERTY::READ | NIMBLE_PROPERTY::NOTIFY | NIMBLE_PROPERTY::WRITE);
  pDataChar->setCallbacks(new DataCharCB());
  pDataChar->createDescriptor("2902", NIMBLE_PROPERTY::READ | NIMBLE_PROPERTY::WRITE);
  pFileChar = pSvc->createCharacteristic(FILE_CHAR_UUID,
                NIMBLE_PROPERTY::READ | NIMBLE_PROPERTY::NOTIFY);
  pFileChar->createDescriptor("2902", NIMBLE_PROPERTY::READ | NIMBLE_PROPERTY::WRITE);
  pSvc->start();
  delay(100);

  NimBLEAdvertising* pAdv = NimBLEDevice::getAdvertising();
  pAdv->addServiceUUID(WEB_SERVICE_UUID);
  pAdv->setName(cfg.bleName.c_str());
  pAdv->setMinInterval(0x20);
  pAdv->setMaxInterval(0x40);
  pAdv->start();
  Serial.printf("[BLE] advertising as: %s (fast: 20-40ms)\n", cfg.bleName.c_str());

  setCpuFrequencyMhz(ACTIVE_CPU_MHZ);
  Serial.printf("[BOOT] CPU -> %d MHz\n", ACTIVE_CPU_MHZ);

  plateState = STATE_BOOT_WINDOW;
  bootWindowDeadlineMs = millis() + (uint32_t)NORMAL_WINDOW_S * 1000UL;
  bootWindowLastTickMs = millis();
  Serial.printf("[STATE] -> BOOT_WINDOW (%us)\n", NORMAL_WINDOW_S);
  {
    char slbuf[64];
    snprintf(slbuf, sizeof(slbuf), "BOOT name=%s interval=%us",
             cfg.bleName.c_str(), cfg.measureInterval);
    SYSLOG_I(slbuf);
  }

  if (cfg.wantsLogging && cfg.currentLogFile.length() > 0 && isTimeValid()) {
    Serial.printf("[BOOT] auto-resuming recording: %s\n",
                  cfg.currentLogFile.c_str());
    startLogging(cfg.currentLogFile, true);
  } else if (cfg.wantsLogging && cfg.currentLogFile.length() > 0) {
    Serial.printf("[BOOT] wantsLogging=true, time invalid — wait for TIME\n");
  }
}

// ─── SETUP ───────────────────────────────────────────────────────────────────
void setup() {
  setCpuFrequencyMhz(BOOT_CPU_MHZ);
  Serial.begin(115200); delay(500);

  esp_sleep_wakeup_cause_t wc = esp_sleep_get_wakeup_cause();
  bool wokeFromDeepSleep = (wc == ESP_SLEEP_WAKEUP_TIMER);

  Serial.println("\n╔══════════════════════════════════════════════════════════════════════╗");
  Serial.println("║   ESP32 Monitor v3.3.9_dualbroadcast_safe — SMART-WAKE + clean DS teardown    ║");
  Serial.println("║   NORMAL (240MHz) | LIGHT_SLEEP (80MHz) | DEEP_SLEEP                ║");
  Serial.println("╚══════════════════════════════════════════════════════════════════════╝\n");

  loadCfg();
  Serial.printf("Loaded cfg: name=%s soil=%d sda=%d scl=%d i2c=0x%02X int=%us emEn=%d\n",
                cfg.bleName.c_str(), cfg.soilPin, cfg.sdaPin, cfg.sclPin,
                cfg.sht35Addr, cfg.measureInterval, (int)cfg.emailEnabled);
  Serial.printf("Wake cause: %s\n",
                wokeFromDeepSleep ? "TIMER (DS-cycle)" : "RESET / cold boot / power-on");

  if (wokeFromDeepSleep) {
    // SMART-WAKE routing:
    //   emailEnabled=false -> silent runDsWakePath (unchanged from v3.3.7).
    //   emailEnabled=true  -> runSmartDsWakePath (Stage 1 silent + conditional
    //                        Stage 2 Wi-Fi/SMTP only when alert AND cooldown).
    if (!cfg.emailEnabled) {
      plateState = STATE_DS_WAKE;
      runDsWakePath();
      return;  // unreachable: runDsWakePath ends in enterDeepSleep
    }
    plateState = STATE_DS_WAKE;
    Serial.println("[BOOT] DS-wake -> SMART_WAKE (emails ON, conditional Wi-Fi)");
    SYSLOG_I("DS-WAKE SMART_WAKE (emails ON, conditional WiFi)");
    runSmartDsWakePath();
    return;  // unreachable: runSmartDsWakePath ends in enterDeepSleep
  }

  // ── Cold boot / RESET path (ordered per spec) ───────────────────────────────
  analogReadResolution(12);
  analogSetAttenuation(ADC_11db);
  pinMode(cfg.soilPin, INPUT);
  Wire.begin(cfg.sdaPin, cfg.sclPin);
  sht35.begin(Wire, cfg.sht35Addr);
  Serial.printf("OK SHT35 (SDA=%d, SCL=%d, addr=0x%02X)  Soil pin=%d\n",
                cfg.sdaPin, cfg.sclPin, cfg.sht35Addr, cfg.soilPin);
  delay(100);

  configTime(0, 0, "");

  if (!LittleFS.begin(true)) {
    Serial.println("X LittleFS FAILED");
  } else {
    Serial.printf("OK LittleFS: %u / %u bytes\n",
                  (unsigned)LittleFS.usedBytes(), (unsigned)LittleFS.totalBytes());
    if (cfg.currentLogFile.length() > 0 && !LittleFS.exists(cfg.currentLogFile)) {
      cfg.currentLogFile = ""; cfg.wantsLogging = false; saveCfg();
    }
    if (lastLogFile.length() > 0 && !LittleFS.exists(lastLogFile)) {
      lastLogFile = ""; saveCfg();
    }
    File root = LittleFS.open("/"); int n = 0;
    if (root && root.isDirectory()) {
      File f = root.openNextFile();
      while (f) { Serial.printf("  [%d] %s  %d B\n", ++n, f.name(), (int)f.size()); f = root.openNextFile(); }
    }
    if (n == 0) Serial.println("  (no files)");
  }
  delay(100);

  prefs.begin("cfg", true);
  long savedEpoch = prefs.getLong("epoch", 0);
  prefs.end();
  if (savedEpoch > 1000000000L) {
    struct timeval tv = { (time_t)savedEpoch, 0 };
    settimeofday(&tv, nullptr);
    timeSynced = true;
    Serial.printf("[BOOT] time restored from NVS: %ld\n", savedEpoch);
  }

  runColdBootPath();

  if (cfg.opMode == OPMODE_NORMAL || cfg.opMode == OPMODE_LIGHT
      || !cfg.wantsLogging) {
    plateState = STATE_NORMAL;
    bootWindowDeadlineMs = 0;
    if (cfg.opMode == OPMODE_LIGHT) {
      setCpuFrequencyMhz(CPU_LIGHT_MHZ);
      Serial.println("[STATE] -> LIGHT_SLEEP (CPU 80MHz)");
      SYSLOG_I("BOOT mode=LIGHT_SLEEP persist forever");
    } else {
      Serial.println("[STATE] -> NORMAL (persist forever, CPU 240MHz)");
      char slbuf[64];
      snprintf(slbuf, sizeof(slbuf),
               "BOOT mode=NORMAL persist (rec=%d opmode=%u)",
               cfg.wantsLogging, cfg.opMode);
      SYSLOG_I(slbuf);
    }
  } else {
    Serial.printf("[STATE] -> BOOT_WINDOW recovery %us (opMode=DS)\n",
                  NORMAL_WINDOW_S);
    SYSLOG_I("BOOT mode=DS-LOGGING recovery window 180s");
  }

  Serial.println("\n╔══════════════════════════════════════════════════════════════════════╗");
  Serial.println("║                  READY v3.3.9_dualbroadcast_safe                              ║");
  Serial.println("╚══════════════════════════════════════════════════════════════════════╝\n");
}

// ─── LOOP ────────────────────────────────────────────────────────────────────
void loop() {
  dataProvider.handleDownload();

  String cmd;
  while (cmdDequeue(cmd)) handleCommand(cmd);

  if (plateState == STATE_BOOT_WINDOW) {
    uint32_t now = millis();
    if (now - bootWindowLastTickMs >= 1000UL) {
      bootWindowLastTickMs = now;
      uint32_t remaining = (bootWindowDeadlineMs > now)
                           ? (bootWindowDeadlineMs - now) / 1000UL : 0;
      Serial.printf("[NORMAL-WINDOW] %us remaining\n", (unsigned)remaining);
      broadcastStatusAdv(g_lastValid ? g_lastTemp : 0.0f,
                         g_lastValid ? g_lastHum  : 0.0f,
                         g_lastValid ? g_lastSoil : 0.0f,
                         isLogging, /*inDsCycle=*/false,
                         cfg.measureInterval, /*durMs=*/0);
    }
    if (now >= bootWindowDeadlineMs) {
      if (cfg.opMode == OPMODE_DS && cfg.wantsLogging) {
        Serial.printf("[STATE] BOOT_WINDOW expired (DS recovery) — DS %us\n",
                      cfg.measureInterval);
        SYSLOG_I("BOOT_WINDOW expired — DS recovery resume");
        enterDeepSleep(cfg.measureInterval);
        return;
      } else {
        plateState = STATE_NORMAL;
        Serial.println("[STATE] BOOT_WINDOW -> NORMAL (window expired, staying available)");
        SYSLOG_I("BOOT_WINDOW expired -> NORMAL (no auto-DS)");
        bootWindowDeadlineMs = 0;
      }
    }
  }

  if (plateState == STATE_DS_COUNTDOWN && (millis() - dsCountdownStepMs >= 1000UL)) {
    dsCountdownStepMs = millis();
    if (dsCountdownSec > 0) {
      dsCountdownSec--;
      char buf[24];
      snprintf(buf, sizeof(buf), "DS_COUNTDOWN:%u", dsCountdownSec);
      if (pDataChar) { pDataChar->setValue((uint8_t*)buf, strlen(buf)); pDataChar->notify(); }
      Serial.printf("[DS-CD] %s\n", buf);
      if (dsCountdownSec == 0) {
        Serial.println("[DS-CD] countdown=0 — disconnecting clients then DS");
        NimBLEServer* pSrv = NimBLEDevice::getServer();
        if (pSrv) {
          delay(200);
          pSrv->disconnect(0);
          delay(300);
        }
        enterDeepSleep(cfg.measureInterval);
        return;
      }
    }
  }

  unsigned long now = millis();
  bool doNotify = (now - lastNotifyMs  >= (unsigned long)cfg.notifyInterval  * 1000UL);
  bool doLog    = (now - lastMeasureMs >= (unsigned long)cfg.measureInterval * 1000UL);

  if (!doNotify && !doLog) {
    delay(20);
    return;
  }

  float t = NAN, h = NAN;
  int16_t err = sht35.measureSingleShot(REPEATABILITY_HIGH, true, t, h);
  float s = readSoilMoisture();

  if (err == 0) {
    if (doLog) {
      dataProvider.writeValueToCurrentSample(t, SignalType::TEMPERATURE_DEGREES_CELSIUS);
      dataProvider.writeValueToCurrentSample(h, SignalType::RELATIVE_HUMIDITY_PERCENTAGE);
      dataProvider.writeValueToCurrentSample(s, SignalType::HCHO_PARTS_PER_BILLION);
      dataProvider.commitSample();
    }
    if (doNotify) {
      lastNotifyMs = millis();
      if (pDataChar) {
        uint8_t d[6];
        int16_t  tr = (int16_t)(t * 100);
        uint16_t hr = (uint16_t)(h * 100);
        uint16_t sr = (uint16_t)(s * 100);
        d[0] = tr & 0xFF; d[1] = (tr >> 8) & 0xFF;
        d[2] = hr & 0xFF; d[3] = (hr >> 8) & 0xFF;
        d[4] = sr & 0xFF; d[5] = (sr >> 8) & 0xFF;
        pDataChar->setValue(d, 6); pDataChar->notify();
      }
    }
    if (doLog) {
      lastMeasureMs = millis();
      g_lastTemp = t; g_lastHum = h; g_lastSoil = s; g_lastValid = true;
      checkAlerts(t, h, s);
      if (isLogging && logFile) {
        struct tm ti;
        if (getLocalTime(&ti) && isTimeValid()) {
          char db[12], tb[10];
          snprintf(db, sizeof(db), "%02d.%02d.%04d", ti.tm_mday, ti.tm_mon + 1, ti.tm_year + 1900);
          snprintf(tb, sizeof(tb), "%02d:%02d:%02d", ti.tm_hour, ti.tm_min, ti.tm_sec);
          String macFull(NimBLEDevice::getAddress().toString().c_str());
          String macShort = macFull.substring(macFull.length() - 8);
          macShort.replace(":", "");
          char line[100];
          snprintf(line, sizeof(line), "%s %s; %.1f; %.1f; %.1f; %s",
                   db, tb, t, h, s, macShort.c_str());
          logFile.println(line); logFile.flush();
          static uint32_t lastEpochSave = 0;
          uint32_t nowMs = millis();
          if (nowMs - lastEpochSave > 30000UL) {
            lastEpochSave = nowMs;
            prefs.begin("cfg", false);
            prefs.putLong("epoch",  (long)time(nullptr));
            prefs.putUInt("sleepS", 0);
            prefs.end();
          }
        }
      }
      Serial.printf("%s; %.1f°C; %.1f%%; soil %.1f%%%s\n",
                    getTimestamp().c_str(), t, h, s, isLogging ? " [REC]" : "");
    }
  } else {
    if (doLog)    { lastMeasureMs = millis(); Serial.printf("[ERR] sensor=%d\n", err); }
    if (doNotify) { lastNotifyMs  = millis(); }
  }
}
