# =============================================================================
# Traffic Matrix NY — LED Highway Sign Display for Matrix Portal S3
# =============================================================================
# Copyright (C) 2026 Keith Elkin
# https://keithelkin.com
#
# This project fetches live traffic message sign data from the NY511 API
# and displays it on an Adafruit Matrix Portal S3 driving RGB LED panels,
# replicating the appearance of highway variable message signs.
#
# All rights reserved. Unauthorized redistribution or commercial use
# without explicit written permission from the author is prohibited.
# =============================================================================

"""
Robust CircuitPython Main Program for Matrix Portal S3 Traffic Sign Display.

Features:
- Fetches live traffic sign data from the NY511 API and displays matched signs.
- MatrixPortal hardware initialized once at startup (not inside the loop).
- SocketPool and Requests Session created once and reused across cycles.
- Aggressive garbage collection to prevent heap fragmentation/memory exhaustion.
- Hardware Watchdog Timer (45s) automatically reboots the board if frozen.
- Graceful WiFi reconnection; displays SSID/IP on matrix at connect time.
- WebLogger captures all print() output into an in-memory ring buffer.
- Emergency Rescue Web Server (raw socket, port 80) streams the log buffer
  to any browser when adafruit_httpserver is unavailable.
- adafruit_httpserver used when available, with defensive fallback to rescue server.
- Shadow library cleanup removes stale single-file httpserver remnants on boot.
- GitHub OTA update engine driven by a JSON manifest file.
  Uses atomic .tmp-then-rename writes with Content-Length validation to prevent
  corrupt/truncated files from landing on the filesystem.
  Full multi-file updates (code + libraries) in one pass.
- Local and cloud version numbers displayed on the LED matrix at boot.

Bugfixes vs. earlier revisions:
- set_text_color() uses integer literals (0xRRGGBB), not CSS strings "#RRGGBB".
- set_text_color() and set_text() pass label index 0 explicitly.
- matrix_debug cast to bool before passing to MatrixPortal().
- OTA version comparison parses manifest JSON correctly.
- os.makedirs() replaced with per-level os.mkdir() (CircuitPython compatible).
- All imports at module top level — no deferred imports inside functions.
- safe_delay() polls the web server during all wait periods so the rescue
  page remains responsive while sign data is being displayed.
"""

# --- VERSION (keep at top for easy access) ---
LOCAL_VERSION = "2.2.68"

# --- Display color constants (hardware-correct: no software remapping needed) ---
# The color_order setting passed to MatrixPortal handles channel mapping at the
# driver level. These are the colors as the user perceives them.
COLOR_CYAN   = 0x00FFFF  # Informational / in-progress
COLOR_GREEN  = 0x00FF00  # Success / connected / verified
COLOR_RED    = 0xFF0000  # Error / failed
COLOR_AMBER  = 0xFF8800  # Warning / pending reboot
COLOR_YELLOW = 0xFFFF00  # Data / version numbers
COLOR_WHITE  = 0xFFFFFF  # Neutral / default

# --- Imports ---
import ssl
import wifi
import socketpool
import adafruit_requests
import time
import sys
import os
import json
import traceback
import terminalio
import gc
import microcontroller
import io
from microcontroller import watchdog as w
from watchdog import WatchDogMode
from adafruit_matrixportal.matrixportal import MatrixPortal

# --- Shadow Library Cleanup ---
# Removes stale single-file adafruit_httpserver.py/.mpy that would shadow the
# package directory and cause import failures after an OTA update.
for _shadow in ["/lib/adafruit_httpserver.py", "/lib/adafruit_httpserver.mpy"]:
    try:
        os.remove(_shadow)
    except OSError:
        pass

# --- WebLogger: in-memory ring buffer that mirrors all print() output ---
class WebLogger:
    def __init__(self, max_lines=60):
        self.buffer = []
        self.max_lines = max_lines
        self.current_line = ""

    def write(self, message):
        if isinstance(message, (bytes, bytearray)):
            try:
                message = message.decode("utf-8")
            except Exception:
                message = str(message)
        elif not isinstance(message, str):
            message = str(message)

        parts = message.split("\n")
        if len(parts) == 1:
            self.current_line += parts[0]
        else:
            self.current_line += parts[0]
            self.buffer.append(self.current_line)
            for part in parts[1:-1]:
                self.buffer.append(part)
            self.current_line = parts[-1]
            while len(self.buffer) > self.max_lines:
                self.buffer.pop(0)

    def get_logs(self):
        all_lines = list(self.buffer)
        if self.current_line:
            all_lines.append(self.current_line)
        return "\n".join(all_lines)

web_logger = WebLogger()
_original_print = print

def print(*args, **kwargs):
    """Overrides built-in print() to mirror output into the WebLogger buffer."""
    sep = kwargs.get("sep", " ")
    end = kwargs.get("end", "\n")
    message = sep.join(str(arg) for arg in args)
    web_logger.write(message + end)
    _original_print(*args, **kwargs)

def log_exception(e):
    """Logs a full exception traceback into the WebLogger."""
    try:
        stream = io.StringIO()
        traceback.print_exception(e, limit=None, file=stream)
        print(stream.getvalue())
    except Exception:
        try:
            stream = io.StringIO()
            sys.print_exception(e, stream)
            print(stream.getvalue())
        except Exception:
            print(f"Exception logging failed: {e}")

# --- Defensive adafruit_httpserver import with fallback ---
# The library renamed its classes in newer versions:
#   HTTPServer -> Server
#   HTTPResponse -> Response
#   HTTPMethod.GET -> GET (imported directly from methods)
# We try the new names first, then fall back to the old names for compatibility.
HAS_HTTPSERVER = False
web_error_message = ""

try:
    # New API (current): Server, Response, GET
    from adafruit_httpserver.server import Server
    from adafruit_httpserver.response import Response
    from adafruit_httpserver.methods import GET
    HAS_HTTPSERVER = True
except Exception as _new_err:
    try:
        # Old API fallback: HTTPServer, HTTPResponse, HTTPMethod
        from adafruit_httpserver.server import HTTPServer as Server
        from adafruit_httpserver.response import HTTPResponse as Response
        from adafruit_httpserver.methods import HTTPMethod
        GET = HTTPMethod.GET
        HAS_HTTPSERVER = True
    except Exception as _old_err:
        try:
            # Package-level fallback
            from adafruit_httpserver import HTTPServer as Server, HTTPResponse as Response, HTTPMethod
            GET = HTTPMethod.GET
            HAS_HTTPSERVER = True
        except Exception as _fallback_err:
            HAS_HTTPSERVER = False
            log_exception(_fallback_err)
            try:
                web_error_message = repr(_fallback_err).split("(")[0].split(".")[-1].replace("Error", "").upper()[:10]
            except Exception:
                web_error_message = "ERROR"

# --- Secrets (ssid, password, ny511key only) ---
try:
    from secrets import secrets
except ImportError:
    print("WiFi secrets are kept in secrets.py, please add them there!")
    raise

# NY511 API URL — only the key comes from secrets, everything else is static

# OTA manifest URL (GitHub raw) — stored in secrets so it doesn't ship in code
ENABLE_OTA   = secrets.get("enable_ota", False)
MANIFEST_URL = secrets.get("github_version_url", "https://raw.githubusercontent.com/kelkin/TrafficMatrixNY/main/ota_manifest.json")

# --- settings.json — all user-configurable values ---
# secrets.py only holds ssid/password/ny511key.
# Everything else lives here and is editable via the web UI.
SETTINGS_FILE = "settings.json"

_default_settings = {
    "color_order":          "RGB",   # Hardware pixel order
    "sign_name_color":      "#0000FF",  # Blue for sign name header
    "sign_text_color":      "#F7B500",  # Road sign yellow for sign message
    "name_display_seconds": 3,
    "msg_display_seconds":  10,
    "page_display_seconds": 5,
    "cycle_sleep_seconds":  30,
    "width":                192,     # Total display width in pixels (64 x num panels)
    "height":               32,      # Display height in pixels
    "depth":                6,       # Bit depth (color quality)
    "matrix_debug":         False,   # Enable MatrixPortal debug output
    "characters_per_line":  30,      # Text wrapping width
    "brightness":           0.8,     # Display brightness 0.0-1.0
    "log_refresh_seconds":  5,       # Log page auto-refresh interval (0=disabled)
    "api_url":              "https://511ny.org/api/getmessagesigns?format=json&key=",
    "api_key":              "",      # Set via web UI or secrets.py
    "unit_name":            "",      # Friendly name shown on LED at boot (e.g. "BEDSIDE", "WALL")
}

def load_settings():
    """Load settings.json, merging with defaults for any missing keys."""
    try:
        with open(SETTINGS_FILE, "r") as f:
            data = json.loads(f.read())
        for k, v in _default_settings.items():
            if k not in data:
                data[k] = v
        return data
    except Exception:
        return dict(_default_settings)

def save_settings(data):
    """Write settings dict to settings.json atomically via .tmp swap."""
    tmp = SETTINGS_FILE + ".tmp"
    try:
        with open(tmp, "w") as f:
            f.write(json.dumps(data))
        try:
            os.remove(SETTINGS_FILE)
        except OSError:
            pass
        os.rename(tmp, SETTINGS_FILE)
        return True
    except Exception as e:
        print(f"save_settings failed: {e}")
        return False

def hex_to_int(hex_str):
    """Convert '#RRGGBB' or 'RRGGBB' string to integer 0xRRGGBB."""
    try:
        return int(hex_str.lstrip("#"), 16)
    except Exception:
        return 0xF7B500  # fallback to sign yellow

def color_for_display(hex_str):
    """Convert a hex color string to the integer needed by set_text_color().
    The hardware color_order passed to MatrixPortal at init handles all channel
    remapping at the driver level. No software remapping needed.
    """
    return hex_to_int(hex_str)

settings = load_settings()

# API URL and key — read from settings.json, fall back to secrets.py
# On first boot, migrate ny511key from secrets.py into settings.json
_api_url = settings.get("api_url", "https://511ny.org/api/getmessagesigns?format=json&key=")
_api_key = settings.get("api_key", "")
if not _api_key and secrets.get("ny511key", ""):
    _api_key = secrets.get("ny511key", "")
    settings["api_key"] = _api_key
    save_settings(settings)
    print("Migrated ny511key from secrets.py to settings.json")
NY511_URL = _api_url + _api_key
# All runtime values read from settings (loaded above)
color_order         = settings.get("color_order", "RGB")
sign_text_color     = [color_for_display(settings.get("sign_text_color", "#F7B500"))]  # Remapped for hardware color order
sign_name_color     = [color_for_display(settings.get("sign_name_color",  "#0000FF"))]  # Remapped for hardware color order
name_disp_secs      = int(settings.get("name_display_seconds", 3))
msg_disp_secs       = int(settings.get("msg_display_seconds", 10))
cycle_sleep_secs    = int(settings.get("cycle_sleep_seconds", 30))
page_disp_secs      = int(settings.get("page_display_seconds", 5))
characters_per_line = int(settings.get("characters_per_line", 30))
brightness          = float(settings.get("brightness", 0.8))
width               = int(settings.get("width", 192))
height              = int(settings.get("height", 32))
bit_depth           = int(settings.get("depth", 6))
matrix_debug        = bool(settings.get("matrix_debug", False))
print("Settings: color_order=" + color_order + " text_color=" + hex(sign_text_color[0])
      + " name=" + str(name_disp_secs) + "s msg=" + str(msg_disp_secs)
      + "s cycle=" + str(cycle_sleep_secs) + "s")

# --- signs.json — favorite sign names (replaces sign_list.txt) ---
SIGNS_FILE       = "signs.json"
SIGNS_CACHE_FILE = "signs_cache.json"

def refresh_signs_cache_from_api():
    """Fetch all sign names from NY511 and save to signs_cache.json.
    Called from the main loop so watchdog feeds work correctly throughout."""
    print("Fetching NY511 sign cache...")
    matrixportal.set_text_color(0x00FFFF, 0)
    matrixportal.set_text(center_multiline_string("LOADING\nSIGNS...", characters_per_line), 0)
    w.feed()

    resp_obj = None
    try:
        resp_obj = requests.get(NY511_URL, timeout=20)
        w.feed()
        if resp_obj.status_code != 200:
            print(f"NY511 cache fetch failed: HTTP {resp_obj.status_code}")
            return False

        api_data = resp_obj.json()
        w.feed()
        resp_obj.close()
        resp_obj = None

        if not isinstance(api_data, list):
            print("NY511 cache: unexpected response format")
            return False

        sign_data = []
        for sign in api_data:
            w.feed()  # Feed watchdog while iterating 933 signs
            if "Name" in sign:
                # Store name + messages (drop lat/long/roadway to save space)
                msgs = sign.get("Messages", [])
                if isinstance(msgs, str):
                    msgs = [msgs]
                elif not isinstance(msgs, list):
                    msgs = []
                roadway = sign.get("Roadway", "")
                sign_data.append({"name": sign["Name"], "messages": msgs, "roadway": roadway})

        sign_data.sort(key=lambda s: s["name"])
        api_data = None
        gc.collect()
        gc.collect()

        ok = save_signs_cache(sign_data)
        print(f"NY511 cache: {len(sign_data)} signs saved={ok}")

        matrixportal.set_text_color(0x00FF00, 0)
        matrixportal.set_text(center_multiline_string(
            "SIGNS\nCACHED", characters_per_line), 0)
        safe_delay(2)
        return ok

    except Exception as e:
        print(f"NY511 cache fetch error: {e}")
        log_exception(e)
        return False
    finally:
        if resp_obj is not None:
            try:
                resp_obj.close()
            except Exception:
                pass
        # Restore normal display color
        matrixportal.set_text_color(sign_text_color[0], 0)
        matrixportal.set_text("", 0)
        gc.collect()

def load_favorite_signs():
    """Load the list of favorite sign names from signs.json."""
    try:
        with open(SIGNS_FILE, "r") as f:
            data = json.loads(f.read())
        return data.get("favorites", [])
    except Exception:
        return []

def save_favorite_signs(favorites_list):
    """Save the list of favorite sign names to signs.json atomically."""
    tmp = SIGNS_FILE + ".tmp"
    try:
        with open(tmp, "w") as f:
            f.write(json.dumps({"favorites": favorites_list}))
        try:
            os.remove(SIGNS_FILE)
        except OSError:
            pass
        os.rename(tmp, SIGNS_FILE)
        return True
    except Exception as e:
        print(f"save_favorite_signs failed: {e}")
        return False

def load_signs_cache():
    """Load sign cache from signs_cache.json.
    Returns list of {"name": str, "messages": list} dicts.
    Handles old format (list of strings) by converting transparently."""
    try:
        with open(SIGNS_CACHE_FILE, "r") as f:
            data = json.loads(f.read())
        signs = data.get("signs", [])
        # Handle old format: list of plain strings
        if signs and isinstance(signs[0], str):
            return [{"name": s, "messages": [], "roadway": ""} for s in signs]
        return signs
    except Exception:
        return []

def save_signs_cache(sign_data):
    """Save sign data to signs_cache.json atomically.
    sign_data: list of {"name": str, "messages": list} dicts."""
    tmp = SIGNS_CACHE_FILE + ".tmp"
    try:
        with open(tmp, "w") as f:
            f.write(json.dumps({"signs": sign_data}))
        try:
            os.remove(SIGNS_CACHE_FILE)
        except OSError:
            pass
        os.rename(tmp, SIGNS_CACHE_FILE)
        return True
    except Exception as e:
        print(f"save_signs_cache failed: {e}")
        return False

# --- Hardware Watchdog ---
w.timeout = 45.0
w.mode = WatchDogMode.RESET
w.feed()

# --- Matrix Portal Init (once at startup) ---
print("Initializing Matrix Portal display...")
matrixportal = MatrixPortal(
    width=width,
    height=height,
    bit_depth=bit_depth,
    debug=matrix_debug,
    color_order=color_order
)
matrixportal.add_text(
    text_font=terminalio.FONT,
    text_position=(0, 15),
    scrolling=False,
    line_spacing=0.8,
    text_color=sign_text_color[0]  # remapped for hardware color order
)
# Note: FramebufferDisplay.brightness only supports 0.0 (off) or 1.0 (full).
# True brightness is controlled via bit_depth at initialization — see settings.
w.feed()

# --- Helper Functions ---
def center_multiline_string(text, width_chars):
    """Centers each line of a multi-line string to fit the matrix display."""
    return "\n".join(line.center(width_chars) for line in text.splitlines())

def clean_string(text):
    """Strips brackets, quotes, and normalises type to str."""
    if text is None:
        return ""
    text = " ".join(str(i) for i in text) if isinstance(text, list) else str(text)
    return text.replace("[", "").replace("]", "").replace('"', "").replace("'", "")

def paginate_message(msg_string, lines_per_page=3):
    """Split a raw message string into display pages.

    Handles both \n separators in the raw string and the literal backslash-n
    that sometimes appears in the API data. Returns a list of strings, each
    containing at most lines_per_page lines joined by newlines.

    Example:
        "LINE1\nLINE2\nLINE3\nLINE4\nLINE5" with lines_per_page=3
        -> ["LINE1\nLINE2\nLINE3", "LINE4\nLINE5"]
    """
    # Normalise escaped newlines from API
    normalised = msg_string.replace("\\n", "\n").replace("\n", "\n")
    lines = [l for l in normalised.split("\n") if l.strip()]
    pages = []
    for i in range(0, max(1, len(lines)), lines_per_page):
        pages.append("\n".join(lines[i:i + lines_per_page]))
    return pages if pages else [""]

def display_sign(match, name_secs, page_secs, lines_per_page=3):
    """Display one matched sign: name first, then all message pages in order."""
    if _reboot_pending[0] or _id_flash_pending[0]:
        return  # Exit immediately if reboot or ID flash requested

    # Show sign name
    clean_name = clean_string(match["name"])
    centered_name = center_multiline_string(clean_name, characters_per_line)
    print(f"Name: {clean_name}")
    matrixportal.set_text_color(sign_name_color[0], 0)
    matrixportal.set_text(centered_name, 0)
    safe_delay(name_secs)
    w.feed()

    if _reboot_pending[0] or _id_flash_pending[0]:
        return  # Exit if reboot or ID flash requested after name display

    # Normalise messages to a list
    raw_messages = match["msg"]
    if isinstance(raw_messages, str):
        raw_messages = [raw_messages]
    elif not isinstance(raw_messages, list):
        raw_messages = [str(raw_messages)]

    # Display each message, paginated
    matrixportal.set_text_color(sign_text_color[0], 0)
    for raw_msg in raw_messages:
        if _reboot_pending[0] or _id_flash_pending[0]:
            return  # Exit immediately if reboot or ID flash requested
        clean_msg = clean_string(raw_msg)
        pages = paginate_message(clean_msg, lines_per_page)
        for page in pages:
            if _reboot_pending[0] or _id_flash_pending[0]:
                return  # Exit immediately if reboot or ID flash requested
            centered_page = center_multiline_string(page, characters_per_line)
            print(f"Page:\n{centered_page}")
            matrixportal.set_text(centered_page, 0)
            safe_delay(page_secs)
            w.feed()

def ensure_dir_exists(filepath):
    """Creates all parent directories for filepath using single-level os.mkdir()."""
    parts = filepath.split("/")
    if len(parts) > 1:
        current_path = ""
        for part in parts[:-1]:
            current_path = (current_path + "/" + part) if current_path else part
            try:
                os.mkdir(current_path)
            except OSError as e:
                if e.errno != 17:  # 17 = EEXIST — directory already exists, fine
                    raise

# --- Raw Socket Rescue Web Server ---
rescue_socket = None
server = None

def start_rescue_server():
    """Binds a raw TCP socket on port 80 to serve the log page when
    adafruit_httpserver is unavailable."""
    global rescue_socket, pool
    if rescue_socket is not None:
        return
    try:
        af_inet    = getattr(pool, "AF_INET",    getattr(socketpool, "AF_INET",    2))
        sock_stream = getattr(pool, "SOCK_STREAM", getattr(socketpool, "SOCK_STREAM", 1))
        rescue_socket = pool.socket(af_inet, sock_stream)
        rescue_socket.settimeout(0.02)
        try:
            import socket as _socket
            rescue_socket.setsockopt(_socket.SOL_SOCKET, _socket.SO_REUSEADDR, 1)
        except Exception:
            pass
        rescue_socket.bind((str(wifi.radio.ipv4_address), 80))
        try:
            rescue_socket.listen(3)
        except TypeError:
            rescue_socket.listen()
        print(f"Rescue Web Server active at http://{wifi.radio.ipv4_address}/")
    except Exception as e:
        print(f"Rescue server bind failed: {e}")
        rescue_socket = None

def safe_send(conn, data):
    """Sends bytes/string over a TCP connection, retrying on EAGAIN (errno 11)."""
    if isinstance(data, str):
        data = data.encode("utf-8")
    sent_total = 0
    while sent_total < len(data):
        try:
            sent = conn.send(data[sent_total:])
            if sent == 0:
                break
            sent_total += sent
        except OSError as e:
            if e.errno == 11:  # EAGAIN — socket buffer full, retry
                time.sleep(0.01)
                continue
            raise

def poll_rescue_server():
    """Non-blocking poll: accepts one connection, sends the full log page, closes.

    Firefox requires a Content-Length header — it will show a blank page or
    connection reset if the response arrives in unpredictable chunks without one.
    Fix: build the complete HTML body as a single string, measure its byte length,
    send the header with that length, then send the body. One complete transaction.
    """
    global rescue_socket
    if rescue_socket is None:
        return
    conn = None
    try:
        conn, addr = rescue_socket.accept()
        conn.settimeout(0.5)
        request_str = ""
        buf = bytearray(512)
        for _ in range(3):
            try:
                num_bytes = conn.recv_into(buf)
                if num_bytes > 0:
                    request_str = buf[:num_bytes].decode("utf-8")
                    break
            except OSError:
                pass
            time.sleep(0.05)

        # Silently discard favicon requests — browsers always send one
        if request_str and "favicon.ico" in request_str:
            try:
                conn.send(b"HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\nConnection: close\r\n\r\n")
                conn.close()
            except Exception:
                pass
            return

        print(f"Rescue connection from {addr}")

        # Escape log content so < > & render correctly in the browser
        log_lines = list(web_logger.buffer)
        if web_logger.current_line:
            log_lines.append(web_logger.current_line)
        log_content = "\n".join(log_lines)
        log_escaped = (log_content
                       .replace("&", "&amp;")
                       .replace("<", "&lt;")
                       .replace(">", "&gt;"))

        # Build the complete HTML body as one string so we can measure it
        body = (
            "<!DOCTYPE html><html><head>"
            "<title>Matrix Portal S3 - Rescue Console</title>"
            "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">"
            "<style>"
            "body{font-family:monospace;background:#111;color:#ff3333;margin:20px;line-height:1.4;}"
            "h1{color:#ff3333;}h2{color:#ffaa00;}"
            "pre{background:#000;padding:15px;border-radius:5px;border:1px solid #333;"
            "overflow-x:auto;white-space:pre-wrap;color:#00ff00;}"
            ".meta{color:#888;font-size:0.85em;margin-bottom:10px;}"
            "</style></head><body>"
            "<h1>&#x1F6A8; Matrix Portal S3 &mdash; Rescue Console</h1>"
            "<div class=\"meta\">Firmware: v" + LOCAL_VERSION +
            " &nbsp;|&nbsp; IP: " + str(wifi.radio.ipv4_address) +
            " &nbsp;|&nbsp; Free RAM: " + str(gc.mem_free()) + " bytes</div>"
            "<h2>Log Output:</h2>"
            "<pre>" + log_escaped + "</pre>"
            "</body></html>"
        )

        # Encode once to get the true byte length for Content-Length
        body_bytes = body.encode("utf-8")
        header = (
            "HTTP/1.1 200 OK\r\n"
            "Content-Type: text/html; charset=utf-8\r\n"
            "Content-Length: " + str(len(body_bytes)) + "\r\n"
            "Connection: close\r\n"
            "\r\n"
        )

        safe_send(conn, header)
        safe_send(conn, body_bytes)
        time.sleep(0.15)
        conn.close()

    except OSError:
        pass
    except Exception as ex:
        log_exception(ex)
        if conn:
            try:
                conn.close()
            except Exception:
                pass
    finally:
        gc.collect()

def poll_server():
    """Poll the active web server once, feeding the watchdog before and after.
    server.poll() can block for several seconds while sending a large response,
    so we must feed the watchdog both before and after each call."""
    if HAS_HTTPSERVER and server is not None:
        try:
            w.feed()
            server.poll()
            w.feed()
        except Exception as _poll_err:
            err_str = str(_poll_err)
            if err_str and "timed out" not in err_str and "ETIMEDOUT" not in err_str:
                print(f"server.poll() error: {err_str}")
    else:
        poll_rescue_server()

# --- Shared mutable flags (defined here so safe_delay can reference them
#     before the web server block initializes further below) ---
_calib_state          = {"active": False}
_refresh_cache_pending = [False]  # Set by web UI, consumed by main loop
_reboot_pending        = [False]  # Set by web routes, handled by main loop after response flushes
_id_flash_pending      = [False]  # Set by /identify route, main loop flashes unit name on panels
_signs_filter          = [""]    # Current search filter for signs page
_signs_show_all        = [False] # Whether to show full unfiltered list
_api_error             = [""]    # Non-empty = API error message, stops fetching until cleared
_signs_page            = [0]     # Current page number for signs page
_signs_show_all        = [False] # Whether to show full unfiltered list

def safe_delay(seconds):
    """Sleeps for `seconds` while continuously feeding the watchdog and
    polling the web server so the log page stays responsive.
    Exits early if _reboot_pending or _id_flash_pending is set so those
    actions happen within seconds rather than waiting for the current
    display cycle to finish."""
    start = time.monotonic()
    while time.monotonic() - start < seconds:
        poll_server()  # includes w.feed() before and after
        if _reboot_pending[0]:
            return  # Exit early — main loop will handle the reboot
        if _id_flash_pending[0]:
            return  # Exit early — main loop will handle the ID flash
        time.sleep(0.01)

# --- WiFi Connection ---
def connect_wifi():
    """Connects to WiFi, showing status on the matrix display."""
    w.feed()
    if wifi.radio.connected:
        return True

    ssid = secrets.get("ssid", "")
    print(f"Connecting to WiFi: {ssid}")
    try:
        matrixportal.set_text_color(COLOR_CYAN, 0)
        matrixportal.set_text(center_multiline_string(f"CONNECTING\n{ssid}", characters_per_line), 0)
    except Exception:
        pass

    try:
        wifi.radio.connect(secrets["ssid"], secrets["password"])
        w.feed()
        ip = str(wifi.radio.ipv4_address)
        print(f"Connected! IP: {ip}")
        try:
            matrixportal.set_text_color(COLOR_GREEN, 0)
            matrixportal.set_text(center_multiline_string(f"{ip}\n{ssid}", characters_per_line), 0)
            safe_delay(5)
        except Exception:
            pass
        return True
    except Exception as e:
        print(f"WiFi connection failed: {e}")
        try:
            matrixportal.set_text_color(COLOR_RED, 0)
            matrixportal.set_text(center_multiline_string("WIFI\nFAILED", characters_per_line), 0)
        except Exception:
            pass
        return False

# --- Initial Network Setup ---
gc.collect()
pool = None
ssl_context = None
requests = None

if connect_wifi():
    pool = socketpool.SocketPool(wifi.radio)
    # Single SSL context with no cert verification — set it and forget it.
    # No cert expiry issues, no support burden for customers.
    ssl_context = ssl.create_default_context()
    try:
        ssl_context.load_verify_locations(cadata="")
    except Exception:
        pass
    requests = adafruit_requests.Session(pool, ssl_context)

    if not HAS_HTTPSERVER:
        start_rescue_server()

    # Show web server status on matrix
    try:
        if HAS_HTTPSERVER:
            matrixportal.set_text_color(COLOR_GREEN, 0)
            matrixportal.set_text(center_multiline_string("WEB OK\nPORT 80", characters_per_line), 0)
        else:
            matrixportal.set_text_color(COLOR_RED, 0)
            matrixportal.set_text(center_multiline_string(f"WEB ERR\n{web_error_message}", characters_per_line), 0)
        safe_delay(3)
    except Exception:
        pass

# --- GitHub Manifest-Based Atomic OTA Updater ---
# Manifest format expected at MANIFEST_URL:
# {
#   "version": "1.1.4",
#   "files": {
#     "code.py": "https://raw.githubusercontent.com/.../code.py",
#     "lib/adafruit_logging.py": "https://raw.githubusercontent.com/...",
#     ...
#   }
# }
def perform_ota_check(requests_session, force=False):
    if not ENABLE_OTA or not MANIFEST_URL:
        print("OTA disabled or MANIFEST_URL not set.")
        return
    if requests_session is None:
        print("OTA skipped: no network session.")
        return

    print(f"Checking for updates... Local: {LOCAL_VERSION}")

    # Display local version on matrix
    matrixportal.set_text_color(COLOR_CYAN, 0)
    matrixportal.set_text(center_multiline_string(f"LOCAL\nVERSION\n{LOCAL_VERSION}", characters_per_line), 0)
    safe_delay(2)

    # Fetch manifest with retry
    response = None
    for retry in range(3):
        w.feed()
        try:
            response = requests_session.get(MANIFEST_URL, timeout=8)
            break
        except Exception as e:
            print(f"Manifest fetch attempt {retry + 1} failed: {e}")
            if retry == 2:
                print("Could not reach GitHub. Skipping OTA.")
                return
            safe_delay(2)

    try:
        if response.status_code != 200:
            print(f"Manifest fetch returned HTTP {response.status_code}. Skipping OTA.")
            return

        # Read and close the response before parsing to free the socket first
        raw_text = response.text
        response.close()
        response = None
        w.feed()
        gc.collect()

        try:
            manifest = json.loads(raw_text)
        except Exception as parse_err:
            print(f"Manifest JSON parse failed: {parse_err}")
            print(f"Raw content (first 200 chars): {raw_text[:200]}")
            return
        finally:
            raw_text = None
            gc.collect()

        remote_version = manifest.get("version", "").strip()
        files_to_download = manifest.get("files", {})

        if not remote_version:
            print("Manifest missing 'version' field. Aborting OTA.")
            return

        print(f"Remote version: {remote_version}")

        # Display remote version on matrix
        matrixportal.set_text_color(COLOR_YELLOW, 0)
        matrixportal.set_text(center_multiline_string(f"CLOUD\nVERSION\n{remote_version}", characters_per_line), 0)
        safe_delay(2)

        if remote_version == LOCAL_VERSION and not force:
            print("Firmware is up to date!")
            matrixportal.set_text_color(COLOR_GREEN, 0)
            matrixportal.set_text(center_multiline_string("VERSION\nVERIFIED\nUP TO DATE", characters_per_line), 0)
            safe_delay(2)
            return

        # New version — download all files to .tmp paths first, then swap atomically
        print(f"Update available: {LOCAL_VERSION} -> {remote_version}")
        print(f"Downloading {len(files_to_download)} file(s)...")
        matrixportal.set_text_color(0x00FF00, 0)  # Green
        matrixportal.set_text(center_multiline_string("DOWNLOADING\nFILES...", characters_per_line), 0)

        successful_swaps = []  # List of (temp_path, final_path) tuples
        total = len(files_to_download)
        current = 0

        for local_path, remote_url in files_to_download.items():
            current += 1
            w.feed()
            print(f"  [{current}/{total}] {local_path}")

            ensure_dir_exists(local_path)
            temp_path = local_path + ".tmp"
            file_response = None

            try:
                file_response = requests_session.get(remote_url, timeout=15)
                w.feed()
                if file_response.status_code != 200:
                    raise RuntimeError(f"HTTP {file_response.status_code}")

                file_content = file_response.text
                w.feed()

                # Validate size against Content-Length if server provides it
                content_length = file_response.headers.get("content-length")
                if content_length is not None:
                    expected = int(content_length)
                    actual = len(file_content.encode("utf-8"))
                    if actual != expected:
                        raise RuntimeError(f"Size mismatch: got {actual}, expected {expected}")

                # Write to .tmp first — never touch the live file until validated
                with open(temp_path, "w") as f:
                    f.write(file_content)

                successful_swaps.append((temp_path, local_path))
                print(f"    Staged: {temp_path}")

            except OSError as fs_err:
                print(f"    Write error for {local_path}: {fs_err}")
                if local_path == "code.py":
                    matrixportal.set_text_color(0xFF0000, 0)  # Red
                    matrixportal.set_text(center_multiline_string("WRITE\nLOCKED", characters_per_line), 0)
                    safe_delay(5)
                    return
                print("    Aborting update to prevent partial state.")
                return
            except Exception as dl_err:
                print(f"    Download failed for {local_path}: {dl_err}")
                print("    Aborting update to prevent partial state.")
                return
            finally:
                if file_response is not None:
                    try:
                        file_response.close()
                    except Exception:
                        pass
                gc.collect()

        # All files downloaded and validated — now do the atomic rename swap
        print("All files staged. Applying atomic swap...")
        for temp_path, final_path in successful_swaps:
            try:
                os.remove(final_path)
            except OSError:
                pass
            os.rename(temp_path, final_path)
            print(f"    Installed: {final_path}")

        print("Update complete! Rebooting...")
        matrixportal.set_text_color(0x00FF00, 0)  # Green
        matrixportal.set_text(center_multiline_string(f"SUCCESS\nNEW:{remote_version}", characters_per_line), 0)
        safe_delay(4)
        microcontroller.reset()

    except Exception as ex:
        print(f"OTA error: {ex}")
        log_exception(ex)
    finally:
        if response is not None:
            try:
                response.close()
            except Exception:
                pass
        gc.collect()

# Run OTA check at startup — use same unverified context, no cert issues ever
perform_ota_check(requests, force=False)

# --- Boot: Show API source for 2 seconds so you can tell which server this unit uses ---
_boot_api_url = settings.get("api_url", "")
if "511ny.org" in _boot_api_url:
    _api_label = "API:\nNY511"
    _api_label_color = COLOR_GREEN
elif "workers.dev" in _boot_api_url or "cloudflare" in _boot_api_url.lower():
    _api_label = "API:\nCLOUDFLARE"
    _api_label_color = COLOR_CYAN
else:
    _api_label = "API:\nOTHER"
    _api_label_color = COLOR_AMBER
matrixportal.set_text_color(_api_label_color, 0)
matrixportal.set_text(center_multiline_string(_api_label, characters_per_line), 0)
print(f"Boot: {_api_label.replace(chr(10), ' ')}")
time.sleep(2)

# --- Boot: Show unit name for 2 seconds if configured ---
_unit_name = settings.get("unit_name", "").strip()
if _unit_name:
    matrixportal.set_text_color(COLOR_YELLOW, 0)
    matrixportal.set_text(center_multiline_string(_unit_name, characters_per_line), 0)
    print(f"Boot: Unit name = {_unit_name}")
    time.sleep(2)

# --- Shared HTML page helpers ---
VALID_COLOR_ORDERS = ["RGB", "RBG", "GRB", "GBR", "BRG", "BGR"]

def html_head(title):
    return (
        "<!DOCTYPE html><html><head>"
        "<title>" + title + "</title>"
        "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">"
        "<style>"
        "body{font-family:monospace;background:#111;color:#eee;margin:0;padding:20px;}"
        "h1{color:#ff3333;margin-top:0;}h2{color:#ffaa00;}"
        "nav{background:#1a1a1a;padding:10px 20px;margin:-20px -20px 20px -20px;"
        "border-bottom:1px solid #333;}"
        "nav a{color:#00ccff;text-decoration:none;margin-right:20px;font-size:1.1em;}"
        "nav a:hover{color:#fff;}"
        "nav a.active{color:#fff;border-bottom:2px solid #ff3333;padding-bottom:2px;}"
        ".meta{color:#888;font-size:0.85em;margin-bottom:15px;}"
        ".card{background:#1a1a1a;border:1px solid #333;border-radius:6px;"
        "padding:15px;margin-bottom:15px;}"
        "pre{background:#000;padding:15px;border-radius:5px;color:#00ff00;"
        "white-space:pre-wrap;overflow-x:auto;margin:0;}"
        "button{font-family:monospace;font-size:1em;padding:8px 18px;"
        "border:none;border-radius:4px;cursor:pointer;margin:4px;}"
        "input[type=text],input[type=number]{"
        "font-family:monospace;font-size:1em;padding:6px 10px;"
        "background:#222;color:#eee;border:1px solid #555;border-radius:4px;width:80px;}"
        "select{font-family:monospace;font-size:1em;padding:6px 10px;"
        "background:#222;color:#eee;border:1px solid #555;border-radius:4px;}"
        "label{display:inline-block;margin-bottom:6px;color:#aaa;min-width:120px;}"
        ".row{margin-bottom:10px;}"
        ".btn-red{background:#cc2222;color:#fff;}.btn-red:hover{background:#ff3333;}"
        ".btn-green{background:#226622;color:#fff;}.btn-green:hover{background:#33aa33;}"
        ".btn-blue{background:#224499;color:#fff;}.btn-blue:hover{background:#3366cc;}"
        ".btn-yellow{background:#886600;color:#fff;}.btn-yellow:hover{background:#bbaa00;}"
        ".btn-gray{background:#444;color:#fff;}.btn-gray:hover{background:#666;}"
        ".btn-cyan{background:#006666;color:#fff;}.btn-cyan:hover{background:#009999;}"
        ".status-ok{color:#33ff33;}.status-err{color:#ff3333;}"
        "table.calib{border-collapse:collapse;width:100%;margin-top:10px;}"
        "table.calib td{padding:10px;text-align:center;border:1px solid #333;vertical-align:top;width:33%;}"
        "table.calib .swatch{width:60px;height:60px;border-radius:6px;margin:0 auto 10px auto;}"
        "table.calib .color-btn{display:block;width:100%;margin:3px 0;}"
        "#sign-filter{width:100%;max-width:400px;margin-bottom:10px;padding:8px;}"
        ".sign-list{max-height:400px;overflow-y:auto;border:1px solid #333;"
        "border-radius:4px;padding:8px;background:#000;}"
        ".sign-item{padding:4px 0;border-bottom:1px solid #1a1a1a;}"
        ".sign-item label{color:#ccc;min-width:0;cursor:pointer;}"
        ".sign-item input[type=checkbox]{margin-right:8px;cursor:pointer;}"
        ".sign-item.fav label{color:#F7B500;}"
        ".color-preview{display:inline-block;width:24px;height:24px;"
        "border-radius:3px;border:1px solid #555;vertical-align:middle;margin-left:8px;}"
        "</style></head>"
    )

def html_nav(active):
    tabs = [("log","/","&#x1F4CB; Log"),
            ("settings","/settings","&#x2699;&#xFE0F; Settings"),
            ("signs","/signs","&#x1F6A6; Traffic Signs"),
            ("sync","/sync","&#x1F4E1; Sync")]
    nav = "<nav>"
    for key, href, label in tabs:
        cls = " class=\"active\"" if active == key else ""
        nav += "<a href=\"" + href + "\"" + cls + ">" + label + "</a>"
    nav += "</nav>"
    return nav

def html_meta():
    return (
        "<div class=\"meta\">Firmware: v" + LOCAL_VERSION +
        " &nbsp;|&nbsp; IP: " + str(wifi.radio.ipv4_address) +
        " &nbsp;|&nbsp; Free RAM: " + str(gc.mem_free()) + " bytes</div>"
    )

def secs_to_hms(total):
    """Convert total seconds integer to (h, m, s) tuple."""
    h = total // 3600
    m = (total % 3600) // 60
    s = total % 60
    return h, m, s

def hms_to_secs(h, m, s):
    """Convert h/m/s to total seconds, clamped to minimum 1 second."""
    total = int(h) * 3600 + int(m) * 60 + int(s)
    return max(1, total)

def parse_post_body(request):
    """Parse a URL-encoded POST body into a dict of key->value strings."""
    params = {}
    try:
        body_str = request.body.decode("utf-8") if request.body else ""
        for part in body_str.split("&"):
            if "=" in part:
                k, v = part.split("=", 1)
                params[k.strip()] = v.strip()
    except Exception as e:
        print(f"parse_post_body error: {e}")
    return params

def _parse_color_field(post_params, key, fallback):
    """Extract and validate a hex color value from POST params.
    Handles %23-encoded # and missing # prefix. Falls back to
    current settings value or the provided fallback if invalid."""
    v = post_params.get(key, settings.get(key, fallback))
    v = v.replace("%23", "#")
    if not v.startswith("#"):
        v = "#" + v
    return v if len(v) == 7 else settings.get(key, fallback)


# --- Start adafruit_httpserver if available ---
if HAS_HTTPSERVER and pool is not None:
    try:
        server = Server(pool)
        server.socket_timeout = 0.05

        # Force Connection: close on all responses so Firefox doesn't wait
        # for persistent connection data that never arrives.
        # adafruit_httpserver doesn't send Content-Length by default,
        # which causes Firefox (strict HTTP/1.1) to hang waiting for more data.
        try:
            server.headers["Connection"] = "close"
        except Exception:
            pass  # If headers API differs, not fatal — Edge will still work

        # ── GET / — Log page ──────────────────────────────────────────────
        @server.route("/", GET)
        def route_index(request):
            logs_html = (web_logger.get_logs()
                         .replace("&","&amp;").replace("<","&lt;").replace(">","&gt;"))
            log_refresh = int(settings.get("log_refresh_seconds", 5))
            # Meta refresh must go inside <head> — inject it before </head>
            refresh_meta = ('<meta http-equiv="refresh" content="' + str(log_refresh) + '">'
                           if log_refresh > 0 else "")
            head = html_head("Matrix Portal S3 - Log")
            if refresh_meta:
                head = head.replace("</head>", refresh_meta + "</head>")
            body = (
                head +
                "<body>" + html_nav("log") +
                "<h1>&#x1F6A8; Matrix Portal S3</h1>" + html_meta() +
                "<div style=\"margin-bottom:8px;color:#888;font-size:0.85em\">"
                + ("Auto-refreshing every " + str(log_refresh) + "s &nbsp;"
                   "<a href=\"/log-refresh/0\" style=\"color:#555\">Pause</a>"
                   if log_refresh > 0 else
                   "Auto-refresh paused &nbsp;"
                   "<a href=\"/log-refresh/5\" style=\"color:#00ccff\">Resume (5s)</a>")
                + "</div>"
                "<div class=\"card\"><h2>Log Output:</h2>"
                "<pre>" + logs_html + "</pre></div>"
                "</body></html>"
            )
            return Response(request, content_type="text/html", headers={"Connection":"close"}, body=body)



        # ── GET /color-test/<order> — Test a color order directly ───────
        # Sends raw yellow directly to the display with the given color_order.
        # Helps find correct order empirically — no software remapping applied.
        # Usage: navigate to /color-test/RGB, /color-test/GBR etc.
        @server.route("/color-test/<order>", GET)
        def route_color_test(request, order):
            order = order.upper()
            if order not in VALID_COLOR_ORDERS:
                order = "RGB"
            try:
                # Show raw yellow (#FFFF00) without any remapping
                matrixportal.set_text_color(0xFFFF00, 0)
                matrixportal.set_text(center_multiline_string(
                    "ORDER\n" + order + "\nYELLOW?", characters_per_line), 0)
                print(f"Color test: showing raw #FFFF00 with order={order}")
            except Exception as e:
                print(f"Color test error: {e}")
            body = (
                html_head("Color Test") +
                "<body>" + html_nav("settings") +
                "<h1>Color Order Test: " + order + "</h1>" + html_meta() +
                "<div class=\"card\">"
                "<p style=\"color:#aaa\">Displaying raw yellow (#FFFF00) on the sign. "
                "If it looks yellow, <strong>" + order + "</strong> is correct.</p>"
                "<p>Try each order:</p>"
                + "".join('<a href="/color-test/' + o + '"><button class="btn-gray" '
                          + ('style="outline:2px solid #fff"' if o == order else '') + '>'
                          + o + '</button></a> ' for o in VALID_COLOR_ORDERS) +
                "<br><br><p style=\"color:#888\">When you find the correct order, "
                "update it in Settings and save.</p>"
                "</div></body></html>"
            )
            return Response(request, content_type="text/html",
                          headers={"Connection":"close"}, body=body)

        # ── GET /log-refresh/<n> — Set log auto-refresh interval ────────
        @server.route("/log-refresh/<n>", GET)
        def route_log_refresh(request, n):
            try:
                settings["log_refresh_seconds"] = max(0, int(n))
                save_settings(settings)
            except Exception:
                pass
            return Response(request, status=(303, "See Other"),
                          headers={"Location": "/", "Connection": "close"}, body="")

        # ── GET /rebooting — Safe landing page after reboot redirect ────
        # This is a GET route so browser refresh won't re-trigger the reboot.
        # Polls the board every 2 seconds until it comes back online.
        @server.route("/rebooting", GET)
        def route_rebooting(request):
            body = (
                html_head("Rebooting...") +
                "<body>" + html_nav("log") +
                "<h1>&#x1F6A8; Rebooting...</h1>"
                "<p style=\"color:#aaa\">Board is restarting. Waiting for it to come back...</p>"
                "<p id=\"status\" style=\"color:#ffaa00\">&#x23F3; Connecting...</p>"
                "<script>"
                "function tryReconnect(){"
                "  fetch('/').then(function(r){"
                "    if(r.ok){window.location='/';}"
                "    else{setTimeout(tryReconnect,2000);}"
                "  }).catch(function(){setTimeout(tryReconnect,2000);})"
                "}"
                "setTimeout(tryReconnect,3000);"
                "</script>"
                "</body></html>"
            )
            return Response(request, content_type="text/html",
                          headers={"Connection":"close"}, body=body)

        # ── POST /reboot ──────────────────────────────────────────────────
        # Uses Post/Redirect/Get pattern:
        # 1. Send a 303 redirect to /rebooting (GET) before rebooting
        # 2. Browser follows redirect, address bar now shows /rebooting
        # 3. Board reboots — browser retries GET /rebooting harmlessly
        # 4. Page polls until board is back, then redirects to /
        # This prevents the "refresh re-submits POST and reboots again" problem.
        @server.route("/reboot", "POST")
        def route_reboot(request):
            print("Reboot requested via web UI.")
            try:
                matrixportal.set_text_color(COLOR_AMBER, 0)
                matrixportal.set_text(center_multiline_string("REBOOT\nPENDING", characters_per_line), 0)
            except Exception:
                pass
            _reboot_pending[0] = True
            return Response(request,
                          status=(303, "See Other"),
                          headers={"Location": "/rebooting", "Connection": "close"},
                          body="")

        # ── POST /identify — Flash unit name on panels so you know which sign you're looking at ─
        @server.route("/identify", "POST")
        def route_identify(request):
            _id_flash_pending[0] = True
            unit_label = settings.get("unit_name", "").strip() or "THIS\nUNIT"
            print(f"ID flash queued: {unit_label!r}")
            body = (
                html_head("Identifying...") +
                "<body>" + html_nav("settings") +
                "<h1>&#x2699;&#xFE0F; Settings</h1>" + html_meta() +
                "<div class=\"card\"><p class=\"status-ok\">"
                "&#x1F4A1; Flashing sign now &mdash; watch the panels!</p>"
                "<a href=\"/settings\"><button class=\"btn-gray\">&#x2190; Back</button></a>"
                "</div></body></html>"
            )
            return Response(request, content_type="text/html",
                            headers={"Connection": "close"}, body=body)

        # ── GET /settings ─────────────────────────────────────────────────
        @server.route("/settings", GET)
        def route_settings(request):
            cur_order = settings.get("color_order", "RGB")
            cur_color      = settings.get("sign_text_color", "#F7B500")
            cur_name_color = settings.get("sign_name_color",  "#0000FF")
            n_h, n_m, n_s = secs_to_hms(int(settings.get("name_display_seconds", 3)))
            m_h, m_m, m_s = secs_to_hms(int(settings.get("msg_display_seconds", 10)))
            p_h, p_m, p_s = secs_to_hms(int(settings.get("page_display_seconds", 5)))
            c_h, c_m, c_s = secs_to_hms(int(settings.get("cycle_sleep_seconds", 30)))
            cur_m_h, cur_m_m, cur_m_s = m_h, m_m, m_s  # Ensure always defined

            order_opts = ""
            for o in VALID_COLOR_ORDERS:
                sel = " selected" if o == cur_order else ""
                order_opts += "<option value=\"" + o + "\"" + sel + ">" + o + "</option>"

            def hms_inputs(prefix, h, m, s):
                return (
                    "<input type=\"number\" name=\"" + prefix + "_h\" value=\"" + str(h) +
                    "\" min=\"0\" max=\"23\" style=\"width:55px\"> h &nbsp;"
                    "<input type=\"number\" name=\"" + prefix + "_m\" value=\"" + str(m) +
                    "\" min=\"0\" max=\"59\" style=\"width:55px\"> m &nbsp;"
                    "<input type=\"number\" name=\"" + prefix + "_s\" value=\"" + str(s) +
                    "\" min=\"0\" max=\"59\" style=\"width:55px\"> s"
                )

            body = (
                html_head("Matrix Portal S3 - Settings") +
                "<body>" + html_nav("settings") +
                "<h1>&#x2699;&#xFE0F; Settings</h1>" + html_meta() +
                (
                "<div class=\"card\" style=\"border:2px solid #ff0000\">"
                "<p class=\"status-err\">&#x26A0; API ERROR: " + _api_error[0].replace("\n"," ") + " — "
                "Update the API URL or API Key below and save to resume.</p>"
                "</div>"
                if _api_error[0] else ""
                ) +

                # Reboot + ID flash
                "<div class=\"card\"><h2>System</h2>"
                "<form method=\"POST\" action=\"/reboot\" style=\"display:inline\">"
                "<button class=\"btn-red\" type=\"submit\">&#x1F504; Reboot Board</button>"
                "</form>"
                "&nbsp;<form method=\"POST\" action=\"/identify\" style=\"display:inline\">"
                "<button class=\"btn-yellow\" type=\"submit\">&#x1F4A1; ID This Sign</button>"
                "</form></div>"

                # All settings in one form
                "<div class=\"card\"><h2>Display Settings</h2>"
                "<form method=\"POST\" action=\"/save-settings\">"

                "<div class=\"row\"><label>Brightness:</label>"
                "<select name=\"depth\">"
                + "".join('<option value="' + str(d) + '"' +
                          (' selected' if int(settings.get("depth", 6)) == d else '') +
                          '>' + {1:"1 - Very Dim", 2:"2 - Dim", 3:"3 - Medium",
                                 4:"4 - Bright", 5:"5 - Very Bright",
                                 6:"6 - Maximum"}[d] + '</option>'
                          for d in range(1, 7)) +
                "</select>"
                "<small style=\"color:#888;margin-left:8px\">(requires reboot)</small>"
                "</div>"
                "<div class=\"row\"><label>Color Order:</label>"
                "<select name=\"color_order\">" + order_opts + "</select></div>"

                "<div class=\"row\"><label>Sign Name Color:</label>"
                "<input type=\"color\" name=\"sign_name_color\" value=\"" + cur_name_color + "\">"
                "<span class=\"color-preview\" id=\"cprev_name\" "
                "style=\"background:" + cur_name_color + "\"></span>"
                "<script>document.querySelector('[name=sign_name_color]').oninput=function(){"
                "document.getElementById('cprev_name').style.background=this.value;};</script>"
                "</div>"
                "<div class=\"row\"><label>Sign Message Color:</label>"
                "<input type=\"color\" name=\"sign_text_color\" value=\"" + cur_color + "\">"
                "<span class=\"color-preview\" id=\"cprev_text\" "
                "style=\"background:" + cur_color + "\"></span>"
                "<script>document.querySelector('[name=sign_text_color]').oninput=function(){"
                "document.getElementById('cprev_text').style.background=this.value;};</script>"
                "</div>"

                "<div class=\"row\"><label>Unit Name:</label>"
                "<input type=\"text\" name=\"unit_name\" value=\"" +
                settings.get("unit_name", "") +
                "\" style=\"width:200px;background:#222;color:#eee;border:1px solid #555;"
                "border-radius:4px;padding:5px;font-family:monospace\">"
                "<small style=\"color:#888;margin-left:8px\">Shown on LED at boot (e.g. BEDSIDE, WALL)</small>"
                "</div>"

                "<div class=\"row\"><label>API URL:</label>"
                "<input type=\"text\" name=\"api_url\" value=\"" +
                settings.get("api_url","https://511ny.org/api/getmessagesigns?format=json&key=") +
                "\" style=\"width:420px;background:#222;color:#eee;border:1px solid #555;"
                "border-radius:4px;padding:5px;font-family:monospace;font-size:0.85em\">"
                "</div>"
                "<div class=\"row\"><label>API Key:</label>"
                "<input type=\"text\" name=\"api_key\" value=\"" +
                settings.get("api_key","") +
                "\" style=\"width:280px;background:#222;color:#eee;border:1px solid #555;"
                "border-radius:4px;padding:5px;font-family:monospace\">"
                "<small style=\"color:#888;margin-left:8px\">Customer API key for your data provider</small>"
                "</div>"

                "<div class=\"row\"><label>Name display:</label>" +
                hms_inputs("name", n_h, n_m, n_s) + "</div>"

                "<div class=\"row\"><label>Page display:</label>" +
                hms_inputs("page", p_h, p_m, p_s) +
                "<small style=\"color:#888\"> &mdash; time per page for long/multi messages</small></div>"

                "<div class=\"row\"><label>Cycle interval:</label>" +
                hms_inputs("cycle", c_h, c_m, c_s) + "</div>"

                "<br><button class=\"btn-green\" type=\"submit\">&#x1F4BE; Save Settings</button>"
                "</form></div>"

                # RGB Calibration
                "<div class=\"card\"><h2>&#x1F3A8; RGB Order Calibration Wizard</h2>"
                "<p style=\"color:#aaa\">Illuminates each panel a different primary color "
                "at 20% brightness so you can identify the correct order for your hardware.</p>"
                "<form method=\"POST\" action=\"/calibrate\">"
                "<button class=\"btn-yellow\" type=\"submit\">&#x25B6; Start Calibration</button>"
                "</form></div>"

                "</body></html>"
            )
            return Response(request, content_type="text/html", headers={"Connection":"close"}, body=body)

        # ── POST /save-settings ───────────────────────────────────────────
        @server.route("/save-settings", "POST")
        def route_save_settings(request):
            global name_disp_secs, msg_disp_secs, page_disp_secs, cycle_sleep_secs
            try:
                p = parse_post_body(request)
                print("POST params: " + str(p))  # Debug — remove after confirming

                new_order = p.get("color_order", settings.get("color_order", "RGB")).upper()
                if new_order not in VALID_COLOR_ORDERS:
                    new_order = "RGB"
                new_api_url = p.get("api_url", settings.get("api_url", "")).strip()
                new_api_key = p.get("api_key", settings.get("api_key", "")).strip()
                new_unit_name = p.get("unit_name", settings.get("unit_name", "")).strip()
                # URL-decode percent-encoded characters from form submission
                for code, char in [("%3A",":"),("%2F","/"),("%3F","?"),("%3D","="),
                                   ("%26","&"),("%23","#"),("%40","@"),("%2B","+"),
                                   ("%20"," "),("%25","%")]:
                    new_api_url = new_api_url.replace(code, char).replace(code.lower(), char)
                    new_api_key = new_api_key.replace(code, char).replace(code.lower(), char)
                try:
                    new_depth = max(1, min(6, int(p.get("depth", settings.get("depth", 6)))))
                except Exception:
                    new_depth = int(settings.get("depth", 6))

                new_color      = _parse_color_field(p, "sign_text_color", "#F7B500")
                new_name_color = _parse_color_field(p, "sign_name_color",  "#0000FF")

                # Use current values as defaults so missing fields don't reset to 0
                cur_n_h, cur_n_m, cur_n_s = secs_to_hms(name_disp_secs)
                cur_m_h, cur_m_m, cur_m_s = secs_to_hms(msg_disp_secs)
                cur_c_h, cur_c_m, cur_c_s = secs_to_hms(cycle_sleep_secs)

                new_name_secs  = hms_to_secs(
                    p.get("name_h", cur_n_h), p.get("name_m", cur_n_m), p.get("name_s", cur_n_s))
                new_msg_secs   = hms_to_secs(
                    p.get("msg_h", cur_m_h),  p.get("msg_m", cur_m_m),  p.get("msg_s", cur_m_s))
                cur_p_h, cur_p_m, cur_p_s = secs_to_hms(page_disp_secs)
                new_page_secs  = hms_to_secs(
                    p.get("page_h", cur_p_h), p.get("page_m", cur_p_m), p.get("page_s", cur_p_s))
                new_cycle_secs = hms_to_secs(
                    p.get("cycle_h", cur_c_h), p.get("cycle_m", cur_c_m), p.get("cycle_s", cur_c_s))

                settings["depth"]                = new_depth
                # Clear API error flag if URL or key changed
                if new_api_url != settings.get("api_url","") or new_api_key != settings.get("api_key",""):
                    _api_error[0] = ""
                    print("API URL/key changed — clearing error flag, fetching will resume.")
                settings["api_url"]              = new_api_url
                settings["api_key"]              = new_api_key
                settings["unit_name"]            = new_unit_name
                settings["color_order"]          = new_order
                settings["sign_text_color"]       = new_color
                settings["sign_name_color"]        = new_name_color
                settings["name_display_seconds"]  = new_name_secs
                settings["msg_display_seconds"]   = new_msg_secs
                settings["page_display_seconds"]  = new_page_secs
                settings["cycle_sleep_seconds"]   = new_cycle_secs

                ok = save_settings(settings)

                # Apply non-color-order changes immediately (no reboot needed)
                name_disp_secs   = new_name_secs
                msg_disp_secs    = new_msg_secs
                page_disp_secs   = new_page_secs
                cycle_sleep_secs = new_cycle_secs
                sign_text_color[0] = color_for_display(new_color)
                sign_name_color[0] = color_for_display(new_name_color)
                matrixportal.set_text_color(sign_text_color[0], 0)
                # Rebuild NY511_URL with new api_url/api_key if changed
                global NY511_URL
                NY511_URL = new_api_url + new_api_key
                # brightness requires reboot to apply (bit_depth change)

                needs_reboot = (new_order != color_order or new_depth != int(settings.get("depth", 6)))
                if ok:
                    status = "Saved! Reboot required to apply color order or brightness change." if needs_reboot else "Saved! Settings applied."
                    cls = "status-ok"
                else:
                    status = "Save failed."
                    cls = "status-err"
                print("Settings saved: order=" + new_order
                      + " msg_color=" + new_color + " name_color=" + new_name_color
                      + " name=" + str(new_name_secs) + "s msg=" + str(new_msg_secs)
                      + "s cycle=" + str(new_cycle_secs) + "s")
            except Exception as e:
                status = "Error: " + str(e)
                cls = "status-err"
                log_exception(e)

            body = (
                html_head("Settings Saved") +
                "<body>" + html_nav("settings") +
                "<h1>&#x2699;&#xFE0F; Settings</h1>" + html_meta() +
                "<div class=\"card\"><p class=\"" + cls + "\">" + status + "</p>"
                "<a href=\"/settings\"><button class=\"btn-gray\">&#x2190; Back</button></a>"
                + ("&nbsp;<form method=\"POST\" action=\"/reboot\" style=\"display:inline\">"
                   "<button class=\"btn-red\" type=\"submit\">&#x1F504; Reboot Now</button>"
                   "</form>" if needs_reboot else "") +
                "</div></body></html>"
            )
            return Response(request, content_type="text/html", headers={"Connection":"close"}, body=body)

        # ── GET /signs — Traffic Signs page ───────────────────────────────
        @server.route("/signs", GET)
        def route_signs(request):
            query  = _signs_filter[0]
            cached = load_signs_cache()
            favs   = set(load_favorite_signs())
            w.feed()

            # Only build the full list when there's a search filter or show_all is set.
            # Loading all 937 signs takes 30-60 seconds — require a search first.
            if query == "__favorites__":
                all_items = sorted([s for s in cached if s["name"] in favs],
                                   key=lambda s: s["name"])
            elif query.startswith("__roadway__:"):
                rw = query[12:]  # strip prefix
                all_items = sorted([s for s in cached
                                    if s.get("roadway","").lower() == rw.lower()],
                                   key=lambda s: s["name"])
            elif query:
                all_items = [s for s in cached if
                             query in s["name"].lower() or
                             query in s.get("roadway", "").lower()]
            else:
                all_items = None  # Show prompt instead
            w.feed()

            if all_items is None:
                items_html = ""
                sign_count_text = str(len(cached)) + " signs cached."
                fav_count = len([s for s in cached if s["name"] in favs])

                # Build sorted unique roadway list for browser
                roadways = sorted(set(
                    s.get("roadway","").strip()
                    for s in cached
                    if s.get("roadway","").strip()
                ))
                w.feed()

                rw_items = "".join(
                    '<div class="sign-item">'
                    '<a href="/signs-roadway/' +
                    rw.replace(" ","+").replace("/","%2F").replace("&","%26") +
                    '" style="color:#eee;text-decoration:none">'
                    '&#x1F6A6; ' + rw + '</a>'
                    '</div>'
                    for rw in roadways
                )
                w.feed()

                list_section = (
                    '<p style="color:#aaa">You have '
                    '<strong style="color:#F7B500">' + str(fav_count) + ' favorites</strong> saved. '
                    'Search by name/roadway above, browse by roadway below, '
                    'or view your favorites.</p>'
                    '<a href="/signs-favorites"><button class="btn-cyan">&#x2B50; My Favorites</button></a>'
                    '<br><br>'
                    '<div style="color:#ffaa00;font-weight:bold;margin-bottom:8px">'
                    '&#x1F6A6; Browse by Roadway</div>'
                    '<div class="sign-list">' + rw_items + '</div>'
                )
                breadcrumb = ""  # No breadcrumb on home view
            else:
                items_parts = []
                for i, sign in enumerate(all_items):
                    if i % 50 == 0:
                        w.feed()
                    name     = sign["name"]
                    checked  = " checked" if name in favs else ""
                    fav_cls  = " fav" if name in favs else ""
                    safe_name = (name.replace("&","&amp;").replace("<","&lt;")
                                     .replace(">","&gt;").replace('"',"&quot;"))
                    msgs = sign.get("messages", [])
                    if msgs:
                        tip = str(msgs[0]).replace('"',"'")[:150]
                    else:
                        tip = "No message"
                    roadway = sign.get("roadway", "")
                    roadway_html = ('<div style="color:#555;font-size:0.78em;padding-left:22px;'
                                    'margin-top:-2px">' + roadway + '</div>' if roadway else "")
                    items_parts.append(
                        '<div class="sign-item' + fav_cls + '" title="' + tip + '">'
                        '<label><input type="checkbox" name="fav" value="' +
                        safe_name + '"' + checked + '> ' + safe_name + '</label>'
                        + roadway_html + '</div>'
                    )
                items_html = "".join(items_parts)
                items_parts = None
                w.feed()
                gc.collect()
                if query.startswith("__roadway__:"):
                    sign_count_text = (str(len(all_items)) + " signs on " +
                                      query[12:] + ".")
                elif query == "__favorites__":
                    sign_count_text = str(len(all_items)) + " favorite signs."
                else:
                    sign_count_text = str(len(all_items)) + " signs shown."

                # Breadcrumb trail
                crumb_base = '<a href="/signs" style="color:#00ccff">&#x1F6A6; Traffic Signs</a>'
                if query.startswith("__roadway__:"):
                    rw_name = query[12:]
                    breadcrumb = (
                        '<div style="font-size:0.85em;color:#888;margin-bottom:10px;padding:6px 0;'
                        'border-bottom:1px solid #222">'
                        + crumb_base +
                        ' <span style="color:#555">&rsaquo;</span> '
                        '<span style="color:#ffaa00">' + rw_name + '</span>'
                        '</div>'
                    )
                elif query == "__favorites__":
                    breadcrumb = (
                        '<div style="font-size:0.85em;color:#888;margin-bottom:10px;padding:6px 0;'
                        'border-bottom:1px solid #222">'
                        + crumb_base +
                        ' <span style="color:#555">&rsaquo;</span> '
                        '<span style="color:#ffaa00">&#x2B50; My Favorites</span>'
                        '</div>'
                    )
                elif query:
                    breadcrumb = (
                        '<div style="font-size:0.85em;color:#888;margin-bottom:10px;padding:6px 0;'
                        'border-bottom:1px solid #222">'
                        + crumb_base +
                        ' <span style="color:#555">&rsaquo;</span> '
                        '<span style="color:#ffaa00">Search: &ldquo;' + query + '&rdquo;</span>'
                        '</div>'
                    )
                else:
                    breadcrumb = ""
                back_btn = ""  # Replaced by breadcrumb
                list_section = (
                    breadcrumb +
                    '<form method="POST" action="/save-signs">'
                    '<div class="sign-list" id="signlist">' + items_html + '</div><br>'
                    '<button class="btn-green" type="submit">&#x1F4BE; Save Favorites</button>'
                    '</form>'
                )

            body = (
                html_head("Traffic Signs") +
                "<body>" + html_nav("signs") +
                "<h1>&#x1F6A6; Traffic Signs</h1>" + html_meta() +
                '<div class="card">'
                '<form method="POST" action="/refresh-signs-cache" style="display:inline">'
                '<button class="btn-cyan" type="submit">&#x1F504; Refresh from NY511</button>'
                '</form>'
                '<span style="color:#888;margin-left:15px;font-size:0.9em">'
                'Fetches ~930 signs. Takes up to 90 seconds.</span>'
                '</div>'
                '<div class="card">' +
                ('<p style="color:#aaa">' + sign_count_text +
                 ' Favorites in <span style="color:#F7B500">yellow</span>. '
                 'Hover a sign name to see its messages.</p>'
                 if cached else
                 '<p style="color:#aaa">No sign cache. Click Refresh to load from NY511.</p>') +
                '<form method="POST" action="/signs-search">'
                '<input type="text" name="q" value="' + (query if not query.startswith("__") else "") + '" '
                'placeholder="Search by sign name or roadway..." autocomplete="off" '
                'style="width:100%;margin-bottom:8px;padding:8px;background:#222;'
                'color:#eee;border:1px solid #555;border-radius:4px;font-family:monospace;">'
                '<button class="btn-gray" type="submit">&#x1F50D; Search</button>'
                ' <a href="/signs-clear"><button class="btn-gray" type="button">&#x2715; Clear</button></a>'
                '</form><br>'
                + (('<div style="margin-bottom:8px">'
                '<button class="btn-gray" type="button" onclick="selectAll()">&#x2611; Select All</button>'
                ' <button class="btn-gray" type="button" onclick="deselectAll()">&#x2610; Deselect All</button>'
                '</div>'
                '<script>'
                'function selectAll(){'
                'document.querySelectorAll("#signlist input[type=checkbox]")'
                '.forEach(function(b){b.checked=true;});}'
                'function deselectAll(){'
                'document.querySelectorAll("#signlist input[type=checkbox]")'
                '.forEach(function(b){b.checked=false;});}'
                '</script>') if all_items is not None else "") +
                list_section +
                '</div></body></html>'
            )
            w.feed()
            return Response(request, content_type="text/html", headers={"Connection":"close"}, body=body)

        # ── GET /signs-clear — Clear the search filter ────────────────────
        @server.route("/signs-clear", GET)
        def route_signs_clear(request):
            _signs_filter[0] = ""
            _signs_show_all[0] = False  # Don't auto-load full list
            return Response(request, status=(303, "See Other"),
                          headers={"Location": "/signs", "Connection": "close"},
                          body="")

        # ── GET /signs-roadway/<rw> — Browse signs on a specific roadway ──
        @server.route("/signs-roadway/<rw>", GET)
        def route_signs_roadway(request, rw):
            # URL-decode the roadway name
            roadway = rw.replace("+", " ")
            for code, char in [("%2F","/"),("%26","&"),("%2D","-"),
                                ("%28","("),("%29",")"),("%2C",",")]:
                roadway = roadway.replace(code, char).replace(code.lower(), char)
            _signs_filter[0] = "__roadway__:" + roadway
            return Response(request, status=(303, "See Other"),
                          headers={"Location": "/signs", "Connection": "close"},
                          body="")

        # ── GET /signs-favorites — Show only favorited signs ─────────────
        @server.route("/signs-favorites", GET)
        def route_signs_favorites(request):
            _signs_filter[0]   = "__favorites__"
            _signs_show_all[0] = False
            return Response(request, status=(303, "See Other"),
                          headers={"Location": "/signs", "Connection": "close"},
                          body="")

        # ── POST /signs-search — Set filter and redirect to /signs ────────
        @server.route("/signs-search", "POST")
        def route_signs_search(request):
            p = parse_post_body(request)
            q = p.get("q", "").strip().lower()
            _signs_filter[0]   = q
            return Response(request, status=(303, "See Other"),
                          headers={"Location": "/signs", "Connection": "close"},
                          body="")

                # ── POST /refresh-signs-cache — Queue a NY511 cache refresh ────────
        # Returns immediately to the browser to avoid watchdog timeout.
        # The actual fetch is done by the main loop on the next cycle.
        @server.route("/refresh-signs-cache", "POST")
        def route_refresh_cache(request):
            _refresh_cache_pending[0] = True
            print("NY511 cache refresh queued — will run on next main loop cycle.")
            body = (
                html_head("Refreshing Signs...") +
                "<body>" + html_nav("signs") +
                "<h1>&#x1F6A6; Traffic Signs</h1>" + html_meta() +
                "<div class=\"card\">"
                "<p style=\"color:#ffaa00\">&#x23F3; Fetching signs from NY511...</p>"
                "<p style=\"color:#aaa\">This takes up to 90 seconds. "
                "The page will redirect automatically when done.</p>"
                "<script>setTimeout(function(){window.location='/signs'},95000);</script>"
                "</div></body></html>"
            )
            return Response(request, content_type="text/html", headers={"Connection":"close"}, body=body)

        # ── POST /save-signs — Save favorite selections ──────────────────
        @server.route("/save-signs", "POST")
        def route_save_signs(request):
            global favsign_list
            try:
                body_str = request.body.decode("utf-8") if request.body else ""
                selected = []
                for part in body_str.split("&"):
                    if part.startswith("fav="):
                        name = part[4:]
                        name = name.replace("+", " ")
                        # Full percent-decode covering all chars used in sign names
                        pct_map = [
                            ("%2C",","),("%28","("),("%29",")"),("%2F","/"),
                            ("%3A",":"),("%5B","["),("%5D","]"),("%2D","-"),
                            ("%2E","."),("%27","'"),("%21","!"),("%40","@"),
                            ("%23","#"),("%24","$"),("%26","&"),("%3D","="),
                            ("%3F","?"),("%20"," "),("%25","%"),
                        ]
                        for code, char in pct_map:
                            name = name.replace(code, char).replace(
                                code.lower(), char)
                        if name:
                            selected.append(name)
                ok = save_favorite_signs(selected)
                favsign_list = selected  # Update live list immediately
                status = "Saved " + str(len(selected)) + " favorite sign(s)."
                cls = "status-ok" if ok else "status-err"
                print(f"Favorites saved: {len(selected)} signs ok={ok}")
            except Exception as e:
                status = "Error: " + str(e)
                cls = "status-err"
                log_exception(e)

            body = (
                html_head("Signs Saved") +
                "<body>" + html_nav("signs") +
                "<h1>&#x1F6A6; Traffic Signs</h1>" + html_meta() +
                "<div class=\"card\"><p class=\"" + cls + "\">" + status + "</p>"
                "<a href=\"/signs\"><button class=\"btn-gray\">&#x2190; Back to Signs</button></a>"
                "</div></body></html>"
            )
            return Response(request, content_type="text/html", headers={"Connection":"close"}, body=body)

        # ── POST /calibrate — Light panels with numbers, show color picker ──
        @server.route("/calibrate", "POST")
        def route_calibrate(request):
            global _calib_state
            _calib_state["active"] = True

            # Calibration ONLY works correctly when color_order is RGB.
            # Read from settings dict (always current) not the module-level
            # color_order variable which may be stale after a settings save.
            current_order = settings.get("color_order", "RGB")
            calib_needs_reset = (current_order != "RGB")
            print(f"Calibration: current color_order={current_order} needs_reset={calib_needs_reset}")
            if calib_needs_reset:
                settings["color_order"] = "RGB"
                save_settings(settings)
                print("Calibration: temporarily set color_order=RGB for accurate test.")
                print("Board must reboot to apply — rebooting now.")
                body = (
                    html_head("Calibration — Rebooting...") +
                    "<body>" + html_nav("settings") +
                    "<h1>&#x1F3A8; RGB Calibration</h1>" + html_meta() +
                    "<div class=\"card\">"
                    "<p style=\"color:#ffaa00\"><strong>Rebooting with neutral color order...</strong></p>"
                    "<p style=\"color:#aaa\">The board is restarting. This page will automatically "
                    "redirect to calibration when the board is back online.</p>"
                    "<p id=\"status\" style=\"color:#888\">&#x23F3; Waiting for board...</p>"
                    "<script>"
                    "function tryReconnect(){"
                    "  fetch('/').then(function(r){"
                    "    if(r.ok){window.location='/settings';}"
                    "    else{setTimeout(tryReconnect,2000);}"
                    "  }).catch(function(){setTimeout(tryReconnect,2000);})"
                    "}"
                    "setTimeout(tryReconnect,6000);"
                    "</script>"
                    "</div></body></html>"
                )
                # Set flag — main loop handles the actual reboot after response flushes
                _reboot_pending[0] = True
                return Response(request, content_type="text/html",
                              headers={"Connection":"close"}, body=body)
            try:
                import displayio

                # 5x7 pixel digit bitmaps for 1, 2, 3
                # Each is a list of (col, row) pixel offsets to SET (foreground)
                DIGITS = {
                    "1": [(2,0),(1,1),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)],
                    "2": [(1,0),(2,0),(3,0),(0,1),(3,1),(3,2),(2,3),(1,4),(0,5),(0,6),(1,6),(2,6),(3,6)],
                    "3": [(0,0),(1,0),(2,0),(3,0),(3,1),(3,2),(1,2),(2,2),(3,3),(3,4),(0,5),(3,5),(1,6),(2,6)],
                }

                display = matrixportal.display
                panel_w = width // 3

                # 4 palette entries: bg colors + white for digit
                # 0=dim red, 1=dim green, 2=dim blue, 3=white digit
                bmp = displayio.Bitmap(width, height, 4)
                pal = displayio.Palette(4)
                pal[0] = 0x330000  # dim red   — panel 1
                pal[1] = 0x003300  # dim green — panel 2
                pal[2] = 0x000033  # dim blue  — panel 3
                pal[3] = 0x555555  # dim white — digit pixels (20% brightness)

                # Fill panel background colors
                for y in range(height):
                    for x in range(width):
                        bmp[x, y] = 0 if x < panel_w else (1 if x < panel_w * 2 else 2)

                # Draw digit for each panel, centered within that panel
                for panel_idx, digit in enumerate(["1", "2", "3"]):
                    panel_start_x = panel_idx * panel_w
                    # Center the 5x7 digit within the 64x32 panel
                    digit_x = panel_start_x + (panel_w - 5) // 2
                    digit_y = (height - 7) // 2
                    for (dx, dy) in DIGITS[digit]:
                        px = digit_x + dx
                        py = digit_y + dy
                        if 0 <= px < width and 0 <= py < height:
                            bmp[px, py] = 3  # white digit pixel

                tg = displayio.TileGrid(bmp, pixel_shader=pal)
                splash = displayio.Group()
                splash.append(tg)
                display.root_group = splash
                w.feed()
            except Exception as disp_err:
                print(f"Calibration display error: {disp_err}")
                log_exception(disp_err)

            # Web UI — panels now labeled P1/P2/P3 to match numbers on display
            rows = ""
            panels = [("P1","330000","1"),("P2","003300","2"),("P3","000033","3")]
            for name, swatch, num in panels:
                btns = ""
                for c, lbl, cls in [("R","Red","btn-red"),("G","Green","btn-green"),("B","Blue","btn-blue")]:
                    btns += (
                        "<button class=\"" + cls + " color-btn\" type=\"button\" "
                        "onclick=\"pick('" + name + "','" + c + "',this)\">" + lbl + "</button>"
                    )
                rows += (
                    "<td>"
                    "<div class=\"swatch\" style=\"background:#" + swatch + ";"
                    "font-size:28px;font-weight:bold;color:#aaa;line-height:60px;\">" + num + "</div>"
                    "<strong>Panel " + num + "</strong><br>"
                    "<small style=\"color:#ffaa00\">What color do you see?</small><br><br>"
                    + btns +
                    "<div id=\"sel_" + name + "\" style=\"margin-top:6px;color:#ffaa00;\"></div></td>"
                )

            body = (
                html_head("RGB Calibration") +
                "<body>" + html_nav("settings") +
                "<h1>&#x1F3A8; RGB Calibration</h1>" + html_meta() +
                "<div class=\"card\">"
                "<p style=\"color:#aaa\">Your display shows 3 panels each lit a different "
                "dim color, numbered 1, 2, and 3.</p>"
                "<p style=\"color:#ffaa00\"><strong>For each panel number below, click the "
                "color you see glowing on your physical display for that panel.</strong><br>"
                "Do not click what you expect to see — click only what you actually see.</p>"
                "<form method=\"POST\" action=\"/calibrate-result\" id=\"calform\">"
                "<input type=\"hidden\" name=\"p1\" id=\"v_P1\">"
                "<input type=\"hidden\" name=\"p2\" id=\"v_P2\">"
                "<input type=\"hidden\" name=\"p3\" id=\"v_P3\">"
                "<table class=\"calib\"><tr>" + rows + "</tr></table><br>"
                "<button class=\"btn-green\" type=\"submit\" id=\"applybtn\" disabled "
                "style=\"font-size:1.1em;padding:10px 30px;\">&#x2713; Apply Color Order</button>"
                "<a href=\"/calibrate-cancel\"><button class=\"btn-gray\" type=\"button\" "
                "style=\"margin-left:10px;\">Cancel</button></a>"
                "</form></div>"
                "<script>"
                "var picks={};"
                "function pick(panel,color,btn){"
                "picks[panel]=color;"
                "document.getElementById('v_'+panel).value=color;"
                "var cell=btn.parentNode;"
                "var btns=cell.querySelectorAll('button');"
                "for(var i=0;i<btns.length;i++){btns[i].style.opacity='0.4';}"
                "btn.style.opacity='1';btn.style.outline='2px solid #fff';"
                "document.getElementById('sel_'+panel).textContent='Selected: '+color;"
                "if(picks['P1']&&picks['P2']&&picks['P3']){"
                "document.getElementById('applybtn').disabled=false;}}"
                "</script>"
                "</body></html>"
            )
            return Response(request, content_type="text/html", headers={"Connection":"close"}, body=body)

        # ── GET /calibrate-cancel — Restore display and go back to settings ─
        @server.route("/calibrate-cancel", GET)
        def route_calibrate_cancel(request):
            global _calib_state
            _calib_state["active"] = False
            try:
                matrixportal.display.root_group = matrixportal.splash
                print("Calibration cancelled — display restored.")
            except Exception as e:
                print(f"Display restore error: {e}")
            body = (
                html_head("Calibration Cancelled") +
                "<body>" + html_nav("settings") +
                "<h1>&#x2699;&#xFE0F; Settings</h1>" + html_meta() +
                "<div class=\"card\"><p style=\"color:#aaa\">Calibration cancelled. Display restored.</p>"
                "<a href=\"/settings\"><button class=\"btn-gray\">&#x2190; Back to Settings</button></a>"
                "</div></body></html>"
            )
            return Response(request, content_type="text/html",
                          headers={"Connection":"close"}, body=body)

        # ── POST /calibrate-result ────────────────────────────────────────
        @server.route("/calibrate-result", "POST")
        def route_calibrate_result(request):
            global _calib_state
            _calib_state["active"] = False
            try:
                matrixportal.display.root_group = matrixportal.splash
            except Exception:
                pass
            try:
                p = parse_post_body(request)
                print("Calibration POST body: " + str(p))  # Debug
                p1 = p.get("p1", "R").upper()
                p2 = p.get("p2", "G").upper()
                p3 = p.get("p3", "B").upper()
                print(f"Calibration: P1={p1} P2={p2} P3={p3}")
                # Board sent P1=R, P2=G, P3=B.
                # User reports what they see on each numbered panel.
                # Concatenating gives the correct color_order string.
                order_str = p1 + p2 + p3
                if order_str not in VALID_COLOR_ORDERS:
                    raise ValueError("Invalid order: " + order_str)
                settings["color_order"] = order_str
                ok = save_settings(settings)
                print(f"Calibration: P1={p1} P2={p2} P3={p3} -> {order_str} saved={ok}")
                status = ("Color order set to <strong>" + order_str + "</strong>. " +
                          ("Saved! Reboot to apply." if ok else "Save failed."))
                cls = "status-ok" if ok else "status-err"
            except Exception as e:
                status = "Calibration error: " + str(e)
                cls = "status-err"
                log_exception(e)

            body = (
                html_head("Calibration Complete") +
                "<body>" + html_nav("settings") +
                "<h1>&#x1F3A8; Calibration Complete</h1>" + html_meta() +
                "<div class=\"card\"><p class=\"" + cls + "\">" + status + "</p>"
                "<a href=\"/settings\"><button class=\"btn-gray\">&#x2190; Back to Settings</button></a>"
                "&nbsp;<form method=\"POST\" action=\"/reboot\" style=\"display:inline\">"
                "<button class=\"btn-red\" type=\"submit\">&#x1F504; Reboot Now</button>"
                "</form></div></body></html>"
            )
            return Response(request, content_type="text/html", headers={"Connection":"close"}, body=body)

        # ── GET /export-settings — Serve settings bundle for sync ───────
        @server.route("/export-settings", GET)
        def route_export_settings(request):
            try:
                with open(SETTINGS_FILE, "r") as f:
                    settings_data = f.read()
            except Exception:
                settings_data = "{}"
            try:
                with open(SIGNS_FILE, "r") as f:
                    signs_data = f.read()
            except Exception:
                signs_data = '{"favorites":[]}'
            bundle = json.dumps({
                "settings": json.loads(settings_data),
                "signs":    json.loads(signs_data),
                "source_ip": str(wifi.radio.ipv4_address),
                "source_version": LOCAL_VERSION
            })
            print(f"Export requested by {request.client_address}")
            return Response(request, content_type="application/json",
                          headers={"Connection":"close"}, body=bundle)

        # ── GET /sync — Sync UI page ──────────────────────────────────────
        @server.route("/sync", GET)
        def route_sync_page(request):
            body = (
                html_head("Matrix Portal S3 - Sync") +
                "<body>" + html_nav("sync") +
                "<h1>&#x1F4E1; Sync from Another Unit</h1>" + html_meta() +
                "<div class=\"card\">"
                "<p style=\"color:#aaa\">Enter the IP address of the source unit "
                "and select which files to sync. Your current files will be overwritten.</p>"
                "<form method=\"POST\" action=\"/sync-from\">"
                "<div class=\"row\">"
                "<label>Source IP:</label>"
                "<input type=\"text\" name=\"source_ip\" placeholder=\"192.168.x.x\" "
                "style=\"width:160px\" required>"
                "</div><br>"
                "<div class=\"row\">"
                "<label style=\"min-width:0\">"
                "<input type=\"checkbox\" name=\"sync_settings\" value=\"1\" checked> "
                "Sync <strong>settings.json</strong> "
                "<span style=\"color:#888\">(color, timing, display settings)</span>"
                "</label>"
                "</div>"
                "<div class=\"row\" style=\"margin-top:8px\">"
                "<label style=\"min-width:0\">"
                "<input type=\"checkbox\" name=\"sync_signs\" value=\"1\" checked> "
                "Sync <strong>signs.json</strong> "
                "<span style=\"color:#888\">(favorite sign list)</span>"
                "</label>"
                "</div><br>"
                "<button class=\"btn-cyan\" type=\"submit\">&#x1F4E1; Sync Now</button>"
                "</form></div>"
                "<div class=\"card\">"
                "<h2>Export This Unit</h2>"
                "<p style=\"color:#aaa\">Other units can sync from this one at:</p>"
                "<p><strong style=\"color:#00ccff\">http://" + str(wifi.radio.ipv4_address) + "/export-settings</strong></p>"
                "</div>"
                "</body></html>"
            )
            return Response(request, content_type="text/html",
                          headers={"Connection":"close"}, body=body)

        # ── POST /sync-from — Fetch and apply settings from another unit ──
        @server.route("/sync-from", "POST")
        def route_sync_from(request):
            p = parse_post_body(request)
            source_ip = p.get("source_ip", "").strip()
            do_settings = p.get("sync_settings", "") == "1"
            do_signs    = p.get("sync_signs", "")    == "1"

            if not source_ip:
                body = (html_head("Sync Error") + "<body>" + html_nav("sync") +
                        "<h1>&#x1F4E1; Sync</h1>" + html_meta() +
                        "<div class=\"card\"><p class=\"status-err\">No source IP provided.</p>"
                        "<a href=\"/sync\"><button class=\"btn-gray\">&#x2190; Back</button></a>"
                        "</div></body></html>")
                return Response(request, content_type="text/html",
                              headers={"Connection":"close"}, body=body)

            print(f"Sync requested from {source_ip} settings={do_settings} signs={do_signs}")
            matrixportal.set_text_color(0x00FFFF, 0)
            matrixportal.set_text(center_multiline_string("SYNCING\nFROM\n" + source_ip, characters_per_line), 0)
            w.feed()

            status_lines = []
            cls = "status-ok"
            sync_resp = None
            try:
                url = "http://" + source_ip + "/export-settings"
                sync_resp = requests.get(url, timeout=10)
                w.feed()
                if sync_resp.status_code != 200:
                    raise RuntimeError("HTTP " + str(sync_resp.status_code))

                bundle = json.loads(sync_resp.text)
                sync_resp.close()
                sync_resp = None
                w.feed()

                source_ver = bundle.get("source_version", "?")
                status_lines.append("Connected to v" + source_ver + " at " + source_ip)

                if do_settings and "settings" in bundle:
                    ok = save_settings(bundle["settings"])
                    if ok:
                        # Reload settings into memory
                        loaded = load_settings()
                        settings.update(loaded)
                        sign_text_color[0] = color_for_display(settings.get("sign_text_color","#F7B500"))
                        sign_name_color[0] = color_for_display(settings.get("sign_name_color","#0000FF"))
                        matrixportal.set_text_color(sign_text_color[0], 0)
                        status_lines.append("&#x2713; settings.json synced")
                    else:
                        status_lines.append("&#x2717; settings.json save failed")
                        cls = "status-err"

                if do_signs and "signs" in bundle:
                    ok = save_favorite_signs(bundle["signs"].get("favorites", []))
                    if ok:
                        favsign_list.clear()
                        favsign_list.extend(bundle["signs"].get("favorites", []))
                        status_lines.append("&#x2713; signs.json synced ("
                                           + str(len(favsign_list)) + " favorites)")
                    else:
                        status_lines.append("&#x2717; signs.json save failed")
                        cls = "status-err"

                if not do_settings and not do_signs:
                    status_lines.append("Nothing selected to sync.")
                    cls = "status-err"

            except Exception as e:
                status_lines.append("Sync error: " + str(e))
                cls = "status-err"
                log_exception(e)
            finally:
                if sync_resp is not None:
                    try:
                        sync_resp.close()
                    except Exception:
                        pass
                gc.collect()

            matrixportal.set_text_color(sign_text_color[0], 0)
            matrixportal.set_text("", 0)

            status_html = "<br>".join(status_lines)
            body = (
                html_head("Sync Complete") +
                "<body>" + html_nav("sync") +
                "<h1>&#x1F4E1; Sync</h1>" + html_meta() +
                "<div class=\"card\"><p class=\"" + cls + "\">" + status_html + "</p>"
                "<a href=\"/sync\"><button class=\"btn-gray\">&#x2190; Back to Sync</button></a>"
                "&nbsp;<form method=\"POST\" action=\"/reboot\" style=\"display:inline\">"
                "<button class=\"btn-red\" type=\"submit\">&#x1F504; Reboot to Apply</button>"
                "</form></div></body></html>"
            )
            return Response(request, content_type="text/html",
                          headers={"Connection":"close"}, body=body)

        server.start("0.0.0.0", port=80)
        print(f"Web server active at http://{wifi.radio.ipv4_address}/")
    except Exception as e:
        print(f"Web server start failed: {e}")
        log_exception(e)
        HAS_HTTPSERVER = False

# --- Load Favorite Signs List ---
favsign_list = load_favorite_signs()
if favsign_list:
    print(f"Loaded {len(favsign_list)} favorite sign(s) from signs.json.")
else:
    print("No favorite signs loaded (signs.json missing or empty).")
    print("Visit the Traffic Signs tab on the web UI to select signs.")

# --- Main Loop ---
cycles = 0
w.feed()

while True:
    cycles += 1
    print(f"\n{'*' * 48}")
    print(f"Cycle #{cycles}  Free RAM: {gc.mem_free()} bytes")
    print(f"{'*' * 48}")
    w.feed()
    gc.collect()

    # Recreate the requests session every cycle to flush SSL/socket buffers.
    # The first HTTPS request accumulates ~800KB of SSL state that doesn't
    # fully release. Recreating each cycle keeps memory stable.
    if cycles > 1 and pool is not None:
        try:
            ssl_context = ssl.create_default_context()
            try:
                ssl_context.load_verify_locations(cadata="")
            except Exception:
                pass
            requests = adafruit_requests.Session(pool, ssl_context)
            gc.collect()
        except Exception as _sess_err:
            print(f"Session refresh failed: {_sess_err}")

    # Handle pending sign cache refresh (queued by web UI)
    if _reboot_pending[0]:
        _reboot_pending[0] = False
        print("Rebooting as requested by web UI...")
        time.sleep(0.5)  # Let any in-flight TCP data finish
        import supervisor
        supervisor.reload()

    if _refresh_cache_pending[0]:
        _refresh_cache_pending[0] = False
        if wifi.radio.connected and requests is not None:
            refresh_signs_cache_from_api()
            # Recreate session after cache refresh to flush SSL state before
            # the regular fetch. Also skip the regular fetch this cycle since
            # we just pulled all sign data from the API anyway.
            try:
                requests = adafruit_requests.Session(pool, ssl_context)
                gc.collect()
                gc.collect()
            except Exception:
                pass
            print("Cache refresh complete — skipping regular fetch this cycle.")
            safe_delay(cycle_sleep_secs)
            continue
        else:
            print("Cache refresh skipped — no network.")

    # Handle ID flash request — alternates colors on the display so you know which unit this is
    if _id_flash_pending[0]:
        _id_flash_pending[0] = False
        unit_label = settings.get("unit_name", "").strip() or "THIS\nUNIT"
        print(f"ID flash: displaying {unit_label!r}")
        flash_colors = [COLOR_YELLOW, COLOR_CYAN, COLOR_GREEN, COLOR_AMBER, COLOR_RED,
                        COLOR_YELLOW, COLOR_CYAN, COLOR_GREEN, COLOR_AMBER, COLOR_RED]
        for fc in flash_colors:
            w.feed()
            matrixportal.set_text_color(fc, 0)
            matrixportal.set_text(center_multiline_string(unit_label, characters_per_line), 0)
            time.sleep(0.4)
        # Restore display to blank so main loop resumes normally
        matrixportal.set_text("", 0)
        print("ID flash complete.")

    # Reconnect WiFi if dropped
    if not wifi.radio.connected:
        print("WiFi dropped. Reconnecting...")
        if not connect_wifi():
            print("Reconnect failed. Retrying in 10s...")
            safe_delay(10)
            continue

    # Check for API error flag — stop fetching until URL/key is fixed or rebooted
    if _api_error[0]:
        matrixportal.set_text_color(COLOR_RED, 0)
        matrixportal.set_text(center_multiline_string(_api_error[0], characters_per_line), 0)
        safe_delay(cycle_sleep_secs)
        continue

    # Fetch NY511 API data
    print("Fetching NY511 API data...")
    response = None
    json_data = None
    matched_signs = []  # Only store the signs we actually need to display
    try:
        poll_server()  # Service web requests before API fetch

        # Poll rapidly while waiting for API response — this is the longest
        # blocking call and most likely time for a browser to connect
        _fetch_done = [False]
        response = requests.get(NY511_URL, timeout=15)
        w.feed()

        # Drain any pending web requests immediately after fetch completes
        for _ in range(5):
            poll_server()
        gc.collect()

        if response.status_code == 401 or response.status_code == 403:
            # Bad API key — set error flag and stop fetching
            _api_error[0] = "BAD\nAPI KEY"
            print(f"API rejected key: HTTP {response.status_code}. Stopping fetches.")
            matrixportal.set_text_color(COLOR_RED, 0)
            matrixportal.set_text(center_multiline_string("BAD\nAPI KEY", characters_per_line), 0)
            try:
                response.close()
            except Exception:
                pass
            response = None
            safe_delay(cycle_sleep_secs)
            continue

        if response.status_code == 404:
            # Bad URL
            _api_error[0] = "BAD\nAPI URL"
            print(f"API URL not found: HTTP 404. Stopping fetches.")
            matrixportal.set_text_color(COLOR_RED, 0)
            matrixportal.set_text(center_multiline_string("BAD\nAPI URL", characters_per_line), 0)
            try:
                response.close()
            except Exception:
                pass
            response = None
            safe_delay(cycle_sleep_secs)
            continue

        if response.status_code == 200:
            print("API fetch successful. Parsing JSON...")
            json_data = response.json()
            w.feed()

            # Close response immediately after parsing to free socket buffer RAM
            try:
                response.close()
            except Exception:
                pass
            response = None

            poll_server()  # Service web requests after JSON parse

            if isinstance(json_data, list):
                sign_count = len(json_data)
                print(f"Loaded {sign_count} signs from API.")
                print("Extracting favorites...")

                # Extract only matching signs into a small list, then free the full dataset
                fav_set = set(favsign_list)
                for sign in json_data:
                    if "Name" in sign and "Messages" in sign and sign["Name"] in fav_set:
                        matched_signs.append({
                            "name": sign["Name"],
                            "msg": sign["Messages"]
                        })

                # Free the full 928-sign JSON list NOW before display loops
                json_data = None
                gc.collect()
                gc.collect()  # Double-collect — CircuitPython sometimes needs two passes
                print(f"Matched {len(matched_signs)} sign(s). Free RAM after GC: {gc.mem_free()}")

                poll_server()  # Service web requests before display loop

                for match in matched_signs:
                    if _reboot_pending[0]:
                        break  # Reboot requested — stop cycling signs immediately
                    w.feed()
                    print(f"\nMATCH: {match['name']}")
                    display_sign(match, name_disp_secs, page_disp_secs)
            else:
                print(f"Unexpected API response type: {type(json_data)}")
        else:
            print(f"API returned HTTP {response.status_code}")

    except Exception as e:
        print(f"API/display error: {e}")
        log_exception(e)
    finally:
        if response is not None:
            try:
                response.close()
            except Exception:
                pass
        json_data = None
        matched_signs = None
        gc.collect()
        gc.collect()
        gc.collect()  # Three passes — SSL buffers sometimes need extra cycles

    print(f"Cycle complete. RAM: {gc.mem_free()} bytes. Waiting {cycle_sleep_secs}s...")
    safe_delay(cycle_sleep_secs)

