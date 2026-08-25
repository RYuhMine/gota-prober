#!/usr/bin/env python3
# GOTA Prober, held under The GPLv2 License, made by RYuh

import sys
import os
import re
import gzip
import urllib.request
import urllib.error
import json
import io
import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, filedialog
from tkinter import font as tkfont
import threading
from datetime import datetime
import webbrowser
import queue
import time
import ssl
import http.client
from urllib.parse import urlparse, urlencode
import struct
import zlib
import base64
import concurrent.futures
import itertools as _itertools

try:
    from Crypto.Cipher import AES
    from Crypto.Util.Padding import pad, unpad
    XIAOMI_CRYPTO_AVAILABLE = True
except ImportError:
    XIAOMI_CRYPTO_AVAILABLE = False

try:
    from tkinterweb import HtmlFrame
    from tkinterweb import Notebook as TkwNotebook
except ImportError:
    HtmlFrame = None
    TkwNotebook = None

NOTEBOOK_CLS = TkwNotebook if TkwNotebook else ttk.Notebook

if sys.stdout is not None and hasattr(sys.stdout, "buffer"):
    try:
        sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
    except Exception:
        pass


def _get_documents_dir():
    home = os.path.expanduser("~")
    candidates = []
    if sys.platform.startswith("win"):
        try:
            import winreg
            with winreg.OpenKey(
                winreg.HKEY_CURRENT_USER,
                r"Software\Microsoft\Windows\CurrentVersion\Explorer\User Shell Folders"
            ) as key:
                val, _ = winreg.QueryValueEx(key, "Personal")
                val = os.path.expandvars(val)
                if val:
                    candidates.append(val)
        except Exception:
            pass
        candidates.append(os.path.join(home, "Documents"))
    elif sys.platform == "darwin":
        candidates.append(os.path.join(home, "Documents"))
    else:
        try:
            xdg_conf = os.path.join(home, ".config", "user-dirs.dirs")
            if os.path.isfile(xdg_conf):
                with open(xdg_conf, "r", encoding="utf-8") as f:
                    for line in f:
                        line = line.strip()
                        if line.startswith("XDG_DOCUMENTS_DIR"):
                            _, _, rhs = line.partition("=")
                            rhs = rhs.strip().strip('"')
                            rhs = rhs.replace("$HOME", home)
                            if rhs:
                                candidates.append(rhs)
        except Exception:
            pass
        candidates.append(os.path.join(home, "Documents"))

    for c in candidates:
        if c:
            return c
    return home


def _get_storage_dir():
    docs = _get_documents_dir()
    storage_dir = os.path.join(docs, "OTAProber")
    try:
        os.makedirs(storage_dir, exist_ok=True)
    except Exception:
        storage_dir = os.path.join(os.path.expanduser("~"), ".ota_prober")
        os.makedirs(storage_dir, exist_ok=True)
    return storage_dir


def _get_serials_storage_path():
    try:
        base_dir = _get_storage_dir()
    except Exception:
        base_dir = os.path.join(os.path.expanduser("~"), ".ota_prober")
        os.makedirs(base_dir, exist_ok=True)
    return os.path.join(base_dir, "serials_imeis.json")


def _load_serials_data():
    path = _get_serials_storage_path()
    default = {"serials": [], "imeis": [], "other": []}
    try:
        if os.path.isfile(path):
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
                if isinstance(data, dict):
                    for key in default:
                        if key not in data or not isinstance(data[key], list):
                            data[key] = []
                    return data
    except Exception:
        pass
    return default


def _save_serials_data(data):
    try:
        path = _get_serials_storage_path()
        tmp_path = path + ".tmp"
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        os.replace(tmp_path, path)
    except Exception:
        pass


_ser_data_lock = threading.Lock()


def _add_serial_note(category, value, note="", tags=None):
    value = (value or "").strip()
    if not value:
        return False
    note = (note or "").strip()
    tags = sorted(set((t or "").strip() for t in (tags or []) if (t or "").strip()))
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    with _ser_data_lock:
        data = _load_serials_data()
        entry = {
            "value": value,
            "note": note,
            "tags": tags,
            "created": now,
            "modified": now,
        }
        data[category].append(entry)
        _save_serials_data(data)
    return True


def _update_serial_note(category, index, value=None, note=None, tags=None):
    with _ser_data_lock:
        data = _load_serials_data()
        if category not in data or index < 0 or index >= len(data[category]):
            return False
        entry = data[category][index]
        if value is not None:
            entry["value"] = (value or "").strip()
        if note is not None:
            entry["note"] = (note or "").strip()
        if tags is not None:
            entry["tags"] = sorted(set((t or "").strip() for t in tags if (t or "").strip()))
        entry["modified"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        _save_serials_data(data)
    return True


def _delete_serial_note(category, index):
    with _ser_data_lock:
        data = _load_serials_data()
        if category not in data or index < 0 or index >= len(data[category]):
            return False
        data[category].pop(index)
        _save_serials_data(data)
    return True


def _get_all_serial_tags(data):
    tags = set()
    for cat in ("serials", "imeis", "other"):
        for entry in data.get(cat, []):
            for t in entry.get("tags", []) or []:
                tags.add(t)
    return sorted(tags)


OTA_HISTORY_FILE = os.path.join(_get_storage_dir(), "ota_history.json")
OTA_COLLECTION_FILE = os.path.join(_get_storage_dir(), "ota_collection.json")

_ota_store_lock = threading.Lock()

OTA_HISTORY_MAX_ENTRIES = 500


def _load_json_file(path, default):
    try:
        if os.path.isfile(path):
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
                if data is not None:
                    return data
    except Exception:
        pass
    return default


def _save_json_file(path, data):
    try:
        tmp_path = path + ".tmp"
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        os.replace(tmp_path, path)
    except Exception:
        pass


def _load_history():
    return _load_json_file(OTA_HISTORY_FILE, [])


def _save_history(entries):
    _save_json_file(OTA_HISTORY_FILE, entries)


def _load_collection():
    return _load_json_file(OTA_COLLECTION_FILE, {})


def _save_collection(coll):
    _save_json_file(OTA_COLLECTION_FILE, coll)


def _norm_str(s):
    return (s or "").strip()


def set_collection_tags(os_kind, url, tags):
    clean_tags = sorted(set(_norm_str(t) for t in (tags or []) if _norm_str(t)))
    with _ota_store_lock:
        coll = _load_collection()
        bucket = coll.get(os_kind, {})
        entry = bucket.get(url)
        if entry is None:
            return False
        entry["tags"] = clean_tags
        _save_collection(coll)
        return True


def get_all_collection_tags(coll):
    tags = set()
    for bucket in coll.values():
        for entry in bucket.values():
            for t in entry.get("tags", []) or []:
                tags.add(t)
    return sorted(tags)


def add_ota_record(os_kind, url, title="", description="", size="",
                   locale="", fingerprint="", alt_filenames=None):
    url = _norm_str(url)
    if not url:
        return

    title = _norm_str(title)
    description = _norm_str(description)
    size = _norm_str(size)
    locale = _norm_str(locale)
    fingerprint = _norm_str(fingerprint)
    alt_filenames = sorted(set(a for a in (alt_filenames or []) if a))
    now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    with _ota_store_lock:
        history = _load_history()
        history.append({
            "timestamp": now_str,
            "os": os_kind,
            "url": url,
            "title": title,
            "description": description,
            "size": size,
            "locale": locale,
            "fingerprint": fingerprint,
            "alt_filenames": alt_filenames,
        })
        if len(history) > OTA_HISTORY_MAX_ENTRIES:
            history = history[-OTA_HISTORY_MAX_ENTRIES:]
        _save_history(history)

        coll = _load_collection()
        bucket = coll.setdefault(os_kind, {})
        entry = bucket.get(url)
        if entry is None:
            entry = {
                "first_seen": now_str,
                "last_seen": now_str,
                "variants": [],
                "alt_filenames": [],
                "locales": [],
                "fingerprints": [],
                "tags": [],
            }
            bucket[url] = entry

        entry["last_seen"] = now_str

        variant = {"title": title, "description": description, "size": size}
        if variant not in entry["variants"]:
            if title or description or size:
                entry["variants"].append(variant)

        for af in alt_filenames:
            if af not in entry["alt_filenames"]:
                entry["alt_filenames"].append(af)

        if locale and locale not in entry["locales"]:
            entry["locales"].append(locale)

        if fingerprint and fingerprint not in entry["fingerprints"]:
            entry["fingerprints"].append(fingerprint)
            if len(entry["fingerprints"]) > 20:
                entry["fingerprints"] = entry["fingerprints"][-20:]

        _save_collection(coll)


LOCALE_TZ_MAP = {
    'af-ZA': 'Africa/Johannesburg', 'am-ET': 'Africa/Addis_Ababa',
    'ar-AE': 'Asia/Dubai', 'ar-BH': 'Asia/Bahrain',
    'ar-DZ': 'Africa/Algiers', 'ar-EG': 'Africa/Cairo',
    'ar-IQ': 'Asia/Baghdad', 'ar-JO': 'Asia/Amman',
    'ar-KW': 'Asia/Kuwait', 'ar-LB': 'Asia/Beirut',
    'ar-LY': 'Africa/Tripoli', 'ar-MA': 'Africa/Casablanca',
    'ar-OM': 'Asia/Muscat', 'ar-PS': 'Asia/Gaza',
    'ar-QA': 'Asia/Qatar', 'ar-SA': 'Asia/Riyadh',
    'ar-SO': 'Africa/Mogadishu', 'ar-SY': 'Asia/Damascus',
    'ar-TN': 'Africa/Tunis', 'ar-YE': 'Asia/Aden',
    'as-IN': 'Asia/Kolkata', 'az-AZ': 'Asia/Baku',
    'be-BY': 'Europe/Minsk', 'bg-BG': 'Europe/Sofia',
    'bn-BD': 'Asia/Dhaka', 'bn-IN': 'Asia/Kolkata',
    'bs-BA': 'Europe/Sarajevo', 'ca-AD': 'Europe/Andorra',
    'ca-ES': 'Europe/Madrid', 'cs-CZ': 'Europe/Prague',
    'cy-GB': 'Europe/London', 'da-DK': 'Europe/Copenhagen',
    'de-AT': 'Europe/Vienna', 'de-BE': 'Europe/Brussels',
    'de-CH': 'Europe/Zurich', 'de-DE': 'Europe/Berlin',
    'de-LI': 'Europe/Vaduz', 'de-LU': 'Europe/Luxembourg',
    'el-CY': 'Asia/Nicosia', 'el-GR': 'Europe/Athens',
    'en-AG': 'America/Antigua', 'en-AU': 'Australia/Sydney',
    'en-BB': 'America/Barbados', 'en-BS': 'America/Nassau',
    'en-BZ': 'America/Belize', 'en-CA': 'America/Toronto',
    'en-DM': 'America/Dominica', 'en-FJ': 'Pacific/Fiji',
    'en-GB': 'Europe/London', 'en-GD': 'America/Grenada',
    'en-GH': 'Africa/Accra', 'en-GY': 'America/Guyana',
    'en-IE': 'Europe/Dublin', 'en-IN': 'Asia/Kolkata',
    'en-JM': 'America/Jamaica', 'en-KE': 'Africa/Nairobi',
    'en-KN': 'America/St_Kitts', 'en-LC': 'America/St_Lucia',
    'en-MT': 'Europe/Malta', 'en-NG': 'Africa/Lagos',
    'en-NZ': 'Pacific/Auckland', 'en-PG': 'Pacific/Port_Moresby',
    'en-PH': 'Asia/Manila', 'en-PK': 'Asia/Karachi',
    'en-SB': 'Pacific/Guadalcanal', 'en-SG': 'Asia/Singapore',
    'en-TT': 'America/Port_of_Spain', 'en-TZ': 'Africa/Dar_es_Salaam',
    'en-UG': 'Africa/Kampala', 'en-US': 'America/New_York',
    'en-VC': 'America/St_Vincent', 'en-VU': 'Pacific/Efate',
    'en-WS': 'Pacific/Apia', 'en-ZA': 'Africa/Johannesburg',
    'en-ZW': 'Africa/Harare', 'es-AR': 'America/Argentina/Buenos_Aires',
    'es-BO': 'America/La_Paz', 'es-CL': 'America/Santiago',
    'es-CO': 'America/Bogota', 'es-CR': 'America/Costa_Rica',
    'es-CU': 'America/Havana', 'es-DO': 'America/Santo_Domingo',
    'es-EC': 'America/Guayaquil', 'es-ES': 'Europe/Madrid',
    'es-GQ': 'Africa/Malabo', 'es-GT': 'America/Guatemala',
    'es-HN': 'America/Tegucigalpa', 'es-MX': 'America/Mexico_City',
    'es-NI': 'America/Managua', 'es-PA': 'America/Panama',
    'es-PE': 'America/Lima', 'es-PH': 'Asia/Manila',
    'es-PR': 'America/Puerto_Rico', 'es-PY': 'America/Asuncion',
    'es-SV': 'America/El_Salvador', 'es-US': 'America/New_York',
    'es-UY': 'America/Montevideo', 'es-VE': 'America/Caracas',
    'et-EE': 'Europe/Tallinn', 'eu-ES': 'Europe/Madrid',
    'fa-IR': 'Asia/Tehran', 'fi-FI': 'Europe/Helsinki',
    'fil-PH': 'Asia/Manila', 'fr-BE': 'Europe/Brussels',
    'fr-BF': 'Africa/Ouagadougou', 'fr-BJ': 'Africa/Porto-Novo',
    'fr-CA': 'America/Montreal', 'fr-CD': 'Africa/Kinshasa',
    'fr-CF': 'Africa/Bangui', 'fr-CH': 'Europe/Zurich',
    'fr-CI': 'Africa/Abidjan', 'fr-CM': 'Africa/Douala',
    'fr-DZ': 'Africa/Algiers', 'fr-FR': 'Europe/Paris',
    'fr-GF': 'America/Cayenne', 'fr-GP': 'America/Guadeloupe',
    'fr-HT': 'America/Port-au-Prince', 'fr-LU': 'Europe/Luxembourg',
    'fr-MA': 'Africa/Casablanca', 'fr-MC': 'Europe/Monaco',
    'fr-MG': 'Indian/Antananarivo', 'fr-ML': 'Africa/Bamako',
    'fr-MQ': 'America/Martinique', 'fr-MU': 'Indian/Mauritius',
    'fr-NE': 'Africa/Niamey', 'fr-PM': 'America/Miquelon',
    'fr-RE': 'Indian/Reunion', 'fr-SC': 'Indian/Mahe',
    'fr-SN': 'Africa/Dakar', 'fr-TG': 'Africa/Lome',
    'fr-TN': 'Africa/Tunis', 'ga-IE': 'Europe/Dublin',
    'gd-GB': 'Europe/London', 'gl-ES': 'Europe/Madrid',
    'gu-IN': 'Asia/Kolkata', 'ha-NG': 'Africa/Lagos',
    'he-IL': 'Asia/Jerusalem', 'hi-IN': 'Asia/Kolkata',
    'hr-HR': 'Europe/Zagreb', 'hu-HU': 'Europe/Budapest',
    'hy-AM': 'Asia/Yerevan', 'id-ID': 'Asia/Jakarta',
    'ig-NG': 'Africa/Lagos', 'is-IS': 'Atlantic/Reykjavik',
    'it-CH': 'Europe/Zurich', 'it-IT': 'Europe/Rome',
    'it-SM': 'Europe/Rome', 'ja-JP': 'Asia/Tokyo',
    'jv-ID': 'Asia/Jakarta', 'ka-GE': 'Asia/Tbilisi',
    'kk-KZ': 'Asia/Almaty', 'km-KH': 'Asia/Phnom_Penh',
    'kn-IN': 'Asia/Kolkata', 'ko-KR': 'Asia/Seoul',
    'ku-IQ': 'Asia/Baghdad', 'ky-KG': 'Asia/Bishkek',
    'lo-LA': 'Asia/Vientiane', 'lt-LT': 'Europe/Vilnius',
    'lv-LV': 'Europe/Riga', 'mg-MG': 'Indian/Antananarivo',
    'mi-NZ': 'Pacific/Auckland', 'mk-MK': 'Europe/Skopje',
    'ml-IN': 'Asia/Kolkata', 'mn-MN': 'Asia/Ulaanbaatar',
    'mr-IN': 'Asia/Kolkata', 'ms-BN': 'Asia/Brunei',
    'ms-MY': 'Asia/Kuala_Lumpur', 'mt-MT': 'Europe/Malta',
    'my-MM': 'Asia/Yangon', 'nb-NO': 'Europe/Oslo',
    'ne-NP': 'Asia/Kathmandu', 'nl-AW': 'America/Aruba',
    'nl-BE': 'Europe/Brussels', 'nl-CW': 'America/Curacao',
    'nl-NL': 'Europe/Amsterdam', 'nl-SR': 'America/Paramaribo',
    'nl-SX': 'America/Lower_Princes', 'nn-NO': 'Europe/Oslo',
    'no-NO': 'Europe/Oslo', 'or-IN': 'Asia/Kolkata',
    'pa-IN': 'Asia/Kolkata', 'pa-PK': 'Asia/Karachi',
    'pl-PL': 'Europe/Warsaw', 'ps-AF': 'Asia/Kabul',
    'pt-AO': 'Africa/Luanda', 'pt-BR': 'America/Sao_Paulo',
    'pt-CV': 'Atlantic/Cape_Verde', 'pt-GW': 'Africa/Bissau',
    'pt-MZ': 'Africa/Maputo', 'pt-PT': 'Europe/Lisbon',
    'pt-ST': 'Africa/Sao_Tome', 'rm-CH': 'Europe/Zurich',
    'ro-RO': 'Europe/Bucharest', 'ru-RU': 'Europe/Moscow',
    'si-LK': 'Asia/Colombo', 'sk-SK': 'Europe/Bratislava',
    'sl-SI': 'Europe/Ljubljana', 'so-SO': 'Africa/Mogadishu',
    'sq-AL': 'Europe/Tirane', 'sr-BA': 'Europe/Belgrade',
    'sr-RS': 'Europe/Belgrade', 'su-ID': 'Asia/Jakarta',
    'sv-FI': 'Europe/Helsinki', 'sv-SE': 'Europe/Stockholm',
    'sw-KE': 'Africa/Nairobi', 'sw-TZ': 'Africa/Dar_es_Salaam',
    'sw-UG': 'Africa/Kampala', 'ta-IN': 'Asia/Kolkata',
    'ta-LK': 'Asia/Colombo', 'ta-SG': 'Asia/Singapore',
    'te-IN': 'Asia/Kolkata', 'tg-TJ': 'Asia/Dushanbe',
    'th-TH': 'Asia/Bangkok', 'tk-TM': 'Asia/Ashgabat',
    'tl-PH': 'Asia/Manila', 'tr-CY': 'Asia/Nicosia',
    'tr-TR': 'Europe/Istanbul', 'ug-CN': 'Asia/Urumqi',
    'uk-UA': 'Europe/Kiev', 'ur-IN': 'Asia/Kolkata',
    'ur-PK': 'Asia/Karachi', 'uz-UZ': 'Asia/Tashkent',
    'vi-VN': 'Asia/Ho_Chi_Minh', 'yi-IL': 'Asia/Jerusalem',
    'yo-NG': 'Africa/Lagos', 'zh-CN': 'Asia/Shanghai',
    'zh-HK': 'Asia/Hong_Kong', 'zh-MO': 'Asia/Macau',
    'zh-SG': 'Asia/Singapore', 'zh-TW': 'Asia/Taipei',
    'zu-ZA': 'Africa/Johannesburg',
}
EXTRA_TZ = ['UTC', 'America/Los_Angeles', 'America/Chicago', 'America/Denver', 'Europe/London', 'Europe/Kiev', 'Europe/Moscow']

CROS_BOARD_APPID_MAP = {
    'nocturne-signed-mpkeys': '{BD7F7139-CC18-49C1-A847-33F155CCBCA8}',
    'hatch-signed-mp-v6keys': '{95EE134E-B47F-43FB-9835-32C276865F9A}',
    'caroline-signed-mpkeys': '{C166AF52-7EE9-4F08-AAA7-B4B895A9F336}',
    'octopus-signed-mp-v17keys': '{9A3BE5D2-C3DC-4AE6-9943-E2C113895DC5}',
    'strongbad-signed-mp-v3keys': '{ABD68995-5A83-31CA-9AC6-49D8194EEA52}',
    'daisy-signed-mp-v2keys': '{D851316B-7E57-4805-A7CE-01829AC14}',
}
CROS_BOARD_HWID_MAP = {
    'nocturne-signed-mpkeys': 'NOCTURNE NNNN',
    'hatch-signed-mp-v6keys': 'DRAGONAIR NNNN',
    'caroline-signed-mpkeys': 'CAROLINE NNNN',
    'octopus-signed-mp-v17keys': 'GRABBITER NNNN',
    'strongbad-signed-mp-v3keys': 'COACHZ NNNN',
    'daisy-signed-mp-v2keys': 'SNOW ELBERT A-E 4016',
}
CROS_TRACKS = ['stable-channel', 'beta-channel', 'dev-channel', 'canary-channel']
CROS_AUSERVER = 'https://tools.google.com/service/update2'


def _zip_dos_date_str(file_date, file_time):
    try:
        year = ((file_date >> 9) & 0x7F) + 1980
        month = (file_date >> 5) & 0x0F
        day = file_date & 0x1F
        hour = (file_time >> 11) & 0x1F
        minute = (file_time >> 5) & 0x3F
        second = (file_time & 0x1F) * 2
        return f"{year:04d}-{month:02d}-{day:02d} {hour:02d}:{minute:02d}:{second:02d}"
    except Exception:
        return ""


def _parse_central_directory(cd_data):
    entries = []
    pos = 0
    while pos + 46 <= len(cd_data):
        if cd_data[pos:pos+4] != b'PK\x01\x02':
            break
        try:
            compression_method = struct.unpack('<H', cd_data[pos+10:pos+12])[0]
            file_time = struct.unpack('<H', cd_data[pos+12:pos+14])[0]
            file_date = struct.unpack('<H', cd_data[pos+14:pos+16])[0]
            crc32 = struct.unpack('<I', cd_data[pos+16:pos+20])[0]
            compressed_size = struct.unpack('<I', cd_data[pos+20:pos+24])[0]
            uncompressed_size = struct.unpack('<I', cd_data[pos+24:pos+28])[0]
            name_len = struct.unpack('<H', cd_data[pos+28:pos+30])[0]
            extra_len = struct.unpack('<H', cd_data[pos+30:pos+32])[0]
            comment_len = struct.unpack('<H', cd_data[pos+32:pos+34])[0]
            local_header_offset = struct.unpack('<I', cd_data[pos+42:pos+46])[0]
            name = cd_data[pos+46:pos+46+name_len].decode('utf-8', errors='replace')
            pos += 46 + name_len + extra_len + comment_len
        except struct.error:
            break

        date_str = _zip_dos_date_str(file_date, file_time)
        entries.append({
            'name': name,
            'uncompressed_size': uncompressed_size,
            'compressed_size': compressed_size,
            'crc32': crc32,
            'date': date_str,
            'compression_method': compression_method,
            'local_header_offset': local_header_offset,
            'is_dir': name.endswith('/'),
        })
    return entries


def fetch_zip_tree(url, token="", status_cb=None, timeout=30):
    def _s(msg):
        if status_cb:
            status_cb(msg)

    ctx = ssl.create_default_context()

    try:
        head_headers = {
            'User-Agent': 'AndroidDownloadManager/14',
            'Accept-Encoding': 'identity',
        }
        if token:
            head_headers['Authorization'] = token
        head_req = urllib.request.Request(url, method='HEAD', headers=head_headers)
        with urllib.request.urlopen(head_req, timeout=timeout, context=ctx) as resp:
            total_size = int(resp.headers.get('Content-Length', '0') or '0')
    except Exception as e:
        raise RuntimeError(f"HEAD request failed: {e}")

    if total_size <= 0:
        raise RuntimeError("Unable to determine file size (Content-Length missing)")

    chunk_size = 64 * 1024
    tail_offset = max(0, total_size - chunk_size)
    range_hdr = f'bytes={tail_offset}-{total_size-1}'
    _s(f"Fetching last {chunk_size//1024} KB...")

    try:
        range_headers = {
            'User-Agent': 'AndroidDownloadManager/14',
            'Accept-Encoding': 'identity',
            'Range': range_hdr,
        }
        if token:
            range_headers['Authorization'] = token
        req = urllib.request.Request(url, headers=range_headers)
        with urllib.request.urlopen(req, timeout=timeout, context=ctx) as resp:
            tail_data = resp.read()
    except Exception as e:
        raise RuntimeError(f"Tail fetch failed: {e}")

    eocd_pos = tail_data.rfind(b'PK\x05\x06')
    if eocd_pos == -1:
        raise RuntimeError("ZIP End of Central Directory not found in tail chunk")

    try:
        cd_size = struct.unpack('<I', tail_data[eocd_pos+12:eocd_pos+16])[0]
        cd_offset = struct.unpack('<I', tail_data[eocd_pos+16:eocd_pos+20])[0]
    except struct.error:
        raise RuntimeError("Invalid EOCD structure")

    cd_start = cd_offset
    cd_end = cd_offset + cd_size
    cd_data = b''

    if cd_start >= tail_offset and cd_end <= total_size:
        start_in_tail = cd_start - tail_offset
        cd_data = tail_data[start_in_tail:start_in_tail + cd_size]
    else:
        range_hdr = f'bytes={cd_start}-{cd_end-1}'
        _s(f"Fetching central directory ({cd_size} bytes)...")
        range_headers = {
            'User-Agent': 'AndroidDownloadManager/14',
            'Accept-Encoding': 'identity',
            'Range': range_hdr,
        }
        if token:
            range_headers['Authorization'] = token
        req = urllib.request.Request(url, headers=range_headers)
        with urllib.request.urlopen(req, timeout=timeout, context=ctx) as resp:
            cd_data = resp.read()

    if len(cd_data) < cd_size:
        raise RuntimeError("Incomplete central directory data")

    return _parse_central_directory(cd_data)


def extract_zip_entry(url, entry, status_cb=None, timeout=30):
    def _s(msg):
        if status_cb:
            status_cb(msg)

    local_offset = entry['local_header_offset']
    comp_size = entry['compressed_size']
    compression_method = entry.get('compression_method', 0)

    header_guess = 512
    range_end = local_offset + header_guess + comp_size
    range_hdr = f'bytes={local_offset}-{range_end}'

    _s(f"Downloading '{entry['name']}' ({comp_size:,} bytes compressed)...")

    ctx = ssl.create_default_context()
    req = urllib.request.Request(url, headers={
        'User-Agent': 'AndroidDownloadManager/14',
        'Accept-Encoding': 'identity',
        'Range': range_hdr,
    })
    try:
        with urllib.request.urlopen(req, timeout=timeout, context=ctx) as resp:
            blob = resp.read()
    except Exception as e:
        raise RuntimeError(f"Range fetch failed: {e}")

    if len(blob) < 30 or blob[:4] != b'PK\x03\x04':
        raise RuntimeError("Local file header not found at expected offset")

    name_len = struct.unpack('<H', blob[26:28])[0]
    extra_len = struct.unpack('<H', blob[28:30])[0]
    data_start = 30 + name_len + extra_len

    if data_start > header_guess:
        range_hdr = f'bytes={local_offset}-{local_offset + data_start + comp_size}'
        req = urllib.request.Request(url, headers={
            'User-Agent': 'AndroidDownloadManager/14',
            'Accept-Encoding': 'identity',
            'Range': range_hdr,
        })
        with urllib.request.urlopen(req, timeout=timeout, context=ctx) as resp:
            blob = resp.read()

    raw = blob[data_start:data_start + comp_size]
    if len(raw) < comp_size:
        raise RuntimeError("Incomplete data — fewer bytes received than compressed_size")

    if compression_method == 0:
        return raw
    elif compression_method == 8:
        _s("Decompressing...")
        return zlib.decompress(raw, -15)
    else:
        raise RuntimeError(f"Unsupported compression method: {compression_method}")


def extract_zip_entry_local(path, entry, status_cb=None):
    def _s(msg):
        if status_cb:
            status_cb(msg)

    local_offset = entry['local_header_offset']
    comp_size = entry['compressed_size']
    compression_method = entry.get('compression_method', 0)

    _s(f"Reading '{entry['name']}' from local file...")
    with open(path, 'rb') as f:
        f.seek(local_offset)
        header = f.read(30)
        if len(header) < 30 or header[:4] != b'PK\x03\x04':
            raise RuntimeError("Local file header not found at expected offset")
        name_len = struct.unpack('<H', header[26:28])[0]
        extra_len = struct.unpack('<H', header[28:30])[0]
        f.seek(local_offset + 30 + name_len + extra_len)
        raw = f.read(comp_size)

    if len(raw) < comp_size:
        raise RuntimeError("Incomplete data read from local file")

    if compression_method == 0:
        return raw
    elif compression_method == 8:
        _s("Decompressing...")
        return zlib.decompress(raw, -15)
    else:
        raise RuntimeError(f"Unsupported compression method: {compression_method}")


def fetch_zip_tree_local(path, status_cb=None):
    def _s(msg):
        if status_cb:
            status_cb(msg)

    total_size = os.path.getsize(path)
    if total_size <= 0:
        raise RuntimeError("File is empty")

    chunk_size = 64 * 1024
    tail_offset = max(0, total_size - chunk_size)
    _s(f"Reading last {chunk_size//1024} KB...")
    with open(path, 'rb') as f:
        f.seek(tail_offset)
        tail_data = f.read()

    eocd_pos = tail_data.rfind(b'PK\x05\x06')
    if eocd_pos == -1:
        raise RuntimeError("ZIP End of Central Directory not found in tail chunk")

    try:
        cd_size = struct.unpack('<I', tail_data[eocd_pos+12:eocd_pos+16])[0]
        cd_offset = struct.unpack('<I', tail_data[eocd_pos+16:eocd_pos+20])[0]
    except struct.error:
        raise RuntimeError("Invalid EOCD structure")

    cd_start = cd_offset
    cd_end = cd_offset + cd_size
    cd_data = b''

    if cd_start >= tail_offset and cd_end <= total_size:
        start_in_tail = cd_start - tail_offset
        cd_data = tail_data[start_in_tail:start_in_tail + cd_size]
    else:
        _s(f"Reading central directory ({cd_size} bytes)...")
        with open(path, 'rb') as f:
            f.seek(cd_start)
            cd_data = f.read(cd_size)

    if len(cd_data) < cd_size:
        raise RuntimeError("Incomplete central directory data")

    return _parse_central_directory(cd_data)


def parse_fingerprint(fingerprint):
    parts = fingerprint.split('/')
    if len(parts) != 6:
        raise ValueError(f"Invalid fingerprint format. Expected 6 parts.\n"
                         f"Format: oem/product/device:api/build_tag/incremental:build_type/key_type\n"
                         f"Got {len(parts)} parts: {parts}")

    oem = parts[0]
    product = parts[1]

    device_api = parts[2].split(':')
    if len(device_api) != 2:
        raise ValueError(f"Invalid device:api format in part 3: {parts[2]}")
    device = device_api[0]
    api_level = device_api[1]

    build_tag = parts[3]

    incremental_type = parts[4].split(':')
    if len(incremental_type) != 2:
        raise ValueError(f"Invalid incremental:build_type format in part 5: {parts[4]}")
    incremental = incremental_type[0]
    build_type = incremental_type[1]

    key_type = parts[5]

    return {
        'fingerprint': fingerprint,
        'oem': oem,
        'product': product,
        'device': device,
        'api_level': api_level,
        'build_tag': build_tag,
        'incremental': incremental,
        'build_type': build_type,
        'key_type': key_type,
    }


def prettify_xml(xml_text):
    if not xml_text or not xml_text.strip():
        return xml_text

    try:
        import xml.dom.minidom as minidom
        parsed = minidom.parseString(xml_text.encode('utf-8') if isinstance(xml_text, str) else xml_text)
        pretty = parsed.toprettyxml(indent="  ")
        lines = [line for line in pretty.splitlines() if line.strip()]
        return '\n'.join(lines)
    except Exception:
        return xml_text


def parse_fingerprint_chromeos(fingerprint):
    if '/' not in fingerprint or ':' not in fingerprint:
        raise ValueError(
            "Invalid ChromiumOS fingerprint format. Expected 3 parts.\n"
            "Format: board/version:track/hwid\n"
            f"Got: {fingerprint}"
        )
    parts = fingerprint.split('/')
    if len(parts) != 3:
        raise ValueError(f"Invalid ChromiumOS fingerprint format. Expected 3 parts.\n"
                         f"Format: board/version:track/hwid\n"
                         f"Got {len(parts)} parts: {parts}")

    board = parts[0]

    version_track = parts[1].split(':')
    if len(version_track) != 2:
        raise ValueError(f"Invalid version:track format in part 2: {parts[1]}")
    version = version_track[0]
    track = version_track[1]

    hwid = parts[2]

    return {
        'fingerprint': fingerprint,
        'board': board,
        'version': version,
        'track': track,
        'hwid': hwid,
    }


def parse_fingerprint_xiaomi(fingerprint):
    parts = fingerprint.split('/')
    if len(parts) != 3:
        raise ValueError(
            "Invalid Xiaomi fingerprint format. Expected 3 parts.\n"
            "Format: codename/rom_version/android_version\n"
            f"Got {len(parts)} parts: {parts}"
        )
    codename, rom_version, android_version = parts
    return {
        'fingerprint': fingerprint,
        'codename': codename,
        'rom_version': rom_version,
        'android_version': android_version,
    }


XIAOMI_MIUI_UPDATE_URL = "https://update.miui.com/updates/miotaV3.php"
XIAOMI_AES_IV = b"0102030405060708"
XIAOMI_AES_DEFAULT_KEY = b"miuiotavalided11"


def _xiaomi_aes_encrypt(plaintext, key=XIAOMI_AES_DEFAULT_KEY):
    cipher = AES.new(key, AES.MODE_CBC, XIAOMI_AES_IV)
    padded = pad(plaintext.encode('utf-8'), cipher.block_size)
    encrypted = cipher.encrypt(padded)
    return base64.urlsafe_b64encode(encrypted).decode('utf-8')


def _xiaomi_aes_decrypt(encrypted_text, key=XIAOMI_AES_DEFAULT_KEY):
    cipher = AES.new(key, AES.MODE_CBC, XIAOMI_AES_IV)
    encrypted_bytes = base64.urlsafe_b64decode(encrypted_text)
    decrypted = cipher.decrypt(encrypted_bytes)
    unpadded = unpad(decrypted, cipher.block_size)
    return json.loads(unpadded.decode('utf-8'))


def build_checkin_request_xiaomi(codename, rom_version, android_version):
    is_global = '_global' in codename
    data = {
        "id": None,
        "c": android_version,
        "d": codename,
        "f": "1",
        "ov": rom_version,
        "l": 'en_US' if is_global else 'zh_CN',
        "r": 'GL' if is_global else 'CN',
        "v": f"miui-{rom_version.replace('OS1', 'V816')}",
    }
    return json.dumps(data, separators=(',', ':'))


def perform_checkin_xiaomi(codename, rom_version, android_version, timeout=15):
    if not XIAOMI_CRYPTO_AVAILABLE:
        raise RuntimeError(
            "The 'pycryptodome' package is required for Xiaomi OTA checks.\n"
            "Install it with: pip install pycryptodome"
        )

    json_data = build_checkin_request_xiaomi(codename, rom_version, android_version)
    encrypted_data = _xiaomi_aes_encrypt(json_data)

    post_data = urlencode({
        "q": encrypted_data,
        "t": "",
        "s": "1",
    }).encode('utf-8')

    req = urllib.request.Request(
        XIAOMI_MIUI_UPDATE_URL,
        data=post_data,
        method='POST',
        headers={
            'User-Agent': 'MiuiUpdaterClient',
            'Content-Type': 'application/x-www-form-urlencoded',
        },
    )
    ctx = ssl.create_default_context()
    with urllib.request.urlopen(req, timeout=timeout, context=ctx) as resp:
        raw_text = resp.read().decode('utf-8', errors='replace')

    if not raw_text:
        raise RuntimeError("Empty response from MIUI update server")

    decrypted = _xiaomi_aes_decrypt(raw_text)
    return decrypted, raw_text, post_data


def extract_build_details_xiaomi(decrypted_response):
    current = decrypted_response.get('CurrentRom', {}) or {}
    latest = decrypted_response.get('LatestRom', {}) or {}

    if not current.get('version'):
        return {'found': False, 'raw': decrypted_response}

    filename = current.get('filename')
    download_url = None
    if filename:
        if current.get('md5') and current.get('md5') == latest.get('md5'):
            download_url = f"https://ultimateota.d.miui.com/{current.get('version')}/{latest.get('filename', filename)}"
        else:
            download_url = f"https://bigota.d.miui.com/{current.get('version')}/{filename}"

    bigversion = current.get('bigversion', '')
    if bigversion == '816':
        bigversion_label = 'HyperOS 1.0'
    elif bigversion and bigversion != '0':
        bigversion_label = f"MIUI {bigversion}"
    else:
        bigversion_label = None

    return {
        'found': True,
        'device': current.get('device', 'Unknown'),
        'version': current.get('version', 'Unknown'),
        'bigversion_label': bigversion_label,
        'osbigversion': current.get('osbigversion'),
        'codebase': current.get('codebase', 'Unknown'),
        'branch': current.get('branch', 'Unknown'),
        'is_beta': current.get('isBeta'),
        'filename': filename,
        'filesize': current.get('filesize'),
        'md5': current.get('md5'),
        'download_url': download_url,
        'changelog': current.get('changelog'),
        'raw': decrypted_response,
    }


def _stringify_ota_field(value):
    if value is None:
        return ''
    if isinstance(value, (dict, list)):
        return json.dumps(value, ensure_ascii=False, sort_keys=True)
    return str(value)


def _flatten_xiaomi_changelog(changelog):
    if not changelog:
        return ''
    if isinstance(changelog, str):
        return changelog
    if isinstance(changelog, list):
        parts = []
        for item in changelog:
            if isinstance(item, dict):
                txt = item.get('txt') or item.get('title') or item.get('name')
                if txt:
                    parts.append(str(txt))
            elif item:
                parts.append(str(item))
        return ' | '.join(parts)
    if isinstance(changelog, dict):
        parts = []
        for key in ('txt', 'en', 'en_US', 'title'):
            val = changelog.get(key)
            if isinstance(val, list):
                parts.extend(str(v) for v in val if v)
            elif val:
                parts.append(str(val))
        if parts:
            return ' | '.join(parts)

        nested_parts = []
        for category, value in changelog.items():
            if isinstance(value, dict):
                cat_texts = []
                for key in ('txt', 'en', 'en_US', 'title'):
                    val = value.get(key)
                    if isinstance(val, list):
                        cat_texts.extend(str(v) for v in val if v)
                    elif val:
                        cat_texts.append(str(val))
                if cat_texts:
                    nested_parts.append(f"{category}: " + ' | '.join(cat_texts))
            elif isinstance(value, list):
                cat_texts = [str(v) for v in value if v]
                if cat_texts:
                    nested_parts.append(f"{category}: " + ' | '.join(cat_texts))
            elif value:
                nested_parts.append(f"{category}: {value}")
        if nested_parts:
            return '\n'.join(nested_parts)

        return json.dumps(changelog, ensure_ascii=False, sort_keys=True)
    return str(changelog)


def _iter_actions(manifest):
    actions_block = manifest.get("actions", {})
    action_list = actions_block.get("action", [])
    if isinstance(action_list, dict):
        action_list = [action_list]
    return action_list


def _parse_playemu_response(resp_data):
    ota_url = None
    ota_size = ""
    ota_sha256 = ""
    next_version = ""
    description_lines = []
    other_urls = []

    root = resp_data.get("response") or resp_data.get("gupdate") or {}

    apps = root.get("apps") or root.get("app") or []
    if isinstance(apps, dict):
        apps = [apps]

    for app in apps:
        uc = app.get("updatecheck", {})
        status = uc.get("status", "")
        if status != "ok":
            continue

        if "pipelines" in uc:
            nv = uc.get("nextversion", "")
            if nv:
                next_version = nv
            for pipeline in uc.get("pipelines", []):
                for op in pipeline.get("operations", []):
                    op_type = op.get("type", "")
                    op_size = op.get("size", "")
                    op_sha = op.get("out", {}).get("sha256", "")
                    urls_list = op.get("urls", [])
                    if op_type == "download" and urls_list:
                        chosen = None
                        for u in urls_list:
                            uval = u.get("url", "")
                            if uval.startswith("https://"):
                                chosen = uval
                                break
                        if not chosen and urls_list:
                            chosen = urls_list[0].get("url", "")
                        if chosen:
                            if ota_url is None:
                                ota_url = chosen
                                ota_size = str(op_size)
                                ota_sha256 = op_sha
                            for u in urls_list:
                                uval = u.get("url", "")
                                if uval and uval != ota_url:
                                    other_urls.append(uval)
                    elif op_type == "crx3" or op.get("path"):
                        path = op.get("path", "")
                        args = op.get("arguments", "")
                        in_sha = op.get("in", {}).get("sha256", "")
                        if path:
                            description_lines.append("Installer: " + path)
                        if args:
                            description_lines.append("Install args: " + args)
                        if in_sha:
                            description_lines.append("Installer SHA256: " + in_sha)

        elif "manifest" in uc or "urls" in uc:
            manifest = uc.get("manifest", {})
            nv = manifest.get("version", "")
            if nv:
                next_version = nv

            codebases = []
            urls_block = uc.get("urls", {})
            url_list = urls_block.get("url", [])
            if isinstance(url_list, dict):
                url_list = [url_list]
            for u in url_list:
                cb = u.get("codebase", "")
                if cb:
                    codebases.append(cb)

            chosen_base = None
            for cb in codebases:
                if cb.startswith("https://"):
                    chosen_base = cb
                    break
            if not chosen_base and codebases:
                chosen_base = codebases[0]

            packages_block = manifest.get("packages", {})
            pkg_list = packages_block.get("package", [])
            if isinstance(pkg_list, dict):
                pkg_list = [pkg_list]

            pkg_name = ""
            pkg_size = ""
            pkg_sha = ""
            if pkg_list:
                pkg = pkg_list[0]
                pkg_name = pkg.get("name", "")
                pkg_size = str(pkg.get("size", ""))
                pkg_sha = pkg.get("hash_sha256", "")

            if not pkg_name:
                pkg_name = manifest.get("run", "")
            if not pkg_name:
                for action in _iter_actions(manifest):
                    if action.get("event") in ("install", "update") and action.get("run"):
                        pkg_name = action["run"]
                        break

            if chosen_base and pkg_name:
                ota_url = chosen_base.rstrip("/") + "/" + pkg_name
                ota_size = pkg_size
                ota_sha256 = pkg_sha
                for cb in codebases:
                    alt = cb.rstrip("/") + "/" + pkg_name
                    if alt != ota_url:
                        other_urls.append(alt)

            args = manifest.get("arguments", "")
            if not args:
                for action in _iter_actions(manifest):
                    if action.get("arguments"):
                        args = action["arguments"]
                        break
            if args:
                description_lines.append("Install args: " + args)
            if pkg_sha:
                ota_sha256 = pkg_sha

        else:
            cb = uc.get("codebase", "")
            if cb:
                ota_url = cb
            ota_size = str(uc.get("size", ""))
            ota_sha256 = uc.get("hash_sha256", "")
            args = uc.get("arguments", "")
            if args:
                description_lines.append("Install args: " + args)

    if next_version:
        description_lines.insert(0, "Version: " + next_version)
    if ota_sha256:
        description_lines.insert(1, "SHA256: " + ota_sha256)
    if ota_size:
        description_lines.insert(2, "Size: " + ota_size + " bytes")
    if other_urls:
        description_lines.append("")
        description_lines.append("Alternative download URLs:")
        for u in other_urls:
            description_lines.append("  " + u)

    return ota_url, ota_size, ota_sha256, next_version, description_lines, other_urls


def build_checkin_request_chromeos(fingerprint, app_id, arch="x86_64", hardware_class=None):
    parsed = parse_fingerprint_chromeos(fingerprint)
    hwid = hardware_class if hardware_class else parsed['hwid']

    request_xml = (
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<request protocol="3.0" version="ChromeOSUpdateEngine-0.1.0.0" '
        'updaterversion="ChromeOSUpdateEngine-0.1.0.0" installsource="ondemand" '
        'ismachine="1" testsource="prober">\n'
        f'<app appid="{app_id}" version="{parsed["version"]}" board="{parsed["board"]}" '
        f'track="{parsed["track"]}" hardware_class="{hwid}" delta_okay="false">\n'
        '<updatecheck targetversionprefix=""></updatecheck>\n'
        '</app>\n'
        '</request>'
    )

    return request_xml


def perform_checkin_chromeos(fingerprint, app_id, arch="x86_64", hardware_class=None):
    request_data = build_checkin_request_chromeos(fingerprint, app_id, arch, hardware_class)
    request_bytes = request_data.encode('utf-8')

    headers = {
        'Content-Type': 'application/xml',
        'User-Agent': 'ChromeOSUpdateEngine/0.1.0.0',
    }

    req = urllib.request.Request(CROS_AUSERVER, data=request_bytes, headers=headers, method='POST')

    with urllib.request.urlopen(req, timeout=10) as response:
        response_data = response.read()
        return response_data.decode('utf-8', errors='replace'), response_data


def find_ota_link_chromeos(response_xml_text):
    if not response_xml_text:
        return None

    import xml.etree.ElementTree as ET
    try:
        root = ET.fromstring(response_xml_text)
    except Exception:
        return None

    ns = ''
    if root.tag.startswith('{'):
        ns = root.tag.split('}')[0] + '}'

    app = root.find(f'{ns}app')
    if app is None:
        return None

    updatecheck = app.find(f'{ns}updatecheck')
    if updatecheck is None or updatecheck.get('status') != 'ok':
        return None

    urls_el = updatecheck.find(f'{ns}urls')
    manifest_el = updatecheck.find(f'{ns}manifest')
    if urls_el is None or manifest_el is None:
        return None

    url_els = urls_el.findall(f'{ns}url')
    codebase = None
    for u in url_els:
        cb = u.get('codebase')
        if cb and cb.startswith('https'):
            codebase = cb
            break
    if codebase is None and url_els:
        codebase = url_els[0].get('codebase')
    if not codebase:
        return None

    actions_el = manifest_el.find(f'{ns}actions')
    run_name = None
    if actions_el is not None:
        for action in actions_el.findall(f'{ns}action'):
            if action.get('event') in ('install', 'update') and action.get('run'):
                run_name = action.get('run')
                break

    packages_el = manifest_el.find(f'{ns}packages')
    size = ''
    if packages_el is not None:
        pkg = packages_el.find(f'{ns}package')
        if pkg is not None:
            if pkg.get('name'):
                run_name = pkg.get('name')
            if pkg.get('size'):
                size = pkg.get('size')

    if not run_name:
        return None

    full_url = codebase.rstrip('/') + '/' + run_name
    version = manifest_el.get('version', '')

    return {
        'url': full_url,
        'title': f"ChromeOS {version}" if version else '',
        'description': '',
        'precondition': '',
        'postcondition': '',
        'size': size,
    }


def encode_varint(value):
    parts = []
    while value > 0x7f:
        parts.append((value & 0x7f) | 0x80)
        value >>= 7
    parts.append(value & 0x7f)
    return bytes(parts)


def encode_string(field_number, value):
    if isinstance(value, str):
        value = value.encode('utf-8')
    tag = (field_number << 3) | 2
    return encode_varint(tag) + encode_varint(len(value)) + value


def encode_int64(field_number, value):
    tag = (field_number << 3) | 0
    return encode_varint(tag) + encode_varint(value & 0xffffffffffffffff)


def encode_bool(field_number, value):
    tag = (field_number << 3) | 0
    return encode_varint(tag) + bytes([1 if value else 0])


def decode_varint(data, offset):
    result = 0
    shift = 0
    while True:
        byte = data[offset]
        result |= (byte & 0x7f) << shift
        offset += 1
        if byte < 0x80:
            break
        shift += 7
    return result, offset


def decode_string(data, offset, length):
    return data[offset:offset+length].decode('utf-8', errors='ignore'), offset + length


def parse_protobuf_response(data):
    settings = {}
    offset = 0

    while offset < len(data):
        tag, offset = decode_varint(data, offset)
        field_number = tag >> 3
        wire_type = tag & 0x07

        if field_number == 5 and wire_type == 2:
            length, offset = decode_varint(data, offset)
            end = offset + length
            name = None
            value = None

            while offset < end:
                inner_tag, offset = decode_varint(data, offset)
                inner_field = inner_tag >> 3
                inner_wire = inner_tag & 0x07

                if inner_wire == 2:
                    str_len, offset = decode_varint(data, offset)
                    if inner_field == 1:
                        name, offset = decode_string(data, offset, str_len)
                    elif inner_field == 2:
                        value, offset = decode_string(data, offset, str_len)
                else:
                    offset += 1

            if name and value:
                settings[name] = value
        else:
            if wire_type == 0:
                _, offset = decode_varint(data, offset)
            elif wire_type == 2:
                length, offset = decode_varint(data, offset)
                offset += length
            elif wire_type == 5:
                offset += 4
            elif wire_type == 1:
                offset += 8

    return settings


_CHECKIN_RESPONSE_FIELDS = {
    1: 'android_id',
    2: 'security_token',
    3: 'time_msec',
    4: 'settings_diff',
    5: 'setting',
    6: 'digest',
    7: 'android_id_alt',
    8: 'market_ok',
    9: 'gservices_digest',
    10: 'checkin_interval_msec',
    11: 'checkin',
    12: 'min_checkin_interval_msec',
    13: 'intent',
    14: 'account',
    15: 'gcm_response',
    16: 'device_data_version',
    17: 'last_checkin_msec',
    18: 'deleted_setting',
    19: 'new_device_cookie',
    20: 'device_checkin_consistency_token',
}

_SETTING_FIELDS = {
    1: 'name',
    2: 'value',
}


def _is_valid_protobuf(data):
    offset = 0
    count = 0
    try:
        while offset < len(data):
            tag, offset = decode_varint(data, offset)
            wire_type = tag & 0x07
            if wire_type in (3, 4, 6, 7):
                return False
            if wire_type == 0:
                _, offset = decode_varint(data, offset)
            elif wire_type == 1:
                if offset + 8 > len(data):
                    return False
                offset += 8
            elif wire_type == 2:
                length, offset = decode_varint(data, offset)
                if offset + length > len(data):
                    return False
                offset += length
            elif wire_type == 5:
                if offset + 4 > len(data):
                    return False
                offset += 4
            else:
                return False
            count += 1
        return count > 0 and offset == len(data)
    except Exception:
        return False


def parse_protobuf_full(data, indent=0, field_names=None):
    if field_names is None:
        field_names = _CHECKIN_RESPONSE_FIELDS

    lines = []
    offset = 0
    pad = '  ' * indent

    while offset < len(data):
        try:
            tag, offset = decode_varint(data, offset)
        except Exception:
            lines.append(f"{pad}[parse error at offset {offset}/{len(data)}]")
            break

        field_number = tag >> 3
        wire_type = tag & 0x07
        field_label = field_names.get(field_number, f'field_{field_number}')

        try:
            if wire_type == 0:
                val, offset = decode_varint(data, offset)
                lines.append(f"{pad}[{field_number}] {field_label}  =  {val}")

            elif wire_type == 1:
                raw8 = data[offset:offset+8]
                offset += 8
                val = struct.unpack_from('<q', raw8)[0]
                lines.append(f"{pad}[{field_number}] {field_label}  =  {val}  (64-bit LE)")

            elif wire_type == 2:
                length, offset = decode_varint(data, offset)
                raw = data[offset:offset+length]
                offset += length

                if field_number == 5 and field_names is _CHECKIN_RESPONSE_FIELDS:
                    child_names = _SETTING_FIELDS
                else:
                    child_names = {}

                if length > 0 and _is_valid_protobuf(raw):
                    nested = parse_protobuf_full(raw, indent + 1, child_names)
                    lines.append(f"{pad}[{field_number}] {field_label}  {{")
                    lines.extend(nested)
                    lines.append(f"{pad}}}")
                else:
                    try:
                        txt = raw.decode('utf-8')
                        txt_repr = repr(txt)[1:-1]
                        lines.append(f"{pad}[{field_number}] {field_label}  =  \"{txt_repr}\"")
                    except Exception:
                        hex_str = raw.hex()
                        if len(hex_str) > 120:
                            hex_str = hex_str[:120] + f' ... ({length} bytes total)'
                        lines.append(f"{pad}[{field_number}] {field_label}  =  <bytes> {hex_str}")

            elif wire_type == 5:
                raw4 = data[offset:offset+4]
                offset += 4
                val = struct.unpack_from('<I', raw4)[0]
                lines.append(f"{pad}[{field_number}] {field_label}  =  {val}  (32-bit LE)")

            else:
                lines.append(f"{pad}[{field_number}] unknown wire_type={wire_type}, stopping parse")
                break

        except Exception as e:
            lines.append(f"{pad}[{field_number}] parse error: {e}")
            break

    return lines


def format_hex_dump(raw_bytes, header_label="RAW RESPONSE"):
    n = len(raw_bytes)
    header = f"=== {header_label}  ({n} bytes) ===\n"
    lines = [header, "--- HEX DUMP ---"]
    for i in range(0, n, 16):
        chunk = raw_bytes[i:i+16]
        hex_part = ' '.join(f'{b:02x}' for b in chunk)
        asc_part = ''.join(chr(b) if 32 <= b < 127 else '.' for b in chunk)
        lines.append(f"  {i:06x}  {hex_part:<47}  {asc_part}")
    return '\n'.join(lines)


def format_raw_response(raw_bytes):
    n = len(raw_bytes)
    header = f"=== RAW PROTOBUF RESPONSE  ({n} bytes) ===\n"

    human_lines = [header, "--- FIELD TREE ---"]
    try:
        tree = parse_protobuf_full(raw_bytes, indent=0)
        human_lines.extend(tree)
    except Exception as e:
        human_lines.append(f"[parser error: {e}]")
    human_str = '\n'.join(human_lines)

    hex_str = format_hex_dump(raw_bytes, header_label="RAW PROTOBUF RESPONSE")

    return human_str, hex_str


def build_checkin_request(fingerprint, locale="en-US", timezone="America/New_York", device_sn="", imei=""):
    try:
        parsed = parse_fingerprint(fingerprint)
    except ValueError as e:
        raise ValueError(f"Failed to parse fingerprint: {e}")

    device = parsed['device']

    build = b''
    build += encode_string(1, fingerprint)
    build += encode_int64(7, 0)
    build += encode_string(9, device)

    checkin = b''
    tag = (1 << 3) | 2
    checkin += encode_varint(tag) + encode_varint(len(build)) + build
    checkin += encode_int64(2, 0)
    checkin += encode_string(8, "WIFI::")
    checkin += encode_int64(9, 0)
    checkin += encode_int64(12, 0)
    checkin += encode_int64(14, 2)
    checkin += encode_bool(18, False)
    checkin += encode_string(19, "WIFI")

    request = b''
    if imei:
        request += encode_string(1, imei)
    tag = (4 << 3) | 2
    request += encode_varint(tag) + encode_varint(len(checkin)) + checkin
    request += encode_int64(2, 0)
    request += encode_string(3, "1-0000000000000000000000000000000000000000")
    request += encode_string(6, locale)
    if imei:
        request += encode_string(10, imei)
    request += encode_string(12, timezone)
    request += encode_int64(14, 3)
    if device_sn:
        request += encode_string(16, device_sn)
    request += encode_int64(20, 0)
    request += encode_int64(22, 0)

    return request


_threading = threading
_checkin_pool_lock = _threading.Lock()
_checkin_pool = {}


def _get_checkin_conn(host, port, is_https, timeout=10):
    key = (host, port, is_https, _threading.get_ident())
    conn = _checkin_pool.get(key)
    if conn is None:
        if is_https:
            _ssl_ctx = ssl.create_default_context()
            _ssl_ctx.check_hostname = False
            _ssl_ctx.verify_mode = ssl.CERT_NONE
            conn = http.client.HTTPSConnection(host, port, timeout=timeout, context=_ssl_ctx)
        else:
            conn = http.client.HTTPConnection(host, port, timeout=timeout)
        _checkin_pool[key] = conn
    return conn


def perform_checkin(fingerprint, locale="en-US", timezone="America/New_York", device_sn="", imei="", url=None):
    parsed = parse_fingerprint(fingerprint)
    request_data = build_checkin_request(fingerprint, locale, timezone, device_sn, imei)
    compressed = gzip.compress(request_data)

    url = (url or 'http://android.googleapis.com/checkin').strip()
    device = parsed['device']
    version = parsed['api_level']
    build = parsed['build_tag']

    parsed_url = urlparse(url)
    is_https = parsed_url.scheme == 'https'
    host = parsed_url.hostname
    port = parsed_url.port or (443 if is_https else 80)
    path = parsed_url.path or '/checkin'
    if parsed_url.query:
        path += '?' + parsed_url.query

    request_headers = {
        'Accept-Encoding': 'gzip, deflate',
        'Content-Encoding': 'gzip',
        'Content-Type': 'application/x-protobuffer',
        'Content-Length': str(len(compressed)),
        'Connection': 'keep-alive',
        'User-Agent': f'Dalvik/2.1.0 (Linux; U; Android {version}; {device} Build/{build})',
    }

    for attempt in range(2):
        conn = _get_checkin_conn(host, port, is_https, timeout=10)
        try:
            conn.request('POST', path, body=compressed, headers=request_headers)
            resp = conn.getresponse()
            response_data = resp.read()
            break
        except Exception:
            try:
                conn.close()
            except Exception:
                pass
            key = (host, port, is_https, _threading.get_ident())
            _checkin_pool.pop(key, None)
            if attempt == 1:
                raise

    try:
        response_data = gzip.decompress(response_data)
    except Exception:
        pass

    settings = parse_protobuf_response(response_data)
    return settings, response_data, request_data, compressed


def get_android_version(api_level):
    try:
        api_str = str(api_level)

        if api_str.upper() == 'KKWT':
            return 'KKWT (API 19)'

        if '.' in api_str:
            version_to_api = {
                '1.0': 1, '1.1': 2, '1.5': 3, '1.6': 4, '2.0': 5, '2.0.1': 6, '2.1': 7,
                '2.2': 8, '2.3': 9, '2.3.3': 10, '3.0': 11, '3.1': 12, '3.2': 13, '4.0': 14,
                '4.0.2': 15, '4.1': 16, '4.1.1': 16, '4.2': 17, '4.3': 18, '4.4': 19, '4.4W': 20, '4.4W.1': 20, '4.4W.2': 20,
                '5.0': 21, '5.0.1': 21, '5.1': 22, '5.1.1': 22, '6.0': 23, '6.0.1': 23, '7.0': 24, '7.0.1': 24,
                '7.1': 25, '7.1.1': 25, '8.0': 26, '8.0.1': 26, '8.1': 27, '8.1.1': 27, '9.0': 28,
                '10.0': 29, '11.0': 30, '12.0': 31, '12L': 32, '13.0': 33, '14.0': 34, '15.0': 35, '16.0': 36, '17.0': 37
            }
            if api_str in version_to_api:
                api_num = version_to_api[api_str]
                return f'{api_str} (API {api_num})'
            else:
                return f'Android {api_str}'

        level = int(api_level)

        if level >= 15 and level <= 20:
            return f'Android {level} (API {level})'

        historical = {
            11: '3.0', 12: '3.1', 13: '3.2', 14: '4.0', 15: '4.0.2', 16: '4.1', 17: '4.2',
            18: '4.3', 19: '4.4', 20: '4.4W.2', 21: '5.0', 22: '5.1', 23: '6.0', 24: '7.0',
            25: '7.1', 26: '8.0', 27: '8.1', 28: '9.0', 29: '10.0', 30: '11.0', 31: '12.0',
            32: '12L', 33: '13.0', 34: '14.0', 35: '15.0', 36: '16.0', 37: '17.0'
        }

        if level in historical:
            return f'{historical[level]} (API {level})'
        elif level > 37:
            return f'Android {level} (API {level})'
        elif level >= 1:
            return f'API {level}'
        else:
            return f'Unknown'
    except Exception:
        return f'Android {api_level}'


def extract_build_date(build_tag):
    try:
        parts = build_tag.split('.')
        if len(parts) < 2:
            return "Unknown"

        date_str = parts[1]

        if len(date_str) < 6 or not date_str[:6].isdigit():
            return "Unknown"

        yy = int(date_str[0:2])
        mm = int(date_str[2:4])
        dd = int(date_str[4:6])

        if not (1 <= mm <= 12 and 1 <= dd <= 31):
            return "Unknown"

        months = ['', 'Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec']
        month_name = months[mm]
        year = 2000 + yy

        return f"{month_name} {dd}, {year}"
    except Exception:
        return "Unknown"


def extract_build_details(fingerprint, settings):
    parsed = parse_fingerprint(fingerprint)

    build_info = {
        'fingerprint': fingerprint,
        'device_codename': parsed['device'],
        'android_version': get_android_version(parsed['api_level']),
        'api_level': parsed['api_level'],
        'build_date': extract_build_date(parsed['build_tag']),
        'build_tag': parsed['build_tag'],
        'build_number': parsed['incremental'],
        'build_flavor': parsed['build_type'],
        'security_keys': parsed['key_type'],
        'android_id': settings.get('android_id', 'Not assigned'),
        'device_country': settings.get('device_country', 'Unknown'),
    }

    return build_info


def find_ota_link(settings):
    if 'update_url' not in settings:
        return None

    return {
        'url': settings['update_url'],
        'title': settings.get('update_title', ''),
        'description': settings.get('update_description', ''),
        'precondition': settings.get('update_precondition', ''),
        'postcondition': settings.get('update_postcondition', ''),
        'size': settings.get('update_size', ''),
    }


def get_service_summary(settings):
    return len(settings)


def format_output(fingerprint, settings, build_info, ota_link):
    output = []
    output.append("=" * 63)
    output.append("DEVICE & BUILD INFORMATION")
    output.append("=" * 63)

    output.append("\n[INPUT]")
    output.append(f"  Device Codename:   {build_info['device_codename']}")
    output.append(f"  Android Version:   {build_info['android_version']}")
    output.append(f"  Build Tag:         {build_info['build_tag']}")
    output.append(f"  Build Number:      {build_info['build_number']}")
    output.append(f"  Build Flavor:      {build_info['build_flavor']}")
    output.append(f"  Security Keys:     {build_info['security_keys']}")

    output.append("\n[SERVER RESPONSE]")
    output.append(f"  Total Settings:    {len(settings)}")
    output.append(f"  Android ID:        {build_info['android_id']}")
    output.append(f"  Device Country:    {build_info['device_country']}")

    output.append("\n[OTA UPDATE]")
    if ota_link:
        output.append(f"  Status:            [OK] Update Available")
        if ota_link.get('title'):
            output.append(f"  Title:             {ota_link['title']}")
        output.append(f"\n  Target URL:")
        output.append(f"    {ota_link['url']}")
        if ota_link.get('size'):
            output.append(f"  Size:              {ota_link['size']}")

        if ota_link.get('description'):
            output.append(f"\n  Description:")
            desc = ota_link['description']
            if len(desc) > 70:
                words = desc.split()
                lines = []
                current_line = []
                for word in words:
                    if len(' '.join(current_line + [word])) <= 70:
                        current_line.append(word)
                    else:
                        if current_line:
                            lines.append('    ' + ' '.join(current_line))
                        current_line = [word]
                if current_line:
                    lines.append('    ' + ' '.join(current_line))
                output.extend(lines)
            else:
                output.append(f"    {desc}")

        if ota_link.get('precondition'):
            output.append(f"\n  Precondition:")
            output.append(f"    {ota_link['precondition']}")

        if ota_link.get('postcondition'):
            output.append(f"\n  Postcondition:")
            output.append(f"    {ota_link['postcondition']}")
    else:
        output.append(f"  Status:            [NONE] No Update Available")

    output.append("\n" + "=" * 63)

    return "\n".join(output)


PAYLOAD_METADATA_PREFIXES = [
    'post-build',
    'pre-build',
    'pre-device',
    'post-build-incremental',
    'post-sdk-level',
    'post-security-patch-level',
    'post-timestamp',
    'ota-type',
    'ota-required-cache',
    'pre-build-incremental',
]

EOCD_SIG = b'PK\x05\x06'
CDFH_SIG = b'PK\x01\x02'
LFH_SIG = b'PK\x03\x04'


def _extract_metadata_kv(blob, prefixes):
    result = {}
    for prefix in prefixes:
        needle = f'{prefix}='.encode('utf-8')
        start = blob.find(needle)
        if start == -1:
            continue
        val_start = start + len(needle)
        end = blob.find(b'\n', val_start)
        if end == -1:
            end = len(blob)
        try:
            value = blob[val_start:end].decode('utf-8', errors='replace').strip('\r')
        except Exception:
            continue
        if value:
            result[prefix] = value
    return result


def _parse_all_metadata_lines(blob, known_prefixes):
    try:
        text = blob.decode('utf-8', errors='replace')
    except Exception:
        return {}

    all_lines = {}
    order = []
    for raw_line in text.splitlines():
        line = raw_line.strip('\r').strip()
        if not line or '=' not in line:
            continue
        key, _, value = line.partition('=')
        key = key.strip()
        value = value.strip()
        if not key or not value:
            continue
        if key not in all_lines:
            order.append(key)
        all_lines[key] = value

    result = {}
    for prefix in known_prefixes:
        if prefix in all_lines:
            result[prefix] = all_lines[prefix]

    for key in order:
        if key not in result:
            result[key] = all_lines[key]

    return result


def _scan_zip_central_directory(tail_blob, tail_offset):
    entries = []
    eocd_pos = tail_blob.rfind(EOCD_SIG)
    if eocd_pos == -1:
        return entries

    try:
        cd_size = struct.unpack('<I', tail_blob[eocd_pos + 12:eocd_pos + 16])[0]
        cd_offset = struct.unpack('<I', tail_blob[eocd_pos + 16:eocd_pos + 20])[0]
    except struct.error:
        return entries

    cd_start_in_blob = cd_offset - tail_offset
    if cd_start_in_blob < 0:
        return entries

    pos = cd_start_in_blob
    end = cd_start_in_blob + cd_size
    while pos < end and pos < len(tail_blob) - 46:
        if tail_blob[pos:pos + 4] != CDFH_SIG:
            break
        compression_method = struct.unpack('<H', tail_blob[pos + 10:pos + 12])[0]
        compressed_size = struct.unpack('<I', tail_blob[pos + 20:pos + 24])[0]
        uncompressed_size = struct.unpack('<I', tail_blob[pos + 24:pos + 28])[0]
        name_len = struct.unpack('<H', tail_blob[pos + 28:pos + 30])[0]
        extra_len = struct.unpack('<H', tail_blob[pos + 30:pos + 32])[0]
        comment_len = struct.unpack('<H', tail_blob[pos + 32:pos + 34])[0]
        local_header_offset = struct.unpack('<I', tail_blob[pos + 42:pos + 46])[0]
        name = tail_blob[pos + 46:pos + 46 + name_len]

        entries.append((name, compressed_size, uncompressed_size,
                        compression_method, local_header_offset))

        pos += 46 + name_len + extra_len + comment_len

    return entries


def _find_zip_entry_by_predicate(tail_blob, tail_offset, name_matches):
    eocd_pos = tail_blob.rfind(EOCD_SIG)
    if eocd_pos == -1:
        return None

    try:
        cd_size = struct.unpack('<I', tail_blob[eocd_pos + 12:eocd_pos + 16])[0]
        cd_offset = struct.unpack('<I', tail_blob[eocd_pos + 16:eocd_pos + 20])[0]
    except struct.error:
        return None

    cd_start_in_blob = cd_offset - tail_offset
    if cd_start_in_blob < 0:
        return None

    pos = cd_start_in_blob
    end = cd_start_in_blob + cd_size
    while pos < end and pos < len(tail_blob) - 46:
        if tail_blob[pos:pos + 4] != CDFH_SIG:
            break
        compression_method = struct.unpack('<H', tail_blob[pos + 10:pos + 12])[0]
        compressed_size = struct.unpack('<I', tail_blob[pos + 20:pos + 24])[0]
        name_len = struct.unpack('<H', tail_blob[pos + 28:pos + 30])[0]
        extra_len = struct.unpack('<H', tail_blob[pos + 30:pos + 32])[0]
        comment_len = struct.unpack('<H', tail_blob[pos + 32:pos + 34])[0]
        local_header_offset = struct.unpack('<I', tail_blob[pos + 42:pos + 46])[0]
        name = tail_blob[pos + 46:pos + 46 + name_len]

        if name_matches(name):
            return local_header_offset, compressed_size, compression_method, name.decode(errors='replace')

        pos += 46 + name_len + extra_len + comment_len

    return None


def _find_zip_metadata_entry(tail_blob, tail_offset):
    return _find_zip_entry_by_predicate(
        tail_blob, tail_offset,
        lambda name: name == b'META-INF/com/android/metadata')


def _find_zip_hboot_entry(tail_blob, tail_offset):
    def _is_root_hboot(name):
        try:
            lname = name.decode('utf-8', errors='replace').lower()
        except Exception:
            return False
        return lname == 'hboot.img'

    return _find_zip_entry_by_predicate(tail_blob, tail_offset, _is_root_hboot)


def _find_zip_radio_versions_entry(tail_blob, tail_offset):
    def _is_root_radio_versions(name):
        try:
            lname = name.decode('utf-8', errors='replace').lower()
        except Exception:
            return False
        return lname == 'radio.versions.img'

    return _find_zip_entry_by_predicate(tail_blob, tail_offset, _is_root_radio_versions)


def _extract_version_baseband(blob):
    try:
        text = blob.decode('utf-8', errors='replace')
    except Exception:
        return None

    for raw_line in text.splitlines():
        line = raw_line.strip()
        low = line.lower()
        if low.startswith('version-baseband:'):
            return line.split(':', 1)[1].strip()
        if low.startswith('version-baseband='):
            return line.split('=', 1)[1].strip()
    return None


def _find_zip_update_script_entry(tail_blob, tail_offset):
    return _find_zip_entry_by_predicate(
        tail_blob, tail_offset,
        lambda name: name == b'META-INF/com/google/android/update-script')


_UPDATE_SCRIPT_ASSERT_RE = re.compile(
    r'assert\s+file_contains\s*\(\s*"[^"]*build\.prop"\s*,\s*'
    r'"ro\.build\.fingerprint=([^"]+)"\s*\)\s*==\s*"true"'
    r'(?:\s*\|\|\s*file_contains\s*\(\s*"[^"]*build\.prop"\s*,\s*'
    r'"ro\.build\.fingerprint=([^"]+)"\s*\)\s*==\s*"true")?',
    re.IGNORECASE
)


def _extract_update_script_fingerprints(blob):
    try:
        text = blob.decode('utf-8', errors='replace')
    except Exception:
        return {}

    m = _UPDATE_SCRIPT_ASSERT_RE.search(text)
    if not m:
        return {}

    first_fp = (m.group(1) or '').strip()
    second_fp = (m.group(2) or '').strip() if m.group(2) else ''

    fields = {}
    if second_fp:
        fields['post-build'] = second_fp
        fields['pre-build'] = first_fp
    elif first_fp:
        fields['post-build'] = first_fp
    return fields


def _extract_printable_strings(blob, min_len=4):
    strings = []
    current = bytearray()

    def _flush():
        if len(current) >= min_len:
            strings.append(current.decode('ascii', errors='replace'))
        current.clear()

    for b in blob:
        if 0x20 <= b <= 0x7E:
            current.append(b)
        else:
            _flush()
    _flush()
    return strings


def _extract_hboot_info(head_blob):
    info = {
        'raw_strings': [],
        'hboot_version': None,
        'build_type': None,
        'variant': None,
        'dirty_tag': None,
    }

    scan_region = head_blob[:4096]
    strings = _extract_printable_strings(scan_region, min_len=3)
    info['raw_strings'] = strings

    for s in strings:
        su = s.upper()
        if su.startswith('HBOOT-') and info['hboot_version'] is None:
            info['hboot_version'] = s
        elif su in ('SHIP', 'ENG', 'ENG.G', 'SHIP.G') and info['build_type'] is None:
            info['build_type'] = s
        elif su.startswith('DIRTY-') and info['dirty_tag'] is None:
            info['dirty_tag'] = s
        elif ('SPL' in su or 'EVT' in su or 'DVT' in su or 'PVT' in su) and info['variant'] is None:
            if not su.startswith('HBOOT-') and su not in ('SHIP', 'ENG', 'ENG.G', 'SHIP.G'):
                info['variant'] = s

    return info


DUMMY_OTA_FILLER_NAMES = (b'filler.dat', b'filler.bin', b'padding.dat', b'filler')


def _detect_dummy_ota(tail_blob, tail_offset):
    entries = _scan_zip_central_directory(tail_blob, tail_offset)
    if not entries:
        return None

    metadata_entry = None
    filler_entry = None
    for name, csize, usize, method, offset in entries:
        if name == b'META-INF/com/android/metadata':
            metadata_entry = (csize, usize)
        lower_name = name.lower()
        if any(lower_name.endswith(fn) or fn in lower_name for fn in DUMMY_OTA_FILLER_NAMES):
            if filler_entry is None or usize > filler_entry[1]:
                filler_entry = (name.decode(errors='replace'), usize)

    if metadata_entry is not None and metadata_entry[1] == 0 and filler_entry is not None:
        return {'filler_name': filler_entry[0], 'filler_size': filler_entry[1]}

    return None


def _find_local_metadata_header(data, offset=0):
    pos = offset
    while pos < len(data) - 30:
        idx = data.find(LFH_SIG, pos)
        if idx == -1:
            break
        try:
            name_len = struct.unpack('<H', data[idx+26:idx+28])[0]
            extra_len = struct.unpack('<H', data[idx+28:idx+30])[0]
            if idx + 30 + name_len > len(data):
                pos = idx + 1
                continue
            name = data[idx+30:idx+30+name_len]
            if name == b'META-INF/com/android/metadata':
                compressed_size = struct.unpack('<I', data[idx+18:idx+22])[0]
                compression_method = struct.unpack('<H', data[idx+10:idx+12])[0]
                return idx, compressed_size, compression_method, name.decode()
        except struct.error:
            pass
        pos = idx + 1
    return None


def _fetch_metadata_precise_via_eocd(_get_range, _s, total_size, out, errors):
    try:
        if total_size <= 0:
            return False

        eocd_window = min(total_size, 66 * 1024)
        eocd_start = total_size - eocd_window
        _s("Fetching end-of-central-directory record…")
        eocd_blob = _get_range(f'bytes={eocd_start}-{total_size - 1}')
        out['bytes_scanned'] += len(eocd_blob)

        eocd_pos = eocd_blob.rfind(EOCD_SIG)
        if eocd_pos == -1:
            errors.append("EOCD signature not found in tail window")
            return False

        try:
            cd_size = struct.unpack('<I', eocd_blob[eocd_pos + 12:eocd_pos + 16])[0]
            cd_offset = struct.unpack('<I', eocd_blob[eocd_pos + 16:eocd_pos + 20])[0]
        except struct.error as e:
            errors.append(f"EOCD parse failed: {e}")
            return False

        if cd_size <= 0 or cd_offset < 0 or cd_offset + cd_size > total_size:
            errors.append("EOCD central directory fields look invalid")
            return False

        _s(f"Fetching central directory ({cd_size:,} bytes)…")
        cd_blob = _get_range(f'bytes={cd_offset}-{cd_offset + cd_size - 1}')
        out['bytes_scanned'] += len(cd_blob)

        synthetic_eocd = (
            EOCD_SIG +
            b'\x00\x00\x00\x00' +
            b'\x00\x00\x00\x00' +
            struct.pack('<I', cd_size) +
            struct.pack('<I', 0) +
            b'\x00\x00'
        )
        fake_blob = cd_blob + synthetic_eocd
        entry = _find_zip_metadata_entry(fake_blob, 0)
        if not entry:
            errors.append("META-INF/com/android/metadata not found in central directory (EOCD fast path)")
            return False

        local_header_offset, compressed_size, compression_method, name = entry

        _s(f"Fetching {name} entry ({compressed_size} bytes)…")
        lh_blob = _get_range(f'bytes={local_header_offset}-{local_header_offset + 4096}')
        out['bytes_scanned'] += len(lh_blob)

        if lh_blob[0:4] != LFH_SIG:
            errors.append("Local file header signature mismatch (EOCD fast path)")
            return False

        name_len = struct.unpack('<H', lh_blob[26:28])[0]
        extra_len = struct.unpack('<H', lh_blob[28:30])[0]
        data_start_in_lh_blob = 30 + name_len + extra_len

        if data_start_in_lh_blob + compressed_size <= len(lh_blob):
            entry_data = lh_blob[data_start_in_lh_blob:data_start_in_lh_blob + compressed_size]
        else:
            abs_data_start = local_header_offset + data_start_in_lh_blob
            entry_data = _get_range(f'bytes={abs_data_start}-{abs_data_start + compressed_size - 1}')
            out['bytes_scanned'] += len(entry_data)

        if compression_method == 0:
            plain = entry_data
        elif compression_method == 8:
            try:
                plain = zlib.decompress(entry_data, -15)
            except Exception as e:
                errors.append(f"Inflate failed (EOCD fast path): {e}")
                return False
        else:
            errors.append(f"Unsupported compression method {compression_method} (EOCD fast path)")
            return False

        if not plain:
            return False

        fields = _parse_all_metadata_lines(plain, PAYLOAD_METADATA_PREFIXES)
        if not fields:
            errors.append(
                "Metadata entry decoded but no known keys matched (EOCD fast path, "
                f"first 200 bytes: {plain[:200]!r})")
            return False

        out['found'] = True
        out['fields'] = fields
        out['source'] = f'ZIP entry {name} (method={compression_method}, EOCD fast path)'
        return True

    except Exception as e:
        errors.append(f"EOCD fast path failed: {e}")
        return False


def _fetch_payload_metadata_inner(url, token="", status_cb=None, timeout=30,
                                  chunk_bytes=2 * 1024 * 1024,
                                  return_raw_tail=False,
                                  local_path=None):
    def _s(msg):
        if status_cb:
            status_cb(msg)

    out = {
        'found': False,
        'fields': {},
        'source': None,
        'error': None,
        'bytes_scanned': 0,
    }
    errors = []
    tail_data = b''
    tail_offset = 0
    total_size = 0

    if local_path:
        def _get_range(range_header):
            spec = range_header.split('=', 1)[1]
            start_s, end_s = spec.split('-', 1)
            start = int(start_s)
            end = int(end_s)
            with open(local_path, 'rb') as f:
                f.seek(start)
                return f.read(end - start + 1)

        def _head_size():
            return os.path.getsize(local_path)
    else:
        def _get_range(range_header):
            req_headers = {
                'User-Agent': 'AndroidDownloadManager/14 (Linux; U; Android 14; sdk_gphone64_x86_64 Build/UE1A.230829.036)',
                'Accept-Encoding': 'identity',
                'Range': range_header,
            }
            if token:
                req_headers['Authorization'] = token
            req = urllib.request.Request(url, headers=req_headers)
            ctx = ssl.create_default_context()
            with urllib.request.urlopen(req, timeout=timeout, context=ctx) as resp:
                return resp.read()

        def _head_size():
            head_headers = {
                'User-Agent': 'AndroidDownloadManager/14 (Linux; U; Android 14; sdk_gphone64_x86_64 Build/UE1A.230829.036)',
                'Accept-Encoding': 'identity',
            }
            if token:
                head_headers['Authorization'] = token
            head_req = urllib.request.Request(url, method='HEAD', headers=head_headers)
            ctx = ssl.create_default_context()
            with urllib.request.urlopen(head_req, timeout=timeout, context=ctx) as resp:
                return int(resp.headers.get('Content-Length', '0') or '0')

    try:
        total_size = _head_size()
    except Exception as e:
        errors.append(f"HEAD size lookup failed: {e}")

    if _fetch_metadata_precise_via_eocd(_get_range, _s, total_size, out, errors):
        if return_raw_tail:
            return {'metadata': out, 'tail_data': tail_data, 'tail_offset': tail_offset, 'total_size': total_size}
        return out

    head_data = b''

    if total_size > 0:
        try:
            tail_offset = max(0, total_size - chunk_bytes)
            _s(f"Fetching last {chunk_bytes // 1024 // 1024} MiB…")
            tail_data = _get_range(f'bytes={tail_offset}-{total_size - 1}')
            out['bytes_scanned'] += len(tail_data)
        except Exception as e:
            errors.append(f"Tail fetch failed: {e}")

    if tail_data:
        dummy_info = _detect_dummy_ota(tail_data, tail_offset)
        if dummy_info:
            out['found'] = False
            out['dummy'] = True
            out['filler_name'] = dummy_info['filler_name']
            out['filler_size'] = dummy_info['filler_size']
            out['source'] = 'ZIP central directory (dummy OTA detection)'
            out['error'] = "Dummy OTA file."
            if return_raw_tail:
                return {'metadata': out, 'tail_data': tail_data, 'tail_offset': tail_offset, 'total_size': total_size}
            return out

    if tail_data:
        anchor = -1
        for prefix in PAYLOAD_METADATA_PREFIXES:
            pos = tail_data.find(f'{prefix}='.encode('utf-8'))
            if pos != -1 and (anchor == -1 or pos < anchor):
                anchor = pos
        if anchor != -1:
            search_start = max(0, anchor - 4096)
            block_start = tail_data.rfind(LFH_SIG, search_start, anchor)
            if block_start == -1:
                block_start = search_start
            else:
                try:
                    name_len = struct.unpack('<H', tail_data[block_start + 26:block_start + 28])[0]
                    extra_len = struct.unpack('<H', tail_data[block_start + 28:block_start + 30])[0]
                    block_start = block_start + 30 + name_len + extra_len
                except struct.error:
                    pass
            block_end = tail_data.find(LFH_SIG, anchor)
            if block_end == -1:
                block_end = tail_data.find(CDFH_SIG, anchor)
            if block_end == -1:
                block_end = tail_data.find(EOCD_SIG, anchor)
            if block_end == -1:
                block_end = len(tail_data)
            fields = _parse_all_metadata_lines(tail_data[block_start:block_end], PAYLOAD_METADATA_PREFIXES)
            if fields:
                out['found'] = True
                out['fields'] = fields
                out['source'] = f'tail raw scan ({len(tail_data):,} bytes)'
                if return_raw_tail:
                    return {'metadata': out, 'tail_data': tail_data, 'tail_offset': tail_offset, 'total_size': total_size}
                return out
        fields = _extract_metadata_kv(tail_data, PAYLOAD_METADATA_PREFIXES)
        if fields:
            out['found'] = True
            out['fields'] = fields
            out['source'] = f'tail raw scan ({len(tail_data):,} bytes, partial)'
            if return_raw_tail:
                return {'metadata': out, 'tail_data': tail_data, 'tail_offset': tail_offset, 'total_size': total_size}
            return out

    if tail_data:
        try:
            _s("Parsing ZIP central directory…")
            entry = _find_zip_metadata_entry(tail_data, tail_offset)
            if entry:
                local_header_offset, compressed_size, compression_method, name = entry

                lh_start_in_tail = local_header_offset - tail_offset
                if 0 <= lh_start_in_tail and lh_start_in_tail + 30 <= len(tail_data):
                    lh_blob = tail_data
                    lh_pos = lh_start_in_tail
                else:
                    _s("Fetching local file header…")
                    lh_blob = _get_range(
                        f'bytes={local_header_offset}-{local_header_offset + 4096}')
                    out['bytes_scanned'] += len(lh_blob)
                    lh_pos = 0

                if lh_blob[lh_pos:lh_pos + 4] == LFH_SIG:
                    name_len = struct.unpack('<H', lh_blob[lh_pos + 26:lh_pos + 28])[0]
                    extra_len = struct.unpack('<H', lh_blob[lh_pos + 28:lh_pos + 30])[0]
                    data_start_in_lh_blob = lh_pos + 30 + name_len + extra_len

                    if data_start_in_lh_blob + compressed_size <= len(lh_blob):
                        entry_data = lh_blob[data_start_in_lh_blob:data_start_in_lh_blob + compressed_size]
                    else:
                        abs_data_start = local_header_offset + 30 + name_len + extra_len
                        _s(f"Fetching {name} entry ({compressed_size} bytes)…")
                        entry_data = _get_range(
                            f'bytes={abs_data_start}-{abs_data_start + compressed_size - 1}')
                        out['bytes_scanned'] += len(entry_data)

                    if compression_method == 0:
                        plain = entry_data
                    elif compression_method == 8:
                        try:
                            plain = zlib.decompress(entry_data, -15)
                        except Exception as e:
                            errors.append(f"Inflate failed: {e}")
                            plain = b''
                    else:
                        errors.append(f"Unsupported compression method {compression_method}")
                        plain = b''

                    if plain:
                        fields = _parse_all_metadata_lines(plain, PAYLOAD_METADATA_PREFIXES)
                        if fields:
                            out['found'] = True
                            out['fields'] = fields
                            out['source'] = f'ZIP entry {name} (method={compression_method})'
                            if return_raw_tail:
                                return {'metadata': out, 'tail_data': tail_data, 'tail_offset': tail_offset, 'total_size': total_size}
                            return out
                        else:
                            errors.append(
                                "Metadata entry decoded but no known keys matched "
                                f"(first 200 bytes: {plain[:200]!r})")
                else:
                    errors.append("Local file header signature mismatch")
            else:
                errors.append("META-INF/com/android/metadata not found in central directory")
        except Exception as e:
            errors.append(f"ZIP parse failed: {e}")

    if not out['found'] and total_size > 0:
        head_size = min(total_size, chunk_bytes)
        head_data = b''
        try:
            _s(f"Fetching first {head_size // 1024 // 1024} MiB (head) for local header…")
            head_data = _get_range(f'bytes=0-{head_size-1}')
            out['bytes_scanned'] += len(head_data)
        except Exception as e:
            errors.append(f"Head fetch for local header failed: {e}")

        if head_data:
            entry = _find_local_metadata_header(head_data, 0)
            if entry:
                local_offset, compressed_size, compression_method, name = entry
                name_len = struct.unpack('<H', head_data[local_offset+26:local_offset+28])[0]
                extra_len = struct.unpack('<H', head_data[local_offset+28:local_offset+30])[0]
                data_start = local_offset + 30 + name_len + extra_len
                if data_start + compressed_size <= len(head_data):
                    entry_data = head_data[data_start:data_start+compressed_size]
                else:
                    abs_data_start = data_start
                    _s(f"Fetching {name} entry ({compressed_size} bytes) from head…")
                    entry_data = _get_range(
                        f'bytes={abs_data_start}-{abs_data_start + compressed_size - 1}')
                    out['bytes_scanned'] += len(entry_data)

                if compression_method == 0:
                    plain = entry_data
                elif compression_method == 8:
                    try:
                        plain = zlib.decompress(entry_data, -15)
                    except Exception as e:
                        errors.append(f"Inflate failed (head): {e}")
                        plain = b''
                else:
                    errors.append(f"Unsupported compression method {compression_method} (head)")
                    plain = b''

                if plain:
                    fields = _parse_all_metadata_lines(plain, PAYLOAD_METADATA_PREFIXES)
                    if fields:
                        out['found'] = True
                        out['fields'] = fields
                        out['source'] = f'ZIP entry from head {name} (method={compression_method})'
                        if return_raw_tail:
                            return {'metadata': out, 'tail_data': tail_data, 'tail_offset': tail_offset, 'total_size': total_size}
                        return out
                    else:
                        errors.append("Head metadata entry decoded but no known keys matched")

    if not out['found'] and total_size > 0:
        if not head_data:
            try:
                head_size = min(total_size, chunk_bytes)
                _s(f"Fetching first {head_size // 1024 // 1024} MiB (head) for key scan…")
                head_data = _get_range(f'bytes=0-{head_size-1}')
                out['bytes_scanned'] += len(head_data)
            except Exception as e:
                errors.append(f"Head fetch for key scan failed: {e}")
                head_data = b''
        if head_data:
            fields = _extract_metadata_kv(head_data, PAYLOAD_METADATA_PREFIXES)
            if fields:
                out['found'] = True
                out['fields'] = fields
                out['source'] = f'head raw scan (known prefixes only, {len(head_data):,} bytes)'
                if return_raw_tail:
                    return {'metadata': out, 'tail_data': tail_data, 'tail_offset': tail_offset, 'total_size': total_size}
                return out

    if not out['found'] and tail_data:
        try:
            _s("No metadata file — checking update-script…")
            update_script_entry = _find_zip_update_script_entry(tail_data, tail_offset)
            if update_script_entry:
                local_header_offset, compressed_size, compression_method, name = update_script_entry

                lh_start_in_tail = local_header_offset - tail_offset
                if 0 <= lh_start_in_tail and lh_start_in_tail + 30 <= len(tail_data):
                    lh_blob = tail_data
                    lh_pos = lh_start_in_tail
                else:
                    _s("Fetching update-script local file header…")
                    lh_blob = _get_range(f'bytes={local_header_offset}-{local_header_offset + 4096}')
                    out['bytes_scanned'] += len(lh_blob)
                    lh_pos = 0

                update_script_plain = b''
                if lh_blob[lh_pos:lh_pos + 4] == LFH_SIG:
                    name_len = struct.unpack('<H', lh_blob[lh_pos + 26:lh_pos + 28])[0]
                    extra_len = struct.unpack('<H', lh_blob[lh_pos + 28:lh_pos + 30])[0]
                    data_start_in_lh_blob = lh_pos + 30 + name_len + extra_len

                    if data_start_in_lh_blob + compressed_size <= len(lh_blob):
                        entry_data = lh_blob[data_start_in_lh_blob:data_start_in_lh_blob + compressed_size]
                    else:
                        abs_data_start = local_header_offset + 30 + name_len + extra_len
                        _s(f"Fetching {name} entry ({compressed_size} bytes)…")
                        entry_data = _get_range(
                            f'bytes={abs_data_start}-{abs_data_start + compressed_size - 1}')
                        out['bytes_scanned'] += len(entry_data)

                    if compression_method == 0:
                        update_script_plain = entry_data
                    elif compression_method == 8:
                        try:
                            update_script_plain = zlib.decompress(entry_data, -15)
                        except Exception as e:
                            errors.append(f"Inflate failed (update-script): {e}")
                    else:
                        errors.append(f"Unsupported compression method {compression_method} (update-script)")

                if update_script_plain:
                    fields = _extract_update_script_fingerprints(update_script_plain)
                    if fields:
                        out['found'] = True
                        out['fields'] = fields
                        out['source'] = f'update-script assert scan ({name})'
                        if return_raw_tail:
                            return {'metadata': out, 'tail_data': tail_data, 'tail_offset': tail_offset, 'total_size': total_size}
                        return out
                    else:
                        errors.append("update-script found but no fingerprint assert() line matched")
        except Exception as e:
            errors.append(f"update-script check failed: {e}")

    if not out['found'] and tail_data:
        try:
            _s("No metadata file — checking for hboot.img…")
            hboot_entry = _find_zip_hboot_entry(tail_data, tail_offset)
            if hboot_entry:
                local_header_offset, compressed_size, compression_method, name = hboot_entry

                lh_start_in_tail = local_header_offset - tail_offset
                if 0 <= lh_start_in_tail and lh_start_in_tail + 30 <= len(tail_data):
                    lh_blob = tail_data
                    lh_pos = lh_start_in_tail
                else:
                    _s("Fetching hboot.img local file header…")
                    lh_blob = _get_range(f'bytes={local_header_offset}-{local_header_offset + 4096}')
                    out['bytes_scanned'] += len(lh_blob)
                    lh_pos = 0

                hboot_plain = b''
                if lh_blob[lh_pos:lh_pos + 4] == LFH_SIG:
                    name_len = struct.unpack('<H', lh_blob[lh_pos + 26:lh_pos + 28])[0]
                    extra_len = struct.unpack('<H', lh_blob[lh_pos + 28:lh_pos + 30])[0]
                    data_start_in_lh_blob = lh_pos + 30 + name_len + extra_len

                    want_bytes = min(compressed_size, 65536) if compression_method == 8 else min(compressed_size, 4096)

                    if data_start_in_lh_blob + want_bytes <= len(lh_blob):
                        entry_data = lh_blob[data_start_in_lh_blob:data_start_in_lh_blob + want_bytes]
                    else:
                        abs_data_start = local_header_offset + 30 + name_len + extra_len
                        _s(f"Fetching {name} header bytes…")
                        entry_data = _get_range(
                            f'bytes={abs_data_start}-{abs_data_start + want_bytes - 1}')
                        out['bytes_scanned'] += len(entry_data)

                    if compression_method == 0:
                        hboot_plain = entry_data
                    elif compression_method == 8:
                        try:
                            d = zlib.decompressobj(-15)
                            hboot_plain = d.decompress(entry_data, 8192)
                        except Exception as e:
                            errors.append(f"hboot.img inflate failed: {e}")
                            hboot_plain = b''
                    else:
                        errors.append(f"hboot.img unsupported compression method {compression_method}")

                if hboot_plain:
                    hboot_info = _extract_hboot_info(hboot_plain)
                    out['found'] = True
                    out['is_hboot'] = True
                    out['hboot_info'] = hboot_info
                    fields = {}
                    fields['image-type'] = 'HBOOT image'
                    if hboot_info.get('hboot_version'):
                        fields['hboot-version'] = hboot_info['hboot_version']
                    if hboot_info.get('variant'):
                        fields['variant'] = hboot_info['variant']
                    if hboot_info.get('build_type'):
                        fields['build-type'] = hboot_info['build_type']
                    if hboot_info.get('dirty_tag'):
                        fields['dirty-tag'] = hboot_info['dirty_tag']
                    out['fields'] = fields
                    out['source'] = f'hboot.img banner scan ({name})'
                    if return_raw_tail:
                        return {'metadata': out, 'tail_data': tail_data, 'tail_offset': tail_offset, 'total_size': total_size}
                    return out
                else:
                    errors.append("hboot.img found but banner could not be decoded")
        except Exception as e:
            errors.append(f"hboot.img check failed: {e}")

    out['error'] = " | ".join(errors) if errors else "metadata not found in head or tail"
    if return_raw_tail:
        return {'metadata': out, 'tail_data': tail_data, 'tail_offset': tail_offset, 'total_size': total_size}
    return out


_RADIO_VERSIONS_CACHE = {}


def _fetch_radio_versions_baseband(url, tail_data, tail_offset, local_path=None,
                                   status_cb=None, timeout=30):
    def _s(msg):
        if status_cb:
            status_cb(msg)

    cache_key = local_path or url
    if cache_key in _RADIO_VERSIONS_CACHE:
        cached = _RADIO_VERSIONS_CACHE[cache_key]
        return cached.get('version_baseband')

    if not tail_data:
        return None

    try:
        entry = _find_zip_radio_versions_entry(tail_data, tail_offset)
        if not entry:
            _RADIO_VERSIONS_CACHE[cache_key] = {'version_baseband': None}
            return None

        local_header_offset, compressed_size, compression_method, name = entry

        if local_path:
            def _get_range(range_header):
                spec = range_header.split('=', 1)[1]
                start_s, end_s = spec.split('-', 1)
                start = int(start_s)
                end = int(end_s)
                with open(local_path, 'rb') as f:
                    f.seek(start)
                    return f.read(end - start + 1)
        else:
            def _get_range(range_header):
                req = urllib.request.Request(url, headers={
                    'User-Agent': 'AndroidDownloadManager/14 (Linux; U; Android 14; sdk_gphone64_x86_64 Build/UE1A.230829.036)',
                    'Accept-Encoding': 'identity',
                    'Range': range_header,
                })
                ctx = ssl.create_default_context()
                with urllib.request.urlopen(req, timeout=timeout, context=ctx) as resp:
                    return resp.read()

        lh_start_in_tail = local_header_offset - tail_offset
        if 0 <= lh_start_in_tail and lh_start_in_tail + 30 <= len(tail_data):
            lh_blob = tail_data
            lh_pos = lh_start_in_tail
        else:
            _s(f"Fetching {name} local file header…")
            lh_blob = _get_range(f'bytes={local_header_offset}-{local_header_offset + 4096}')
            lh_pos = 0

        if lh_blob[lh_pos:lh_pos + 4] != LFH_SIG:
            _RADIO_VERSIONS_CACHE[cache_key] = {'version_baseband': None}
            return None

        name_len = struct.unpack('<H', lh_blob[lh_pos + 26:lh_pos + 28])[0]
        extra_len = struct.unpack('<H', lh_blob[lh_pos + 28:lh_pos + 30])[0]
        data_start_in_lh_blob = lh_pos + 30 + name_len + extra_len

        if data_start_in_lh_blob + compressed_size <= len(lh_blob):
            entry_data = lh_blob[data_start_in_lh_blob:data_start_in_lh_blob + compressed_size]
        else:
            abs_data_start = local_header_offset + 30 + name_len + extra_len
            _s(f"Fetching {name} entry ({compressed_size} bytes)…")
            entry_data = _get_range(f'bytes={abs_data_start}-{abs_data_start + compressed_size - 1}')

        if compression_method == 0:
            plain = entry_data
        elif compression_method == 8:
            try:
                plain = zlib.decompress(entry_data, -15)
            except Exception:
                plain = b''
        else:
            plain = b''

        version_baseband = _extract_version_baseband(plain) if plain else None

        _RADIO_VERSIONS_CACHE[cache_key] = {
            'version_baseband': version_baseband,
            'raw_bytes': plain,
        }
        return version_baseband
    except Exception:
        return None


def fetch_payload_metadata(url, token="", status_cb=None, timeout=30,
                           chunk_bytes=2 * 1024 * 1024,
                           return_raw_tail=False,
                           local_path=None):
    result = _fetch_payload_metadata_inner(
        url, token=token, status_cb=status_cb, timeout=timeout,
        chunk_bytes=chunk_bytes, return_raw_tail=True,
        local_path=local_path)

    meta = result['metadata']
    tail_data = result.get('tail_data', b'')
    tail_offset = result.get('tail_offset', 0)

    if meta.get('found'):
        baseband = _fetch_radio_versions_baseband(
            url, tail_data, tail_offset, local_path=local_path,
            status_cb=status_cb, timeout=timeout)
        if baseband:
            meta.setdefault('fields', {})
            meta['fields']['version-baseband'] = baseband

    if return_raw_tail:
        return result
    return meta


LEGACY_LASTMOD_PREFIX = "Mon, 16 May 2016"

OTA_DEVICE_ALIASES = {
    'UNO_sprout': 'sprout-myphone-uno',
    'Sparkle_V_sprout': 'sprout-karbonn',
}


def _ota_alias_device(device):
    return OTA_DEVICE_ALIASES.get(device, device)


def _device_name_candidates_from_url(url):
    try:
        path = urlparse(url).path
        dir_name = path.rsplit('/', 2)[-2] if path.count('/') >= 2 else ''
    except Exception:
        dir_name = ''
    if not dir_name:
        return []
    parts = dir_name.split('_')
    if parts and parts[0].lower() in ('google', 'com'):
        parts = parts[1:]
    candidates = list(parts)
    if len(parts) > 1:
        candidates.append('_'.join(parts))
    return candidates


def _ota_device_name_candidates(device, url=None):
    candidates = []
    aliased = OTA_DEVICE_ALIASES.get(device)
    if aliased:
        candidates.append(aliased)
    if url:
        candidates.extend(_device_name_candidates_from_url(url))
    candidates.append(device)
    if '_' in device:
        candidates.append(device.replace('_', ''))
    seen = set()
    out = []
    for c in candidates:
        if c not in seen:
            seen.add(c)
            out.append(c)
    return out


_OTA_LONGFORM_SUFFIX_RE = re.compile(
    r'^([0-9a-fA-F]{8,40})\.(?:[0-9a-fA-F]{8,40}\.)?(?:[0-9a-fA-F]{8}-)?'
    r'('
    r'(?:loose_ota-)?(?:re_)?(?:un)?(?:signed[_-])+.+'
    r'|incremental-.+'
    r'|[A-Za-z0-9]+\.M\d+_\d+-.+'
    r'|update'
    r')\.zip$'
)


def _split_ota_longform_filename(fname):
    m = _OTA_LONGFORM_SUFFIX_RE.match(fname)
    if not m:
        return None, None
    return m.group(1), m.group(2)


OTA_SHA1_SUFFIX_CACHE = {}


def remember_ota_longform(url):
    fname = urlparse(url).path.rsplit('/', 1)[-1]
    sha1, suffix = _split_ota_longform_filename(fname)
    if sha1:
        OTA_SHA1_SUFFIX_CACHE[sha1.lower()] = suffix


def _ota_suffix_variants(device_and_builds):
    return [
        f"signed-{device_and_builds}",
        f"re_signed-{device_and_builds}",
        f"Dotasigned-{device_and_builds}",
        f"signed-signed-{device_and_builds}",
        f"signed_signed-{device_and_builds}",
        f"loose_ota-signed-{device_and_builds}",
        f"signed-unsigned-{device_and_builds}",
    ]


_OTA_CORE_PARTS_RE = re.compile(
    r'^(?P<device>.+?)(?:-ota)?-(?P<post>[A-Za-z0-9]+)-from-(?P<pre>[A-Za-z0-9]+)(?:[_-].+)?$'
)


def _parse_ota_suffix_core(core):
    core_stripped = re.sub(r'\.[0-9a-fA-F]{8}$', '', core)
    m = _OTA_CORE_PARTS_RE.match(core_stripped)
    if not m:
        return None, None, None
    return m.group('device'), m.group('post'), m.group('pre')


_SIGNED_PREFIXES = ('loose_ota-signed-', 'signed-signed-', 'signed_signed-',
                    'signed-unsigned-', 're_signed-', 'Dotasigned-', 'signed-')


def probe_direct_url_alternate(url, token="", status_cb=None, timeout=12, max_workers=40):
    def _s(msg):
        if status_cb:
            status_cb(msg)

    out = {'checked': False, 'reason': None, 'results': []}

    parsed = urlparse(url)
    dir_path = parsed.path.rsplit('/', 1)[0] + '/'
    base_prefix = f"{parsed.scheme}://{parsed.netloc}{dir_path}"
    fname = parsed.path.rsplit('/', 1)[-1]

    sha1, suffix = _split_ota_longform_filename(fname)

    if sha1:
        OTA_SHA1_SUFFIX_CACHE[sha1.lower()] = suffix

        given_is_doubled = fname.lower().startswith(f"{sha1.lower()}.{sha1.lower()}.")

        core = suffix
        is_signed_family = False
        for pfx in _SIGNED_PREFIXES:
            if core.startswith(pfx):
                core = core[len(pfx):]
                is_signed_family = True
                break

        candidates = [f"{sha1}.zip"]
        seen_candidates = {candidates[0]}

        if is_signed_family:
            for variant_suffix in _ota_suffix_variants(core):
                plain_name = f"{sha1}.{variant_suffix}.zip"
                doubled_name = f"{sha1}.{sha1}.{variant_suffix}.zip"

                if not (variant_suffix == suffix and not given_is_doubled):
                    if plain_name not in seen_candidates:
                        seen_candidates.add(plain_name)
                        candidates.append(plain_name)
                if not (variant_suffix == suffix and given_is_doubled):
                    if doubled_name not in seen_candidates:
                        seen_candidates.add(doubled_name)
                        candidates.append(doubled_name)

            core_device, core_post, core_pre = _parse_ota_suffix_core(core)
            if core_device and core_post and core_pre:
                sha1_stems = [sha1]
                if sha1 and len(sha1) >= 12:
                    sha1_12 = sha1[:12]
                    if sha1_12 != sha1:
                        sha1_stems.append(sha1_12)
                for sha1_stem in sha1_stems:
                    for device_variant in _ota_device_name_candidates(core_device, url=url):
                        for name in build_alternative_filenames(
                                sha1_stem, device_variant, core_post, core_pre, None):
                            if name not in seen_candidates:
                                seen_candidates.add(name)
                                candidates.append(name)

        _s("Trying short (bare sha1) and alternate long-form variants…")
        out['checked'] = True
        out['results'] = check_alternative_ota_names(base_prefix, candidates, token=token, status_cb=status_cb, timeout=timeout, max_workers=max_workers)
        return out

    bare_m = re.match(r'^([0-9a-fA-F]{8,40})\.zip$', fname) or re.match(r'^([A-Za-z0-9_]{6,40})\.zip$', fname)
    if not bare_m:
        out['reason'] = "URL filename doesn't look like a bare sha1.zip or a known long-form OTA name"
        return out

    sha1 = bare_m.group(1)
    known_suffix = OTA_SHA1_SUFFIX_CACHE.get(sha1.lower())
    if not known_suffix:
        out['reason'] = ("Bare sha1.zip given, but no long-form suffix is known yet for this "
                         "sha1 in this session — paste the long-form URL once first.")
        return out

    core = known_suffix
    is_signed_family = False
    for pfx in _SIGNED_PREFIXES:
        if core.startswith(pfx):
            core = core[len(pfx):]
            is_signed_family = True
            break

    candidates = [f"{sha1}.{known_suffix}.zip", f"{sha1}.{sha1}.{known_suffix}.zip"]

    if is_signed_family:
        for variant_suffix in _ota_suffix_variants(core):
            plain_name = f"{sha1}.{variant_suffix}.zip"
            doubled_name = f"{sha1}.{sha1}.{variant_suffix}.zip"
            if plain_name not in candidates:
                candidates.append(plain_name)
            if doubled_name not in candidates:
                candidates.append(doubled_name)

        core_device, core_post, core_pre = _parse_ota_suffix_core(core)
        if core_device and core_post and core_pre:
            sha1_stems = [sha1]
            if sha1 and len(sha1) >= 12:
                sha1_12 = sha1[:12]
                if sha1_12 != sha1:
                    sha1_stems.append(sha1_12)
            for sha1_stem in sha1_stems:
                for device_variant in _ota_device_name_candidates(core_device, url=url):
                    for name in build_alternative_filenames(
                            sha1_stem, device_variant, core_post, core_pre, None):
                        if name not in candidates:
                            candidates.append(name)

    _s("Trying long (descriptive) form, including doubled-sha1 variant…")
    out['checked'] = True
    out['results'] = check_alternative_ota_names(base_prefix, candidates, token=token, status_cb=status_cb, timeout=timeout, max_workers=max_workers)
    return out


def _build_id_from_fingerprint(fingerprint):
    try:
        parsed = parse_fingerprint(fingerprint)
        return parsed['build_tag'], parsed['device'], parsed.get('product')
    except Exception:
        return None, None, None


def _extract_sha1_from_url(url):
    path = urlparse(url).path
    fname = path.rsplit('/', 1)[-1]
    if fname.lower().endswith('.zip'):
        fname = fname[:-4]
    stem = fname.split('.')[0]
    return stem


def build_alternative_filenames(sha1, device, post_build_id, pre_build_id, incremental):
    names = []
    short = sha1[:8] if sha1 else ''
    short12 = sha1[:12] if sha1 and len(sha1) >= 12 else sha1

    if pre_build_id and post_build_id:
        names.append(f"{sha1}.signed-{device}-{post_build_id}-from-{pre_build_id}.zip")
        names.append(f"{sha1}.re_signed-{device}-{post_build_id}-from-{pre_build_id}.zip")
        names.append(f"{sha1}.Dotasigned-{device}-{post_build_id}-from-{pre_build_id}.zip")
        names.append(f"{sha1}.signed-{device}-{post_build_id}-from-{pre_build_id}.{short}.zip")
        names.append(f"{sha1}.re_signed-{device}-{post_build_id}-from-{pre_build_id}.{short}.zip")
        names.append(f"{sha1}.signed-signed-{device}-{post_build_id}-from-{pre_build_id}.zip")
        names.append(f"{sha1}.signed-signed-{device}-{post_build_id}-from-{pre_build_id}.{short}.zip")
        names.append(f"{sha1}.{sha1}.signed-{device}-{post_build_id}-from-{pre_build_id}.zip")
        names.append(f"{sha1}.{sha1}.signed-{device}-{post_build_id}-from-{pre_build_id}.{short}.zip")
        names.append(f"{sha1}.{sha1}.signed_signed-{device}-{post_build_id}-from-{pre_build_id}.zip")
        names.append(f"{sha1}.{sha1}.signed_signed-{device}-{post_build_id}-from-{pre_build_id}.{short}.zip")
        names.append(f"{sha1}.loose_ota-signed-{device}-{post_build_id}-from-{pre_build_id}.zip")
        if short12 != sha1:
            names.append(f"{short12}.signed-{device}-{post_build_id}-from-{pre_build_id}.zip")
            names.append(f"{short12}.signed-{device}-{post_build_id}-from-{pre_build_id}.{short}.zip")
            names.append(f"{short12}.signed-signed-{device}-{post_build_id}-from-{pre_build_id}.zip")
            names.append(f"{short12}.signed-signed-{device}-{post_build_id}-from-{pre_build_id}.{short}.zip")
            names.append(f"{short12}.Dotasigned-{device}-{post_build_id}-from-{pre_build_id}.zip")
            names.append(f"{short12}.Dotasigned-{device}-{post_build_id}-from-{pre_build_id}.{short}.zip")
            names.append(f"{short12}.loose_ota-signed-{device}-{post_build_id}-from-{pre_build_id}.zip")
            names.append(f"{short12}.loose_ota-signed-{device}-{post_build_id}-from-{pre_build_id}.{short}.zip")
        names.append(f"{sha1}.signed-{device}-{post_build_id}-from-{pre_build_id}-full_radio.zip")
        names.append(f"{sha1}.signed-{device}-{post_build_id}-from-{pre_build_id}-fullradio.zip")
        names.append(f"{sha1}.signed-{device}-{post_build_id}-from-{pre_build_id}_full_radio.zip")
        names.append(f"{sha1}.signed-{device}-{post_build_id}-from-{pre_build_id}_fullradio.zip")
        names.append(f"{sha1}.{sha1}.signed-{device}-{post_build_id}-from-{pre_build_id}_full_radio.zip")
        names.append(f"{sha1}.{sha1}.signed-{device}-{post_build_id}-from-{pre_build_id}_fullradio.zip")
        names.append(f"{sha1}.signed-signed-{device}-{post_build_id}-from-{pre_build_id}_full_radio.zip")
        names.append(f"{sha1}.signed-signed-{device}-{post_build_id}-from-{pre_build_id}_fullradio.zip")
        names.append(f"{sha1}.{sha1}.signed-signed-{device}-{post_build_id}-from-{pre_build_id}_full_radio.zip")
        names.append(f"{sha1}.{sha1}.signed-signed-{device}-{post_build_id}-from-{pre_build_id}_fullradio.zip")
        names.append(f"{sha1}.{sha1}.re-signed-{device}-{post_build_id}-from-{pre_build_id}.zip")
        names.append(f"{sha1}.{sha1}.re-signed-{device}-{post_build_id}-from-{pre_build_id}.{short}.zip")
        short_end = sha1[-8:] if sha1 and len(sha1) >= 8 else sha1
        names.append(f"{sha1}.signed-two-step.signed-{device}-{post_build_id}-from-{pre_build_id}.zip")
        names.append(f"{sha1}.signed-two-step.signed-{device}-{post_build_id}-from-{pre_build_id}.{short}.zip")
        names.append(f"{sha1}.signed-two-step.signed-{device}-{post_build_id}-from-{pre_build_id}.{short_end}.zip")
        for extra in ('new-timestamp', 'superblock-fix', 'fullradio-fix-superblock',
                      'restricted-radio', 'factory-recovery-ok', 'radio-restricted',
                      'fullradio'):
            names.append(f"{sha1}.signed-{device}-{post_build_id}-from-{pre_build_id}-{extra}.zip")
            names.append(f"{sha1}.re_signed-{device}-{post_build_id}-from-{pre_build_id}-{extra}.zip")
            names.append(f"{sha1}.{sha1}.re-signed-{device}-{post_build_id}-from-{pre_build_id}.{extra}.zip")
            names.append(f"{sha1}.{sha1}.signed-{device}-{post_build_id}-from-{pre_build_id}-{extra}.zip")
            names.append(f"{sha1}.loose_ota-signed-{device}-{post_build_id}-from-{pre_build_id}-{extra}.zip")
            names.append(f"{sha1}.{sha1}.loose_ota-signed-{device}-{post_build_id}-from-{pre_build_id}-{extra}.zip")

        for extra in (None, 'fullradio-superblock-fix', 'superblock-fix', 'fullradio-fix-superblock',
                      'radio-restricted', 'fullradio'):
            suffix_tail = f"-{extra}" if extra else ""
            names.append(
                f"{sha1}.signed-{device}-ota-{post_build_id}-from-{pre_build_id}{suffix_tail}.zip")
            names.append(
                f"{sha1}.signed-unsigned-{device}-ota-{post_build_id}-from-{pre_build_id}{suffix_tail}.zip")
            names.append(
                f"{sha1}.{short}-signed-unsigned-{device}-ota-{post_build_id}-from-{pre_build_id}{suffix_tail}.zip")
    elif post_build_id and incremental:
        names.append(f"{sha1}.signed-{device}-ota-{incremental}.zip")
        names.append(f"{sha1}.signed-signed-{device}-ota-{incremental}.zip")

    names.append(f"{sha1}.update.zip")

    names.extend(n[:-4] + "1.zip" for n in list(names) if n.endswith(".zip"))

    return names


def check_alternative_ota_names(base_prefix, candidates, token="", status_cb=None, timeout=12,
                                max_workers=40, max_retries=1):
    def _s(msg):
        if status_cb:
            status_cb(msg)

    def _attempt_once(candidate_url):
        try:
            req_headers = {
                'User-Agent': 'AndroidDownloadManager/14 (Linux; U; Android 14; sdk_gphone64_x86_64 Build/UE1A.230829.036)',
                'Accept-Encoding': 'identity',
                'Range': 'bytes=0-0',
            }
            if token:
                req_headers['Authorization'] = token
            req = urllib.request.Request(candidate_url, method='GET', headers=req_headers)
            ctx = ssl.create_default_context()
            with urllib.request.urlopen(req, timeout=timeout, context=ctx) as resp:
                return resp.getcode() in (200, 206), False
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return False, True
            return e.code in (200, 206), False
        except Exception:
            return False, False

    def _check_one(name):
        candidate_url = base_prefix + name
        working, is_404 = _attempt_once(candidate_url)
        attempts = 0
        while not working and not is_404 and attempts < max_retries:
            attempts += 1
            working, is_404 = _attempt_once(candidate_url)
        return name, candidate_url, working

    if not candidates:
        return []

    total = len(candidates)
    results_by_index = [None] * total
    done_count = 0

    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        future_to_index = {
            executor.submit(_check_one, name): i
            for i, name in enumerate(candidates)
        }
        for future in concurrent.futures.as_completed(future_to_index):
            i = future_to_index[future]
            try:
                results_by_index[i] = future.result()
            except Exception:
                results_by_index[i] = (candidates[i], base_prefix + candidates[i], False)
            done_count += 1
            _s(f"Checking alternatives… {done_count}/{total} done")

    return results_by_index


def probe_alternative_filenames(url, last_modified,
                                pre_build_fingerprint, post_build_fingerprint,
                                token="", status_cb=None, timeout=12, max_workers=40):
    def _s(msg):
        if status_cb:
            status_cb(msg)

    out = {'checked': False, 'reason': None, 'results': []}

    base_url = url
    if 'ota-api' in base_url:
        base_url = base_url.replace('ota-api', 'ota')

    parsed = urlparse(base_url)
    dir_path = parsed.path.rsplit('/', 1)[0] + '/'
    base_prefix = f"{parsed.scheme}://{parsed.netloc}{dir_path}"
    sha1 = _extract_sha1_from_url(base_url)

    original_fname = parsed.path.rsplit('/', 1)[-1]

    _longform_markers = ('.signed-', '.signed_', '.Dotasigned-', '.re_signed-',
                         '.loose_ota-', '.incremental-', '.update.')
    if any(marker in original_fname for marker in _longform_markers) or \
            _split_ota_longform_filename(original_fname)[0] is not None:
        pass

    post_build_id, device, product = _build_id_from_fingerprint(post_build_fingerprint) if post_build_fingerprint else (None, None, None)
    pre_build_id, _, _ = _build_id_from_fingerprint(pre_build_fingerprint) if pre_build_fingerprint else (None, None, None)

    incremental = None
    if post_build_fingerprint:
        try:
            incremental = parse_fingerprint(post_build_fingerprint)['incremental']
        except Exception:
            incremental = None

    if not device:
        _fname_sha1, _fname_suffix = _split_ota_longform_filename(original_fname)
        if _fname_suffix:
            _core = _fname_suffix
            for _pfx in _SIGNED_PREFIXES:
                if _core.startswith(_pfx):
                    _core = _core[len(_pfx):]
                    break
            _fd, _fp, _fpr = _parse_ota_suffix_core(_core)
            if _fd and _fp and _fpr:
                device = _fd
                post_build_id = _fp
                pre_build_id = _fpr

    if not device:
        out['reason'] = "Could not determine device codename (post-build fingerprint missing or unparsable)"
        candidates = [f"{sha1}.zip", f"{sha1}.update.zip"]
    else:
        candidates = []
        seen_candidates = set()
        sha1_stems = [sha1]
        if sha1 and len(sha1) >= 12:
            sha1_12 = sha1[:12]
            if sha1_12 != sha1:
                sha1_stems.append(sha1_12)
        device_names = list(dict.fromkeys(
            [device] + ([product] if product and product != device else [])
        ))
        for sha1_stem in sha1_stems:
            for base_device in device_names:
                for device_variant in _ota_device_name_candidates(base_device, url=base_url):
                    for name in build_alternative_filenames(
                            sha1_stem, device_variant, post_build_id, pre_build_id, incremental):
                        if name not in seen_candidates:
                            seen_candidates.add(name)
                            candidates.append(name)

        pre_key = ''
        post_key = ''
        try:
            pre_key = parse_fingerprint(pre_build_fingerprint).get('key_type', '') if pre_build_fingerprint else ''
            post_key = parse_fingerprint(post_build_fingerprint).get('key_type', '') if post_build_fingerprint else ''
        except Exception:
            pass
        if 'dev-keys' in pre_key and 'release-keys' in post_key:
            for base_device in device_names:
                for device_variant in _ota_device_name_candidates(base_device, url=base_url):
                    name = f"{sha1}-{device_variant}-devkeys-to-releasekeys-{post_build_id}.zip"
                    if name not in seen_candidates:
                        seen_candidates.add(name)
                        candidates.append(name)

    if not candidates:
        out['reason'] = "Not enough build info to construct candidate filenames"
        return out

    out['checked'] = True
    _s(f"Checking {len(candidates)} alternative filename(s)…")
    out['results'] = check_alternative_ota_names(base_prefix, candidates, token=token, status_cb=status_cb, timeout=timeout, max_workers=max_workers)

    if out['checked'] and not any(ok for _n, _u, ok in out['results']):
        if last_modified and last_modified.startswith(LEGACY_LASTMOD_PREFIX):
            out['reason'] = ("No alternative names found, but they should exist for this OTA "
                             "(Last-Modified matches the legacy 16 May 2016 naming era).")
        else:
            out['reason'] = "No working alternative names found."

    return out


def probe_ota_url(url, token="", status_cb=None, timeout=15):
    def _s(msg):
        if status_cb:
            status_cb(msg)

    result = {
        'general': [],
        'headers': [],
        'redirects': [],
        'security': [],
        'timing': [],
        'summary': '',
    }

    redirect_chain = []
    current_url = url
    max_redirects = 12
    final_hdrs = {}
    final_status = None
    size_human = ''

    t_start = time.perf_counter()
    t_connect = None
    t_ttfb = None
    tls_done = False

    for hop in range(max_redirects):
        parsed = urlparse(current_url)
        is_https = parsed.scheme == 'https'
        host = parsed.netloc
        path = (parsed.path or '/') + (('?' + parsed.query) if parsed.query else '')

        _s(f"HEAD hop {hop+1}: {host}{path[:60]}...")

        try:
            t0 = time.perf_counter()
            ctx = ssl.create_default_context() if is_https else None

            if is_https:
                conn = http.client.HTTPSConnection(host, timeout=timeout, context=ctx)
            else:
                conn = http.client.HTTPConnection(host, timeout=timeout)

            conn.connect()
            t_connect = (time.perf_counter() - t0) * 1000

            if is_https and not tls_done:
                try:
                    sock = conn.sock
                    cipher_name, proto, bits = sock.cipher()
                    peer_cert = sock.getpeercert()
                    result['security'].append(('Protocol', proto or 'unknown'))
                    result['security'].append(('Cipher Suite', cipher_name or 'unknown'))
                    result['security'].append(('Key Bits', str(bits) if bits else 'unknown'))
                    if peer_cert:
                        subj = dict(x[0] for x in peer_cert.get('subject', []))
                        issuer = dict(x[0] for x in peer_cert.get('issuer', []))
                        result['security'].append(('Cert CN', subj.get('commonName', '—')))
                        result['security'].append(('Cert Org', subj.get('organizationName', '—')))
                        result['security'].append(('Issuer', issuer.get('organizationName', '—')))
                        result['security'].append(('Not Before', peer_cert.get('notBefore', '—')))
                        result['security'].append(('Not After', peer_cert.get('notAfter', '—')))
                        sans = peer_cert.get('subjectAltName', [])
                        if sans:
                            result['security'].append(('SAN', ', '.join(v for _, v in sans)))
                    tls_done = True
                except Exception as tls_err:
                    result['security'].append(('TLS error', str(tls_err)))
            elif not is_https and not tls_done:
                result['security'].append(('Protocol', 'HTTP (no TLS)'))
                tls_done = True

            req_headers = {
                'User-Agent': 'AndroidDownloadManager/14 (Linux; U; Android 14; sdk_gphone64_x86_64 Build/UE1A.230829.036)',
                'Accept-Encoding': 'identity',
                'Connection': 'close',
            }
            if token:
                req_headers['Authorization'] = token
            conn.request('HEAD', path, headers=req_headers)
            resp = conn.getresponse()
            t_ttfb = (time.perf_counter() - t0) * 1000

            status = resp.status
            hdrs = {k.lower(): v for k, v in resp.getheaders()}
            conn.close()

            redirect_chain.append((current_url, status))
            final_hdrs = hdrs
            final_status = status

            if status in (301, 302, 303, 307, 308):
                loc = hdrs.get('location', '')
                if not loc:
                    break
                if loc.startswith('/'):
                    loc = f"{parsed.scheme}://{parsed.netloc}{loc}"
                elif not loc.startswith('http'):
                    loc = f"{parsed.scheme}://{parsed.netloc}/{loc}"
                current_url = loc
                tls_done = False
                continue
            else:
                break

        except Exception as exc:
            result['summary'] = f"Error on hop {hop+1}: {exc}"
            return result

    t_total = (time.perf_counter() - t_start) * 1000

    result['redirects'] = [f"[{code}] {u}" for u, code in redirect_chain]

    final_url = redirect_chain[-1][0] if redirect_chain else url
    gen = result['general']
    gen.append(('Original URL', url))
    gen.append(('Final URL', final_url))
    gen.append(('HTTP Status', f"{final_status} {http.client.responses.get(final_status, '')}"))
    gen.append(('Redirect Hops', str(len(redirect_chain) - 1)))

    cl = final_hdrs.get('content-length', '')
    if cl:
        try:
            sb = int(cl)
            if sb >= 1_073_741_824:
                size_human = f"{sb/1_073_741_824:.2f} GiB"
            elif sb >= 1_048_576:
                size_human = f"{sb/1_048_576:.2f} MiB"
            else:
                size_human = f"{sb/1024:.1f} KiB"
            gen.append(('File Size', f"{size_human}  ({sb:,} bytes)"))
        except ValueError:
            gen.append(('File Size', cl))

    for label, key in [
        ('Content-Type', 'content-type'),
        ('Server', 'server'),
        ('Via', 'via'),
        ('ETag', 'etag'),
        ('Last-Modified', 'last-modified'),
        ('Accept-Ranges', 'accept-ranges'),
        ('Cache-Control', 'cache-control'),
        ('Expires', 'expires'),
        ('Age', 'age'),
    ]:
        v = final_hdrs.get(key)
        if v:
            gen.append((label, v))

    for cdn_key in ('x-cache', 'cf-cache-status', 'x-served-by',
                    'x-cache-hits', 'x-amz-cf-pop', 'x-amz-cf-id'):
        if cdn_key in final_hdrs:
            gen.append((cdn_key, final_hdrs[cdn_key]))

    for dkey in ('content-md5', 'digest', 'x-goog-hash',
                 'x-amz-checksum-sha256', 'x-amz-checksum-crc32'):
        if dkey in final_hdrs:
            gen.append((dkey, final_hdrs[dkey]))

    for gkey in ('x-goog-generation', 'x-goog-metageneration',
                 'x-goog-stored-content-encoding',
                 'x-goog-stored-content-length',
                 'x-goog-storage-class', 'x-goog-expiration',
                 'x-guploader-uploadid', 'x-robots-tag',
                 'x-goog-download-filename'):
        if gkey in final_hdrs:
            gen.append((gkey, final_hdrs[gkey]))

    gen_val = final_hdrs.get('x-goog-generation', '')
    if gen_val:
        try:
            import datetime as _dt_mod
            ts_sec = int(gen_val) / 1_000_000
            dt = _dt_mod.datetime.utcfromtimestamp(ts_sec)
            gen.append(('Created (from generation)', dt.strftime('%Y-%m-%d %H:%M:%S UTC')))
        except Exception:
            pass

    for skey in ('strict-transport-security', 'access-control-allow-origin',
                 'x-content-type-options', 'x-frame-options',
                 'content-security-policy', 'permissions-policy',
                 'cross-origin-resource-policy'):
        if skey in final_hdrs:
            gen.append((skey, final_hdrs[skey]))

    result['headers'] = sorted(final_hdrs.items())

    tim = result['timing']
    if t_connect is not None:
        tim.append(('TCP + TLS handshake', f"{t_connect:.1f} ms"))
    if t_ttfb is not None:
        tim.append(('Time to first byte', f"{t_ttfb:.1f} ms"))
    tim.append(('Total probe time', f"{t_total:.1f} ms"))

    nhops = len(redirect_chain) - 1
    result['summary'] = (
        f"Done - HTTP {final_status}, {nhops} redirect(s), "
        f"{len(final_hdrs)} response headers"
        + (f", {size_human}" if size_human else "")
    )
    return result


class OTAProberGUI:

    APP_BG = '#f0f0f0'
    HISTORY_PAGE_SIZE = 20
    COLLECTION_PAGE_SIZE = 20

    KEY_TYPES_ALL = [
        "user/release-keys",
        "userdebug/release-keys",
        "eng/release-keys",
        "user/dev-keys",
        "user/test-keys",
        "userdebug/dev-keys",
        "userdebug/test-keys",
        "eng/dev-keys",
        "eng/test-keys",
    ]

    COLLECTION_SORT_OPTIONS = [
        ("Last seen (newest)", "last_seen_desc"),
        ("Last seen (oldest)", "last_seen_asc"),
        ("First seen (newest)", "first_seen_desc"),
        ("First seen (oldest)", "first_seen_asc"),
        ("Title (A-Z)", "title_asc"),
        ("Title (Z-A)", "title_desc"),
        ("Size (largest)", "size_desc"),
        ("Size (smallest)", "size_asc"),
    ]

    def __init__(self, root):
        self.root = root
        self.root.title("OTA Prober")
        self.root.geometry("1000x950")
        self.root.configure(bg='#f0f0f0')

        self.setup_styles()
        self.create_widgets()
        self.query_thread = None
        self.keyscan_thread = None

        self._setup_layout_independent_shortcuts()

        self._brute_log_buffer = []
        self._brute_log_window = None
        self._brute_log_text = None
        self._brute_log_lock = threading.Lock()
        self._brute_log_pending = []
        self._brute_log_poll_scheduled = False

        self._urlbrute_log_buffer = []
        self._urlbrute_log_window = None
        self._urlbrute_log_text = None
        self._urlbrute_log_lock = threading.Lock()
        self._urlbrute_log_pending = []
        self._urlbrute_log_poll_scheduled = False
        self._urlbrute_running = False
        self._urlbrute_stop_flag = False
        self._urlbrute_pause_event = threading.Event()
        self._urlbrute_pause_event.set()
        self._urlbrute_queue = None
        self._urlbrute_worker_threads = []
        self._urlbrute_found_count = 0
        self._urlbrute_checked_count = 0
        self._urlbrute_total_count = 0
        self._urlbrute_lock = threading.Lock()

        self._devbrute_log_buffer = []
        self._devbrute_log_window = None
        self._devbrute_log_text = None
        self._devbrute_log_lock = threading.Lock()
        self._devbrute_log_pending = []
        self._devbrute_log_poll_scheduled = False
        self._devbrute_running = False
        self._devbrute_stop_flag = False
        self._devbrute_pause_event = threading.Event()
        self._devbrute_pause_event.set()
        self._devbrute_queue = None
        self._devbrute_producer_thread = None
        self._devbrute_worker_threads = []
        self._devbrute_found_count = 0
        self._devbrute_checked_count = 0
        self._devbrute_total = 0
        self._devbrute_lock = threading.Lock()
        self._devbrute_speed = 0.0
        self._devbrute_speed_ts = 0.0
        self._devbrute_speed_count = 0
        self._devbrute_wordlist_path = ""

        self.notebook.bind('<<NotebookTabChanged>>', self._on_tab_changed)

        self._download_ota_window = None
        self._download_progress_var = None
        self._download_status_var = None
        self._download_speed_var = None
        self._download_thread = None
        self._download_stop_event = threading.Event()

        self._ser_page_size = 500
        self._ser_pages = {"serials": 0, "imeis": 0, "other": 0}
        self._ser_sort_col = {"serials": "value", "imeis": "value", "other": "value"}
        self._ser_sort_dir = {"serials": "asc", "imeis": "asc", "other": "asc"}
        self._ser_total_items = {"serials": 0, "imeis": 0, "other": 0}

        self.dogfood_detected = False

    def _setup_layout_independent_shortcuts(self):
        CTRL_CHARS = {
            '\x03': 'copy',
            '\x16': 'paste',
            '\x18': 'cut',
            '\x01': 'all',
        }

        def get_focused_text_widget():
            w = self.root.focus_get()
            if isinstance(w, (tk.Entry, ttk.Entry, tk.Text, scrolledtext.ScrolledText)):
                return w
            return None

        def do_copy(w):
            try:
                if isinstance(w, (tk.Entry, ttk.Entry)):
                    if w.selection_present():
                        text = w.selection_get()
                        self.root.clipboard_clear()
                        self.root.clipboard_append(text)
                else:
                    if w.tag_ranges(tk.SEL):
                        text = w.get(tk.SEL_FIRST, tk.SEL_LAST)
                        self.root.clipboard_clear()
                        self.root.clipboard_append(text)
            except tk.TclError:
                pass

        def do_paste(w):
            try:
                clip = self.root.clipboard_get()
                if isinstance(w, (tk.Entry, ttk.Entry)):
                    if w.selection_present():
                        w.delete(tk.SEL_FIRST, tk.SEL_LAST)
                    w.insert(tk.INSERT, clip)
                else:
                    if w.tag_ranges(tk.SEL):
                        w.delete(tk.SEL_FIRST, tk.SEL_LAST)
                    w.insert(tk.INSERT, clip)
            except tk.TclError:
                pass

        def do_cut(w):
            try:
                if isinstance(w, (tk.Entry, ttk.Entry)):
                    if w.selection_present():
                        text = w.selection_get()
                        self.root.clipboard_clear()
                        self.root.clipboard_append(text)
                        w.delete(tk.SEL_FIRST, tk.SEL_LAST)
                else:
                    if w.tag_ranges(tk.SEL):
                        text = w.get(tk.SEL_FIRST, tk.SEL_LAST)
                        self.root.clipboard_clear()
                        self.root.clipboard_append(text)
                        w.delete(tk.SEL_FIRST, tk.SEL_LAST)
            except tk.TclError:
                pass

        def do_select_all(w):
            try:
                if isinstance(w, (tk.Entry, ttk.Entry)):
                    w.selection_range(0, tk.END)
                else:
                    w.tag_add(tk.SEL, '1.0', tk.END)
            except tk.TclError:
                pass

        def on_key(event):
            if not (event.state & 0x4):
                return

            if event.keysym.lower() in ('c', 'v', 'x'):
                return

            action = CTRL_CHARS.get(event.char)

            w = get_focused_text_widget()
            if not w:
                return

            if action == 'copy':
                do_copy(w)
            elif action == 'paste':
                do_paste(w)
            elif action == 'cut':
                do_cut(w)
            elif action == 'all' or event.keysym.lower() == 'a':
                do_select_all(w)
            else:
                return

            return "break"

        self.root.bind_all('<Key>', on_key)

    def setup_styles(self):
        style = ttk.Style()
        style.theme_use('clam')

        style.configure('Header.TLabel', font=('Arial', 12, 'bold'), background='#f0f0f0')
        style.configure('Normal.TLabel', font=('Arial', 10), background='#f0f0f0')
        style.configure('Title.TLabel', font=('Arial', 14, 'bold'), background='#f0f0f0')

    def _brute_export_log(self):
        with self._brute_log_lock:
            if not self._brute_log_buffer:
                messagebox.showinfo("Export Log", "Logs are empty.")
                return
            content = "\n".join(msg for msg, _ in self._brute_log_buffer)

        file_path = filedialog.asksaveasfilename(
            title="Save logs",
            defaultextension=".txt",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")]
        )
        if not file_path:
            return

        try:
            with open(file_path, "w", encoding="utf-8") as f:
                f.write(content)
            self.brute_status_var.set(f"Saved: {os.path.basename(file_path)}")
        except Exception as e:
            messagebox.showerror("Export Error", f"Unable to save:\n{e}")

    def create_widgets(self):
        main_frame = ttk.Frame(self.root, padding="10")
        main_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))

        title_row = ttk.Frame(main_frame)
        title_row.grid(row=0, column=0, columnspan=3, sticky=(tk.W, tk.E), pady=(0, 20))

        self.app_title_var = tk.StringVar(value="Android OTA Prober")
        title = ttk.Label(title_row, textvariable=self.app_title_var, style='Title.TLabel')
        title.bind('<Button-1>', lambda e: messagebox.showinfo("RYuh", "hold on, im licking some bilds..."))
        title.pack(side=tk.LEFT)

        mode_frame = ttk.Frame(title_row)
        mode_frame.pack(side=tk.LEFT, padx=(20, 0))

        self.os_mode_var = tk.StringVar(value="android")
        ttk.Radiobutton(mode_frame, text="Android", variable=self.os_mode_var,
                        value="android", command=self._on_os_mode_changed).grid(row=0, column=0, padx=(0, 15))
        ttk.Radiobutton(mode_frame, text="Xiaomi", variable=self.os_mode_var,
                        value="xiaomi", command=self._on_os_mode_changed).grid(row=0, column=1, padx=(0, 15))
        ttk.Radiobutton(mode_frame, text="ChromeOS", variable=self.os_mode_var,
                        value="chromeos", command=self._on_os_mode_changed).grid(row=0, column=2, padx=(0, 15))
        ttk.Radiobutton(mode_frame, text="Play Games Emulator", variable=self.os_mode_var,
                        value="playemu", command=self._on_os_mode_changed).grid(row=0, column=3, padx=(0, 15))

        history_frame = ttk.Frame(title_row)
        history_frame.pack(side=tk.RIGHT)

        self.collection_button = ttk.Button(history_frame, text="📦 Collection", command=self.open_collection_window)
        self.collection_button.pack(side=tk.RIGHT, padx=(6, 0))

        self.history_button = ttk.Button(history_frame, text="🕘 History", command=self.open_history_window)
        self.history_button.pack(side=tk.RIGHT, padx=(6, 0))

        self.additional_features_button = ttk.Button(
            history_frame, text="🧩 Scan URLs",
            command=self.open_additional_features_window)
        self.additional_features_button.pack(side=tk.RIGHT, padx=(6, 0))

        self.scan_fingerprints_button = ttk.Button(
            history_frame, text="🧬 Scan Fingerprints",
            command=self.open_scan_fingerprints_window)
        self.scan_fingerprints_button.pack(side=tk.RIGHT, padx=(6, 0))

        self.serials_imeis_button = ttk.Button(
            history_frame, text="🔢 Serials/IMEIs",
            command=self.open_serials_imeis_window)
        self.serials_imeis_button.pack(side=tk.RIGHT, padx=(6, 0))

        self.download_ota_button = ttk.Button(
            history_frame, text="⬇️ Download OTA",
            command=self.open_download_ota_window)
        self.download_ota_button.pack(side=tk.RIGHT, padx=(6, 0))

        self.cros_board_preset_var = tk.StringVar(value=next(iter(CROS_BOARD_APPID_MAP.keys())))
        self.cros_appid_var = tk.StringVar(value=next(iter(CROS_BOARD_APPID_MAP.values())))

        self.input_frame = ttk.LabelFrame(main_frame, text="Device Fingerprint", padding="10")
        self.input_frame.grid(row=2, column=0, columnspan=3, sticky=(tk.W, tk.E), pady=(0, 15))
        input_frame = self.input_frame

        ttk.Label(input_frame, text="Enter fingerprint:", style='Normal.TLabel').grid(row=0, column=0, sticky=tk.W, pady=5)

        self.device_sn_label = ttk.Label(input_frame, text="Device SN (Optional):", style='Normal.TLabel')
        self.device_sn_label.grid(row=0, column=1, sticky=tk.W, padx=5, pady=5)

        self.fingerprint_var = tk.StringVar()
        self.fingerprint_entry = ttk.Entry(input_frame, textvariable=self.fingerprint_var, width=70, font=('Courier', 10))
        self.fingerprint_entry.grid(row=1, column=0, sticky=(tk.W, tk.E), pady=5)
        self.fingerprint_entry.insert(0, "google/shamu/shamu:5.1/LYZ28E/1858530:user/release-keys")

        self.device_sn_var = tk.StringVar()
        self.device_sn_entry = ttk.Entry(input_frame, textvariable=self.device_sn_var, width=20, font=('Courier', 10))
        self.device_sn_entry.grid(row=1, column=1, sticky=(tk.W, tk.E), padx=5, pady=5)

        self.imei_label = ttk.Label(input_frame, text="IMEI (Optional):", style='Normal.TLabel')
        self.imei_label.grid(row=0, column=2, sticky=tk.W, padx=5, pady=5)

        self.imei_var = tk.StringVar()
        self.imei_entry = ttk.Entry(input_frame, textvariable=self.imei_var, width=20, font=('Courier', 10))
        self.imei_entry.grid(row=1, column=2, sticky=(tk.W, tk.E), padx=5, pady=5)

        self.fingerprint_format_var = tk.StringVar(
            value="Format: oem/product/device:api/build_tag/incremental:build_type/key_type")
        ttk.Label(input_frame, textvariable=self.fingerprint_format_var,
                  style='Normal.TLabel', foreground='#666666').grid(row=2, column=0, sticky=tk.W)

        input_frame.columnconfigure(0, weight=1)
        input_frame.columnconfigure(1, weight=0)
        self._cros_appid_row_widgets = []
        self._cros_only_widgets = []

        self.params_frame = ttk.LabelFrame(main_frame, text="Request Parameters", padding="10")
        self.params_frame.grid(row=3, column=0, columnspan=3, sticky=(tk.W, tk.E), pady=(0, 15))

        ttk.Label(self.params_frame, text="Locale:", style='Normal.TLabel').grid(row=0, column=0, sticky=tk.W, padx=5)
        self.locale_var = tk.StringVar(value="en-US")
        self.locale_combo = ttk.Combobox(self.params_frame, textvariable=self.locale_var, width=20)
        locale_list = sorted(LOCALE_TZ_MAP.keys())
        self.locale_combo['values'] = locale_list
        self.locale_combo.grid(row=0, column=1, sticky=tk.W, padx=5)
        self.locale_combo.bind('<<ComboboxSelected>>', self._on_locale_selected)
        self.locale_combo.bind('<KeyRelease>', self._on_locale_typed)

        ttk.Label(self.params_frame, text="Timezone:", style='Normal.TLabel').grid(row=0, column=2, sticky=tk.W, padx=5)
        self.timezone_var = tk.StringVar(value="America/New_York")
        tz_combo = ttk.Combobox(self.params_frame, textvariable=self.timezone_var, width=24)
        tz_combo['values'] = sorted(set(LOCALE_TZ_MAP.values()) | set(EXTRA_TZ))
        tz_combo.grid(row=0, column=3, sticky=tk.W, padx=5)

        ttk.Button(self.params_frame, text="Set Default", command=self.reset_params).grid(row=0, column=4, padx=10)

        options_frame = ttk.LabelFrame(main_frame, text="Options", padding="10")
        options_frame.grid(row=4, column=0, columnspan=3, sticky=(tk.W, tk.E), pady=(0, 15))

        self.json_var = tk.BooleanVar(value=False)
        self.json_check = ttk.Checkbutton(options_frame, text="Output as JSON", variable=self.json_var)
        self.json_check.grid(row=0, column=0, sticky=tk.W, padx=5)

        self.save_var = tk.BooleanVar(value=False)
        self.save_check = ttk.Checkbutton(options_frame, text="Save to file", variable=self.save_var)
        self.save_check.grid(row=0, column=1, sticky=tk.W, padx=5)

        self.scan_locales_label = ttk.Label(options_frame, text="Scan Locales (comma/space separated):", style='Normal.TLabel')
        self.scan_locales_label.grid(row=0, column=2, sticky=tk.W, padx=(20, 5))
        self.scan_locales_var = tk.StringVar(value="en-US,uk-UA,zh-CN")
        self.scan_locales_entry = ttk.Entry(options_frame, textvariable=self.scan_locales_var, width=30)
        self.scan_locales_entry.grid(row=0, column=3, sticky=tk.W, padx=5)

        _CHECKIN_URLS = [
            'http://android.googleapis.com/checkin',
            'http://device-provisioning.googleapis.com/checkin',
            'http://android.clients.google.com/checkin',
            'http://checkin.gstatic.com/checkin',
            'http://jmt17.google.com/checkin',
            'http://checkin.gstatic-cn.com/checkin',
        ]
        self.checkin_url_label = ttk.Label(options_frame, text="Checkin URL:", style='Normal.TLabel')
        self.checkin_url_label.grid(row=0, column=4, sticky=tk.W, padx=(20, 5))
        self.checkin_url_var = tk.StringVar(value=_CHECKIN_URLS[0])
        self.checkin_url_combo = ttk.Combobox(
            options_frame,
            textvariable=self.checkin_url_var,
            values=_CHECKIN_URLS,
            width=42,
        )
        self.checkin_url_combo.grid(row=0, column=5, sticky=tk.W, padx=5)

        button_frame = ttk.Frame(main_frame)
        button_frame.grid(row=5, column=0, columnspan=3, sticky=(tk.W, tk.E), pady=(0, 15))

        self.query_button = ttk.Button(button_frame, text="Query Device", command=self.on_query_click)
        self.query_button.pack(side=tk.LEFT, padx=5)

        self.keyscan_button = ttk.Button(button_frame, text="Scan Key Types", command=self.on_keyscan_click)
        self.keyscan_button.pack(side=tk.LEFT, padx=5)
        self._keyscan_button_pack_info = {'side': tk.LEFT, 'padx': 5}

        self.otachain_button = ttk.Button(button_frame, text="OTA Chain Check", command=self.on_otachain_click)
        self.otachain_button.pack(side=tk.LEFT, padx=5)
        self._otachain_button_pack_info = {'side': tk.LEFT, 'padx': 5}

        self.keyscan_stop_button = ttk.Button(button_frame, text="⏹ Stop Scan", command=self.on_stop_scan_click, state=tk.DISABLED)
        self.keyscan_stop_button.pack(side=tk.LEFT, padx=5)
        self._keyscan_stop_button_pack_info = {'side': tk.LEFT, 'padx': 5}
        self._keyscan_stop_event = threading.Event()
        self._otachain_stop_event = threading.Event()

        self.clear_button = ttk.Button(button_frame, text="Clear Output", command=self.on_clear_click)
        self.clear_button.pack(side=tk.LEFT, padx=5)

        self.copy_button = ttk.Button(button_frame, text="Copy to Clipboard", command=self.on_copy_click)
        self.copy_button.pack(side=tk.LEFT, padx=5)

        self.cros_header_frame = ttk.Frame(button_frame)
        self.cros_header_frame.pack(side=tk.LEFT, padx=(10, 0))
        ttk.Label(self.cros_header_frame, text="Board:").pack(side=tk.LEFT, padx=(0, 3))
        self.cros_board_label = ttk.Label(self.cros_header_frame, text="")
        self.cros_board_combo = ttk.Combobox(self.cros_header_frame, textvariable=self.cros_board_preset_var, width=18)
        self.cros_board_combo['values'] = list(CROS_BOARD_APPID_MAP.keys()) + ['(custom)']
        self.cros_board_combo.pack(side=tk.LEFT, padx=(0, 6))
        self.cros_board_combo.bind('<<ComboboxSelected>>', self._on_cros_board_preset_selected)
        ttk.Label(self.cros_header_frame, text="App ID:").pack(side=tk.LEFT, padx=(0, 3))
        self.cros_appid_label = ttk.Label(self.cros_header_frame, text="")
        self.cros_appid_combo = ttk.Combobox(self.cros_header_frame, textvariable=self.cros_appid_var, width=36)
        self.cros_appid_combo['values'] = list(CROS_BOARD_APPID_MAP.values())
        self.cros_appid_combo.pack(side=tk.LEFT)
        self.cros_appid_combo.configure(state='normal')

        self.playemu_editor_frame = ttk.LabelFrame(main_frame, text="Play Games Emulator — Omaha Request", padding="6")
        self.playemu_editor_frame.grid(row=6, column=0, columnspan=3, sticky=(tk.W, tk.E), pady=(0, 10))
        self._build_playemu_editor(self.playemu_editor_frame)

        status_bar = ttk.Frame(main_frame)
        status_bar.grid(row=7, column=0, columnspan=3, sticky=(tk.W, tk.E), pady=(0, 10))
        self.status_var = tk.StringVar(value="Ready")
        self.status_label = ttk.Label(status_bar, textvariable=self.status_var, foreground='#0066cc', style='Normal.TLabel')
        self.status_label.pack(side=tk.LEFT)

        self.dogfood_label = ttk.Label(status_bar, text="", foreground='#cc9900', style='Normal.TLabel', font=('Arial', 9, 'bold'))
        self.dogfood_label.pack(side=tk.RIGHT)

        output_frame = ttk.LabelFrame(main_frame, text="Results", padding="10")
        output_frame.grid(row=8, column=0, columnspan=3, sticky=(tk.W, tk.E, tk.N, tk.S), pady=(0, 0))

        header_frame = ttk.Frame(output_frame)
        header_frame.pack(fill=tk.X, pady=(0, 10))

        self.status_icon_var = tk.StringVar(value="")
        self.status_icon_label = ttk.Label(header_frame, textvariable=self.status_icon_var, font=('Arial', 16))
        self.status_icon_label.pack(side=tk.LEFT, padx=(0, 10))

        self.copy_link_button = ttk.Button(header_frame, text="Copy link", command=self.on_copy_link_click, state=tk.DISABLED)
        self.copy_link_button.pack(side=tk.RIGHT, padx=(10, 0))

        self.ota_link_label = ttk.Label(header_frame, text="", font=('Courier', 10), anchor=tk.W)
        self.ota_link_label.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.ota_link_label.bind('<Button-1>', self.on_header_link_click)

        self.notebook = NOTEBOOK_CLS(output_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        self.desc_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.desc_frame, text="Description")

        if HtmlFrame:
            self.html_frame = HtmlFrame(self.desc_frame)
            self.html_frame.pack(fill=tk.BOTH, expand=True)
            self.desc_text = None
        else:
            self.desc_text = scrolledtext.ScrolledText(
                self.desc_frame,
                wrap=tk.WORD,
                width=120,
                height=20,
                font=('Arial', 10),
                bg='white',
                fg='#333333'
            )
            self.desc_text.pack(fill=tk.BOTH, expand=True)
            self.html_frame = None

        self.log_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.log_frame, text="Full Log")

        self.output_text = scrolledtext.ScrolledText(
            self.log_frame,
            wrap=tk.WORD,
            width=120,
            height=20,
            font=('Courier', 9),
            bg='white',
            fg='#333333'
        )
        self.output_text.pack(fill=tk.BOTH, expand=True)

        self.output_text.tag_configure('header', foreground='#0066cc', font=('Courier', 10, 'bold'))
        self.output_text.tag_configure('success', foreground='#006600', font=('Courier', 9, 'bold'))
        self.output_text.tag_configure('error', foreground='#cc0000', font=('Courier', 9, 'bold'))
        self.output_text.tag_configure('info', foreground='#666666', font=('Courier', 9))
        self.output_text.tag_configure('link', foreground='#0066cc', font=('Courier', 9, 'underline'))
        self.output_text.tag_configure('section', foreground='#004499', font=('Courier', 10, 'bold'))

        self.output_text.tag_bind('link', '<Button-1>', self.on_link_click)
        self.output_text.tag_bind('link', '<Enter>', lambda e: self.output_text.config(cursor='hand2'))
        self.output_text.tag_bind('link', '<Leave>', lambda e: self.output_text.config(cursor='xterm'))

        self.url_map = {}
        self.current_ota_link = None
        self.current_ota_precondition = ''
        self.current_ota_postcondition = ''

        self.raw_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.raw_frame, text="Raw Response")
        self._build_raw_tab()

        self.raw_req_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.raw_req_frame, text="Raw Request")
        self._build_raw_request_tab()

        self.httpinfo_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.httpinfo_frame, text="HTTP Info")
        self._build_httpinfo_tab()

        self.brute_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.brute_frame, text="Bruteforce")
        self._build_bruteforce_tab()

        self.urlbrute_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.urlbrute_frame, text="URL Bruteforce")
        self._build_urlbrute_tab()

        self.devbrute_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.devbrute_frame, text="Device Bruteforce")
        self._build_devbrute_tab()

        self.rawreq_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.rawreq_frame, text="Send Raw Request")
        self._build_rawreq_tab()

        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)
        main_frame.columnconfigure(0, weight=1)
        main_frame.rowconfigure(8, weight=1)

        self._set_os_mode_visibility()

    def _set_ota_link_header(self, url, max_chars=110):
        display = url
        if len(display) > max_chars:
            head = max_chars * 2 // 3
            tail = max_chars - head - 1
            display = f"{display[:head]}…{display[-tail:]}"
        self.ota_link_label.config(text=f"🔗 {display}", foreground='#0066cc')

    def _on_tab_changed(self, event):
        current = self.notebook.index(self.notebook.select())
        tab_text = self.notebook.tab(current, "text")
        mode = self.os_mode_var.get()
        _brute_tabs = ("Bruteforce", "URL Bruteforce", "Device Bruteforce", "Send Raw Request")
        if tab_text in _brute_tabs or mode in ("chromeos", "xiaomi", "playemu"):
            self.params_frame.grid_remove()
        else:
            self.params_frame.grid()

        if tab_text == "HTTP Info":
            self._on_httpinfo_subtab_changed()

    def _update_input_frame_visibility(self):
        mode = self.os_mode_var.get()
        if mode == "playemu":
            self.input_frame.grid_remove()
        else:
            self.input_frame.grid()

    def _on_httpinfo_subtab_changed(self, event=None):
        try:
            sub_tab = self.httpinfo_nb.select()
            sub_text = self.httpinfo_nb.tab(sub_tab, "text")
        except Exception:
            return

        local_capable_tabs = ("Payload Metadata", "ZIP Tree")
        if hasattr(self, 'httpinfo_local_btn'):
            if sub_text in local_capable_tabs:
                if not self.httpinfo_local_btn.winfo_ismapped():
                    self.httpinfo_local_btn.pack(side=tk.LEFT, padx=(8, 0))
            else:
                self.httpinfo_local_btn.pack_forget()

        if sub_text == "ZIP Tree":
            has_source = bool(self.httpinfo_url_var.get().strip()) or bool(self.httpinfo_local_path)
            if has_source and not self.zip_tree.get_children():
                self._httpinfo_zip_tree_scan()

    def _httpinfo_choose_local_file(self):
        path = filedialog.askopenfilename(
            title="Choose OTA / ZIP file",
            filetypes=[("ZIP / OTA files", "*.zip *.bin"), ("All files", "*.*")]
        )
        if not path:
            return
        self.httpinfo_local_path = path
        self.httpinfo_url_var.set(path)
        self.zip_tree_cache = {
            'url': None,
            'tail_data': None,
            'tail_offset': 0,
            'total_size': 0,
            'entries': None,
        }
        for child in self.zip_tree.get_children():
            self.zip_tree.delete(child)
        self.httpinfo_status_var.set(f"Local file selected: {os.path.basename(path)}")
        self._httpinfo_start()

    def _on_cros_board_preset_selected(self, event):
        board = self.cros_board_preset_var.get().strip()
        if board == '(custom)' or board not in CROS_BOARD_APPID_MAP:
            return
        app_id = CROS_BOARD_APPID_MAP[board]
        hwid = CROS_BOARD_HWID_MAP.get(board, 'NNNN')
        self.cros_appid_var.set(app_id)
        track = 'stable-channel'
        current = self.fingerprint_var.get().strip()
        try:
            parsed = parse_fingerprint_chromeos(current)
            track = parsed['track']
        except Exception:
            pass
        self.fingerprint_var.set(f"{board}/0.0.0.0:{track}/{hwid}")

    def _on_os_mode_changed(self):
        self._set_os_mode_visibility()
        mode = self.os_mode_var.get()
        if mode == "chromeos":
            self.app_title_var.set("ChromeOS OTA Prober")
            self.fingerprint_var.set("nocturne-signed-mpkeys/0.0.0.0:stable-channel/NOCTURNE NNNN")
            self.fingerprint_format_var.set("Format: board/version:track/hwid  (use version 0.0.0.0 to force the latest update; track: stable-channel/beta-channel/dev-channel/canary-channel)")
        elif mode == "xiaomi":
            self.app_title_var.set("Xiaomi OTA Prober")
            self.fingerprint_var.set("dada_global/OS2.0.222.0.WOCMIXM/16")
            self.fingerprint_format_var.set("Format: codename/rom_version/android_version  (append _global to codename for Global ROM, e.g. venus_global)")
        elif mode == "playemu":
            self.app_title_var.set("Play Games Emulator OTA Prober")
            self.fingerprint_var.set("")
            self.fingerprint_format_var.set("Configure Omaha request parameters below and click Query")
        else:
            self.app_title_var.set("Android OTA Prober")
            self.fingerprint_var.set("google/shamu/shamu:5.1/LYZ28E/1858530:user/release-keys")
            self.fingerprint_format_var.set("Format: oem/product/device:api/build_tag/incremental:build_type/key_type")
        if hasattr(self, 'brute_bt_lf'):
            self._set_brute_os_mode()

    def _set_brute_os_mode(self):
        mode = self.os_mode_var.get()
        is_cros = mode == "chromeos"
        is_xiaomi = mode == "xiaomi"

        cros_fp, xiaomi_fp, android_fp = "{BOARD}/{VER}:{TRACK}/NOCTURNE NNNN", "{DEVICE}/{ROM}/{AND}", "google/baracus/baracus:6.0/{BUILD}/{INC}:{KEY}"
        cros_tags, xiaomi_tags, android_tags = "nocturne-signed-mpkeys", "dada_global\nvenus_global", "MRTA.181211.008"
        cros_keys, xiaomi_keys, android_keys = "\n".join(CROS_TRACKS), "OS1.0.2.0.UNCMIXM\nOS1.0.3.0.UNCMIXM", "user/release-keys\nuser/test-keys"
        cros_start, xiaomi_start, android_start = "0", "13", "370000"
        cros_end, xiaomi_end, android_end = "0", "15", "400000"

        if is_cros:
            self.brute_fp_hint_var.set("Use {BOARD}, {VER} and {TRACK} as placeholders:")
            self.brute_fp_legend_var.set("{BOARD} = board name   {VER} = version   {TRACK} = update track")
            if self.brute_fp_var.get() in (android_fp, xiaomi_fp):
                self.brute_fp_var.set(cros_fp)

            self.brute_bt_lf.configure(text="Board Tags")
            if self.brute_tags_text.get("1.0", tk.END).strip() in (android_tags, xiaomi_tags):
                self.brute_tags_text.delete("1.0", tk.END)
                self.brute_tags_text.insert(tk.END, cros_tags)

            self.brute_kt_lf.configure(text="Tracks")
            if self.brute_keys_text.get("1.0", tk.END).strip() in (android_keys, xiaomi_keys):
                self.brute_keys_text.delete("1.0", tk.END)
                self.brute_keys_text.insert(tk.END, cros_keys)

            self.brute_loc_lf.grid_remove()

            self.brute_inc_lf.configure(text="Version Range")
            self.brute_inc_row_labels[0].config(text="Base:")
            if self.brute_inc_start_var.get() in (android_start, xiaomi_start):
                self.brute_inc_start_var.set(cros_start)
            if self.brute_inc_end_var.get() in (android_end, xiaomi_end):
                self.brute_inc_end_var.set(cros_end)

            self.brute_appid_row.pack(fill=tk.X, pady=(4, 0))

        elif is_xiaomi:
            self.brute_fp_hint_var.set("Use {DEVICE}, {ROM} and {AND} as placeholders:")
            self.brute_fp_legend_var.set("{DEVICE} = codename (e.g. venus_global)   {ROM} = ROM version (e.g. OS1.0.2.0.UNCMIXM)   {AND} = Android version")
            if self.brute_fp_var.get() in (android_fp, cros_fp):
                self.brute_fp_var.set(xiaomi_fp)

            self.brute_bt_lf.configure(text="Devices (codenames)")
            if self.brute_tags_text.get("1.0", tk.END).strip() in (android_tags, cros_tags):
                self.brute_tags_text.delete("1.0", tk.END)
                self.brute_tags_text.insert(tk.END, xiaomi_tags)

            self.brute_kt_lf.configure(text="ROM Versions")
            if self.brute_keys_text.get("1.0", tk.END).strip() in (android_keys, cros_keys):
                self.brute_keys_text.delete("1.0", tk.END)
                self.brute_keys_text.insert(tk.END, xiaomi_keys)

            self.brute_loc_lf.grid_remove()

            self.brute_inc_lf.configure(text="Android Version Range")
            self.brute_inc_row_labels[0].config(text="Start:")
            if self.brute_inc_start_var.get() in (android_start, cros_start):
                self.brute_inc_start_var.set(xiaomi_start)
            if self.brute_inc_end_var.get() in (android_end, cros_end):
                self.brute_inc_end_var.set(xiaomi_end)

            self.brute_appid_row.pack_forget()

        else:
            self.brute_fp_hint_var.set("Use {BUILD}, {INC} and {KEY} as placeholders:")
            self.brute_fp_legend_var.set("{BUILD} = build ID   {INC} = incremental   {KEY} = key type")
            if self.brute_fp_var.get() in (cros_fp, xiaomi_fp):
                self.brute_fp_var.set(android_fp)

            self.brute_bt_lf.configure(text="Build Tags")
            if self.brute_tags_text.get("1.0", tk.END).strip() in (cros_tags, xiaomi_tags):
                self.brute_tags_text.delete("1.0", tk.END)
                self.brute_tags_text.insert(tk.END, android_tags)

            self.brute_kt_lf.configure(text="Key Types")
            if self.brute_keys_text.get("1.0", tk.END).strip() in (cros_keys, xiaomi_keys):
                self.brute_keys_text.delete("1.0", tk.END)
                self.brute_keys_text.insert(tk.END, android_keys)

            self.brute_loc_lf.grid()

            self.brute_inc_lf.configure(text="Incremental Range")
            self.brute_inc_row_labels[0].config(text="Start:")
            if self.brute_inc_start_var.get() in (android_start, cros_start):
                self.brute_inc_start_var.set(android_start)
            if self.brute_inc_end_var.get() in (android_end, cros_end):
                self.brute_inc_end_var.set(android_end)

            self.brute_appid_row.pack_forget()

    def _set_os_mode_visibility(self):
        mode = self.os_mode_var.get()
        is_cros = mode == "chromeos"
        is_xiaomi = mode == "xiaomi"
        is_playemu = mode == "playemu"

        if hasattr(self, 'playemu_editor_frame'):
            if is_playemu:
                self.playemu_editor_frame.grid()
            else:
                self.playemu_editor_frame.grid_remove()

        _brute_tab_pairs = [
            ('brute_frame', 'Bruteforce'),
            ('urlbrute_frame', 'URL Bruteforce'),
            ('devbrute_frame', 'Device Bruteforce'),
        ]
        for attr, label in _brute_tab_pairs:
            frame = getattr(self, attr, None)
            if frame is None:
                continue
            if is_playemu:
                try:
                    self.notebook.forget(frame)
                except Exception:
                    pass
            else:
                present = any(
                    self.notebook.tab(t, 'text') == label
                    for t in self.notebook.tabs()
                )
                if not present:
                    try:
                        rawreq_idx = next(
                            (i for i, t in enumerate(self.notebook.tabs())
                             if self.notebook.tab(t, 'text') == 'Send Raw Request'),
                            None
                        )
                        if rawreq_idx is not None:
                            self.notebook.insert(rawreq_idx, frame, text=label)
                        else:
                            self.notebook.add(frame, text=label)
                    except Exception:
                        try:
                            self.notebook.add(frame, text=label)
                        except Exception:
                            pass

        if hasattr(self, 'cros_header_frame'):
            if is_cros:
                self.cros_header_frame.pack(side=tk.LEFT, padx=(10, 0), after=self.copy_button)
            else:
                self.cros_header_frame.pack_forget()
        for w in self._cros_only_widgets:
            if is_cros:
                w.grid()
            else:
                w.grid_remove()

        if is_cros or is_xiaomi or is_playemu:
            self.keyscan_button.pack_forget()
            self.otachain_button.pack_forget()
            self.keyscan_stop_button.pack_forget()
        else:
            if not self.keyscan_button.winfo_ismapped():
                self.keyscan_button.pack(before=self.clear_button, **self._keyscan_button_pack_info)
            if not self.otachain_button.winfo_ismapped():
                self.otachain_button.pack(before=self.clear_button, **self._otachain_button_pack_info)
            if not self.keyscan_stop_button.winfo_ismapped():
                self.keyscan_stop_button.pack(before=self.clear_button, **self._keyscan_stop_button_pack_info)

        if is_cros or is_xiaomi or is_playemu:
            self.scan_locales_label.grid_remove()
            self.scan_locales_entry.grid_remove()
            self.checkin_url_label.grid_remove()
            self.checkin_url_combo.grid_remove()
        else:
            self.scan_locales_label.grid()
            self.scan_locales_entry.grid()
            self.checkin_url_label.grid()
            self.checkin_url_combo.grid()

        if hasattr(self, '_cros_hidden_httpinfo_tabs'):
            for frame, tab_text in self._cros_hidden_httpinfo_tabs:
                if tab_text == "Alternative Filenames":
                    should_hide = is_cros or is_xiaomi or is_playemu
                elif tab_text == "Payload Metadata":
                    should_hide = is_cros or is_playemu
                else:
                    should_hide = is_cros
                if should_hide:
                    try:
                        self.httpinfo_nb.forget(frame)
                    except Exception:
                        pass
                else:
                    try:
                        self.httpinfo_nb.add(frame, text=tab_text)
                    except Exception:
                        pass

        if hasattr(self, 'zip_tree_frame'):
            try:
                self.httpinfo_nb.forget(self.zip_tree_frame)
            except Exception:
                pass
            if not (is_cros or is_xiaomi or is_playemu):
                try:
                    self.httpinfo_nb.add(self.zip_tree_frame, text="ZIP Tree")
                except Exception:
                    pass

        if hasattr(self, 'notebook'):
            self._on_tab_changed(None)
        else:
            if is_cros:
                self.params_frame.grid_remove()
            else:
                self.params_frame.grid()

        if hasattr(self, 'device_sn_label'):
            if is_cros or is_xiaomi or is_playemu:
                self.device_sn_label.grid_remove()
                self.device_sn_entry.grid_remove()
                if hasattr(self, 'imei_label'):
                    self.imei_label.grid_remove()
                    self.imei_entry.grid_remove()
            else:
                self.device_sn_label.grid()
                self.device_sn_entry.grid()
                if hasattr(self, 'imei_label'):
                    self.imei_label.grid()
                    self.imei_entry.grid()

        if hasattr(self, 'input_frame') and hasattr(self, 'notebook'):
            self._update_input_frame_visibility()

        if hasattr(self, 'httpinfo_token_label'):
            if is_cros or is_xiaomi or is_playemu:
                self.httpinfo_token_label.pack_forget()
                self.httpinfo_token_entry.pack_forget()
            else:
                self.httpinfo_token_label.pack(side=tk.LEFT, padx=(0, 4), before=self.httpinfo_fetch_btn)
                self.httpinfo_token_entry.pack(side=tk.LEFT, padx=(0, 8), before=self.httpinfo_fetch_btn)

        _android_only_btns = [
            'download_ota_button',
            'serials_imeis_button',
            'scan_fingerprints_button',
            'additional_features_button',
        ]
        for attr in _android_only_btns:
            btn = getattr(self, attr, None)
            if btn is None:
                continue
            if is_cros or is_xiaomi or is_playemu:
                btn.pack_forget()
            else:
                if not btn.winfo_ismapped():
                    btn.pack(side=tk.RIGHT, padx=(6, 0))

    def _on_locale_selected(self, event):
        loc = self.locale_var.get().strip()
        if loc in LOCALE_TZ_MAP:
            self.timezone_var.set(LOCALE_TZ_MAP[loc])

    def _on_locale_typed(self, event):
        if event.keysym == 'Return':
            loc = self.locale_var.get().strip()
            if loc in LOCALE_TZ_MAP:
                self.timezone_var.set(LOCALE_TZ_MAP[loc])

    def reset_params(self):
        self.locale_var.set("en-US")
        self.timezone_var.set("America/New_York")
        self.update_status("Parameters reset to default", 'success')

    def _build_raw_tab(self):
        wrapper = ttk.Frame(self.raw_frame, padding="4")
        wrapper.pack(fill=tk.BOTH, expand=True)

        toolbar = ttk.Frame(wrapper)
        toolbar.pack(fill=tk.X, pady=(0, 4))

        self.raw_view_var = tk.StringVar(value="human")

        ttk.Radiobutton(toolbar, text="Human-readable",
                        variable=self.raw_view_var, value="human",
                        command=self._raw_switch_view).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Radiobutton(toolbar, text="Hex dump",
                        variable=self.raw_view_var, value="hex",
                        command=self._raw_switch_view).pack(side=tk.LEFT, padx=(0, 16))

        ttk.Button(toolbar, text="💾  Save Human",
                   command=lambda: self._raw_save("human")).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(toolbar, text="💾  Save Hex",
                   command=lambda: self._raw_save("hex")).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(toolbar, text="📦  Save Raw .gz",
                   command=self._raw_save_gzip).pack(side=tk.LEFT)

        self.raw_text = scrolledtext.ScrolledText(
            wrapper,
            wrap=tk.NONE,
            font=('Courier', 9),
            bg='white',
            fg='#333333'
        )
        self.raw_text.pack(fill=tk.BOTH, expand=True)

        self._raw_human = ""
        self._raw_hex = ""
        self._last_raw_bytes = None

    def _raw_populate(self, human, hex_):
        self._raw_human = human
        self._raw_hex = hex_
        self._raw_switch_view()

    def _raw_switch_view(self):
        content = self._raw_human if self.raw_view_var.get() == "human" else self._raw_hex
        self.raw_text.config(state=tk.NORMAL)
        self.raw_text.delete(1.0, tk.END)
        self.raw_text.insert(tk.END, content)
        self.raw_text.see("1.0")

    def _raw_save(self, mode):
        content = self._raw_human if mode == "human" else self._raw_hex
        if not content:
            messagebox.showinfo("Raw Response", "No data to save yet.")
            return
        ext = "_human.txt" if mode == "human" else "_hex.txt"
        script_dir = os.path.dirname(os.path.abspath(__file__))
        path = filedialog.asksaveasfilename(
            initialdir=script_dir,
            initialfile=f"raw_response{ext}",
            defaultextension=".txt",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")]
        )
        if path:
            with open(path, 'w', encoding='utf-8') as f:
                f.write(content)
            self.update_status(f"Saved to {path}", 'success')

    def _raw_save_gzip(self):
        raw = getattr(self, '_last_raw_bytes', None)
        if not raw:
            messagebox.showinfo("Raw .gz", "No raw response data yet. Run a query first.")
            return
        script_dir = os.path.dirname(os.path.abspath(__file__))
        path = filedialog.asksaveasfilename(
            initialdir=script_dir,
            initialfile="raw_response.gz",
            defaultextension=".gz",
            filetypes=[("Gzip files", "*.gz"), ("All files", "*.*")]
        )
        if not path:
            return
        try:
            with open(path, 'wb') as f:
                f.write(raw)
            self.update_status(f"Saved raw .gz to {os.path.basename(path)}", 'success')
        except Exception as e:
            messagebox.showerror("Save Error", str(e))

    def _build_raw_request_tab(self):
        wrapper = ttk.Frame(self.raw_req_frame, padding="4")
        wrapper.pack(fill=tk.BOTH, expand=True)

        toolbar = ttk.Frame(wrapper)
        toolbar.pack(fill=tk.X, pady=(0, 4))

        self.raw_req_view_var = tk.StringVar(value="human")

        ttk.Radiobutton(toolbar, text="Human-readable",
                        variable=self.raw_req_view_var, value="human",
                        command=self._raw_req_switch_view).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Radiobutton(toolbar, text="Hex dump",
                        variable=self.raw_req_view_var, value="hex",
                        command=self._raw_req_switch_view).pack(side=tk.LEFT, padx=(0, 16))

        ttk.Button(toolbar, text="💾  Save Human",
                   command=lambda: self._raw_req_save("human")).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(toolbar, text="💾  Save Hex",
                   command=lambda: self._raw_req_save("hex")).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(toolbar, text="📦  Save Raw .gz",
                   command=self._raw_req_save_gz).pack(side=tk.LEFT)

        self.raw_req_text = scrolledtext.ScrolledText(
            wrapper,
            wrap=tk.NONE,
            font=('Courier', 9),
            bg='white',
            fg='#333333'
        )
        self.raw_req_text.pack(fill=tk.BOTH, expand=True)

        self._raw_req_human = ""
        self._raw_req_hex = ""
        self._last_request_data = None
        self._last_request_gz = None

    def _raw_request_populate(self):
        req = getattr(self, '_last_request_data', None)
        if not req:
            return
        if isinstance(req, (bytes, bytearray)):
            raw_bytes = bytes(req)
        else:
            raw_bytes = req if isinstance(req, bytes) else str(req).encode('utf-8')

        n = len(raw_bytes)
        stripped = raw_bytes.lstrip()
        if stripped[:1] in (b'{', b'['):
            try:
                parsed = json.loads(raw_bytes.decode('utf-8', errors='replace'))
                human_dump = ("=== RAW JSON REQUEST  ({} bytes) ===\n".format(n)
                              + json.dumps(parsed, indent=2, ensure_ascii=False)
                              )
            except Exception:
                human_dump = "=== RAW JSON REQUEST  ({} bytes) ===\n".format(n) + raw_bytes.decode('utf-8', errors='replace')
            hex_dump = format_hex_dump(raw_bytes, header_label="RAW JSON REQUEST")
        elif stripped[:1] == b'<' or stripped[:5].lower().startswith(b'<?xml'):
            try:
                import xml.dom.minidom
                pretty = xml.dom.minidom.parseString(raw_bytes).toprettyxml(indent='  ')
                human_dump = "=== RAW XML REQUEST  ({} bytes) ===\n".format(n) + pretty
            except Exception:
                human_dump = "=== RAW XML REQUEST  ({} bytes) ===\n".format(n) + raw_bytes.decode('utf-8', errors='replace')
            hex_dump = format_hex_dump(raw_bytes, header_label="RAW XML REQUEST")
        elif b'=' in raw_bytes and b'&' in raw_bytes and b' ' not in raw_bytes[:50]:
            from urllib.parse import parse_qs, unquote_plus
            text = raw_bytes.decode('utf-8', errors='replace')
            lines = [f"=== RAW FORM REQUEST  ({n} bytes) ==="]
            for part in text.split('&'):
                if '=' in part:
                    k, _, v = part.partition('=')
                    lines.append(f"  {unquote_plus(k)} = {unquote_plus(v)}")
                else:
                    lines.append(f"  {unquote_plus(part)}")
            human_dump = '\n'.join(lines)
            hex_dump = format_hex_dump(raw_bytes, header_label="RAW FORM REQUEST")
        else:
            try:
                human_dump, hex_dump = format_raw_response(raw_bytes)
            except Exception:
                human_dump = repr(raw_bytes)
                hex_dump = format_hex_dump(raw_bytes, header_label="RAW REQUEST (PROTOBUF)")

        self._raw_req_human = human_dump
        self._raw_req_hex = hex_dump
        self._raw_req_switch_view()

    def _raw_req_switch_view(self):
        content = self._raw_req_human if self.raw_req_view_var.get() == "human" else self._raw_req_hex
        self.raw_req_text.config(state=tk.NORMAL)
        self.raw_req_text.delete(1.0, tk.END)
        self.raw_req_text.insert(tk.END, content)
        self.raw_req_text.see("1.0")

    def _raw_req_save(self, mode):
        content = self._raw_req_human if mode == "human" else self._raw_req_hex
        if not content:
            messagebox.showinfo("Raw Request", "No request data yet. Run a query first.")
            return
        ext = "_request_human.txt" if mode == "human" else "_request_hex.txt"
        script_dir = os.path.dirname(os.path.abspath(__file__))
        path = filedialog.asksaveasfilename(
            initialdir=script_dir,
            initialfile=f"raw{ext}",
            defaultextension=".txt",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")]
        )
        if path:
            with open(path, 'w', encoding='utf-8') as f:
                f.write(content)
            self.update_status(f"Saved to {os.path.basename(path)}", 'success')

    def _raw_req_save_gz(self):
        gz = getattr(self, '_last_request_gz', None)
        if not gz:
            messagebox.showinfo("Raw Request .gz", "No request data yet. Run a query first.")
            return
        script_dir = os.path.dirname(os.path.abspath(__file__))
        path = filedialog.asksaveasfilename(
            initialdir=script_dir,
            initialfile="raw_request.gz",
            defaultextension=".gz",
            filetypes=[("Gzip files", "*.gz"), ("All files", "*.*")]
        )
        if not path:
            return
        try:
            with open(path, 'wb') as f:
                f.write(gz)
            self.update_status(f"Saved request .gz to {os.path.basename(path)}", 'success')
        except Exception as e:
            messagebox.showerror("Save Error", str(e))

    def _build_httpinfo_tab(self):
        wrapper = ttk.Frame(self.httpinfo_frame, padding="8")
        wrapper.pack(fill=tk.BOTH, expand=True)

        url_lf = ttk.LabelFrame(wrapper, text="OTA URL", padding="6")
        url_lf.pack(fill=tk.X, pady=(0, 6))
        self.httpinfo_url_var = tk.StringVar()
        ttk.Entry(url_lf, textvariable=self.httpinfo_url_var,
                  font=('Courier', 9)).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 8))
        self.httpinfo_token_label = ttk.Label(url_lf, text="Token:", font=('Courier', 9))
        self.httpinfo_token_label.pack(side=tk.LEFT, padx=(0, 4))
        self.httpinfo_token_var = tk.StringVar()
        self.httpinfo_token_entry = ttk.Entry(url_lf, textvariable=self.httpinfo_token_var, width=18,
                                              font=('Courier', 9))
        self.httpinfo_token_entry.pack(side=tk.LEFT, padx=(0, 8))
        self.httpinfo_fetch_btn = ttk.Button(url_lf, text="▶  Fetch",
                                             command=self._httpinfo_start)
        self.httpinfo_fetch_btn.pack(side=tk.LEFT)

        self.httpinfo_local_path = None
        self.httpinfo_local_btn = ttk.Button(url_lf, text="📂 Open local file…",
                                             command=self._httpinfo_choose_local_file)
        self.httpinfo_local_btn.pack(side=tk.LEFT, padx=(8, 0))
        self.httpinfo_local_btn.pack_forget()

        self.httpinfo_status_var = tk.StringVar(value="Enter an OTA URL and press Fetch")
        ttk.Label(wrapper, textvariable=self.httpinfo_status_var,
                  foreground='#0066cc').pack(anchor=tk.W, pady=(0, 4))
        self.httpinfo_progress = ttk.Progressbar(wrapper, mode='indeterminate')
        self.httpinfo_progress.pack(fill=tk.X, pady=(0, 6))

        self.httpinfo_nb = NOTEBOOK_CLS(wrapper)
        self.httpinfo_nb.pack(fill=tk.BOTH, expand=True)
        self.httpinfo_nb.bind('<<NotebookTabChanged>>', self._on_httpinfo_subtab_changed)

        def _make_tree(parent, col1="Field", col2="Value"):
            f = ttk.Frame(parent)
            cols = ("field", "value")
            tv = ttk.Treeview(f, columns=cols, show="headings")
            tv.heading("field", text=col1)
            tv.heading("value", text=col2)
            tv.column("field", width=260, stretch=False)
            tv.column("value", width=560, stretch=True)
            sb = ttk.Scrollbar(f, orient=tk.VERTICAL, command=tv.yview)
            tv.configure(yscrollcommand=sb.set)
            tv.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
            sb.pack(side=tk.RIGHT, fill=tk.Y)

            def _copy_value(event=None):
                sel = tv.selection()
                if not sel:
                    return
                value = tv.item(sel[0], 'values')[1]
                self.root.clipboard_clear()
                self.root.clipboard_append(value)
                self.httpinfo_status_var.set(f"Copied: {value[:80]}{'…' if len(value) > 80 else ''}")

            def _copy_row(event=None):
                sel = tv.selection()
                if not sel:
                    return
                k, v = tv.item(sel[0], 'values')
                self.root.clipboard_clear()
                self.root.clipboard_append(f"{k}: {v}")
                self.httpinfo_status_var.set(f"Copied row: {k}")

            tv.bind('<<TreeviewSelect>>', _copy_value)
            tv.bind('<Double-ButtonRelease-1>', _copy_row)
            return f, tv

        gen_f, self.hi_tree_general = _make_tree(self.httpinfo_nb, "Property", "Value")
        self.httpinfo_nb.add(gen_f, text="General")

        hdr_f, self.hi_tree_headers = _make_tree(self.httpinfo_nb, "Header", "Value")
        self.httpinfo_nb.add(hdr_f, text="Response Headers")

        redir_f, self.hi_tree_redirects = _make_tree(self.httpinfo_nb, "#", "URL")
        self.httpinfo_nb.add(redir_f, text="Redirect Chain")

        sec_f, self.hi_tree_security = _make_tree(self.httpinfo_nb, "Property", "Value")
        self.httpinfo_nb.add(sec_f, text="Security / TLS")

        tim_f, self.hi_tree_timing = _make_tree(self.httpinfo_nb, "Phase", "ms")
        self.httpinfo_nb.add(tim_f, text="Timing")

        meta_f = ttk.Frame(self.httpinfo_nb)
        self.httpinfo_nb.add(meta_f, text="Payload Metadata")

        meta_tree_wrap = ttk.Frame(meta_f)
        meta_tree_wrap.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        meta_tree_wrap.pack_propagate(False)
        meta_tree_wrap.rowconfigure(0, weight=1)
        meta_tree_wrap.rowconfigure(1, weight=0)
        meta_tree_wrap.columnconfigure(0, weight=1)
        meta_tree_wrap.columnconfigure(1, weight=0, minsize=0)
        cols = ("field", "value")
        self.hi_tree_metadata = ttk.Treeview(meta_tree_wrap, columns=cols, show="headings")
        self.hi_tree_metadata.heading("field", text="Field")
        self.hi_tree_metadata.heading("value", text="Value")
        self.hi_tree_metadata.column("field", width=260, stretch=False)
        self.hi_tree_metadata.column("value", width=900, stretch=False)
        meta_vsb = ttk.Scrollbar(meta_tree_wrap, orient=tk.VERTICAL, command=self.hi_tree_metadata.yview)
        meta_hsb = ttk.Scrollbar(meta_tree_wrap, orient=tk.HORIZONTAL, command=self.hi_tree_metadata.xview)
        self.hi_tree_metadata.configure(yscrollcommand=meta_vsb.set, xscrollcommand=meta_hsb.set)
        self.hi_tree_metadata.grid(row=0, column=0, sticky="nsew")
        meta_vsb.grid(row=0, column=1, sticky="ns")
        meta_hsb.grid(row=1, column=0, sticky="ew")
        meta_corner = ttk.Frame(meta_tree_wrap, width=meta_vsb.winfo_reqwidth(),
                                height=meta_hsb.winfo_reqheight())
        meta_corner.grid(row=1, column=1, sticky="nsew")

        def _block_column_resize(event):
            if self.hi_tree_metadata.identify_region(event.x, event.y) == "separator":
                return "break"
        self.hi_tree_metadata.bind('<Button-1>', _block_column_resize, add=False)
        self.hi_tree_metadata.bind('<B1-Motion>', _block_column_resize, add=False)

        def _copy_meta_value(event=None):
            sel = self.hi_tree_metadata.selection()
            if not sel:
                return
            k, value = self.hi_tree_metadata.item(sel[0], 'values')
            self.root.clipboard_clear()
            self.root.clipboard_append(value)
            self.hi_metadata_status_var.set(f"Copied: {k}")

        def _copy_meta_row(event=None):
            sel = self.hi_tree_metadata.selection()
            if not sel:
                return
            k, v = self.hi_tree_metadata.item(sel[0], 'values')
            self.root.clipboard_clear()
            self.root.clipboard_append(f"{k}: {v}")
            self.hi_metadata_status_var.set(f"Copied row: {k}")

        self.hi_tree_metadata.bind('<<TreeviewSelect>>', _copy_meta_value)
        self.hi_tree_metadata.bind('<Double-ButtonRelease-1>', _copy_meta_row)

        try:
            base_font = tkfont.nametofont("TkDefaultFont")
            baseband_font = tkfont.Font(font=base_font)
            baseband_font.configure(slant="italic", family="Courier New")
        except Exception:
            baseband_font = ("Courier New", 10, "italic")
        self.hi_tree_metadata.tag_configure("baseband_extra", font=baseband_font)

        meta_side = ttk.Frame(meta_f, padding=(8, 6), width=270)
        meta_side.pack(side=tk.RIGHT, fill=tk.Y)
        meta_side.pack_propagate(False)
        ttk.Label(meta_side, text="Status", font=('TkDefaultFont', 9, 'bold')).pack(anchor=tk.N, pady=(0, 4))
        self.hi_metadata_status_var = tk.StringVar(value="")
        ttk.Label(meta_side, textvariable=self.hi_metadata_status_var, wraplength=220,
                  justify=tk.LEFT, foreground='#666666').pack(anchor=tk.N, fill=tk.X)

        alt_f = ttk.Frame(self.httpinfo_nb)
        self.httpinfo_nb.add(alt_f, text="Alternative Filenames")

        alt_controls = ttk.Frame(alt_f)
        alt_controls.pack(anchor=tk.W, fill=tk.X, pady=(0, 4))
        ttk.Label(alt_controls, text="Parallel checks:").pack(side=tk.LEFT)
        self.hi_altnames_parallelism_var = tk.IntVar(value=5)
        ttk.Spinbox(alt_controls, from_=1, to=100, width=5, increment=1,
                    textvariable=self.hi_altnames_parallelism_var,
                    justify=tk.CENTER).pack(side=tk.LEFT, padx=(4, 8))

        self.hi_altnames_enabled_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(alt_controls, text="Check alternative filenames",
                        variable=self.hi_altnames_enabled_var).pack(side=tk.LEFT, padx=(0, 8))

        self.hi_altnames_status_var = tk.StringVar(value="")
        ttk.Label(alt_controls, textvariable=self.hi_altnames_status_var, wraplength=900,
                  justify=tk.LEFT, foreground='#666666').pack(side=tk.LEFT, fill=tk.X, expand=True)

        alt_wrap = ttk.Frame(alt_f)
        alt_wrap.pack(fill=tk.BOTH, expand=True)
        self.hi_list_altnames = tk.Listbox(alt_wrap, font=('Courier', 9), activestyle='none',
                                           exportselection=False)
        alt_sb = ttk.Scrollbar(alt_wrap, orient=tk.VERTICAL, command=self.hi_list_altnames.yview)
        self.hi_list_altnames.configure(yscrollcommand=alt_sb.set)
        self.hi_list_altnames.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        alt_sb.pack(side=tk.RIGHT, fill=tk.Y)

        def _copy_alt_selection(event=None):
            sel = self.hi_list_altnames.curselection()
            if not sel:
                return
            value = self.hi_list_altnames.get(sel[0])
            self.root.clipboard_clear()
            self.root.clipboard_append(value)
            self.hi_altnames_status_var.set(f"Copied: {value}")

        self.hi_list_altnames.bind('<<ListboxSelect>>', _copy_alt_selection)

        self.zip_tree_frame = ttk.Frame(self.httpinfo_nb)
        self.zip_tree_tab_index = len(self.httpinfo_nb.tabs())
        self.httpinfo_nb.add(self.zip_tree_frame, text="ZIP Tree")

        zip_toolbar = ttk.Frame(self.zip_tree_frame)
        zip_toolbar.pack(fill=tk.X, pady=(0, 4))

        ttk.Button(zip_toolbar, text="Scan ZIP Tree", command=self._httpinfo_zip_tree_scan).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(zip_toolbar, text="Expand All", command=self._zip_tree_expand_all).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(zip_toolbar, text="Collapse All", command=self._zip_tree_collapse_all).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(zip_toolbar, text="Copy Path", command=self._zip_tree_copy_path).pack(side=tk.LEFT, padx=(0, 4))
        self.zip_tree_extract_btn = ttk.Button(zip_toolbar, text="Extract File...", command=self._zip_tree_extract_selected)
        self.zip_tree_extract_btn.pack(side=tk.LEFT, padx=(0, 12))

        self.zip_tree_status_var = tk.StringVar(value="Press 'Scan ZIP Tree' to view contents.")
        status_lbl = ttk.Label(zip_toolbar, textvariable=self.zip_tree_status_var, foreground='#0066cc')
        status_lbl.pack(side=tk.LEFT, fill=tk.X, expand=True)

        self.zip_tree = ttk.Treeview(self.zip_tree_frame, columns=("size", "comp", "ratio", "date", "crc"), show="tree headings")
        self.zip_tree.heading("#0", text="Name")
        self.zip_tree.heading("size", text="Uncompressed")
        self.zip_tree.heading("comp", text="Compressed")
        self.zip_tree.heading("ratio", text="Ratio")
        self.zip_tree.heading("date", text="Date")
        self.zip_tree.heading("crc", text="CRC32")
        self.zip_tree.column("#0", width=350)
        self.zip_tree.column("size", width=120, anchor=tk.E)
        self.zip_tree.column("comp", width=120, anchor=tk.E)
        self.zip_tree.column("ratio", width=80, anchor=tk.E)
        self.zip_tree.column("date", width=150)
        self.zip_tree.column("crc", width=100, anchor=tk.CENTER)

        vsb = ttk.Scrollbar(self.zip_tree_frame, orient=tk.VERTICAL, command=self.zip_tree.yview)
        self.zip_tree.configure(yscrollcommand=vsb.set)
        self.zip_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)

        self.zip_tree_cache = {
            'url': None,
            'tail_data': None,
            'tail_offset': 0,
            'total_size': 0,
            'entries': None,
        }

        self._cros_hidden_httpinfo_tabs = [
            (meta_f, "Payload Metadata"),
            (alt_f, "Alternative Filenames"),
        ]

        self._httpinfo_last_result = None
        self._httpinfo_metadata_loaded = False
        self._httpinfo_altnames_loaded = False
        self._httpinfo_pending_jobs = 0

    def _httpinfo_start(self):
        url = self.httpinfo_url_var.get().strip()
        if not url:
            messagebox.showerror("HTTP Info", "Please enter an OTA URL first.")
            return

        token = self.httpinfo_token_var.get().strip()
        is_local = bool(self.httpinfo_local_path) and self.httpinfo_local_path == url

        try:
            current_tab_text = self.httpinfo_nb.tab(self.httpinfo_nb.select(), 'text')
        except Exception:
            current_tab_text = None

        self.httpinfo_fetch_btn.config(state=tk.DISABLED)
        self.httpinfo_progress.start(12)

        if is_local:
            self.httpinfo_status_var.set(f"Reading local file: {os.path.basename(self.httpinfo_local_path)}")
            self._httpinfo_pending_jobs = 1

            for ch in self.hi_tree_metadata.get_children():
                self.hi_tree_metadata.delete(ch)
            self.hi_metadata_status_var.set("Loading…")

            self.hi_list_altnames.delete(0, tk.END)
            self.hi_altnames_status_var.set("Not applicable for local files.")

            self._httpinfo_last_result = None
            threading.Thread(target=self._httpinfo_metadata_worker, args=(url, token), daemon=True).start()

        elif current_tab_text in ("Payload Metadata", "Alternative Filenames"):
            self.httpinfo_status_var.set("Checking alternative filenames and metadata…")
            self._httpinfo_pending_jobs = 3

            for ch in self.hi_tree_metadata.get_children():
                self.hi_tree_metadata.delete(ch)
            self.hi_metadata_status_var.set("Loading…")

            self.hi_list_altnames.delete(0, tk.END)
            self.hi_altnames_status_var.set(
                "Checking…" if self.hi_altnames_enabled_var.get() else "Disabled.")

            self._httpinfo_last_result = None

            self._httpinfo_shared_meta_event = threading.Event()
            self._httpinfo_shared_meta_result = {}

            threading.Thread(target=self._httpinfo_metadata_worker, args=(url, token), daemon=True).start()
            threading.Thread(target=self._httpinfo_altnames_worker, args=(url, token), daemon=True).start()
            threading.Thread(target=self._httpinfo_worker, args=(url, token), daemon=True).start()

        else:
            self.httpinfo_status_var.set("Probing…")
            self._httpinfo_pending_jobs = 1
            self._httpinfo_last_result = None
            threading.Thread(target=self._httpinfo_worker, args=(url, token), daemon=True).start()

    def _httpinfo_worker(self, url, token=""):
        try:
            result = probe_ota_url(url, token=token, status_cb=lambda m: self.root.after(
                0, self.httpinfo_status_var.set, m))
            self._httpinfo_last_result = result
            self.root.after(0, self._httpinfo_display, result)
        except Exception as exc:
            self.root.after(0, self.httpinfo_status_var.set, f"Error: {exc}")
        finally:
            self.root.after(0, self._httpinfo_done)

    def _httpinfo_done(self):
        self.httpinfo_progress.stop()
        self.httpinfo_fetch_btn.config(state=tk.NORMAL)
        self._httpinfo_pending_jobs = max(0, self._httpinfo_pending_jobs - 1)
        if self._httpinfo_pending_jobs == 0:
            current = self.httpinfo_status_var.get()
            if current in ("Fetching metadata and alternative filenames…", "Probing…"):
                self.httpinfo_status_var.set("")

    def _httpinfo_metadata_worker(self, url, token=""):
        try:
            is_local = bool(self.httpinfo_local_path) and self.httpinfo_local_path == url
            result = fetch_payload_metadata(
                url, token=token, status_cb=lambda m: self.root.after(0, self.hi_metadata_status_var.set, m),
                return_raw_tail=True,
                local_path=url if is_local else None)
            meta = result['metadata']
            self.root.after(0, self._httpinfo_display_metadata, meta)

            shared_event = getattr(self, '_httpinfo_shared_meta_event', None)
            shared_holder = getattr(self, '_httpinfo_shared_meta_result', None)
            if shared_holder is not None:
                shared_holder['meta'] = meta
            if shared_event is not None:
                shared_event.set()

            if result.get('tail_data'):
                self.zip_tree_cache['url'] = url
                self.zip_tree_cache['tail_data'] = result['tail_data']
                self.zip_tree_cache['tail_offset'] = result['tail_offset']
                self.zip_tree_cache['total_size'] = result['total_size']
                entries = self._parse_zip_entries_from_tail(
                    result['tail_data'],
                    result['tail_offset'],
                    result['total_size']
                )
                self.zip_tree_cache['entries'] = entries
                self.root.after(0, lambda: self._httpinfo_display_zip_tree(entries))
            else:
                self.zip_tree_cache['url'] = None
                self.zip_tree_cache['entries'] = None

        except Exception as exc:
            self.root.after(0, self.hi_metadata_status_var.set, f"Metadata error: {exc}")
        finally:
            shared_event = getattr(self, '_httpinfo_shared_meta_event', None)
            if shared_event is not None:
                shared_event.set()
            self.root.after(0, self._httpinfo_done)

    def _parse_zip_entries_from_tail(self, tail_data, tail_offset, total_size):
        entries = []
        eocd_pos = tail_data.rfind(b'PK\x05\x06')
        if eocd_pos == -1:
            return entries
        try:
            cd_size = struct.unpack('<I', tail_data[eocd_pos+12:eocd_pos+16])[0]
            cd_offset = struct.unpack('<I', tail_data[eocd_pos+16:eocd_pos+20])[0]
        except struct.error:
            return entries
        cd_start = cd_offset
        cd_end = cd_offset + cd_size
        cd_data = b''

        if cd_start >= tail_offset and cd_end <= total_size:
            start_in_tail = cd_start - tail_offset
            cd_data = tail_data[start_in_tail:start_in_tail + cd_size]
        else:
            return entries

        pos = 0
        while pos + 46 <= len(cd_data):
            if cd_data[pos:pos+4] != b'PK\x01\x02':
                break
            try:
                compression_method = struct.unpack('<H', cd_data[pos+10:pos+12])[0]
                file_time = struct.unpack('<H', cd_data[pos+12:pos+14])[0]
                file_date = struct.unpack('<H', cd_data[pos+14:pos+16])[0]
                crc32 = struct.unpack('<I', cd_data[pos+16:pos+20])[0]
                compressed_size = struct.unpack('<I', cd_data[pos+20:pos+24])[0]
                uncompressed_size = struct.unpack('<I', cd_data[pos+24:pos+28])[0]
                name_len = struct.unpack('<H', cd_data[pos+28:pos+30])[0]
                extra_len = struct.unpack('<H', cd_data[pos+30:pos+32])[0]
                comment_len = struct.unpack('<H', cd_data[pos+32:pos+34])[0]
                local_header_offset = struct.unpack('<I', cd_data[pos+42:pos+46])[0]
                name = cd_data[pos+46:pos+46+name_len].decode('utf-8', errors='replace')
                pos += 46 + name_len + extra_len + comment_len
            except struct.error:
                break

            date_str = _zip_dos_date_str(file_date, file_time)

            entries.append({
                'name': name,
                'uncompressed_size': uncompressed_size,
                'compressed_size': compressed_size,
                'crc32': crc32,
                'date': date_str,
                'compression_method': compression_method,
                'local_header_offset': local_header_offset,
                'is_dir': name.endswith('/'),
            })

        return entries

    def _httpinfo_altnames_worker(self, url, token=""):
        if not self.hi_altnames_enabled_var.get():
            self.root.after(0, self._httpinfo_display_altnames,
                            {'checked': False, 'reason': 'Alternative filename checking is disabled.', 'results': []})
            self.root.after(0, self._httpinfo_done)
            return
        meta = {}
        shared_event = getattr(self, '_httpinfo_shared_meta_event', None)
        shared_holder = getattr(self, '_httpinfo_shared_meta_result', None)
        if shared_event is not None:
            shared_event.wait(timeout=45)
            if shared_holder is not None:
                meta = shared_holder.get('meta') or {}
        if not meta:
            try:
                meta = fetch_payload_metadata(url, token=token)
            except Exception:
                meta = {}

        last_modified = ''
        for label, val in (self._httpinfo_last_result or {}).get('general', []):
            if label == 'Last-Modified':
                last_modified = val
                break
        if not last_modified:
            try:
                req = urllib.request.Request(url, method='HEAD', headers={
                    'User-Agent': 'AndroidDownloadManager/14 (Linux; U; Android 14; sdk_gphone64_x86_64 Build/UE1A.230829.036)',
                    'Accept-Encoding': 'identity',
                })
                ctx = ssl.create_default_context()
                with urllib.request.urlopen(req, timeout=12, context=ctx) as resp:
                    last_modified = resp.headers.get('Last-Modified', '') or ''
            except Exception:
                pass

        try:
            status_cb = lambda m: self.root.after(0, self.hi_altnames_status_var.set, m)
            try:
                max_workers = max(1, int(self.hi_altnames_parallelism_var.get()))
            except Exception:
                max_workers = 5

            direct = probe_direct_url_alternate(url, token=token, status_cb=status_cb, max_workers=max_workers)

            pre_fp = meta.get('fields', {}).get('pre-build') or self.current_ota_precondition
            post_fp = meta.get('fields', {}).get('post-build') or self.current_ota_postcondition
            alt = probe_alternative_filenames(
                url, last_modified, pre_fp, post_fp, token=token, status_cb=status_cb, max_workers=max_workers)

            seen_urls = {url, url.lower()}
            merged_results = []
            for name, candidate_url, ok in list(direct.get('results', [])) + list(alt.get('results', [])):
                if candidate_url in seen_urls or candidate_url.lower() in seen_urls:
                    continue
                seen_urls.add(candidate_url)
                merged_results.append((name, candidate_url, ok))

            merged = {
                'checked': direct.get('checked') or alt.get('checked'),
                'reason': alt.get('reason') or direct.get('reason'),
                'results': merged_results,
            }
            try:
                working_names = [name for name, curl, ok in merged_results if ok]
                if working_names:
                    add_ota_record(
                        os_kind=self.os_mode_var.get(),
                        url=self.current_ota_link or url,
                        title='',
                        description='',
                        size='',
                        locale=self.locale_var.get().strip() if hasattr(self, 'locale_var') else '',
                        fingerprint='',
                        alt_filenames=working_names,
                    )
            except Exception:
                pass

            self.root.after(0, self._httpinfo_display_altnames, merged)
        except Exception as exc:
            self.root.after(0, self._httpinfo_display_altnames,
                            {'checked': False, 'reason': f"Error: {exc}", 'results': []})
        finally:
            self.root.after(0, self._httpinfo_done)

    def _httpinfo_display(self, r):
        def _fill(tree, rows):
            for ch in tree.get_children():
                tree.delete(ch)
            for k, v in rows:
                tree.insert("", tk.END, values=(k, v))

        _fill(self.hi_tree_general, r.get('general', []))
        _fill(self.hi_tree_headers, r.get('headers', []))
        _fill(self.hi_tree_redirects,
              [(str(i+1), u) for i, u in enumerate(r.get('redirects', []))])
        _fill(self.hi_tree_security, r.get('security', []))
        _fill(self.hi_tree_timing, r.get('timing', []))

        summary = r.get('summary', '')
        self.httpinfo_status_var.set(summary)

    def _httpinfo_display_metadata(self, meta):
        for ch in self.hi_tree_metadata.get_children():
            self.hi_tree_metadata.delete(ch)

        def _autosize_value_column(values):
            longest = max((len(str(v)) for v in values), default=0)
            px = max(900, min(longest * 7 + 40, 2400))
            self.hi_tree_metadata.column("value", width=px, stretch=False)

        if meta.get('dummy'):
            filler_name = meta.get('filler_name', '?')
            filler_size = meta.get('filler_size', 0)
            if filler_size >= 1_073_741_824:
                size_human = f"{filler_size/1_073_741_824:.2f} GiB"
            elif filler_size >= 1_048_576:
                size_human = f"{filler_size/1_048_576:.2f} MiB"
            elif filler_size >= 1024:
                size_human = f"{filler_size/1024:.1f} KiB"
            else:
                size_human = f"{filler_size} B"
            size_val = f"{size_human}  ({filler_size:,} bytes)"
            self.hi_tree_metadata.insert("", tk.END, values=("Filler file", filler_name))
            self.hi_tree_metadata.insert("", tk.END, values=("Filler size", size_val))
            _autosize_value_column([filler_name, size_val])
            self.hi_metadata_status_var.set("Dummy OTA file.")
        elif meta.get('found'):
            fields = meta.get('fields', {})
            for k, v in fields.items():
                tags = ("baseband_extra",) if k == 'version-baseband' else ()
                self.hi_tree_metadata.insert("", tk.END, values=(k, v), tags=tags)
            _autosize_value_column(fields.values())
            if meta.get('is_hboot'):
                self.hi_metadata_status_var.set(
                    "No Android metadata file — this is an HBOOT image "
                    f"(hboot.img). Version info from {meta.get('source', '?')}.")
            else:
                self.hi_metadata_status_var.set(
                    f"Found in {meta.get('source', '?')} — {len(fields)} field(s)")
        else:
            err = meta.get('error') or "No metadata fields found (package may not expose plaintext metadata)."
            self.hi_metadata_status_var.set(err.strip(' |'))

    def _httpinfo_display_altnames(self, alt):
        self.hi_list_altnames.delete(0, tk.END)

        if not alt.get('checked'):
            self.hi_altnames_status_var.set(alt.get('reason') or 'Not checked')
            return

        seen = set()
        working = []
        for name, candidate_url, ok in alt.get('results', []):
            if not ok or candidate_url in seen:
                continue
            seen.add(candidate_url)
            working.append(candidate_url)

        if not working:
            self.hi_altnames_status_var.set(alt.get('reason') or "No working alternative links found.")
            return

        for u in working:
            self.hi_list_altnames.insert(tk.END, u)
        self.hi_altnames_status_var.set(f"Found {len(working)} working alternative link(s).")

    def _httpinfo_zip_tree_scan(self):
        url = self.httpinfo_url_var.get().strip()
        if not url:
            messagebox.showerror("ZIP Tree", "Please enter an OTA URL first.")
            return

        token = self.httpinfo_token_var.get().strip()

        for child in self.zip_tree.get_children():
            self.zip_tree.delete(child)
        self.zip_tree_status_var.set("Scanning...")
        self.httpinfo_progress.start(12)
        self.httpinfo_fetch_btn.config(state=tk.DISABLED)

        threading.Thread(target=self._httpinfo_zip_tree_worker, args=(url, token), daemon=True).start()

    def _httpinfo_zip_tree_worker(self, url, token=""):
        entries = None
        is_local = bool(self.httpinfo_local_path) and self.httpinfo_local_path == url
        if self.zip_tree_cache.get('url') == url and self.zip_tree_cache.get('entries') is not None:
            entries = self.zip_tree_cache['entries']
            self.root.after(0, lambda: self.zip_tree_status_var.set("Using cached data..."))
        else:
            try:
                if is_local:
                    entries = fetch_zip_tree_local(
                        url,
                        status_cb=lambda m: self.root.after(0, self.zip_tree_status_var.set, m)
                    )
                else:
                    entries = fetch_zip_tree(
                        url, token=token,
                        status_cb=lambda m: self.root.after(0, self.zip_tree_status_var.set, m)
                    )
                self.zip_tree_cache['url'] = url
                self.zip_tree_cache['entries'] = entries
            except Exception as e:
                self.root.after(0, self.zip_tree_status_var.set, f"Error: {e}")
                self.root.after(0, self._httpinfo_zip_tree_done)
                return

        self.root.after(0, self._httpinfo_display_zip_tree, entries)
        self.root.after(0, self._httpinfo_zip_tree_done)

    def _httpinfo_zip_tree_done(self):
        self.httpinfo_progress.stop()
        self.httpinfo_fetch_btn.config(state=tk.NORMAL)
        if self.zip_tree_status_var.get() in ("Scanning...", "Loading..."):
            self.zip_tree_status_var.set("Ready")

    def _httpinfo_display_zip_tree(self, entries):
        for child in self.zip_tree.get_children():
            self.zip_tree.delete(child)

        self.zip_tree_node_entries = {}

        if not entries:
            self.zip_tree_status_var.set("No entries found in ZIP (maybe empty or unsupported).")
            return

        total_files = 0
        total_uncomp = 0
        total_comp = 0
        dir_paths = set()

        tree_dict = {}
        for entry in entries:
            name = entry['name']
            if name.endswith('/'):
                name = name[:-1]
            parts = name.split('/')
            is_dir = entry.get('is_dir', False) or entry['name'].endswith('/') or parts[-1] == ''
            if is_dir:
                current = tree_dict
                path_so_far = []
                for part in parts:
                    if part == '':
                        continue
                    path_so_far.append(part)
                    key = '/'.join(path_so_far)
                    dir_paths.add(key)
                    if key not in current:
                        current[key] = {}
                    current = current[key]
            else:
                total_files += 1
                total_uncomp += entry['uncompressed_size']
                total_comp += entry['compressed_size']
                if len(parts) == 1:
                    tree_dict[parts[0]] = entry
                else:
                    parent_path = '/'.join(parts[:-1])
                    parent = tree_dict
                    if parent_path:
                        path_so_far = []
                        for p in parent_path.split('/'):
                            path_so_far.append(p)
                            dir_paths.add('/'.join(path_so_far))
                            if p not in parent:
                                parent[p] = {}
                            parent = parent[p]
                    parent[parts[-1]] = entry

        total_dirs = len(dir_paths)

        def fmt_sizes(uncomp, comp):
            ratio = f"{comp/uncomp*100:.1f}%" if uncomp > 0 else "0%"
            size_str = f"{uncomp/1024/1024:.2f} MB" if uncomp > 1024*1024 else f"{uncomp/1024:.1f} KB"
            comp_str = f"{comp/1024/1024:.2f} MB" if comp > 1024*1024 else f"{comp/1024:.1f} KB"
            return ratio, size_str, comp_str

        def insert_file_node(parent_node, key, entry):
            uncomp = entry['uncompressed_size']
            comp = entry['compressed_size']
            ratio, size_str, comp_str = fmt_sizes(uncomp, comp)
            file_node = self.zip_tree.insert(parent_node, tk.END, text=key,
                                             values=(size_str, comp_str, ratio, entry.get('date', ''), f"{entry.get('crc32', 0):08X}"))
            self.zip_tree_node_entries[file_node] = entry

        def add_nodes(parent_node, node_dict):
            for key, value in sorted(node_dict.items()):
                if isinstance(value, dict) and 'name' not in value:
                    node = self.zip_tree.insert(parent_node, tk.END, text=key, values=("", "", "", "", ""), open=False)
                    add_nodes(node, value)
                    self.zip_tree.item(node, values=("(folder)", "", "", "", ""))
                else:
                    insert_file_node(parent_node, key, value)

        for key, value in sorted(tree_dict.items()):
            if isinstance(value, dict) and 'name' not in value:
                node = self.zip_tree.insert("", tk.END, text=key, values=("", "", "", "", ""), open=False)
                add_nodes(node, value)
                self.zip_tree.item(node, values=("(folder)", "", "", "", ""))
            else:
                insert_file_node("", key, value)

        total = total_files + total_dirs
        size_mb = total_uncomp / (1024*1024)
        comp_mb = total_comp / (1024*1024)
        self.zip_tree_status_var.set(
            f"Total: {total_files} files, {total_dirs} directories, "
            f"uncompressed {size_mb:.2f} MB, compressed {comp_mb:.2f} MB"
        )

    def _zip_tree_expand_all(self):
        for child in self.zip_tree.get_children():
            self._expand_recursive(child)

    def _expand_recursive(self, node):
        self.zip_tree.item(node, open=True)
        for child in self.zip_tree.get_children(node):
            self._expand_recursive(child)

    def _zip_tree_collapse_all(self):
        for child in self.zip_tree.get_children():
            self.zip_tree.item(child, open=False)
            self._collapse_recursive(child)

    def _collapse_recursive(self, node):
        for child in self.zip_tree.get_children(node):
            self.zip_tree.item(child, open=False)
            self._collapse_recursive(child)

    def _zip_tree_copy_path(self):
        sel = self.zip_tree.selection()
        if not sel:
            return
        node = sel[0]
        path_parts = []
        while node:
            text = self.zip_tree.item(node, 'text')
            path_parts.append(text)
            node = self.zip_tree.parent(node)
        full_path = '/'.join(reversed(path_parts))
        self.root.clipboard_clear()
        self.root.clipboard_append(full_path)
        self.zip_tree_status_var.set(f"Copied: {full_path}")

    def _zip_tree_extract_selected(self):
        sel = self.zip_tree.selection()
        if not sel:
            messagebox.showinfo("Extract File", "Select a file in the ZIP tree first.")
            return
        node = sel[0]
        entry = getattr(self, 'zip_tree_node_entries', {}).get(node)
        if entry is None:
            messagebox.showinfo("Extract File", "Please select a file (not a folder).")
            return

        url = self.httpinfo_url_var.get().strip()
        is_local = bool(self.httpinfo_local_path) and self.httpinfo_local_path == url
        source = self.httpinfo_local_path if is_local else url
        if not source:
            messagebox.showerror("Extract File", "No source URL/file set.")
            return

        default_name = entry['name'].split('/')[-1] or 'extracted_file'
        save_path = filedialog.asksaveasfilename(
            title="Save extracted file as",
            initialfile=default_name,
        )
        if not save_path:
            return

        self.zip_tree_extract_btn.config(state=tk.DISABLED)
        self.zip_tree_status_var.set(f"Extracting '{entry['name']}'...")
        threading.Thread(
            target=self._zip_tree_extract_worker,
            args=(source, entry, save_path, is_local),
            daemon=True,
        ).start()

    def _zip_tree_extract_worker(self, source, entry, save_path, is_local):
        try:
            if is_local:
                data = extract_zip_entry_local(
                    source, entry,
                    status_cb=lambda m: self.root.after(0, self.zip_tree_status_var.set, m)
                )
            else:
                data = extract_zip_entry(
                    source, entry,
                    status_cb=lambda m: self.root.after(0, self.zip_tree_status_var.set, m)
                )
            with open(save_path, 'wb') as f:
                f.write(data)
            self.root.after(0, self.zip_tree_status_var.set,
                            f"Extracted '{entry['name']}' -> {save_path} ({len(data):,} bytes)")
        except Exception as e:
            self.root.after(0, self.zip_tree_status_var.set, f"Extract error: {e}")
            self.root.after(0, lambda: messagebox.showerror("Extract File", str(e)))
        finally:
            self.root.after(0, lambda: self.zip_tree_extract_btn.config(state=tk.NORMAL))

    def _build_bruteforce_tab(self):
        _outer = ttk.Frame(self.brute_frame)
        _outer.pack(fill=tk.BOTH, expand=True)

        _canvas = tk.Canvas(_outer, borderwidth=0, highlightthickness=0)
        _vsb = ttk.Scrollbar(_outer, orient="vertical", command=_canvas.yview)
        _canvas.configure(yscrollcommand=_vsb.set)

        _vsb.pack(side=tk.RIGHT, fill=tk.Y)
        _canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        wrapper = ttk.Frame(_canvas, padding="8")
        _canvas_window = _canvas.create_window((0, 0), window=wrapper, anchor="nw")

        def _on_frame_configure(event):
            _canvas.configure(scrollregion=_canvas.bbox("all"))

        def _on_canvas_configure(event):
            _canvas.itemconfig(_canvas_window, width=event.width)

        wrapper.bind("<Configure>", _on_frame_configure)
        _canvas.bind("<Configure>", _on_canvas_configure)

        def _on_mousewheel(event):
            try:
                _canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
            except tk.TclError:
                pass

        def _bind_mousewheel(widget):
            widget.bind("<MouseWheel>", _on_mousewheel)
            for child in widget.winfo_children():
                _bind_mousewheel(child)

        wrapper.bind("<Map>", lambda e: _bind_mousewheel(wrapper))

        btn_row = ttk.Frame(wrapper)
        btn_row.pack(fill=tk.X, pady=(0, 4))
        self.brute_start_btn = ttk.Button(btn_row, text="▶  Start Bruteforce", command=self._brute_start)
        self.brute_pause_btn = ttk.Button(btn_row, text="⏸  Pause", command=self._brute_pause, state=tk.DISABLED)
        self.brute_continue_btn = ttk.Button(btn_row, text="⏩  Continue", command=self._brute_continue, state=tk.DISABLED)
        self.brute_stop_btn = ttk.Button(btn_row, text="⏹  Stop", command=self._brute_stop, state=tk.DISABLED)
        self.brute_stop_save_btn = ttk.Button(btn_row, text="💾  Stop + Save Progress", command=self._brute_stop_and_save, state=tk.DISABLED)
        self.brute_load_progress_btn = ttk.Button(btn_row, text="📂  Load Progress", command=self._brute_load_progress)
        self.brute_clear_log_btn = ttk.Button(btn_row, text="🗑  Clear Log", command=self._brute_clear_log)
        self.brute_open_log_btn = ttk.Button(btn_row, text="📋  Open Log Window", command=self._open_brute_log_window)
        self.brute_export_log_btn = ttk.Button(btn_row, text="💾 Export Log", command=self._brute_export_log)
        for btn in (self.brute_start_btn, self.brute_pause_btn, self.brute_continue_btn,
                    self.brute_stop_btn, self.brute_stop_save_btn, self.brute_load_progress_btn,
                    self.brute_clear_log_btn, self.brute_export_log_btn, self.brute_open_log_btn):
            btn.pack(side=tk.LEFT, padx=3)
        self.brute_status_var = tk.StringVar(value="Idle — fill in settings below, then press Start Bruteforce")
        ttk.Label(btn_row, textvariable=self.brute_status_var, foreground='#0066cc').pack(side=tk.LEFT, padx=10)
        ttk.Separator(btn_row, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=6, pady=2)
        ttk.Label(btn_row, text="Speed:", foreground='#555').pack(side=tk.LEFT)
        self.brute_speed_var = tk.StringVar(value="— req/s")
        ttk.Label(btn_row, textvariable=self.brute_speed_var, foreground='#cc6600',
                  font=('Courier', 9, 'bold')).pack(side=tk.LEFT, padx=(4, 0))

        self.brute_progress = ttk.Progressbar(wrapper, mode='determinate')
        self.brute_progress.pack(fill=tk.X, pady=(0, 6))

        fp_lf = ttk.LabelFrame(wrapper, text="Fingerprint Template", padding="6")
        fp_lf.pack(fill=tk.X, pady=(0, 6))
        self.brute_fp_hint_var = tk.StringVar(value="Use {BUILD}, {INC} and {KEY} as placeholders:")
        ttk.Label(fp_lf, textvariable=self.brute_fp_hint_var).pack(anchor=tk.W)
        self.brute_fp_var = tk.StringVar(
            value="google/baracus/baracus:6.0/{BUILD}/{INC}:{KEY}"
        )
        ttk.Entry(fp_lf, textvariable=self.brute_fp_var, font=('Courier', 9)).pack(fill=tk.X, pady=3)
        self.brute_fp_legend_var = tk.StringVar(value="{BUILD} = build ID   {INC} = incremental   {KEY} = key type")
        ttk.Label(fp_lf, textvariable=self.brute_fp_legend_var, foreground='#666666').pack(anchor=tk.W)

        self.brute_appid_row = ttk.Frame(fp_lf)
        ttk.Label(self.brute_appid_row, text="App ID:").pack(side=tk.LEFT, padx=(0, 6))
        self.brute_appid_var = tk.StringVar(value=next(iter(CROS_BOARD_APPID_MAP.values())))
        ttk.Entry(self.brute_appid_row, textvariable=self.brute_appid_var, font=('Courier', 9), width=45).pack(side=tk.LEFT, fill=tk.X, expand=True)

        mid = ttk.Frame(wrapper)
        mid.pack(fill=tk.X, pady=(0, 6))
        mid.columnconfigure(0, weight=3)
        mid.columnconfigure(1, weight=3)
        mid.columnconfigure(2, weight=1)
        mid.columnconfigure(3, weight=0)

        self.brute_bt_lf = ttk.LabelFrame(mid, text="Build Tags", padding="6")
        self.brute_bt_lf.grid(row=0, column=0, sticky=tk.NSEW, padx=(0, 6))
        self.brute_tags_text = tk.Text(self.brute_bt_lf, height=2, font=('Courier', 9))
        self.brute_tags_text.pack(fill=tk.BOTH, expand=True)
        self.brute_tags_text.insert(tk.END, "MRTA.181211.008")

        self.brute_kt_lf = ttk.LabelFrame(mid, text="Key Types", padding="6")
        self.brute_kt_lf.grid(row=0, column=1, sticky=tk.NSEW, padx=(0, 6))
        self.brute_keys_text = tk.Text(self.brute_kt_lf, height=2, font=('Courier', 9))
        self.brute_keys_text.pack(fill=tk.BOTH, expand=True)
        self.brute_keys_text.insert(tk.END,
                                    "user/release-keys\nuser/test-keys")

        self.brute_loc_lf = ttk.LabelFrame(mid, text="Locales", padding="6")
        self.brute_loc_lf.grid(row=0, column=2, sticky=tk.NSEW, padx=(0, 6))
        self.brute_locales_text = tk.Text(self.brute_loc_lf, height=2, font=('Courier', 9))
        self.brute_locales_text.pack(fill=tk.BOTH, expand=True)
        self.brute_locales_text.insert(tk.END, "en-US\nuk-UA\nru-RU")

        self.brute_inc_lf = ttk.LabelFrame(mid, text="Incremental Range", padding="6")
        self.brute_inc_lf.grid(row=0, column=3, sticky=tk.NSEW)
        self.brute_inc_lf.columnconfigure(1, weight=1)
        self.brute_inc_start_var = tk.StringVar(value="370000")
        self.brute_inc_end_var = tk.StringVar(value="400000")
        self.brute_inc_step_var = tk.StringVar(value="1")
        self.brute_inc_row_labels = []
        self.brute_inc_row_entries = []
        for row_i, (lbl, var) in enumerate(zip(
                ["Start:", "End:", "Step:"],
                [self.brute_inc_start_var, self.brute_inc_end_var, self.brute_inc_step_var])):
            l = ttk.Label(self.brute_inc_lf, text=lbl)
            l.grid(row=row_i, column=0, sticky=tk.W, pady=3)
            e = ttk.Entry(self.brute_inc_lf, textvariable=var, width=12)
            e.grid(row=row_i, column=1, sticky=tk.EW, padx=(6, 0), pady=3)
            self.brute_inc_row_labels.append(l)
            self.brute_inc_row_entries.append(e)

        serial_section = ttk.LabelFrame(wrapper, text="Serial Bruteforce", padding="6")
        serial_section.pack(fill=tk.X, pady=(6, 0))

        self.brute_serial_enabled_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(serial_section, text="Bruteforce serial numbers",
                        variable=self.brute_serial_enabled_var).grid(row=0, column=0, sticky=tk.W, padx=(0, 10))

        self.brute_serial_frame = ttk.Frame(serial_section)
        self.brute_serial_frame.grid(row=1, column=0, columnspan=2, sticky=tk.W, pady=(4, 0))

        _tmpl_row = ttk.Frame(self.brute_serial_frame)
        _tmpl_row.pack(fill=tk.X, pady=(0, 4))
        ttk.Label(_tmpl_row, text="Template:", width=9).pack(side=tk.LEFT, padx=(0, 4))
        self.brute_serial_template_var = tk.StringVar(value="M6GG7220G00{num1}")
        ttk.Entry(_tmpl_row, textvariable=self.brute_serial_template_var, width=28).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Label(_tmpl_row, text="Use {num1}…{num5} as placeholders  (legacy {num} = {num1})",
                  foreground='#888').pack(side=tk.LEFT)

        _num_rows = [
            ("{num1}:", "brute_serial_start_var", "brute_serial_end_var", "brute_serial_step_var",
             "brute_serial_hex_var", "brute_serial_base36_var"),
            ("{num2}:", "brute_serial_start2_var", "brute_serial_end2_var", "brute_serial_step2_var",
             "brute_serial_hex2_var", "brute_serial_base36_2_var"),
            ("{num3}:", "brute_serial_start3_var", "brute_serial_end3_var", "brute_serial_step3_var",
             "brute_serial_hex3_var", "brute_serial_base36_3_var"),
            ("{num4}:", "brute_serial_start4_var", "brute_serial_end4_var", "brute_serial_step4_var",
             "brute_serial_hex4_var", "brute_serial_base36_4_var"),
            ("{num5}:", "brute_serial_start5_var", "brute_serial_end5_var", "brute_serial_step5_var",
             "brute_serial_hex5_var", "brute_serial_base36_5_var"),
        ]
        for label_text, start_attr, end_attr, step_attr, hex_attr, b36_attr in _num_rows:
            row = ttk.Frame(self.brute_serial_frame)
            row.pack(fill=tk.X, pady=(0, 2))
            ttk.Label(row, text=label_text, width=9, font=('Courier', 9, 'bold')).pack(side=tk.LEFT, padx=(0, 4))
            ttk.Label(row, text="Start:").pack(side=tk.LEFT, padx=(0, 4))
            setattr(self, start_attr, tk.StringVar(value="1"))
            ttk.Entry(row, textvariable=getattr(self, start_attr), width=8).pack(side=tk.LEFT, padx=(0, 8))
            ttk.Label(row, text="End:").pack(side=tk.LEFT, padx=(0, 4))
            setattr(self, end_attr, tk.StringVar(value="9999"))
            ttk.Entry(row, textvariable=getattr(self, end_attr), width=8).pack(side=tk.LEFT, padx=(0, 8))
            ttk.Label(row, text="Step:").pack(side=tk.LEFT, padx=(0, 4))
            setattr(self, step_attr, tk.StringVar(value="1"))
            ttk.Entry(row, textvariable=getattr(self, step_attr), width=6).pack(side=tk.LEFT, padx=(0, 12))
            setattr(self, hex_attr, tk.BooleanVar(value=False))
            ttk.Checkbutton(row, text="HEX", variable=getattr(self, hex_attr)).pack(side=tk.LEFT)
            setattr(self, b36_attr, tk.BooleanVar(value=False))
            ttk.Checkbutton(row, text="Base36", variable=getattr(self, b36_attr)).pack(side=tk.LEFT, padx=(8, 0))

        imei_section = ttk.LabelFrame(wrapper, text="IMEI Bruteforce", padding="6")
        imei_section.pack(fill=tk.X, pady=(6, 0))

        imei_row0 = ttk.Frame(imei_section)
        imei_row0.pack(fill=tk.X, pady=(0, 4))

        self.brute_imei_enabled_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(imei_row0, text="Bruteforce IMEI",
                        variable=self.brute_imei_enabled_var).pack(side=tk.LEFT, padx=(0, 16))

        ttk.Label(imei_row0, text="TAC (8 digits — Reporting Body + manufacturer + model):").pack(side=tk.LEFT, padx=(0, 6))
        self.brute_imei_tac_var = tk.StringVar(value="35674108")
        ttk.Entry(imei_row0, textvariable=self.brute_imei_tac_var, width=12, font=("Courier", 9)).pack(side=tk.LEFT)

        imei_row1 = ttk.Frame(imei_section)
        imei_row1.pack(fill=tk.X, pady=(0, 2))

        ttk.Label(imei_row1, text="SNR Start:").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_imei_snr_start_var = tk.StringVar(value="000001")
        ttk.Entry(imei_row1, textvariable=self.brute_imei_snr_start_var, width=10, font=("Courier", 9)).pack(side=tk.LEFT, padx=(0, 12))

        ttk.Label(imei_row1, text="SNR End:").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_imei_snr_end_var = tk.StringVar(value="000100")
        ttk.Entry(imei_row1, textvariable=self.brute_imei_snr_end_var, width=10, font=("Courier", 9)).pack(side=tk.LEFT, padx=(0, 12))

        ttk.Label(imei_row1, text="Step:").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_imei_snr_step_var = tk.StringVar(value="1")
        ttk.Entry(imei_row1, textvariable=self.brute_imei_snr_step_var, width=6, font=("Courier", 9)).pack(side=tk.LEFT, padx=(0, 16))

        self.brute_imei_zeropad_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(imei_row1, text="Zero-pad SNR to 6 digits",
                        variable=self.brute_imei_zeropad_var).pack(side=tk.LEFT)

        ttk.Label(imei_section,
                  text="Check digit (15th) is computed automatically via the Luhn algorithm.  "
                       "TAC = first 8 digits of IMEI (e.g. 35674108 = Samsung).",
                  foreground="#666666").pack(anchor=tk.W, pady=(2, 0))

        htc_section = ttk.LabelFrame(wrapper, text="HTC Serial Bruteforce  (HT<Y><M><C><DD><SSSSS>)", padding="6")
        htc_section.pack(fill=tk.X, pady=(6, 0))

        htc_row0 = ttk.Frame(htc_section)
        htc_row0.pack(fill=tk.X, pady=(0, 3))
        self.brute_htc_enabled_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(htc_row0, text="Bruteforce HTC serials",
                        variable=self.brute_htc_enabled_var).pack(side=tk.LEFT, padx=(0, 16))
        ttk.Label(htc_row0, text="Year codes (Y, space-sep):").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_htc_years_var = tk.StringVar(value="6 7 8")
        ttk.Entry(htc_row0, textvariable=self.brute_htc_years_var, width=18).pack(side=tk.LEFT, padx=(0, 16))
        ttk.Label(htc_row0, text="Month codes (M):").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_htc_months_var = tk.StringVar(value="1 2 3 4 5 6 7 8 9 A B C")
        ttk.Entry(htc_row0, textvariable=self.brute_htc_months_var, width=28).pack(side=tk.LEFT)

        htc_row1 = ttk.Frame(htc_section)
        htc_row1.pack(fill=tk.X, pady=(0, 3))
        ttk.Label(htc_row1, text="Device codes DD (2-char, space-sep):").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_htc_devcodes_var = tk.StringVar(value="1A 1B 1C 01 02 03 0A 10")
        ttk.Entry(htc_row1, textvariable=self.brute_htc_devcodes_var, width=32).pack(side=tk.LEFT, padx=(0, 16))
        ttk.Label(htc_row1, text="Unknown C chars:").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_htc_uchars_var = tk.StringVar(value="0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ")
        ttk.Entry(htc_row1, textvariable=self.brute_htc_uchars_var, width=40).pack(side=tk.LEFT)

        htc_row2 = ttk.Frame(htc_section)
        htc_row2.pack(fill=tk.X, pady=(0, 2))
        ttk.Label(htc_row2, text="Seq Start (SSSSS):").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_htc_seq_start_var = tk.StringVar(value="0")
        ttk.Entry(htc_row2, textvariable=self.brute_htc_seq_start_var, width=8, font=("Courier", 9)).pack(side=tk.LEFT, padx=(0, 12))
        ttk.Label(htc_row2, text="Seq End:").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_htc_seq_end_var = tk.StringVar(value="99999")
        ttk.Entry(htc_row2, textvariable=self.brute_htc_seq_end_var, width=8, font=("Courier", 9)).pack(side=tk.LEFT, padx=(0, 12))
        ttk.Label(htc_row2, text="Step:").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_htc_seq_step_var = tk.StringVar(value="1")
        ttk.Entry(htc_row2, textvariable=self.brute_htc_seq_step_var, width=6, font=("Courier", 9)).pack(side=tk.LEFT)

        ttk.Label(htc_section,
                  text="Format: HT + Y(year last digit) + M(month: 1-9,A,B,C) + C(unknown) + DD(device) + SSSSS(seq 0-99999).  "
                       "Known DD codes: U11=1A  U11+=1B  U12+=1C  OneM7=01  OneM8=02  OneM9=03  OneA9=0A  HTC10=10",
                  foreground="#666666", wraplength=900, justify=tk.LEFT).pack(anchor=tk.W, pady=(2, 0))

        pixel_section = ttk.LabelFrame(wrapper,
                                       text="Pixel/Google Date Serial Bruteforce  (e.g. M6GG7322G04376 → BASE+Y+M+DD+G+SSSSS)",
                                       padding="6")
        pixel_section.pack(fill=tk.X, pady=(6, 0))

        px_row0 = ttk.Frame(pixel_section)
        px_row0.pack(fill=tk.X, pady=(0, 3))
        self.brute_pixel_enabled_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(px_row0, text="Bruteforce Pixel date serials",
                        variable=self.brute_pixel_enabled_var).pack(side=tk.LEFT, padx=(0, 16))
        ttk.Label(px_row0, text="Base prefix (e.g. M6GG):").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_pixel_base_var = tk.StringVar(value="M6GG")
        ttk.Entry(px_row0, textvariable=self.brute_pixel_base_var, width=10).pack(side=tk.LEFT, padx=(0, 16))
        ttk.Label(px_row0, text="Factory char (e.g. G=Google):").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_pixel_factory_var = tk.StringVar(value="G")
        ttk.Entry(px_row0, textvariable=self.brute_pixel_factory_var, width=5).pack(side=tk.LEFT)

        px_row1 = ttk.Frame(pixel_section)
        px_row1.pack(fill=tk.X, pady=(0, 3))
        ttk.Label(px_row1, text="Year codes (Y, space-sep, last digit):").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_pixel_years_var = tk.StringVar(value="7 8 9")
        ttk.Entry(px_row1, textvariable=self.brute_pixel_years_var, width=16).pack(side=tk.LEFT, padx=(0, 16))
        ttk.Label(px_row1, text="Month codes (M, 1-9 A-C):").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_pixel_months_var = tk.StringVar(value="1 2 3 4 5 6 7 8 9 A B C")
        ttk.Entry(px_row1, textvariable=self.brute_pixel_months_var, width=28).pack(side=tk.LEFT)

        px_row2 = ttk.Frame(pixel_section)
        px_row2.pack(fill=tk.X, pady=(0, 3))
        ttk.Label(px_row2, text="Day Start (DD, 01-31):").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_pixel_day_start_var = tk.StringVar(value="1")
        ttk.Entry(px_row2, textvariable=self.brute_pixel_day_start_var, width=6, font=("Courier", 9)).pack(side=tk.LEFT, padx=(0, 12))
        ttk.Label(px_row2, text="Day End:").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_pixel_day_end_var = tk.StringVar(value="31")
        ttk.Entry(px_row2, textvariable=self.brute_pixel_day_end_var, width=6, font=("Courier", 9)).pack(side=tk.LEFT, padx=(0, 16))
        ttk.Label(px_row2, text="Seq Start (SSSSS):").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_pixel_seq_start_var = tk.StringVar(value="0")
        ttk.Entry(px_row2, textvariable=self.brute_pixel_seq_start_var, width=8, font=("Courier", 9)).pack(side=tk.LEFT, padx=(0, 12))
        ttk.Label(px_row2, text="Seq End:").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_pixel_seq_end_var = tk.StringVar(value="99999")
        ttk.Entry(px_row2, textvariable=self.brute_pixel_seq_end_var, width=8, font=("Courier", 9)).pack(side=tk.LEFT, padx=(0, 12))
        ttk.Label(px_row2, text="Step:").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_pixel_seq_step_var = tk.StringVar(value="1")
        ttk.Entry(px_row2, textvariable=self.brute_pixel_seq_step_var, width=6, font=("Courier", 9)).pack(side=tk.LEFT)

        ttk.Label(pixel_section,
                  text="Generates: BASE + Y + M + DD(zero-padded 2 digits) + factory + SSSSS(zero-padded 5 digits).  "
                       "Example: M6GG + 7 + 3 + 22 + G + 04376  =  M6GG7322G04376",
                  foreground="#666666", wraplength=900, justify=tk.LEFT).pack(anchor=tk.W, pady=(2, 0))

        moto_section = ttk.LabelFrame(wrapper,
                                      text="Motorola Serial Bruteforce  (P02<R><FF><SSSSS>)",
                                      padding="6")
        moto_section.pack(fill=tk.X, pady=(6, 0))

        moto_row0 = ttk.Frame(moto_section)
        moto_row0.pack(fill=tk.X, pady=(0, 3))
        self.brute_moto_enabled_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(moto_row0, text="Bruteforce Motorola serials",
                        variable=self.brute_moto_enabled_var).pack(side=tk.LEFT, padx=(0, 16))
        ttk.Label(moto_row0, text="Revision chars R (space-sep):").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_moto_revisions_var = tk.StringVar(value="7 8 9 A B C U")
        ttk.Entry(moto_row0, textvariable=self.brute_moto_revisions_var, width=22).pack(side=tk.LEFT, padx=(0, 16))
        ttk.Label(moto_row0, text="Factory codes FF (2-char, space-sep):").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_moto_factories_var = tk.StringVar(value="XQ XS XY BN BA BY BC")
        ttk.Entry(moto_row0, textvariable=self.brute_moto_factories_var, width=30).pack(side=tk.LEFT)

        moto_row1 = ttk.Frame(moto_section)
        moto_row1.pack(fill=tk.X, pady=(0, 3))
        ttk.Label(moto_row1, text="Seq alphabet (chars to use):").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_moto_alphabet_var = tk.StringVar(value="0123456789ABCDEFGHJKLMNPQRSTUVWXYZ")
        ttk.Entry(moto_row1, textvariable=self.brute_moto_alphabet_var, width=40).pack(side=tk.LEFT, padx=(0, 16))
        ttk.Label(moto_row1, text="Seq length:").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_moto_seqlen_var = tk.StringVar(value="5")
        ttk.Entry(moto_row1, textvariable=self.brute_moto_seqlen_var, width=4).pack(side=tk.LEFT)

        moto_row2 = ttk.Frame(moto_section)
        moto_row2.pack(fill=tk.X, pady=(0, 2))
        ttk.Label(moto_row2, text="Seq index Start:").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_moto_seq_start_var = tk.StringVar(value="0")
        ttk.Entry(moto_row2, textvariable=self.brute_moto_seq_start_var, width=10, font=("Courier", 9)).pack(side=tk.LEFT, padx=(0, 12))
        ttk.Label(moto_row2, text="Seq index End:").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_moto_seq_end_var = tk.StringVar(value="100000")
        ttk.Entry(moto_row2, textvariable=self.brute_moto_seq_end_var, width=10, font=("Courier", 9)).pack(side=tk.LEFT, padx=(0, 12))
        ttk.Label(moto_row2, text="Step:").pack(side=tk.LEFT, padx=(0, 4))
        self.brute_moto_seq_step_var = tk.StringVar(value="1")
        ttk.Entry(moto_row2, textvariable=self.brute_moto_seq_step_var, width=6, font=("Courier", 9)).pack(side=tk.LEFT)

        ttk.Label(moto_section,
                  text="Format: P02 + R(revision: 7/8/U…) + FF(factory: XQ/XS/BN…) + SSSSS(alphanumeric seq, indexed by position in alphabet).  "
                       "Examples: P027XQ28V3  P027BA6TBD  P02UQL000J  — Seq index maps linearly through the alphabet.",
                  foreground="#666666", wraplength=900, justify=tk.LEFT).pack(anchor=tk.W, pady=(2, 0))

        opt_lf = ttk.LabelFrame(wrapper, text="Options", padding="6")
        opt_lf.pack(fill=tk.X, pady=(6, 0))
        self.brute_stop_on_find_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(opt_lf, text="Pause on new OTA (press Continue to resume)",
                        variable=self.brute_stop_on_find_var).pack(side=tk.LEFT, padx=8)
        self.brute_skip_dupes_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(opt_lf, text="Skip duplicate OTA URLs",
                        variable=self.brute_skip_dupes_var).pack(side=tk.LEFT, padx=8)
        self._brute_hide_dupes_log_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(opt_lf, text="Hide duplicates in log",
                        variable=self._brute_hide_dupes_log_var).pack(side=tk.LEFT, padx=8)
        self._brute_hide_no_ota_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(opt_lf, text="Hide 'no OTA' in log",
                        variable=self._brute_hide_no_ota_var).pack(side=tk.LEFT, padx=8)
        self.brute_save_otas_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(opt_lf, text="Save OTAs.txt",
                        variable=self.brute_save_otas_var).pack(side=tk.LEFT, padx=8)
        ttk.Label(opt_lf, text="Parallel workers:").pack(side=tk.LEFT, padx=(16, 4))
        self.brute_workers_var = tk.StringVar(value="10")
        ttk.Spinbox(opt_lf, from_=1, to=1000, textvariable=self.brute_workers_var, width=5).pack(side=tk.LEFT)

        self._brute_stop_flag = False
        self._brute_pause_event = threading.Event()
        self._brute_found_data = {}
        self._brute_found_count = 0
        self._brute_queue = None
        self._brute_producer_thread = None
        self._brute_worker_threads = []
        self._brute_progress_lock = threading.Lock()
        self._brute_processed = 0
        self._brute_total = 0
        self._brute_running = False
        self._brute_dogfood_count = 0
        self._brute_speed_ts = 0.0
        self._brute_speed_count = 0

        self._brute_log_buffer = []
        self._brute_log_lock = threading.Lock()
        self._brute_log_pending = []
        self._brute_log_poll_scheduled = False
        self._set_brute_os_mode()

    def _toggle_serial_fields(self):
        if self.brute_serial_enabled_var.get():
            self.brute_serial_frame.grid()
        else:
            self.brute_serial_frame.grid_remove()

    def _open_brute_log_window(self):
        if self._brute_log_window is not None and self._brute_log_window.winfo_exists():
            self._brute_log_window.lift()
            self._brute_log_window.focus_force()
            return

        win = tk.Toplevel(self.root)
        win.title("Bruteforce Log")
        win.geometry("900x600")
        win.protocol("WM_DELETE_WINDOW", self._close_brute_log_window)

        frame = ttk.Frame(win, padding="10")
        frame.pack(fill=tk.BOTH, expand=True)

        toolbar = ttk.Frame(frame)
        toolbar.pack(fill=tk.X, pady=(0, 6))

        ttk.Button(toolbar, text="🗑 Clear Log", command=self._brute_clear_log).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="💾 Export Log", command=self._brute_export_log).pack(side=tk.LEFT, padx=2)

        text = scrolledtext.ScrolledText(frame, wrap=tk.WORD, font=('Courier', 9), bg='white', fg='#333')
        text.pack(fill=tk.BOTH, expand=True)

        text.tag_configure('found', foreground='#006600', font=('Courier', 9, 'bold'))
        text.tag_configure('skip', foreground='#aaaaaa')
        text.tag_configure('error', foreground='#cc0000')
        text.tag_configure('header', foreground='#004499', font=('Courier', 9, 'bold'))
        text.tag_configure('info', foreground='#333333')
        text.tag_configure('changed', foreground='#cc6600', font=('Courier', 9, 'bold'))
        text.tag_configure('dogfood', foreground='#cc9900', font=('Courier', 9, 'bold'))
        text.tag_configure('duplicate', foreground='#b8860b', font=('Courier', 9, 'bold'))

        for line, tag in self._brute_log_buffer:
            text.insert(tk.END, line + '\n', tag)
        text.see(tk.END)
        text.config(state=tk.DISABLED)

        self._brute_log_window = win
        self._brute_log_text = text

    def _close_brute_log_window(self):
        if self._brute_log_window:
            self._brute_log_window.destroy()
            self._brute_log_window = None
            self._brute_log_text = None

    def _brute_log(self, msg, tag='info'):
        self._brute_log_block([(msg, tag)])

    def _brute_log_block(self, lines):
        with self._brute_log_lock:
            self._brute_log_buffer.extend(lines)
            self._brute_log_pending.extend(lines)
        if not self._brute_log_poll_scheduled:
            self._brute_log_poll_scheduled = True
            self.root.after(0, self._brute_flush_log)

    def _brute_flush_log(self):
        pending = None
        with self._brute_log_lock:
            if self._brute_log_pending:
                pending = self._brute_log_pending
                self._brute_log_pending = []
            still_needed = bool(self._brute_log_pending) or self._brute_running
            if not pending and not still_needed:
                self._brute_log_poll_scheduled = False

        if pending and self._brute_log_text and self._brute_log_window and self._brute_log_window.winfo_exists():
            try:
                self._brute_log_text.config(state=tk.NORMAL)
                for msg, tag in pending:
                    self._brute_log_text.insert(tk.END, msg + '\n', tag)
                self._brute_log_text.see(tk.END)
                self._brute_log_text.config(state=tk.DISABLED)
            except Exception:
                pass

        if self._brute_running or pending:
            self._brute_log_poll_scheduled = True
            self.root.after(100, self._brute_flush_log)
        else:
            self._brute_log_poll_scheduled = False

    def _brute_clear_log(self):
        with self._brute_log_lock:
            self._brute_log_buffer.clear()
            self._brute_log_pending.clear()
        if self._brute_log_text and self._brute_log_window and self._brute_log_window.winfo_exists():
            self._brute_log_text.config(state=tk.NORMAL)
            self._brute_log_text.delete(1.0, tk.END)
            self._brute_log_text.config(state=tk.DISABLED)

    def _brute_pause(self):
        if not self._brute_running:
            return
        self._brute_pause_event.clear()
        self.brute_pause_btn.config(state=tk.DISABLED)
        self.brute_continue_btn.config(state=tk.NORMAL)
        self.brute_stop_btn.config(state=tk.NORMAL)
        self.brute_stop_save_btn.config(state=tk.NORMAL)
        self.brute_status_var.set("⏸ Paused — press Continue to resume")

    def _brute_continue(self):
        if not self._brute_running:
            return
        self._brute_pause_event.set()
        self.brute_continue_btn.config(state=tk.DISABLED)
        self.brute_pause_btn.config(state=tk.NORMAL)
        self.brute_stop_btn.config(state=tk.NORMAL)
        self.brute_stop_save_btn.config(state=tk.NORMAL)
        self.brute_status_var.set("Resuming...")

    def _brute_stop(self):
        if not self._brute_running:
            return
        self._brute_stop_flag = True
        self._brute_pause_event.set()
        self.brute_status_var.set("Stopping...")
        self.brute_stop_btn.config(state=tk.DISABLED)
        self.brute_stop_save_btn.config(state=tk.DISABLED)
        self.brute_pause_btn.config(state=tk.DISABLED)
        self.brute_continue_btn.config(state=tk.DISABLED)

    def _brute_start(self):
        if self._brute_running:
            self._brute_stop()
            time.sleep(0.2)

        is_cros = self.os_mode_var.get() == "chromeos"
        is_xiaomi = self.os_mode_var.get() == "xiaomi"
        template = self.brute_fp_var.get().strip()
        serial_enabled = self.brute_serial_enabled_var.get()

        if is_xiaomi:
            self._brute_start_xiaomi(template, serial_enabled)
            return

        if is_cros:
            use_board = '{BOARD}' in template
            use_ver = '{VER}' in template
            use_track = '{TRACK}' in template
            app_id = self.brute_appid_var.get().strip()

            raw_tags = self.brute_tags_text.get("1.0", tk.END).strip()
            board_tags = [t.strip() for t in raw_tags.splitlines() if t.strip()]
            if not board_tags:
                board_tags = ["nocturne-signed-mpkeys"] if use_board else [""]

            raw_tracks = self.brute_keys_text.get("1.0", tk.END).strip()
            tracks = [t.strip() for t in raw_tracks.splitlines() if t.strip()]
            if not tracks:
                tracks = ["stable-channel"] if use_track else [""]

            locales = [""]

            try:
                inc_start_str = self.brute_inc_start_var.get().strip()
                inc_end_str = self.brute_inc_end_var.get().strip()
                inc_step_str = self.brute_inc_step_var.get().strip()
                if inc_start_str and inc_end_str and use_ver:
                    inc_start = int(inc_start_str)
                    inc_end = int(inc_end_str)
                    inc_step = int(inc_step_str) if inc_step_str else 1
                    if inc_step <= 0:
                        inc_step = 1
                else:
                    inc_start, inc_end, inc_step = 0, 0, 1
            except ValueError:
                inc_start, inc_end, inc_step = 0, 0, 1

            inc_count = (inc_end - inc_start) // inc_step + 1 if use_ver else 1
            build_count = len(board_tags) if use_board else 1
            key_count = len(tracks) if use_track else 1
            locale_count = 1
            serial_count = self._compute_serial_count() if serial_enabled else 1
            total = build_count * key_count * inc_count * locale_count * serial_count
            if total == 0:
                total = 1

            self._brute_stop_flag = False
            self._brute_pause_event.set()
            self._brute_found_data.clear()
            self._brute_found_count = 0
            self._brute_processed = 0
            self._brute_total = total
            self._brute_dogfood_count = 0

            self._brute_clear_log()

            self.brute_start_btn.config(state=tk.DISABLED)
            self.brute_pause_btn.config(state=tk.NORMAL)
            self.brute_continue_btn.config(state=tk.DISABLED)
            self.brute_stop_btn.config(state=tk.NORMAL)
            self.brute_stop_save_btn.config(state=tk.NORMAL)
            self.brute_progress['maximum'] = total
            self.brute_progress['value'] = 0

            self._brute_log(f"Starting ChromeOS bruteforce: {total} combinations", 'header')
            self._brute_log(f"Template: {template}", 'header')
            self._brute_log(f"App ID: {app_id}", 'header')
            if serial_enabled:
                self._brute_log("Serial bruteforce enabled.", 'header')
            self._brute_log("=" * 70, 'header')

            try:
                n_workers = max(1, min(1000, int(self.brute_workers_var.get())))
            except ValueError:
                n_workers = 10

            self._brute_queue = queue.Queue(maxsize=10000)

            self._brute_producer_thread = threading.Thread(
                target=self._brute_producer_chromeos,
                args=(board_tags, tracks, inc_start, inc_end, inc_step, template, n_workers,
                      use_board, use_ver, use_track, app_id, serial_enabled),
                daemon=True
            )
            self._brute_producer_thread.start()

            self._brute_worker_threads = []
            for _ in range(n_workers):
                t = threading.Thread(target=self._brute_worker_chromeos, args=(serial_enabled,), daemon=True)
                t.start()
                self._brute_worker_threads.append(t)

            self._brute_running = True
            self._brute_speed_ts = time.monotonic()
            self._brute_speed_count = 0
            self.brute_speed_var.set("0 req/s")
            self.root.after(500, self._brute_monitor)
            self.root.after(1000, self._brute_update_speed)
            return

        use_build = '{BUILD}' in template
        use_inc = '{INC}' in template
        use_key = '{KEY}' in template

        raw_tags = self.brute_tags_text.get("1.0", tk.END).strip()
        build_tags = [t.strip() for t in raw_tags.splitlines() if t.strip()]
        if not build_tags:
            if use_build:
                build_tags = ["DEFAULT"]
            else:
                build_tags = [""]

        raw_keys = self.brute_keys_text.get("1.0", tk.END).strip()
        key_types = [k.strip() for k in raw_keys.splitlines() if k.strip()]
        if not key_types:
            if use_key:
                key_types = ["user/release-keys"]
            else:
                key_types = [""]

        raw_locales = self.brute_locales_text.get("1.0", tk.END).strip()
        locales = [l.strip() for l in raw_locales.splitlines() if l.strip()]
        if not locales:
            default_loc = self.locale_var.get().strip()
            locales = [default_loc if default_loc else "en-US"]

        try:
            inc_start_str = self.brute_inc_start_var.get().strip()
            inc_end_str = self.brute_inc_end_var.get().strip()
            inc_step_str = self.brute_inc_step_var.get().strip()
            if inc_start_str and inc_end_str and use_inc:
                inc_start = int(inc_start_str)
                inc_end = int(inc_end_str)
                inc_step = int(inc_step_str) if inc_step_str else 1
                if inc_step <= 0:
                    inc_step = 1
            else:
                inc_start, inc_end, inc_step = 0, 0, 1
        except ValueError:
            inc_start, inc_end, inc_step = 0, 0, 1

        if use_inc:
            inc_count = (inc_end - inc_start) // inc_step + 1
        else:
            inc_count = 1
        build_count = len(build_tags) if use_build else 1
        key_count = len(key_types) if use_key else 1
        locale_count = len(locales)
        serial_count = self._compute_serial_count() if serial_enabled else 1
        imei_enabled = self.brute_imei_enabled_var.get()
        imei_count = self._compute_imei_count() if imei_enabled else 1
        htc_enabled = self.brute_htc_enabled_var.get()
        htc_count = self._compute_htc_count() if htc_enabled else 1
        pixel_enabled = self.brute_pixel_enabled_var.get()
        pixel_count = self._compute_pixel_count() if pixel_enabled else 1
        moto_enabled = self.brute_moto_enabled_var.get()
        moto_count = self._compute_moto_count() if moto_enabled else 1
        sn_count = max(serial_count, 1) * max(htc_count, 1) * max(pixel_count, 1) * max(moto_count, 1)
        total = build_count * key_count * inc_count * locale_count * sn_count * imei_count
        if total == 0:
            total = 1

        _resume_skip = getattr(self, "_brute_resume_skip", 0)
        remaining = max(1, total - _resume_skip)

        self._brute_stop_flag = False
        self._brute_pause_event.set()
        self._brute_found_data.clear()
        self._brute_found_count = 0
        self._brute_processed = 0
        self._brute_total = remaining
        self._brute_dogfood_count = 0
        self._brute_cache_skip_dupes = self.brute_skip_dupes_var.get()
        self._brute_cache_pause_on_find = self.brute_stop_on_find_var.get()
        self._brute_cache_save_otas = self.brute_save_otas_var.get()
        self._brute_cache_hide_dupes_log = getattr(self, '_brute_hide_dupes_log_var', tk.BooleanVar(value=False)).get()
        self._brute_cache_hide_no_ota = getattr(self, '_brute_hide_no_ota_var', tk.BooleanVar(value=False)).get()

        self._brute_clear_log()

        self.brute_start_btn.config(state=tk.DISABLED)
        self.brute_pause_btn.config(state=tk.NORMAL)
        self.brute_continue_btn.config(state=tk.DISABLED)
        self.brute_stop_btn.config(state=tk.NORMAL)
        self.brute_stop_save_btn.config(state=tk.NORMAL)
        self.brute_progress['maximum'] = remaining
        self.brute_progress['value'] = 0

        self._brute_log(f"Starting bruteforce: {total} combinations", 'header')
        self._brute_log(f"Template: {template}", 'header')
        self._brute_log(f"Locales to test: {', '.join(locales)}", 'header')
        if serial_enabled:
            self._brute_log("Serial bruteforce enabled.", 'header')
        if imei_enabled:
            tac = self.brute_imei_tac_var.get().strip()
            self._brute_log(f"IMEI bruteforce enabled. TAC={tac}, {imei_count} IMEIs.", 'header')
        if htc_enabled:
            self._brute_log(f"HTC serial bruteforce enabled. ~{htc_count} candidates.", 'header')
        if pixel_enabled:
            self._brute_log(f"Pixel date serial bruteforce enabled. ~{pixel_count} candidates.", 'header')
        if moto_enabled:
            self._brute_log(f"Motorola serial bruteforce enabled. ~{moto_count} candidates.", 'header')
        self._brute_log("=" * 70, 'header')

        try:
            n_workers = max(1, min(1000, int(self.brute_workers_var.get())))
        except ValueError:
            n_workers = 10

        self._brute_queue = queue.Queue(maxsize=10000)

        _skip = getattr(self, "_brute_resume_skip", 0)
        self._brute_resume_skip = 0
        self._brute_producer_thread = threading.Thread(
            target=self._brute_producer,
            args=(build_tags, key_types, inc_start, inc_end, inc_step, template, n_workers,
                  use_build, use_inc, use_key, locales, serial_enabled, _skip),
            daemon=True
        )
        self._brute_producer_thread.start()
        if _skip > 0:
            self._brute_log(f"Resuming: fast-forwarding past {_skip} already-processed combinations...", 'header')

        device_sn = getattr(self, 'device_sn_var', tk.StringVar()).get().strip()
        imei = getattr(self, 'imei_var', tk.StringVar()).get().strip()

        self._brute_worker_threads = []
        for _ in range(n_workers):
            t = threading.Thread(target=self._brute_worker, args=(device_sn, imei, serial_enabled), daemon=True)
            t.start()
            self._brute_worker_threads.append(t)

        self._brute_running = True
        self._brute_speed_ts = time.monotonic()
        self._brute_speed_count = 0
        self.brute_speed_var.set("0 req/s")
        self.root.after(500, self._brute_monitor)
        self.root.after(1000, self._brute_update_speed)

    @staticmethod
    def _luhn_check_digit(fourteen_digits):
        digits = [int(d) for d in fourteen_digits]
        total = 0
        for i, d in enumerate(digits):
            if i % 2 == 1:
                d *= 2
                if d > 9:
                    d -= 9
            total += d
        check = (10 - (total % 10)) % 10
        return fourteen_digits + str(check)

    def _generate_imeis(self):
        if not self.brute_imei_enabled_var.get():
            yield None
            return
        tac = self.brute_imei_tac_var.get().strip()
        if len(tac) != 8 or not tac.isdigit():
            yield None
            return
        try:
            snr_start = int(self.brute_imei_snr_start_var.get().strip())
            snr_end = int(self.brute_imei_snr_end_var.get().strip())
            snr_step = int(self.brute_imei_snr_step_var.get().strip()) if self.brute_imei_snr_step_var.get().strip() else 1
            if snr_step <= 0:
                snr_step = 1
            if snr_start > snr_end:
                snr_start, snr_end = snr_end, snr_start
        except ValueError:
            yield None
            return
        zeropad = self.brute_imei_zeropad_var.get()
        yielded = False
        for snr in range(snr_start, snr_end + 1, snr_step):
            snr_str = f"{snr:06d}" if zeropad else str(snr)
            fourteen = tac + snr_str[-6:]
            yield self._luhn_check_digit(fourteen)
            yielded = True
        if not yielded:
            yield None

    def _compute_imei_count(self):
        if not self.brute_imei_enabled_var.get():
            return 1
        try:
            snr_start = int(self.brute_imei_snr_start_var.get().strip())
            snr_end = int(self.brute_imei_snr_end_var.get().strip())
            snr_step = int(self.brute_imei_snr_step_var.get().strip()) if self.brute_imei_snr_step_var.get().strip() else 1
            if snr_step <= 0:
                snr_step = 1
            if snr_start > snr_end:
                snr_start, snr_end = snr_end, snr_start
            return (snr_end - snr_start) // snr_step + 1
        except ValueError:
            return 1

    def _compute_serial_count(self):
        if not self.brute_serial_enabled_var.get():
            return 1
        template = self.brute_serial_template_var.get().strip()
        has_num1 = '{num1}' in template or '{num}' in template
        has_num2 = '{num2}' in template
        has_num3 = '{num3}' in template
        has_num4 = '{num4}' in template
        has_num5 = '{num5}' in template

        def _count(start_var, end_var, step_var):
            try:
                start = int(start_var.get().strip())
                end = int(end_var.get().strip())
                raw_s = step_var.get().strip()
                step = int(raw_s) if raw_s else 1
                if step <= 0:
                    step = 1
                if start > end:
                    start, end = end, start
                return (end - start) // step + 1
            except ValueError:
                return 1

        count = 1
        if has_num1:
            count *= _count(self.brute_serial_start_var, self.brute_serial_end_var, self.brute_serial_step_var)
        if has_num2:
            count *= _count(self.brute_serial_start2_var, self.brute_serial_end2_var, self.brute_serial_step2_var)
        if has_num3:
            count *= _count(self.brute_serial_start3_var, self.brute_serial_end3_var, self.brute_serial_step3_var)
        if has_num4:
            count *= _count(self.brute_serial_start4_var, self.brute_serial_end4_var, self.brute_serial_step4_var)
        if has_num5:
            count *= _count(self.brute_serial_start5_var, self.brute_serial_end5_var, self.brute_serial_step5_var)
        return count

    def _brute_producer(self, build_tags, key_types, inc_start, inc_end, inc_step, template, n_workers,
                        use_build, use_inc, use_key, locales, serial_enabled, skip_count=0):
        try:
            builds = build_tags if use_build else [""]
            keys = key_types if use_key else [""]
            inc_values = range(inc_start, inc_end + 1, inc_step) if use_inc else [0]

            def _sn_sequence():
                htc_enabled = self.brute_htc_enabled_var.get()
                pixel_enabled = self.brute_pixel_enabled_var.get()
                moto_enabled = getattr(self, 'brute_moto_enabled_var', None)
                moto_on = moto_enabled.get() if moto_enabled else False

                if serial_enabled:
                    yield from self._generate_serials()
                if htc_enabled:
                    for v in self._generate_htc_serials():
                        if v is not None:
                            yield v
                if pixel_enabled:
                    for v in self._generate_pixel_serials():
                        if v is not None:
                            yield v
                if moto_on:
                    for v in self._generate_moto_serials():
                        if v is not None:
                            yield v
                if not (serial_enabled or htc_enabled or pixel_enabled or moto_on):
                    yield None

            def _all_combos():
                for bt in builds:
                    for inc in inc_values:
                        for kt in keys:
                            for loc in locales:
                                for imei_val in self._generate_imeis():
                                    for active_sn in _sn_sequence():
                                        yield (bt, kt,
                                               str(inc) if use_inc else "",
                                               loc, template, active_sn, imei_val)

            skipped = 0
            for combo in _all_combos():
                if self._brute_stop_flag:
                    break
                if skipped < skip_count:
                    skipped += 1
                    continue
                if self._brute_stop_flag:
                    return
                self._brute_queue.put(combo, block=True)
        finally:
            for _ in range(n_workers):
                self._brute_queue.put(None)

    def _generate_htc_serials(self):
        if not self.brute_htc_enabled_var.get():
            yield None
            return
        years = [c.strip() for c in self.brute_htc_years_var.get().split() if c.strip()]
        months = [c.strip() for c in self.brute_htc_months_var.get().split() if c.strip()]
        dcodes = [c.strip() for c in self.brute_htc_devcodes_var.get().split() if c.strip()]
        uchars = list(self.brute_htc_uchars_var.get().strip())
        try:
            seq_start = int(self.brute_htc_seq_start_var.get().strip())
            seq_end = int(self.brute_htc_seq_end_var.get().strip())
            seq_step = int(self.brute_htc_seq_step_var.get().strip()) if self.brute_htc_seq_step_var.get().strip() else 1
            if seq_step <= 0:
                seq_step = 1
            if seq_start > seq_end:
                seq_start, seq_end = seq_end, seq_start
        except ValueError:
            yield None
            return
        if not (years and months and dcodes and uchars):
            yield None
            return
        yielded = False
        for y, m, c, dd in _itertools.product(years, months, uchars, dcodes):
            for seq in range(seq_start, seq_end + 1, seq_step):
                yield f"HT{y}{m}{c}{dd}{seq:05d}"
                yielded = True
        if not yielded:
            yield None

    def _compute_htc_count(self):
        if not self.brute_htc_enabled_var.get():
            return 1
        try:
            years = [c for c in self.brute_htc_years_var.get().split() if c.strip()]
            months = [c for c in self.brute_htc_months_var.get().split() if c.strip()]
            dcodes = [c for c in self.brute_htc_devcodes_var.get().split() if c.strip()]
            uchars = list(self.brute_htc_uchars_var.get().strip())
            seq_start = int(self.brute_htc_seq_start_var.get().strip())
            seq_end = int(self.brute_htc_seq_end_var.get().strip())
            seq_step = int(self.brute_htc_seq_step_var.get().strip()) if self.brute_htc_seq_step_var.get().strip() else 1
            if seq_step <= 0:
                seq_step = 1
            if seq_start > seq_end:
                seq_start, seq_end = seq_end, seq_start
            combos = len(years) * len(months) * len(uchars) * len(dcodes)
            seq_count = (seq_end - seq_start) // seq_step + 1
            return combos * seq_count
        except (ValueError, ZeroDivisionError):
            return 1

    def _generate_pixel_serials(self):
        if not self.brute_pixel_enabled_var.get():
            yield None
            return
        base = self.brute_pixel_base_var.get().strip()
        factory = self.brute_pixel_factory_var.get().strip()
        years = [c.strip() for c in self.brute_pixel_years_var.get().split() if c.strip()]
        months = [c.strip() for c in self.brute_pixel_months_var.get().split() if c.strip()]
        try:
            day_start = int(self.brute_pixel_day_start_var.get().strip())
            day_end = int(self.brute_pixel_day_end_var.get().strip())
            seq_start = int(self.brute_pixel_seq_start_var.get().strip())
            seq_end = int(self.brute_pixel_seq_end_var.get().strip())
            seq_step = int(self.brute_pixel_seq_step_var.get().strip()) if self.brute_pixel_seq_step_var.get().strip() else 1
            if seq_step <= 0:
                seq_step = 1
            if day_start > day_end:
                day_start, day_end = day_end, day_start
            if seq_start > seq_end:
                seq_start, seq_end = seq_end, seq_start
        except ValueError:
            yield None
            return
        if not (base and factory and years and months):
            yield None
            return
        yielded = False
        for y, m in _itertools.product(years, months):
            for day in range(day_start, day_end + 1):
                for seq in range(seq_start, seq_end + 1, seq_step):
                    yield f"{base}{y}{m}{day:02d}{factory}{seq:05d}"
                    yielded = True
        if not yielded:
            yield None

    def _compute_pixel_count(self):
        if not self.brute_pixel_enabled_var.get():
            return 1
        try:
            years = [c for c in self.brute_pixel_years_var.get().split() if c.strip()]
            months = [c for c in self.brute_pixel_months_var.get().split() if c.strip()]
            day_start = int(self.brute_pixel_day_start_var.get().strip())
            day_end = int(self.brute_pixel_day_end_var.get().strip())
            seq_start = int(self.brute_pixel_seq_start_var.get().strip())
            seq_end = int(self.brute_pixel_seq_end_var.get().strip())
            seq_step = int(self.brute_pixel_seq_step_var.get().strip()) if self.brute_pixel_seq_step_var.get().strip() else 1
            if seq_step <= 0:
                seq_step = 1
            if day_start > day_end:
                day_start, day_end = day_end, day_start
            if seq_start > seq_end:
                seq_start, seq_end = seq_end, seq_start
            date_combos = len(years) * len(months) * (day_end - day_start + 1)
            seq_count = (seq_end - seq_start) // seq_step + 1
            return date_combos * seq_count
        except (ValueError, ZeroDivisionError):
            return 1

    def _generate_moto_serials(self):
        if not self.brute_moto_enabled_var.get():
            yield None
            return
        revisions = [c.strip() for c in self.brute_moto_revisions_var.get().split() if c.strip()]
        factories = [c.strip() for c in self.brute_moto_factories_var.get().split() if c.strip()]
        alphabet = self.brute_moto_alphabet_var.get().strip()
        try:
            seq_len = max(1, int(self.brute_moto_seqlen_var.get().strip()))
            seq_start = int(self.brute_moto_seq_start_var.get().strip())
            seq_end = int(self.brute_moto_seq_end_var.get().strip())
            seq_step = int(self.brute_moto_seq_step_var.get().strip()) if self.brute_moto_seq_step_var.get().strip() else 1
            if seq_step <= 0:
                seq_step = 1
            if seq_start > seq_end:
                seq_start, seq_end = seq_end, seq_start
        except ValueError:
            yield None
            return
        if not (revisions and factories and alphabet):
            yield None
            return
        base = len(alphabet)
        max_index = base ** seq_len

        def index_to_seq(n):
            chars = []
            for _ in range(seq_len):
                chars.append(alphabet[n % base])
                n //= base
            return ''.join(reversed(chars))

        yielded = False
        for rev, ff in _itertools.product(revisions, factories):
            for idx in range(seq_start, min(seq_end + 1, max_index), seq_step):
                yield f"P02{rev}{ff}{index_to_seq(idx)}"
                yielded = True
        if not yielded:
            yield None

    def _compute_moto_count(self):
        if not self.brute_moto_enabled_var.get():
            return 1
        try:
            revisions = [c.strip() for c in self.brute_moto_revisions_var.get().split() if c.strip()]
            factories = [c.strip() for c in self.brute_moto_factories_var.get().split() if c.strip()]
            alphabet = self.brute_moto_alphabet_var.get().strip()
            seq_len = max(1, int(self.brute_moto_seqlen_var.get().strip()))
            seq_start = int(self.brute_moto_seq_start_var.get().strip())
            seq_end = int(self.brute_moto_seq_end_var.get().strip())
            seq_step = int(self.brute_moto_seq_step_var.get().strip()) if self.brute_moto_seq_step_var.get().strip() else 1
            if seq_step <= 0:
                seq_step = 1
            if seq_start > seq_end:
                seq_start, seq_end = seq_end, seq_start
            max_index = len(alphabet) ** seq_len
            seq_count = (min(seq_end, max_index - 1) - seq_start) // seq_step + 1
            return len(revisions) * len(factories) * max(0, seq_count)
        except (ValueError, ZeroDivisionError):
            return 1

    def _brute_stop_and_save(self):
        self._brute_stop()
        path = filedialog.asksaveasfilename(
            title="Save Bruteforce Progress",
            defaultextension=".json",
            filetypes=[("JSON progress file", "*.json"), ("All files", "*.*")],
        )
        if not path:
            return

        def _safe(var, fallback=""):
            try:
                return var.get()
            except Exception:
                return fallback

        processed = getattr(self, "_brute_processed", 0)
        total = getattr(self, "_brute_total", 0)
        found = getattr(self, "_brute_found_count", 0)

        data = {
            "version": 2,
            "saved_at": datetime.now().isoformat(),
            "progress": {
                "processed": processed,
                "total": total,
                "found": found,
                "skip_count": processed,
            },
            "settings": {
                "os_mode": _safe(self.os_mode_var),
                "template": _safe(self.brute_fp_var),
                "build_tags": self.brute_tags_text.get("1.0", tk.END).strip(),
                "key_types": self.brute_keys_text.get("1.0", tk.END).strip(),
                "locales": self.brute_locales_text.get("1.0", tk.END).strip()
                if hasattr(self, "brute_locales_text") else "",
                "inc_start": _safe(self.brute_inc_start_var),
                "inc_end": _safe(self.brute_inc_end_var),
                "inc_step": _safe(self.brute_inc_step_var),
                "workers": _safe(self.brute_workers_var),
                "serial_enabled": _safe(self.brute_serial_enabled_var, False),
                "serial_template": _safe(self.brute_serial_template_var),
                "serial_start": _safe(self.brute_serial_start_var),
                "serial_end": _safe(self.brute_serial_end_var),
                "serial_step": _safe(self.brute_serial_step_var),
                "serial_hex": _safe(self.brute_serial_hex_var, False),
                "serial_base36": _safe(self.brute_serial_base36_var, False),
                "serial_start2": _safe(self.brute_serial_start2_var),
                "serial_end2": _safe(self.brute_serial_end2_var),
                "serial_step2": _safe(self.brute_serial_step2_var),
                "serial_hex2": _safe(self.brute_serial_hex2_var, False),
                "serial_base36_2": _safe(self.brute_serial_base36_2_var, False),
                "serial_start3": _safe(self.brute_serial_start3_var),
                "serial_end3": _safe(self.brute_serial_end3_var),
                "serial_step3": _safe(self.brute_serial_step3_var),
                "serial_hex3": _safe(self.brute_serial_hex3_var, False),
                "serial_base36_3": _safe(self.brute_serial_base36_3_var, False),
                "serial_start4": _safe(self.brute_serial_start4_var),
                "serial_end4": _safe(self.brute_serial_end4_var),
                "serial_step4": _safe(self.brute_serial_step4_var),
                "serial_hex4": _safe(self.brute_serial_hex4_var, False),
                "serial_base36_4": _safe(self.brute_serial_base36_4_var, False),
                "serial_start5": _safe(self.brute_serial_start5_var),
                "serial_end5": _safe(self.brute_serial_end5_var),
                "serial_step5": _safe(self.brute_serial_step5_var),
                "serial_hex5": _safe(self.brute_serial_hex5_var, False),
                "serial_base36_5": _safe(self.brute_serial_base36_5_var, False),
                "imei_enabled": _safe(self.brute_imei_enabled_var, False),
                "imei_tac": _safe(self.brute_imei_tac_var),
                "imei_snr_start": _safe(self.brute_imei_snr_start_var),
                "imei_snr_end": _safe(self.brute_imei_snr_end_var),
                "imei_snr_step": _safe(self.brute_imei_snr_step_var),
                "imei_zeropad": _safe(self.brute_imei_zeropad_var, True),
                "htc_enabled": _safe(self.brute_htc_enabled_var, False),
                "htc_years": _safe(self.brute_htc_years_var),
                "htc_months": _safe(self.brute_htc_months_var),
                "htc_devcodes": _safe(self.brute_htc_devcodes_var),
                "htc_uchars": _safe(self.brute_htc_uchars_var),
                "htc_seq_start": _safe(self.brute_htc_seq_start_var),
                "htc_seq_end": _safe(self.brute_htc_seq_end_var),
                "htc_seq_step": _safe(self.brute_htc_seq_step_var),
                "pixel_enabled": _safe(self.brute_pixel_enabled_var, False),
                "pixel_base": _safe(self.brute_pixel_base_var),
                "pixel_factory": _safe(self.brute_pixel_factory_var),
                "pixel_years": _safe(self.brute_pixel_years_var),
                "pixel_months": _safe(self.brute_pixel_months_var),
                "pixel_day_start": _safe(self.brute_pixel_day_start_var),
                "pixel_day_end": _safe(self.brute_pixel_day_end_var),
                "pixel_seq_start": _safe(self.brute_pixel_seq_start_var),
                "pixel_seq_end": _safe(self.brute_pixel_seq_end_var),
                "pixel_seq_step": _safe(self.brute_pixel_seq_step_var),
                "moto_enabled": _safe(self.brute_moto_enabled_var, False),
                "moto_revisions": _safe(self.brute_moto_revisions_var),
                "moto_factories": _safe(self.brute_moto_factories_var),
                "moto_alphabet": _safe(self.brute_moto_alphabet_var),
                "moto_seqlen": _safe(self.brute_moto_seqlen_var),
                "moto_seq_start": _safe(self.brute_moto_seq_start_var),
                "moto_seq_end": _safe(self.brute_moto_seq_end_var),
                "moto_seq_step": _safe(self.brute_moto_seq_step_var),
                "stop_on_find": _safe(self.brute_stop_on_find_var, True),
                "skip_dupes": _safe(self.brute_skip_dupes_var, True),
                "save_otas": _safe(self.brute_save_otas_var, False),
            }
        }
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
            messagebox.showinfo("Progress Saved",
                                f"Progress saved to:\n{path}\n\n"
                                f"Processed: {data['progress']['processed']} / {data['progress']['total']}\n"
                                f"OTAs found: {data['progress']['found']}")
        except Exception as e:
            messagebox.showerror("Save Failed", str(e))

    def _brute_load_progress(self):
        path = filedialog.askopenfilename(
            title="Load Bruteforce Progress",
            filetypes=[("JSON progress file", "*.json"), ("All files", "*.*")],
        )
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception as e:
            messagebox.showerror("Load Failed", str(e))
            return

        s = data.get("settings", {})

        def _set(var, key, default=""):
            val = s.get(key, default)
            try:
                if isinstance(var, tk.BooleanVar):
                    var.set(bool(val))
                else:
                    var.set(str(val))
            except Exception:
                pass

        def _set_text(widget, key):
            val = s.get(key, "")
            widget.delete("1.0", tk.END)
            widget.insert("1.0", val)

        _set(self.os_mode_var, "os_mode")
        _set(self.brute_fp_var, "template")
        _set_text(self.brute_tags_text, "build_tags")
        _set_text(self.brute_keys_text, "key_types")
        if hasattr(self, "brute_locales_text"):
            _set_text(self.brute_locales_text, "locales")
        _set(self.brute_inc_start_var, "inc_start")
        _set(self.brute_inc_end_var, "inc_end")
        _set(self.brute_inc_step_var, "inc_step")
        _set(self.brute_workers_var, "workers")
        _set(self.brute_serial_enabled_var, "serial_enabled", False)
        _set(self.brute_serial_template_var, "serial_template")
        _set(self.brute_serial_start_var, "serial_start")
        _set(self.brute_serial_end_var, "serial_end")
        _set(self.brute_serial_step_var, "serial_step")
        _set(self.brute_serial_hex_var, "serial_hex", False)
        _set(self.brute_serial_base36_var, "serial_base36", False)
        _set(self.brute_serial_start2_var, "serial_start2", "1")
        _set(self.brute_serial_end2_var, "serial_end2", "9999")
        _set(self.brute_serial_step2_var, "serial_step2", "1")
        _set(self.brute_serial_hex2_var, "serial_hex2", False)
        _set(self.brute_serial_base36_2_var, "serial_base36_2", False)
        _set(self.brute_serial_start3_var, "serial_start3", "1")
        _set(self.brute_serial_end3_var, "serial_end3", "9999")
        _set(self.brute_serial_step3_var, "serial_step3", "1")
        _set(self.brute_serial_hex3_var, "serial_hex3", False)
        _set(self.brute_serial_base36_3_var, "serial_base36_3", False)
        _set(self.brute_serial_start4_var, "serial_start4", "1")
        _set(self.brute_serial_end4_var, "serial_end4", "9999")
        _set(self.brute_serial_step4_var, "serial_step4", "1")
        _set(self.brute_serial_hex4_var, "serial_hex4", False)
        _set(self.brute_serial_base36_4_var, "serial_base36_4", False)
        _set(self.brute_serial_start5_var, "serial_start5", "1")
        _set(self.brute_serial_end5_var, "serial_end5", "9999")
        _set(self.brute_serial_step5_var, "serial_step5", "1")
        _set(self.brute_serial_hex5_var, "serial_hex5", False)
        _set(self.brute_serial_base36_5_var, "serial_base36_5", False)
        _set(self.brute_imei_enabled_var, "imei_enabled", False)
        _set(self.brute_imei_tac_var, "imei_tac")
        _set(self.brute_imei_snr_start_var, "imei_snr_start")
        _set(self.brute_imei_snr_end_var, "imei_snr_end")
        _set(self.brute_imei_snr_step_var, "imei_snr_step")
        _set(self.brute_imei_zeropad_var, "imei_zeropad", True)
        _set(self.brute_htc_enabled_var, "htc_enabled", False)
        _set(self.brute_htc_years_var, "htc_years")
        _set(self.brute_htc_months_var, "htc_months")
        _set(self.brute_htc_devcodes_var, "htc_devcodes")
        _set(self.brute_htc_uchars_var, "htc_uchars")
        _set(self.brute_htc_seq_start_var, "htc_seq_start")
        _set(self.brute_htc_seq_end_var, "htc_seq_end")
        _set(self.brute_htc_seq_step_var, "htc_seq_step")
        _set(self.brute_pixel_enabled_var, "pixel_enabled", False)
        _set(self.brute_pixel_base_var, "pixel_base")
        _set(self.brute_pixel_factory_var, "pixel_factory")
        _set(self.brute_pixel_years_var, "pixel_years")
        _set(self.brute_pixel_months_var, "pixel_months")
        _set(self.brute_pixel_day_start_var, "pixel_day_start")
        _set(self.brute_pixel_day_end_var, "pixel_day_end")
        _set(self.brute_pixel_seq_start_var, "pixel_seq_start")
        _set(self.brute_pixel_seq_end_var, "pixel_seq_end")
        _set(self.brute_pixel_seq_step_var, "pixel_seq_step")
        _set(self.brute_moto_enabled_var, "moto_enabled", False)
        _set(self.brute_moto_revisions_var, "moto_revisions")
        _set(self.brute_moto_factories_var, "moto_factories")
        _set(self.brute_moto_alphabet_var, "moto_alphabet")
        _set(self.brute_moto_seqlen_var, "moto_seqlen")
        _set(self.brute_moto_seq_start_var, "moto_seq_start")
        _set(self.brute_moto_seq_end_var, "moto_seq_end")
        _set(self.brute_moto_seq_step_var, "moto_seq_step")
        _set(self.brute_stop_on_find_var, "stop_on_find", True)
        _set(self.brute_skip_dupes_var, "skip_dupes", True)
        _set(self.brute_save_otas_var, "save_otas", False)

        prog = data.get("progress", {})
        processed = prog.get("processed", 0)
        total = prog.get("total", 0)
        found = prog.get("found", 0)
        skip_count = prog.get("skip_count", processed)

        self._brute_resume_skip = skip_count

        ans = messagebox.askyesno(
            "Resume Bruteforce?",
            f"Progress loaded from:\n{path}\n\n"
            f"Last session: {processed} / {total} processed, {found} OTAs found.\n"
            f"Will skip first {skip_count} combinations and resume from there.\n\n"
            f"Start bruteforce now?"
        )
        if ans:
            self._brute_start()

    def _generate_serials(self):
        if not self.brute_serial_enabled_var.get():
            return
        template = self.brute_serial_template_var.get().strip()
        has_num1 = '{num1}' in template or '{num}' in template
        has_num2 = '{num2}' in template
        has_num3 = '{num3}' in template
        has_num4 = '{num4}' in template
        has_num5 = '{num5}' in template
        if not any([has_num1, has_num2, has_num3, has_num4, has_num5]):
            return

        _B36_CHARS = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"

        def _b36(n, width):
            if n == 0:
                return "0" * width
            chars = []
            while n:
                chars.append(_B36_CHARS[n % 36])
                n //= 36
            return ''.join(reversed(chars)).zfill(width)

        def _make_formatter(start_var, end_var, step_var, hex_var, b36_var):
            try:
                start = int(start_var.get().strip())
                end = int(end_var.get().strip())
                raw_s = step_var.get().strip()
                step = int(raw_s) if raw_s else 1
                if step <= 0:
                    step = 1
                if start > end:
                    start, end = end, start
            except ValueError:
                return None
            if b36_var.get():
                width = max(len(_b36(start, 1)), len(_b36(end, 1)))
                fmt = lambda n, w=width: _b36(n, w)
            elif hex_var.get():
                width = max(len(f"{start:X}"), len(f"{end:X}"))
                fmt = lambda n, w=width: f"{n:0{w}X}"
            else:
                width = max(len(str(start)), len(str(end)))
                fmt = lambda n, w=width: f"{n:0{w}d}"
            return start, end, step, fmt

        cfg1 = _make_formatter(
            self.brute_serial_start_var, self.brute_serial_end_var,
            self.brute_serial_step_var, self.brute_serial_hex_var,
            self.brute_serial_base36_var) if has_num1 else None

        cfg2 = _make_formatter(
            self.brute_serial_start2_var, self.brute_serial_end2_var,
            self.brute_serial_step2_var, self.brute_serial_hex2_var,
            self.brute_serial_base36_2_var) if has_num2 else None

        cfg3 = _make_formatter(
            self.brute_serial_start3_var, self.brute_serial_end3_var,
            self.brute_serial_step3_var, self.brute_serial_hex3_var,
            self.brute_serial_base36_3_var) if has_num3 else None

        cfg4 = _make_formatter(
            self.brute_serial_start4_var, self.brute_serial_end4_var,
            self.brute_serial_step4_var, self.brute_serial_hex4_var,
            self.brute_serial_base36_4_var) if has_num4 else None

        cfg5 = _make_formatter(
            self.brute_serial_start5_var, self.brute_serial_end5_var,
            self.brute_serial_step5_var, self.brute_serial_hex5_var,
            self.brute_serial_base36_5_var) if has_num5 else None

        if has_num1 and cfg1 is None:
            return
        if has_num2 and cfg2 is None:
            return
        if has_num3 and cfg3 is None:
            return
        if has_num4 and cfg4 is None:
            return
        if has_num5 and cfg5 is None:
            return

        def _vals(cfg):
            s, e, st, fmt = cfg
            for n in range(s, e + 1, st):
                yield fmt(n)

        active = []
        if has_num1:
            active.append(('{num1}', cfg1))
        if has_num2:
            active.append(('{num2}', cfg2))
        if has_num3:
            active.append(('{num3}', cfg3))
        if has_num4:
            active.append(('{num4}', cfg4))
        if has_num5:
            active.append(('{num5}', cfg5))

        def _expand(t, pairs):
            if not pairs:
                yield t
                return
            placeholder, cfg = pairs[0]
            rest = pairs[1:]
            for v in _vals(cfg):
                t2 = t.replace(placeholder, v)
                if placeholder == '{num1}':
                    t2 = t2.replace('{num}', v)
                yield from _expand(t2, rest)

        yield from _expand(template, active)

    def _brute_worker(self, device_sn="", imei="", serial_enabled=False):
        while True:
            self._brute_pause_event.wait()
            if self._brute_stop_flag:
                break
            try:
                item = self._brute_queue.get(timeout=0.5)
            except queue.Empty:
                continue
            if item is None:
                break
            build_tag, key_type, inc, loc, template, serial, imei_val = item

            fp = template
            if '{BUILD}' in template:
                fp = fp.replace('{BUILD}', build_tag)
            if '{INC}' in template:
                fp = fp.replace('{INC}', inc)
            if '{KEY}' in template:
                fp = fp.replace('{KEY}', key_type)

            actual_sn = serial if serial is not None else device_sn
            actual_imei = imei_val if imei_val is not None else imei

            tz = LOCALE_TZ_MAP.get(loc, 'America/New_York')

            _NETWORK_ERRS = ("handshake operation timed out",
                             "read operation timed out",
                             "_ssl.c",
                             "urlopen error",
                             "timed out",
                             "connection reset",
                             "connection refused",
                             "remote end closed")
            max_hard_retries = 3
            hard_attempt = 0
            while True:
                if self._brute_stop_flag:
                    break
                self._brute_pause_event.wait()
                if self._brute_stop_flag:
                    break
                try:
                    _curl = getattr(self, 'checkin_url_var', None)
                    _curl = _curl.get().strip() if _curl else None
                    settings, raw_bytes, _req, _reqgz = perform_checkin(fp, locale=loc, timezone=tz, device_sn=actual_sn, imei=actual_imei, url=_curl)
                    if not settings:
                        hard_attempt += 1
                        if hard_attempt >= max_hard_retries:
                            label = self._brute_combo_label(build_tag, key_type, inc, loc, serial, actual_imei)
                            self._brute_log(f"  {label} → no response (after {max_hard_retries} retries)", 'skip')
                            self._brute_increment_progress()
                            break
                        continue
                    ota = find_ota_link(settings)
                    self._brute_process_result(fp, build_tag, key_type, inc, loc, ota, raw_bytes, serial, imei_val)
                    self._brute_increment_progress()
                    break
                except Exception as e:
                    err_str = str(e).lower()
                    is_network = any(ne in err_str for ne in _NETWORK_ERRS)
                    if is_network:
                        continue
                    hard_attempt += 1
                    if hard_attempt >= max_hard_retries:
                        label = self._brute_combo_label(build_tag, key_type, inc, loc, serial, actual_imei)
                        self._brute_log(f"  {label} → ERROR: {e} (after {max_hard_retries} retries)", 'error')
                        self._brute_increment_progress()
                        break

    @staticmethod
    def _brute_combo_label(build_tag, key_type, inc, loc, serial=None, actual_imei=None):
        parts = []
        if build_tag:
            parts.append(f"BUILD={build_tag}")
        if key_type:
            parts.append(f"KEY={key_type}")
        if inc:
            parts.append(f"INC={inc}")
        if loc:
            parts.append(f"LOCALE={loc}")
        label = " ".join(parts)
        if serial is not None:
            label += f" SERIAL={serial}"
        if actual_imei is not None:
            label += f" IMEI={actual_imei}"
        return label

    def _brute_process_result(self, fp, build_tag, key_type, inc, loc, ota, raw_bytes, serial=None, imei_val=None):
        skip_dupes = getattr(self, '_brute_cache_skip_dupes', self.brute_skip_dupes_var.get())
        pause_on_find = getattr(self, '_brute_cache_pause_on_find', self.brute_stop_on_find_var.get())
        save_otas = getattr(self, '_brute_cache_save_otas', self.brute_save_otas_var.get())
        hide_dupes_log = getattr(self, '_brute_cache_hide_dupes_log', True)
        hide_no_ota = getattr(self, '_brute_cache_hide_no_ota', False)

        is_dogfood = False
        if raw_bytes:
            raw_lower = raw_bytes.lower()
            if b'droidfood' in raw_lower or b'platform_dogfood' in raw_lower:
                is_dogfood = True

        mode = self.os_mode_var.get()
        if mode == "xiaomi":
            label = f"DEVICE={build_tag} ROM={key_type} AND={inc}"
        elif mode == "chromeos":
            label = f"BOARD={build_tag} TRACK={key_type} VER={inc}"
        else:
            label = self._brute_combo_label(build_tag, key_type, inc, loc)
            if serial is not None:
                label += f" SERIAL={serial}"
            if imei_val is not None:
                label += f" IMEI={imei_val}"

        if ota is None:
            if is_dogfood:
                with self._brute_progress_lock:
                    self._brute_dogfood_count += 1
                serial_str = f": {serial}" if serial is not None else ""
                self._brute_log(f"  🐶 [DOGFOOD] No OTA but dogfood serial found{serial_str}  {label}", 'dogfood')
            elif not hide_no_ota:
                self._brute_log(f"  {label} → no OTA", 'skip')
            return
        url = ota.get('url')
        if not url:
            if is_dogfood:
                with self._brute_progress_lock:
                    self._brute_dogfood_count += 1
                serial_str = f": {serial}" if serial is not None else ""
                self._brute_log(f"  🐶 [DOGFOOD] No OTA URL but dogfood serial found{serial_str}  {label}", 'dogfood')
            elif not hide_no_ota:
                self._brute_log(f"  {label} → no OTA URL", 'skip')
            return

        title = ota.get('title', '')
        desc = ota.get('description', '')
        size = ota.get('size', '')
        meta = (title, desc, size)

        with self._brute_progress_lock:
            meta_set = self._brute_found_data.get(url)
            if meta_set is None:
                self._brute_found_data[url] = {meta}
                is_new = True
                is_changed = False
                is_duplicate = False
            elif meta in meta_set:
                is_new = False
                is_changed = False
                is_duplicate = True
            else:
                meta_set.add(meta)
                is_new = False
                is_changed = True
                is_duplicate = False
            self._brute_found_count += 1
            if is_dogfood:
                self._brute_dogfood_count += 1
            local_count = len(self._brute_found_data)

        if is_duplicate:
            if is_dogfood:
                serial_str = f": {serial}" if serial is not None else ""
                self._brute_log(f"  🐶 [DOGFOOD] Dogfood serial found{serial_str}  {label}", 'dogfood')
            elif not hide_dupes_log:
                self._brute_log(f"  {label} → OTA found (duplicate URL and metadata)", 'duplicate')
            return

        try:
            add_ota_record(
                os_kind=self.os_mode_var.get(),
                url=url,
                title=title,
                description=desc,
                size=size,
                locale=loc,
                fingerprint=fp,
            )
        except Exception:
            pass

        tag = 'found'
        if is_dogfood:
            tag = 'dogfood'
        if is_new:
            block = [("", tag), (f"  ★ NEW #{local_count}  {label}", tag),
                     (f"    Fingerprint : {fp}", tag),
                     (f"    URL         : {url}", tag)]
            if is_dogfood:
                block.append((f"    🐶 DOGFOOD serial detected!", 'dogfood'))
            if title:
                block.append((f"    Title       : {title}", tag))
            if desc:
                block.append((f"    Description : {desc[:80]}{'...' if len(desc) > 80 else ''}", tag))
            if size:
                block.append((f"    Size        : {size}", tag))
            block.append(("", tag))
            self._brute_log_block(block)
        elif is_changed:
            change_msg = "Found OTA with different description (UPDATED)"
            block = [("", 'changed'), (f"  ⚡ {change_msg}  {label}", 'changed'),
                     (f"    Fingerprint : {fp}", 'changed'),
                     (f"    URL         : {url}", 'changed')]
            if is_dogfood:
                block.append((f"    🐶 DOGFOOD serial detected!", 'dogfood'))
            if title:
                block.append((f"    Title       : {title}", 'changed'))
            if desc:
                block.append((f"    Description : {desc[:80]}{'...' if len(desc) > 80 else ''}", 'changed'))
            if size:
                block.append((f"    Size        : {size}", 'changed'))
            block.append(("", 'changed'))
            self._brute_log_block(block)
        else:
            return

        if save_otas:
            try:
                script_dir = os.path.dirname(os.path.abspath(__file__))
                otas_path = os.path.join(script_dir, "OTAs.txt")
                with open(otas_path, 'a', encoding='utf-8') as f:
                    f.write(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}]")
                    if is_changed:
                        f.write(" [UPDATED]")
                    if is_dogfood:
                        f.write(" [DOGFOOD]")
                    f.write("\n")
                    f.write(f"  Fingerprint : {fp}\n")
                    f.write(f"  URL         : {url}\n")
                    if title:
                        f.write(f"  Title       : {title}\n")
                    if desc:
                        f.write(f"  Description : {desc}\n")
                    if size:
                        f.write(f"  Size        : {size}\n")
                    if serial is not None:
                        f.write(f"  Serial      : {serial}\n")
                    f.write("\n")
                self._brute_log(f"    Saved to OTAs.txt", 'info')
            except Exception as e:
                self._brute_log(f"    Could not save to OTAs.txt: {e}", 'error')

        if pause_on_find and is_new:
            self._brute_pause_event.clear()
            self.brute_pause_btn.config(state=tk.DISABLED)
            self.brute_continue_btn.config(state=tk.NORMAL)
            self.brute_stop_btn.config(state=tk.NORMAL)
            self.brute_stop_save_btn.config(state=tk.NORMAL)
            pause_msg = f"⏸ Paused after new OTA found (#{local_count}) — press Continue"
            self.brute_status_var.set(pause_msg)

    def _brute_increment_progress(self):
        with self._brute_progress_lock:
            self._brute_processed += 1
            self._brute_speed_count += 1
            processed = self._brute_processed
            total = self._brute_total
            found = self._brute_found_count
            unique = len(self._brute_found_data)
            dogfood = self._brute_dogfood_count
        self.root.after(0, lambda p=processed, t=total, f=found, u=unique, d=dogfood:
                        self._brute_update_progress_ui(p, t, f, u, d))

    def _brute_update_progress_ui(self, processed, total, found, unique, dogfood):
        try:
            self.brute_progress['value'] = processed
            dogfood_str = f", dogfood s/ns={dogfood}" if dogfood > 0 else ""
            self.brute_status_var.set(
                f"[{processed}/{total}]  "
                f"found={found}, unique={unique}{dogfood_str}"
            )
        except Exception:
            pass

    def _brute_update_speed(self):
        if not self._brute_running:
            self.brute_speed_var.set("— req/s")
            return
        now = time.monotonic()
        with self._brute_progress_lock:
            elapsed = now - self._brute_speed_ts
            count = self._brute_speed_count
            self._brute_speed_count = 0
            self._brute_speed_ts = now
        if elapsed > 0:
            speed = count / elapsed
            self.brute_speed_var.set(
                f"{speed/1000:.1f}k req/s" if speed >= 1000 else f"{speed:.1f} req/s"
            )
        self.root.after(1000, self._brute_update_speed)

    def _brute_producer_chromeos(self, board_tags, tracks, inc_start, inc_end, inc_step, template, n_workers,
                                 use_board, use_ver, use_track, app_id, serial_enabled):
        try:
            boards = board_tags if use_board else [""]
            trks = tracks if use_track else [""]
            if use_ver:
                inc_values = range(inc_start, inc_end + 1, inc_step)
            else:
                inc_values = [0]

            def _all_combos_cros():
                for bt in boards:
                    for inc in inc_values:
                        for tr in trks:
                            for serial in (self._generate_serials() if serial_enabled else (None,)):
                                yield (bt, tr, str(inc) if use_ver else "", template, app_id, serial)

            for combo in _all_combos_cros():
                if self._brute_stop_flag:
                    break
                if self._brute_stop_flag:
                    return
                self._brute_queue.put(combo, block=True)
        finally:
            for _ in range(n_workers):
                self._brute_queue.put(None)

    def _brute_worker_chromeos(self, serial_enabled=False):
        while True:
            self._brute_pause_event.wait()
            if self._brute_stop_flag:
                break
            try:
                item = self._brute_queue.get(timeout=0.5)
            except queue.Empty:
                continue
            if item is None:
                break
            board_tag, track, ver, template, app_id, serial = item

            fp = template
            if '{BOARD}' in template:
                fp = fp.replace('{BOARD}', board_tag)
            if '{VER}' in template:
                fp = fp.replace('{VER}', ver if ver else '0.0.0.0')
            if '{TRACK}' in template:
                fp = fp.replace('{TRACK}', track)

            _NETWORK_ERRS = ("handshake operation timed out",
                             "read operation timed out",
                             "_ssl.c",
                             "urlopen error",
                             "timed out",
                             "connection reset",
                             "connection refused",
                             "remote end closed")
            max_hard_retries = 3
            hard_attempt = 0
            while True:
                if self._brute_stop_flag:
                    break
                self._brute_pause_event.wait()
                if self._brute_stop_flag:
                    break
                try:
                    parsed = parse_fingerprint_chromeos(fp)
                    response_text, raw_bytes = perform_checkin_chromeos(fp, app_id, hardware_class=parsed['hwid'])
                    if not response_text:
                        hard_attempt += 1
                        if hard_attempt >= max_hard_retries:
                            label = f"BOARD={board_tag} TRACK={track} VER={ver}"
                            if serial is not None:
                                label += f" SERIAL={serial}"
                            self._brute_log(f"  {label} → no response (after {max_hard_retries} retries)", 'skip')
                            self._brute_increment_progress()
                            break
                        continue
                    ota = find_ota_link_chromeos(response_text)
                    self._brute_process_result(fp, board_tag, track, ver, "", ota, raw_bytes, serial)
                    self._brute_increment_progress()
                    break
                except Exception as e:
                    err_str = str(e).lower()
                    is_network = any(ne in err_str for ne in _NETWORK_ERRS)
                    if is_network:
                        continue
                    hard_attempt += 1
                    if hard_attempt >= max_hard_retries:
                        label = f"BOARD={board_tag} TRACK={track} VER={ver}"
                        if serial is not None:
                            label += f" SERIAL={serial}"
                        self._brute_log(f"  {label} → ERROR: {e} (after {max_hard_retries} retries)", 'error')
                        self._brute_increment_progress()
                        break

    def _brute_start_xiaomi(self, template, serial_enabled):
        use_device = '{DEVICE}' in template
        use_rom = '{ROM}' in template
        use_and = '{AND}' in template

        raw_devices = self.brute_tags_text.get("1.0", tk.END).strip()
        devices = [d.strip() for d in raw_devices.splitlines() if d.strip()]
        if not devices:
            devices = ["dada_global"] if use_device else [""]

        raw_roms = self.brute_keys_text.get("1.0", tk.END).strip()
        roms = [r.strip() for r in raw_roms.splitlines() if r.strip()]
        if not roms:
            roms = ["OS1.0.2.0.UNCMIXM"] if use_rom else [""]

        try:
            and_start_str = self.brute_inc_start_var.get().strip()
            and_end_str = self.brute_inc_end_var.get().strip()
            and_step_str = self.brute_inc_step_var.get().strip()
            if and_start_str and and_end_str and use_and:
                and_start = int(and_start_str)
                and_end = int(and_end_str)
                and_step = int(and_step_str) if and_step_str else 1
                if and_step <= 0:
                    and_step = 1
            else:
                and_start, and_end, and_step = 0, 0, 1
        except ValueError:
            and_start, and_end, and_step = 0, 0, 1

        and_count = (and_end - and_start) // and_step + 1 if use_and else 1
        device_count = len(devices) if use_device else 1
        rom_count = len(roms) if use_rom else 1
        serial_count = self._compute_serial_count() if serial_enabled else 1
        total = device_count * rom_count * and_count * serial_count
        if total == 0:
            total = 1

        _resume_skip = getattr(self, "_brute_resume_skip", 0)
        remaining = max(1, total - _resume_skip)

        self._brute_stop_flag = False
        self._brute_pause_event.set()
        self._brute_found_data.clear()
        self._brute_found_count = 0
        self._brute_processed = 0
        self._brute_total = remaining
        self._brute_dogfood_count = 0

        self._brute_clear_log()

        self.brute_start_btn.config(state=tk.DISABLED)
        self.brute_pause_btn.config(state=tk.NORMAL)
        self.brute_continue_btn.config(state=tk.DISABLED)
        self.brute_stop_btn.config(state=tk.NORMAL)
        self.brute_stop_save_btn.config(state=tk.NORMAL)
        self.brute_progress['maximum'] = remaining
        self.brute_progress['value'] = 0

        self._brute_log(f"Starting Xiaomi bruteforce: {total} combinations", 'header')
        self._brute_log(f"Template: {template}", 'header')
        if serial_enabled:
            self._brute_log("Serial bruteforce enabled.", 'header')
        self._brute_log("=" * 70, 'header')

        try:
            n_workers = max(1, min(1000, int(self.brute_workers_var.get())))
        except ValueError:
            n_workers = 10

        self._brute_queue = queue.Queue(maxsize=10000)

        self._brute_producer_thread = threading.Thread(
            target=self._brute_producer_xiaomi,
            args=(devices, roms, and_start, and_end, and_step, template, n_workers,
                  use_device, use_rom, use_and, serial_enabled),
            daemon=True
        )
        self._brute_producer_thread.start()

        self._brute_worker_threads = []
        for _ in range(n_workers):
            t = threading.Thread(target=self._brute_worker_xiaomi, args=(serial_enabled,), daemon=True)
            t.start()
            self._brute_worker_threads.append(t)

        self._brute_running = True
        self._brute_speed_ts = time.monotonic()
        self._brute_speed_count = 0
        self.brute_speed_var.set("0 req/s")
        self.root.after(500, self._brute_monitor)
        self.root.after(1000, self._brute_update_speed)

    def _brute_producer_xiaomi(self, devices, roms, and_start, and_end, and_step, template, n_workers,
                               use_device, use_rom, use_and, serial_enabled):
        try:
            devs = devices if use_device else [""]
            rom_list = roms if use_rom else [""]
            if use_and:
                and_values = range(and_start, and_end + 1, and_step)
            else:
                and_values = [0]

            def _all_combos_xiaomi():
                for dv in devs:
                    for av in and_values:
                        for rv in rom_list:
                            for serial in (self._generate_serials() if serial_enabled else (None,)):
                                yield (dv, rv, str(av) if use_and else "", template, serial)

            for combo in _all_combos_xiaomi():
                if self._brute_stop_flag:
                    break
                if self._brute_stop_flag:
                    return
                self._brute_queue.put(combo, block=True)
        finally:
            for _ in range(n_workers):
                self._brute_queue.put(None)

    def _brute_worker_xiaomi(self, serial_enabled=False):
        while True:
            self._brute_pause_event.wait()
            if self._brute_stop_flag:
                break
            try:
                item = self._brute_queue.get(timeout=0.5)
            except queue.Empty:
                continue
            if item is None:
                break
            device, rom, android_ver, template, serial = item

            fp = template
            if '{DEVICE}' in template:
                fp = fp.replace('{DEVICE}', device)
            if '{ROM}' in template:
                fp = fp.replace('{ROM}', rom)
            if '{AND}' in template:
                fp = fp.replace('{AND}', android_ver)

            _NETWORK_ERRS = ("handshake operation timed out",
                             "read operation timed out",
                             "_ssl.c",
                             "urlopen error",
                             "timed out",
                             "connection reset",
                             "connection refused",
                             "remote end closed")
            max_hard_retries = 3
            hard_attempt = 0
            while True:
                if self._brute_stop_flag:
                    break
                self._brute_pause_event.wait()
                if self._brute_stop_flag:
                    break
                try:
                    parsed = parse_fingerprint_xiaomi(fp)
                    decrypted, raw_text, _req_body = perform_checkin_xiaomi(
                        parsed['codename'], parsed['rom_version'], parsed['android_version'])
                    if not raw_text:
                        hard_attempt += 1
                        if hard_attempt >= max_hard_retries:
                            label = f"DEVICE={device} ROM={rom} AND={android_ver}"
                            if serial is not None:
                                label += f" SERIAL={serial}"
                            self._brute_log(f"  {label} → no response (after {max_hard_retries} retries)", 'skip')
                            self._brute_increment_progress()
                            break
                        continue
                    details = extract_build_details_xiaomi(decrypted)
                    if details.get('found') and details.get('download_url'):
                        ota = {
                            'url': details['download_url'],
                            'title': _stringify_ota_field(details.get('bigversion_label') or details.get('version', '')),
                            'description': _flatten_xiaomi_changelog(details.get('changelog')),
                            'size': _stringify_ota_field(details.get('filesize', '')),
                        }
                    else:
                        ota = None
                    self._brute_process_result(fp, device, rom, android_ver, "", ota, raw_text.encode('utf-8'), serial)
                    self._brute_increment_progress()
                    break
                except Exception as e:
                    err_str = str(e).lower()
                    is_network = any(ne in err_str for ne in _NETWORK_ERRS)
                    if is_network:
                        continue
                    hard_attempt += 1
                    if hard_attempt >= max_hard_retries:
                        label = f"DEVICE={device} ROM={rom} AND={android_ver}"
                        if serial is not None:
                            label += f" SERIAL={serial}"
                        self._brute_log(f"  {label} → ERROR: {e} (after {max_hard_retries} retries)", 'error')
                        self._brute_increment_progress()
                        break

    def _brute_monitor(self):
        if self._brute_stop_flag:
            self._brute_finish(stop=True)
            return
        if self._brute_producer_thread and self._brute_producer_thread.is_alive():
            self.root.after(500, self._brute_monitor)
            return
        alive = any(t.is_alive() for t in self._brute_worker_threads)
        if alive:
            self.root.after(500, self._brute_monitor)
            return
        self._brute_finish(stop=False)

    def _brute_finish(self, stop=False):
        if stop:
            self._brute_log("=" * 70, 'header')
            self._brute_log("Bruteforce stopped by user.", 'header')
            self.brute_status_var.set("Stopped by user.")
        else:
            self._brute_log("=" * 70, 'header')
            dogfood_str = f", dogfood s/ns={self._brute_dogfood_count}" if self._brute_dogfood_count > 0 else ""
            self._brute_log(f"Bruteforce finished. Found {self._brute_found_count} OTA(s) for different keys, unique URLs: {len(self._brute_found_data)}{dogfood_str}.", 'header')
            self.brute_status_var.set(f"Done — {self._brute_found_count} keys with OTA, {len(self._brute_found_data)} unique{dogfood_str}.")
        self.brute_start_btn.config(state=tk.NORMAL)
        self.brute_pause_btn.config(state=tk.DISABLED)
        self.brute_continue_btn.config(state=tk.DISABLED)
        self.brute_stop_btn.config(state=tk.DISABLED)
        self.brute_stop_save_btn.config(state=tk.DISABLED)
        self._brute_running = False
        self.brute_speed_var.set("— req/s")

    def _build_urlbrute_tab(self):
        _outer = ttk.Frame(self.urlbrute_frame)
        _outer.pack(fill=tk.BOTH, expand=True)

        _canvas = tk.Canvas(_outer, borderwidth=0, highlightthickness=0)
        _vsb = ttk.Scrollbar(_outer, orient="vertical", command=_canvas.yview)
        _canvas.configure(yscrollcommand=_vsb.set)

        _vsb.pack(side=tk.RIGHT, fill=tk.Y)
        _canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        wrapper = ttk.Frame(_canvas, padding="8")
        _cw = _canvas.create_window((0, 0), window=wrapper, anchor="nw")

        def _on_frame_configure(event):
            _canvas.configure(scrollregion=_canvas.bbox("all"))

        def _on_canvas_configure(event):
            _canvas.itemconfig(_cw, width=event.width)

        wrapper.bind("<Configure>", _on_frame_configure)
        _canvas.bind("<Configure>", _on_canvas_configure)

        def _on_mousewheel(event):
            try:
                _canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
            except tk.TclError:
                pass

        def _bind_mousewheel(widget):
            widget.bind("<MouseWheel>", _on_mousewheel)
            for child in widget.winfo_children():
                _bind_mousewheel(child)

        wrapper.bind("<Map>", lambda e: _bind_mousewheel(wrapper))

        btn_row = ttk.Frame(wrapper)
        btn_row.pack(fill=tk.X, pady=(0, 4))
        self.ub_start_btn = ttk.Button(btn_row, text="▶  Start URL Bruteforce", command=self._ub_start)
        self.ub_pause_btn = ttk.Button(btn_row, text="⏸  Pause", command=self._ub_pause, state=tk.DISABLED)
        self.ub_continue_btn = ttk.Button(btn_row, text="⏩  Continue", command=self._ub_continue, state=tk.DISABLED)
        self.ub_stop_btn = ttk.Button(btn_row, text="⏹  Stop", command=self._ub_stop, state=tk.DISABLED)
        self.ub_log_btn = ttk.Button(btn_row, text="📋  Open Log", command=self._ub_open_log)
        self.ub_export_btn = ttk.Button(btn_row, text="💾  Export Log", command=self._ub_export_log)
        self.ub_clearlog_btn = ttk.Button(btn_row, text="🗑  Clear Log", command=self._ub_clear_log)
        for b in (self.ub_start_btn, self.ub_pause_btn, self.ub_continue_btn,
                  self.ub_stop_btn, self.ub_log_btn, self.ub_export_btn, self.ub_clearlog_btn):
            b.pack(side=tk.LEFT, padx=3)
        self.ub_status_var = tk.StringVar(value="Idle")
        ttk.Label(btn_row, textvariable=self.ub_status_var, foreground='#0066cc').pack(side=tk.LEFT, padx=10)
        ttk.Separator(btn_row, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=6, pady=2)
        ttk.Label(btn_row, text="Speed:", foreground='#555').pack(side=tk.LEFT)
        self.ub_speed_var = tk.StringVar(value="— req/s")
        ttk.Label(btn_row, textvariable=self.ub_speed_var, foreground='#cc6600',
                  font=('Courier', 9, 'bold')).pack(side=tk.LEFT, padx=(4, 0))

        self.ub_progress = ttk.Progressbar(wrapper, mode='determinate')
        self.ub_progress.pack(fill=tk.X, pady=(0, 6))

        url_lf = ttk.LabelFrame(wrapper, text="URL Templates", padding="6")
        url_lf.pack(fill=tk.X, pady=(0, 6))
        ttk.Label(url_lf, text="Use {brut} as placeholder.", foreground='#888').pack(anchor=tk.W)
        self.ub_urls_text = tk.Text(url_lf, height=4, font=('Courier', 9))
        self.ub_urls_text.pack(fill=tk.BOTH, expand=True)
        self.ub_urls_text.insert(tk.END, "https://android.googleapis.com/packages/ota-api/{brut}.zip")

        mid = ttk.Frame(wrapper)
        mid.pack(fill=tk.X, pady=(0, 6))
        mid.columnconfigure(0, weight=3)
        mid.columnconfigure(1, weight=1)

        cs_lf = ttk.LabelFrame(mid, text="Charset", padding="6")
        cs_lf.grid(row=0, column=0, sticky=tk.NSEW, padx=(0, 6))
        self.ub_charset_text = tk.Text(cs_lf, height=3, font=('Courier', 9))
        self.ub_charset_text.pack(fill=tk.BOTH, expand=True)
        self.ub_charset_text.insert(tk.END, "abcdefghijklmnopqrstuvwxyz0123456789")
        pr = ttk.Frame(cs_lf)
        pr.pack(fill=tk.X, pady=(4, 0))
        ttk.Label(pr, text="Presets:").pack(side=tk.LEFT, padx=(0, 4))
        for label, chars in [("a-z", "abcdefghijklmnopqrstuvwxyz"),
                             ("A-Z", "ABCDEFGHIJKLMNOPQRSTUVWXYZ"),
                             ("0-9", "0123456789"),
                             ("a-z+0-9", "abcdefghijklmnopqrstuvwxyz0123456789"),
                             ("HEX", "0123456789abcdef"),
                             ("ALL", "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_")]:
            ttk.Button(pr, text=label,
                       command=lambda c=chars: (self.ub_charset_text.delete("1.0", tk.END),
                                                self.ub_charset_text.insert(tk.END, c))
                       ).pack(side=tk.LEFT, padx=2)

        len_lf = ttk.LabelFrame(mid, text="Length", padding="6")
        len_lf.grid(row=0, column=1, sticky=tk.NSEW)
        self.ub_fixed_var = tk.BooleanVar(value=False)

        def _toggle_len(*_):
            if self.ub_fixed_var.get():
                self._ub_minlen_lbl.config(text="Length:")
                self._ub_maxlen_lbl.grid_remove()
                self._ub_maxlen_spin.grid_remove()
            else:
                self._ub_minlen_lbl.config(text="Min:")
                self._ub_maxlen_lbl.grid()
                self._ub_maxlen_spin.grid()

        ttk.Checkbutton(len_lf, text="Fixed length", variable=self.ub_fixed_var,
                        command=_toggle_len).grid(row=0, column=0, columnspan=2, sticky=tk.W)
        self._ub_minlen_lbl = ttk.Label(len_lf, text="Min:")
        self._ub_minlen_lbl.grid(row=1, column=0, sticky=tk.W, pady=4)
        self.ub_minlen_var = tk.StringVar(value="1")
        ttk.Spinbox(len_lf, from_=1, to=20, textvariable=self.ub_minlen_var, width=5).grid(row=1, column=1, sticky=tk.W)
        self._ub_maxlen_lbl = ttk.Label(len_lf, text="Max:")
        self._ub_maxlen_lbl.grid(row=2, column=0, sticky=tk.W, pady=4)
        self.ub_maxlen_var = tk.StringVar(value="4")
        self._ub_maxlen_spin = ttk.Spinbox(len_lf, from_=1, to=20, textvariable=self.ub_maxlen_var, width=5)
        self._ub_maxlen_spin.grid(row=2, column=1, sticky=tk.W)

        opt_lf = ttk.LabelFrame(wrapper, text="Options", padding="6")
        opt_lf.pack(fill=tk.X, pady=(0, 6))
        ttk.Label(opt_lf, text="Workers:").pack(side=tk.LEFT, padx=(0, 4))
        self.ub_workers_var = tk.StringVar(value="10")
        ttk.Spinbox(opt_lf, from_=1, to=500, textvariable=self.ub_workers_var, width=5).pack(side=tk.LEFT)
        ttk.Label(opt_lf, text="Timeout (s):").pack(side=tk.LEFT, padx=(16, 4))
        self.ub_timeout_var = tk.StringVar(value="10")
        ttk.Entry(opt_lf, textvariable=self.ub_timeout_var, width=5).pack(side=tk.LEFT)
        ttk.Label(opt_lf, text="Fail HTTP codes:").pack(side=tk.LEFT, padx=(16, 4))
        self.ub_codes_var = tk.StringVar(value="404")
        ttk.Entry(opt_lf, textvariable=self.ub_codes_var, width=14).pack(side=tk.LEFT)
        self.ub_stop_on_find_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(opt_lf, text="Pause on first found",
                        variable=self.ub_stop_on_find_var).pack(side=tk.LEFT, padx=(16, 0))
        self._ub_hide_no_ota_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(opt_lf, text="Hide 'not found' in log",
                        variable=self._ub_hide_no_ota_var).pack(side=tk.LEFT, padx=(12, 0))
        self._ub_hide_dupes_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(opt_lf, text="Hide duplicates in log",
                        variable=self._ub_hide_dupes_var).pack(side=tk.LEFT, padx=(12, 0))

        ub_wl_lf = ttk.LabelFrame(wrapper, text="Wordlist Mode  (replaces charset bruteforce when a file is loaded)", padding="6")
        ub_wl_lf.pack(fill=tk.X, pady=(0, 6))
        ub_wl_row = ttk.Frame(ub_wl_lf)
        ub_wl_row.pack(fill=tk.X, pady=(0, 2))
        self.ub_wordlist_enabled_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(ub_wl_row, text="Use wordlist file for {brut}",
                        variable=self.ub_wordlist_enabled_var,
                        command=self._ub_toggle_wordlist).pack(side=tk.LEFT, padx=(0, 8))
        self.ub_wordlist_path_var = tk.StringVar(value="")
        self._ub_wordlist_entry = ttk.Entry(ub_wl_row, textvariable=self.ub_wordlist_path_var,
                                            font=('Courier', 9), width=46, state=tk.DISABLED)
        self._ub_wordlist_entry.pack(side=tk.LEFT, padx=(0, 6))
        self._ub_wordlist_browse_btn = ttk.Button(ub_wl_row, text="📂 Browse…",
                                                  command=self._ub_browse_wordlist, state=tk.DISABLED)
        self._ub_wordlist_browse_btn.pack(side=tk.LEFT, padx=(0, 6))
        self._ub_wordlist_clear_btn = ttk.Button(ub_wl_row, text="✕ Clear",
                                                 command=self._ub_clear_wordlist, state=tk.DISABLED)
        self._ub_wordlist_clear_btn.pack(side=tk.LEFT)
        self.ub_wordlist_info_var = tk.StringVar(value="")
        ttk.Label(ub_wl_lf, textvariable=self.ub_wordlist_info_var, foreground='#888').pack(anchor=tk.W, pady=(2, 0))

        self._ub_wordlist_path = ""
        self._ub_stop_flag = False
        self._ub_pause_event = threading.Event()
        self._ub_pause_event.set()
        self._ub_queue = None
        self._ub_producer_thread = None
        self._ub_worker_threads = []
        self._ub_running = False
        self._ub_found_count = 0
        self._ub_checked_count = 0
        self._ub_total = 0
        self._ub_lock = threading.Lock()
        self._ub_speed_ts = 0.0
        self._ub_speed_count = 0
        self._ub_log_buffer = []
        self._ub_log_lock = threading.Lock()
        self._ub_log_pending = []
        self._ub_log_poll_scheduled = False
        self._ub_log_window = None
        self._ub_log_text = None

    def _ub_log(self, msg, tag='info'):
        with self._ub_log_lock:
            self._ub_log_buffer.append((msg, tag))
            self._ub_log_pending.append((msg, tag))
        if not self._ub_log_poll_scheduled:
            self._ub_log_poll_scheduled = True
            self.root.after(0, self._ub_flush_log)

    def _ub_flush_log(self):
        pending = None
        with self._ub_log_lock:
            if self._ub_log_pending:
                pending = self._ub_log_pending[:]
                self._ub_log_pending.clear()
        if pending and self._ub_log_text and self._ub_log_window and self._ub_log_window.winfo_exists():
            try:
                self._ub_log_text.config(state=tk.NORMAL)
                for msg, tag in pending:
                    self._ub_log_text.insert(tk.END, msg + '\n', tag)
                self._ub_log_text.see(tk.END)
                self._ub_log_text.config(state=tk.DISABLED)
            except Exception:
                pass
        if self._ub_running or pending:
            self._ub_log_poll_scheduled = True
            self.root.after(100, self._ub_flush_log)
        else:
            self._ub_log_poll_scheduled = False

    def _ub_clear_log(self):
        with self._ub_log_lock:
            self._ub_log_buffer.clear()
            self._ub_log_pending.clear()
        if self._ub_log_text and self._ub_log_window and self._ub_log_window.winfo_exists():
            self._ub_log_text.config(state=tk.NORMAL)
            self._ub_log_text.delete(1.0, tk.END)
            self._ub_log_text.config(state=tk.DISABLED)

    def _ub_export_log(self):
        with self._ub_log_lock:
            if not self._ub_log_buffer:
                messagebox.showinfo("Export Log", "Log is empty.")
                return
            content = "\n".join(m for m, _ in self._ub_log_buffer)
        path = filedialog.asksaveasfilename(defaultextension=".txt",
                                            filetypes=[("Text", "*.txt"), ("All", "*.*")])
        if path:
            try:
                with open(path, "w", encoding="utf-8") as f:
                    f.write(content)
                self.ub_status_var.set(f"Saved: {os.path.basename(path)}")
            except Exception as e:
                messagebox.showerror("Export Error", str(e))

    def _ub_open_log(self):
        if self._ub_log_window and self._ub_log_window.winfo_exists():
            self._ub_log_window.lift()
            self._ub_log_window.focus_force()
            return
        win = tk.Toplevel(self.root)
        win.title("URL Bruteforce Log")
        win.geometry("900x600")
        win.protocol("WM_DELETE_WINDOW", self._ub_close_log)
        frame = ttk.Frame(win, padding="10")
        frame.pack(fill=tk.BOTH, expand=True)
        tb = ttk.Frame(frame)
        tb.pack(fill=tk.X, pady=(0, 6))
        ttk.Button(tb, text="🗑 Clear", command=self._ub_clear_log).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="💾 Export", command=self._ub_export_log).pack(side=tk.LEFT, padx=2)
        text = scrolledtext.ScrolledText(frame, wrap=tk.WORD, font=('Courier', 9), bg='white', fg='#333')
        text.pack(fill=tk.BOTH, expand=True)
        text.tag_configure('found', foreground='#006600', font=('Courier', 9, 'bold'))
        text.tag_configure('skip', foreground='#aaaaaa')
        text.tag_configure('error', foreground='#cc0000')
        text.tag_configure('retry', foreground='#cc6600')
        text.tag_configure('header', foreground='#004499', font=('Courier', 9, 'bold'))
        text.tag_configure('info', foreground='#333333')
        text.tag_configure('duplicate', foreground='#b8860b', font=('Courier', 9, 'bold'))
        with self._ub_log_lock:
            buf = list(self._ub_log_buffer)
        for msg, tag in buf:
            text.insert(tk.END, msg + '\n', tag)
        text.see(tk.END)
        text.config(state=tk.DISABLED)
        self._ub_log_window = win
        self._ub_log_text = text

    def _ub_close_log(self):
        if self._ub_log_window:
            self._ub_log_window.destroy()
            self._ub_log_window = None
            self._ub_log_text = None

    def _ub_toggle_wordlist(self):
        enabled = self.ub_wordlist_enabled_var.get()
        state = tk.NORMAL if enabled else tk.DISABLED
        self._ub_wordlist_entry.config(state=state)
        self._ub_wordlist_browse_btn.config(state=state)
        self._ub_wordlist_clear_btn.config(state=state)
        if not enabled:
            self.ub_wordlist_info_var.set("")

    def _ub_browse_wordlist(self):
        path = filedialog.askopenfilename(
            title="Select wordlist file",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")])
        if not path:
            return
        self.ub_wordlist_path_var.set(path)
        self._ub_wordlist_path = path
        try:
            count = 0
            leftover = ""
            with open(path, "r", encoding="utf-8", errors="replace") as fh:
                while True:
                    chunk = fh.read(65536)
                    if not chunk:
                        if leftover.strip():
                            count += 1
                        break
                    lines = (leftover + chunk).split("\n")
                    leftover = lines[-1]
                    for line in lines[:-1]:
                        if line.strip():
                            count += 1
            self.ub_wordlist_info_var.set(f"{count} words  ({os.path.basename(path)})")
        except Exception as e:
            self.ub_wordlist_info_var.set(f"Could not read file: {e}")

    def _ub_clear_wordlist(self):
        self.ub_wordlist_path_var.set("")
        self._ub_wordlist_path = ""
        self.ub_wordlist_info_var.set("")

    def _ub_wordlist_iter(self, path):
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as fh:
                leftover = ""
                while True:
                    chunk = fh.read(65536)
                    if not chunk:
                        if leftover.strip():
                            yield leftover.strip()
                        break
                    lines = (leftover + chunk).split("\n")
                    leftover = lines[-1]
                    for line in lines[:-1]:
                        line = line.strip()
                        if line:
                            yield line
        except Exception:
            return

    def _ub_pause(self):
        if not self._ub_running:
            return
        self._ub_pause_event.clear()
        self.ub_pause_btn.config(state=tk.DISABLED)
        self.ub_continue_btn.config(state=tk.NORMAL)
        self.ub_status_var.set("⏸ Paused — press Continue to resume")

    def _ub_continue(self):
        if not self._ub_running:
            return
        self._ub_pause_event.set()
        self.ub_pause_btn.config(state=tk.NORMAL)
        self.ub_continue_btn.config(state=tk.DISABLED)
        self.ub_status_var.set("▶ Running…")

    def _ub_stop(self):
        if not self._ub_running:
            return
        self._ub_stop_flag = True
        self._ub_pause_event.set()
        self.ub_stop_btn.config(state=tk.DISABLED)
        self.ub_status_var.set("Stopping…")

    def _ub_finish(self, stop=False):
        self._ub_running = False
        self.ub_speed_var.set("— req/s")
        self.ub_start_btn.config(state=tk.NORMAL)
        self.ub_pause_btn.config(state=tk.DISABLED)
        self.ub_continue_btn.config(state=tk.DISABLED)
        self.ub_stop_btn.config(state=tk.DISABLED)
        try:
            self.ub_progress.stop()
            self.ub_progress.config(mode='determinate')
            self.ub_progress['value'] = 0
        except Exception:
            pass
        self._ub_log("=" * 70, 'header')
        if stop:
            self._ub_log("URL Bruteforce stopped by user.", 'header')
            self.ub_status_var.set("Stopped by user.")
        else:
            self._ub_log(f"URL Bruteforce finished. Found {self._ub_found_count}, checked {self._ub_checked_count}.", 'header')
            self.ub_status_var.set(f"Done — found {self._ub_found_count}, checked {self._ub_checked_count}.")

    def _ub_monitor(self):
        if self._ub_stop_flag:
            self._ub_finish(stop=True)
            return
        if self._ub_producer_thread and self._ub_producer_thread.is_alive():
            self.root.after(500, self._ub_monitor)
            return
        if any(t.is_alive() for t in self._ub_worker_threads):
            self.root.after(500, self._ub_monitor)
            return
        self._ub_finish(stop=False)

    def _ub_increment_progress(self):
        with self._ub_lock:
            self._ub_checked_count += 1
            self._ub_speed_count += 1
            checked = self._ub_checked_count
            total = self._ub_total
            found = self._ub_found_count
        self.root.after(0, lambda c=checked, t=total, f=found: self._ub_update_progress_ui(c, t, f))

    def _ub_update_progress_ui(self, checked, total, found):
        try:
            self.ub_progress['value'] = checked
            if total:
                self.ub_status_var.set(f"[{checked}/{total}]  found={found}")
            else:
                self.ub_status_var.set(f"[{checked}]  found={found}")
        except Exception:
            pass

    def _ub_update_speed(self):
        if not self._ub_running:
            self.ub_speed_var.set("— req/s")
            return
        now = time.monotonic()
        with self._ub_lock:
            elapsed = now - self._ub_speed_ts
            count = self._ub_speed_count
            self._ub_speed_count = 0
            self._ub_speed_ts = now
        if elapsed > 0:
            speed = count / elapsed
            self.ub_speed_var.set(
                f"{speed/1000:.1f}k req/s" if speed >= 1000 else f"{speed:.1f} req/s"
            )
        self.root.after(1000, self._ub_update_speed)

    def _ub_start(self):
        if self._ub_running:
            self._ub_stop()
            return

        templates = [l.strip() for l in self.ub_urls_text.get("1.0", tk.END).splitlines() if l.strip()]
        if not templates:
            messagebox.showerror("URL Bruteforce", "Enter at least one URL template.")
            return
        for t in templates:
            if '{brut}' not in t:
                messagebox.showerror("URL Bruteforce", f"Template missing {{brut}}:\n{t}")
                return

        use_wordlist = self.ub_wordlist_enabled_var.get()
        wordlist_path = self.ub_wordlist_path_var.get().strip() if use_wordlist else ""

        if use_wordlist and not wordlist_path:
            messagebox.showerror("URL Bruteforce", "Wordlist mode enabled but no file selected.")
            return

        charset = list(dict.fromkeys(self.ub_charset_text.get("1.0", tk.END).strip()))
        if not use_wordlist and not charset:
            messagebox.showerror("URL Bruteforce", "Charset is empty.")
            return

        try:
            min_len = max(1, int(self.ub_minlen_var.get()))
        except ValueError:
            messagebox.showerror("URL Bruteforce", "Invalid length value.")
            return

        fixed = self.ub_fixed_var.get()
        if fixed:
            max_len = min_len
        else:
            try:
                max_len = max(min_len, int(self.ub_maxlen_var.get()))
            except ValueError:
                max_len = min_len

        try:
            n_workers = max(1, int(self.ub_workers_var.get()))
        except ValueError:
            n_workers = 10
        try:
            timeout = max(1, int(self.ub_timeout_var.get()))
        except ValueError:
            timeout = 10
        try:
            fail_codes = {int(c.strip()) for c in self.ub_codes_var.get().split(',') if c.strip()}
        except ValueError:
            fail_codes = {404}
        stop_on_find = self.ub_stop_on_find_var.get()
        hide_no_ota = self._ub_hide_no_ota_var.get()
        hide_dupes = self._ub_hide_dupes_var.get()

        if use_wordlist:
            total = 0
        elif fixed:
            total = len(charset) ** min_len
        else:
            total = sum(len(charset) ** l for l in range(min_len, max_len + 1))
        total *= len(templates)

        self._ub_stop_flag = False
        self._ub_pause_event.set()
        self._ub_found_count = 0
        self._ub_checked_count = 0
        self._ub_total = total
        self._ub_running = True
        self._ub_found_urls = set()
        self._ub_queue = queue.Queue()
        self._ub_speed_ts = time.monotonic()
        self._ub_speed_count = 0
        self.ub_speed_var.set("0 req/s")

        if use_wordlist:
            self.ub_progress.config(mode='indeterminate')
            self.ub_progress.start(50)
        else:
            self.ub_progress.config(mode='determinate')
            self.ub_progress['maximum'] = max(1, total)
            self.ub_progress['value'] = 0
        self.ub_start_btn.config(state=tk.DISABLED)
        self.ub_pause_btn.config(state=tk.NORMAL)
        self.ub_stop_btn.config(state=tk.NORMAL)
        self.ub_continue_btn.config(state=tk.DISABLED)
        self.ub_status_var.set("▶ Running…")

        self._ub_log("=" * 70, 'header')
        if use_wordlist:
            self._ub_log(f"URL Bruteforce start | mode: WORDLIST | file: {os.path.basename(wordlist_path)} | "
                         f"templates: {len(templates)} | workers: {n_workers}", 'header')
        else:
            self._ub_log(f"URL Bruteforce start | templates: {len(templates)} | charset: {len(charset)} chars | "
                         f"length: {'%d (fixed)' % min_len if fixed else '%d-%d' % (min_len, max_len)} | "
                         f"total≈{total} | workers: {n_workers}", 'header')
        for t in templates:
            self._ub_log(f"  {t}", 'info')
        self._ub_log("-" * 70, 'header')

        if use_wordlist:
            self._ub_producer_thread = threading.Thread(
                target=self._ub_producer_wordlist,
                args=(wordlist_path, templates, n_workers),
                daemon=True)
        else:
            self._ub_producer_thread = threading.Thread(
                target=self._ub_producer,
                args=(charset, min_len, max_len, fixed, templates, n_workers),
                daemon=True)
        self._ub_producer_thread.start()

        self._ub_worker_threads = []
        for _ in range(n_workers):
            t = threading.Thread(target=self._ub_worker,
                                 args=(timeout, fail_codes, stop_on_find, hide_no_ota, hide_dupes),
                                 daemon=True)
            t.start()
            self._ub_worker_threads.append(t)

        self.root.after(500, self._ub_monitor)
        self.root.after(1000, self._ub_update_speed)

    def _ub_producer(self, charset, min_len, max_len, fixed, templates, n_workers):
        lengths = [min_len] if fixed else range(min_len, max_len + 1)
        try:
            for length in lengths:
                for combo in _itertools.product(charset, repeat=length):
                    word = ''.join(combo)
                    if self._ub_stop_flag:
                        break
                    self._ub_pause_event.wait()
                    if self._ub_stop_flag:
                        break
                    for tmpl in templates:
                        self._ub_queue.put((word, tmpl.replace('{brut}', word)))
                if self._ub_stop_flag:
                    break
        finally:
            for _ in range(n_workers):
                self._ub_queue.put(None)

    def _ub_producer_wordlist(self, wordlist_path, templates, n_workers):
        try:
            for word in self._ub_wordlist_iter(wordlist_path):
                if self._ub_stop_flag:
                    break
                self._ub_pause_event.wait()
                if self._ub_stop_flag:
                    break
                for tmpl in templates:
                    self._ub_queue.put((word, tmpl.replace('{brut}', word)))
        finally:
            for _ in range(n_workers):
                self._ub_queue.put(None)

    def _ub_worker(self, timeout, fail_codes, stop_on_find, hide_no_ota=False, hide_dupes=False):
        _NET_ERRS = ("timed out", "connection reset", "connection refused",
                     "remote end closed", "urlopen error", "_ssl.c", "handshake")
        ctx = ssl.create_default_context()
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE

        while True:
            self._ub_pause_event.wait()
            if self._ub_stop_flag:
                try:
                    while True:
                        self._ub_queue.get_nowait()
                except queue.Empty:
                    pass
                break

            try:
                item = self._ub_queue.get(timeout=0.05)
            except queue.Empty:
                continue
            if item is None:
                break

            self._ub_pause_event.wait()
            if self._ub_stop_flag:
                try:
                    while True:
                        self._ub_queue.get_nowait()
                except queue.Empty:
                    pass
                break

            word, url = item
            status = None
            last_err = None

            while True:
                if self._ub_stop_flag:
                    break
                self._ub_pause_event.wait()
                if self._ub_stop_flag:
                    break
                try:
                    req = urllib.request.Request(url, method="HEAD")
                    with urllib.request.urlopen(req, timeout=timeout, context=ctx) as r:
                        status = r.getcode()
                    last_err = None
                    break
                except urllib.error.HTTPError as e:
                    status = e.code
                    last_err = None
                    break
                except Exception as e:
                    err_s = str(e).lower()
                    if any(ne in err_s for ne in _NET_ERRS):
                        last_err = str(e)
                        self._ub_log(f"  ↻ retry: {url} — {e}", 'retry')
                        continue
                    last_err = str(e)
                    break

            if last_err:
                if not hide_no_ota:
                    self._ub_log(f"✗ ERR    {url}  — {last_err}", 'error')
            elif status in fail_codes:
                if not hide_no_ota:
                    self._ub_log(f"  [{status}]  {url}", 'skip')
            else:
                with self._ub_lock:
                    self._ub_found_count += 1
                    is_dup = url in self._ub_found_urls
                    if not is_dup:
                        self._ub_found_urls.add(url)
                if is_dup:
                    if not hide_dupes:
                        self._ub_log(f"  DUP [{status}]  {url}", 'duplicate')
                else:
                    self._ub_log(f"✓ FOUND [{status}]  {url}", 'found')
                if stop_on_find and not is_dup:
                    self._ub_pause_event.clear()
                    self.root.after(0, self._ub_pause_on_find)

            self._ub_increment_progress()

    def _ub_pause_on_find(self):
        if not self._ub_running:
            return
        self.ub_pause_btn.config(state=tk.DISABLED)
        self.ub_continue_btn.config(state=tk.NORMAL)
        self.ub_status_var.set("⏸ Paused on find — press Continue to resume")

    def _build_devbrute_tab(self):
        _outer = ttk.Frame(self.devbrute_frame)
        _outer.pack(fill=tk.BOTH, expand=True)
        _canvas = tk.Canvas(_outer, borderwidth=0, highlightthickness=0)
        _vsb = ttk.Scrollbar(_outer, orient="vertical", command=_canvas.yview)
        _canvas.configure(yscrollcommand=_vsb.set)
        _vsb.pack(side=tk.RIGHT, fill=tk.Y)
        _canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        wrapper = ttk.Frame(_canvas, padding="8")
        _cw = _canvas.create_window((0, 0), window=wrapper, anchor="nw")
        wrapper.bind("<Configure>", lambda e: _canvas.configure(scrollregion=_canvas.bbox("all")))
        _canvas.bind("<Configure>", lambda e: _canvas.itemconfig(_cw, width=e.width))

        def _mw(e):
            try:
                _canvas.yview_scroll(int(-1 * (e.delta / 120)), "units")
            except tk.TclError:
                pass

        def _bind_mw(w):
            w.bind("<MouseWheel>", _mw)
            for c in w.winfo_children():
                _bind_mw(c)
        wrapper.bind("<Map>", lambda e: _bind_mw(wrapper))

        btn_row = ttk.Frame(wrapper)
        btn_row.pack(fill=tk.X, pady=(0, 4))
        self.db_start_btn = ttk.Button(btn_row, text="▶  Start Device Bruteforce", command=self._db_start)
        self.db_pause_btn = ttk.Button(btn_row, text="⏸  Pause", command=self._db_pause, state=tk.DISABLED)
        self.db_continue_btn = ttk.Button(btn_row, text="⏩  Continue", command=self._db_continue, state=tk.DISABLED)
        self.db_stop_btn = ttk.Button(btn_row, text="⏹  Stop", command=self._db_stop, state=tk.DISABLED)
        self.db_log_btn = ttk.Button(btn_row, text="📋  Open Log", command=self._db_open_log)
        self.db_export_btn = ttk.Button(btn_row, text="💾  Export Log", command=self._db_export_log)
        self.db_clearlog_btn = ttk.Button(btn_row, text="🗑  Clear Log", command=self._db_clear_log)
        for b in (self.db_start_btn, self.db_pause_btn, self.db_continue_btn,
                  self.db_stop_btn, self.db_log_btn, self.db_export_btn, self.db_clearlog_btn):
            b.pack(side=tk.LEFT, padx=3)
        self.db_status_var = tk.StringVar(value="Idle")
        ttk.Label(btn_row, textvariable=self.db_status_var, foreground='#0066cc').pack(side=tk.LEFT, padx=10)
        ttk.Separator(btn_row, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=6, pady=2)
        ttk.Label(btn_row, text="Speed:", foreground='#555').pack(side=tk.LEFT)
        self.db_speed_var = tk.StringVar(value="— req/s")
        ttk.Label(btn_row, textvariable=self.db_speed_var, foreground='#cc6600',
                  font=('Courier', 9, 'bold')).pack(side=tk.LEFT, padx=(4, 0))

        self.db_progress = ttk.Progressbar(wrapper, mode='determinate')
        self.db_progress.pack(fill=tk.X, pady=(0, 6))

        tmpl_lf = ttk.LabelFrame(wrapper,
                                 text="Fingerprint Template",
                                 padding="6")
        tmpl_lf.pack(fill=tk.X, pady=(0, 6))
        ttk.Label(tmpl_lf,
                  text="Use {device} as the name placeholder, and {key} as the keys placeholder.",
                  foreground='#888').pack(anchor=tk.W)
        self.db_template_var = tk.StringVar(
            value="google/{device}/{device}:5.1/LYZ28E/1858530:{key}")
        ttk.Entry(tmpl_lf, textvariable=self.db_template_var,
                  font=('Courier', 10), width=80).pack(fill=tk.X, pady=(4, 0))

        keys_lf = ttk.LabelFrame(wrapper,
                                 text="Keys",
                                 padding="6")
        keys_lf.pack(fill=tk.X, pady=(0, 6))
        self.db_keys_text = tk.Text(keys_lf, height=4, font=('Courier', 9))
        self.db_keys_text.pack(fill=tk.BOTH, expand=True)
        self.db_keys_text.insert(tk.END, "user/release-keys\nuserdebug/test-keys\nuserdebug/dev-keys")

        mid = ttk.Frame(wrapper)
        mid.pack(fill=tk.X, pady=(0, 6))
        mid.columnconfigure(0, weight=3)
        mid.columnconfigure(1, weight=1)

        cs_lf = ttk.LabelFrame(mid, text="Device Name Charset", padding="6")
        cs_lf.grid(row=0, column=0, sticky=tk.NSEW, padx=(0, 6))
        self.db_charset_text = tk.Text(cs_lf, height=3, font=('Courier', 9))
        self.db_charset_text.pack(fill=tk.BOTH, expand=True)
        self.db_charset_text.insert(tk.END, "abcdefghijklmnopqrstuvwxyz0123456789")
        pr = ttk.Frame(cs_lf)
        pr.pack(fill=tk.X, pady=(4, 0))
        ttk.Label(pr, text="Presets:").pack(side=tk.LEFT, padx=(0, 4))
        for label, chars in [
            ("a-z", "abcdefghijklmnopqrstuvwxyz"),
            ("A-Z", "ABCDEFGHIJKLMNOPQRSTUVWXYZ"),
            ("0-9", "0123456789"),
            ("a-z+0-9", "abcdefghijklmnopqrstuvwxyz0123456789"),
            ("HEX", "0123456789abcdef"),
            ("ALL", "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_"),
        ]:
            ttk.Button(pr, text=label,
                       command=lambda c=chars: (self.db_charset_text.delete("1.0", tk.END),
                                                self.db_charset_text.insert(tk.END, c))
                       ).pack(side=tk.LEFT, padx=2)

        len_lf = ttk.LabelFrame(mid, text="Device Name Length", padding="6")
        len_lf.grid(row=0, column=1, sticky=tk.NSEW)
        self.db_fixed_var = tk.BooleanVar(value=False)

        def _toggle_len(*_):
            if self.db_fixed_var.get():
                self._db_minlen_lbl.config(text="Length:")
                self._db_maxlen_lbl.grid_remove()
                self._db_maxlen_spin.grid_remove()
            else:
                self._db_minlen_lbl.config(text="Min:")
                self._db_maxlen_lbl.grid()
                self._db_maxlen_spin.grid()

        ttk.Checkbutton(len_lf, text="Fixed length", variable=self.db_fixed_var,
                        command=_toggle_len).grid(row=0, column=0, columnspan=2, sticky=tk.W)
        self._db_minlen_lbl = ttk.Label(len_lf, text="Min:")
        self._db_minlen_lbl.grid(row=1, column=0, sticky=tk.W, pady=4)
        self.db_minlen_var = tk.StringVar(value="3")
        ttk.Spinbox(len_lf, from_=1, to=30, textvariable=self.db_minlen_var, width=5).grid(row=1, column=1, sticky=tk.W)
        self._db_maxlen_lbl = ttk.Label(len_lf, text="Max:")
        self._db_maxlen_lbl.grid(row=2, column=0, sticky=tk.W, pady=4)
        self.db_maxlen_var = tk.StringVar(value="6")
        self._db_maxlen_spin = ttk.Spinbox(len_lf, from_=1, to=30, textvariable=self.db_maxlen_var, width=5)
        self._db_maxlen_spin.grid(row=2, column=1, sticky=tk.W)

        wl_lf = ttk.LabelFrame(wrapper, text="Wordlist Mode  (replaces charset bruteforce when a file is loaded)", padding="6")
        wl_lf.pack(fill=tk.X, pady=(0, 6))
        wl_row = ttk.Frame(wl_lf)
        wl_row.pack(fill=tk.X, pady=(0, 2))
        self.db_wordlist_enabled_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(wl_row, text="Use wordlist file for {device}",
                        variable=self.db_wordlist_enabled_var,
                        command=self._db_toggle_wordlist).pack(side=tk.LEFT, padx=(0, 8))
        self.db_wordlist_path_var = tk.StringVar(value="")
        self._db_wordlist_entry = ttk.Entry(wl_row, textvariable=self.db_wordlist_path_var,
                                            font=('Courier', 9), width=46, state=tk.DISABLED)
        self._db_wordlist_entry.pack(side=tk.LEFT, padx=(0, 6))
        self._db_wordlist_browse_btn = ttk.Button(wl_row, text="📂 Browse…",
                                                  command=self._db_browse_wordlist, state=tk.DISABLED)
        self._db_wordlist_browse_btn.pack(side=tk.LEFT, padx=(0, 6))
        self._db_wordlist_clear_btn = ttk.Button(wl_row, text="✕ Clear",
                                                 command=self._db_clear_wordlist, state=tk.DISABLED)
        self._db_wordlist_clear_btn.pack(side=tk.LEFT)
        self.db_wordlist_info_var = tk.StringVar(value="")
        ttk.Label(wl_lf, textvariable=self.db_wordlist_info_var, foreground='#888').pack(anchor=tk.W, pady=(2, 0))

        opt_lf = ttk.LabelFrame(wrapper, text="Options", padding="6")
        opt_lf.pack(fill=tk.X, pady=(0, 6))
        ttk.Label(opt_lf, text="Workers:").pack(side=tk.LEFT, padx=(0, 4))
        self.db_workers_var = tk.StringVar(value="10")
        ttk.Spinbox(opt_lf, from_=1, to=500, textvariable=self.db_workers_var, width=5).pack(side=tk.LEFT)
        ttk.Label(opt_lf, text="Locale:").pack(side=tk.LEFT, padx=(16, 4))
        self.db_locale_var = tk.StringVar(value="en-US")
        ttk.Entry(opt_lf, textvariable=self.db_locale_var, width=10).pack(side=tk.LEFT)
        self.db_stop_on_find_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(opt_lf, text="Pause on first found",
                        variable=self.db_stop_on_find_var).pack(side=tk.LEFT, padx=(16, 0))
        self._db_hide_no_ota_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(opt_lf, text="Hide 'no OTA' in log",
                        variable=self._db_hide_no_ota_var).pack(side=tk.LEFT, padx=(12, 0))
        self._db_hide_dupes_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(opt_lf, text="Hide duplicates in log",
                        variable=self._db_hide_dupes_var).pack(side=tk.LEFT, padx=(12, 0))

        sn_lf = ttk.LabelFrame(wrapper, text="Device Identifiers (optional)", padding="6")
        sn_lf.pack(fill=tk.X, pady=(0, 6))
        sn_row = ttk.Frame(sn_lf)
        sn_row.pack(fill=tk.X)
        ttk.Label(sn_row, text="Serial Number (S/N):").pack(side=tk.LEFT, padx=(0, 4))
        self.db_sn_var = tk.StringVar(value="")
        ttk.Entry(sn_row, textvariable=self.db_sn_var, width=24, font=('Courier', 10)).pack(side=tk.LEFT)
        ttk.Label(sn_row, text="IMEI:").pack(side=tk.LEFT, padx=(16, 4))
        self.db_imei_var = tk.StringVar(value="")
        ttk.Entry(sn_row, textvariable=self.db_imei_var, width=20, font=('Courier', 10)).pack(side=tk.LEFT)
        ttk.Label(sn_lf, text="Leave blank to send without these fields.",
                  foreground='#888').pack(anchor=tk.W, pady=(4, 0))

    def _db_toggle_wordlist(self):
        enabled = self.db_wordlist_enabled_var.get()
        state = tk.NORMAL if enabled else tk.DISABLED
        self._db_wordlist_entry.config(state=state)
        self._db_wordlist_browse_btn.config(state=state)
        self._db_wordlist_clear_btn.config(state=state)
        if not enabled:
            self.db_wordlist_info_var.set("")

    def _db_browse_wordlist(self):
        path = filedialog.askopenfilename(
            title="Select wordlist file",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")])
        if not path:
            return
        self.db_wordlist_path_var.set(path)
        self._devbrute_wordlist_path = path
        try:
            count = 0
            with open(path, "r", encoding="utf-8", errors="replace") as fh:
                while True:
                    chunk = fh.read(65536)
                    if not chunk:
                        break
                    count += chunk.count("\n")
            self.db_wordlist_info_var.set(f"≈{count} words  ({os.path.basename(path)})")
        except Exception as e:
            self.db_wordlist_info_var.set(f"Could not read file: {e}")

    def _db_clear_wordlist(self):
        self.db_wordlist_path_var.set("")
        self._devbrute_wordlist_path = ""
        self.db_wordlist_info_var.set("")

    def _db_wordlist_iter(self, path):
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as fh:
                leftover = ""
                while True:
                    chunk = fh.read(65536)
                    if not chunk:
                        if leftover.strip():
                            yield leftover.strip()
                        break
                    lines = (leftover + chunk).split("\n")
                    leftover = lines[-1]
                    for line in lines[:-1]:
                        word = line.strip()
                        if word:
                            yield word
        except Exception:
            return

    def _db_log(self, msg, tag='info'):
        with self._devbrute_log_lock:
            self._devbrute_log_buffer.append((msg, tag))
            self._devbrute_log_pending.append((msg, tag))
        if not self._devbrute_log_poll_scheduled:
            self._devbrute_log_poll_scheduled = True
            self.root.after(0, self._db_flush_log)

    def _db_flush_log(self):
        pending = None
        with self._devbrute_log_lock:
            if self._devbrute_log_pending:
                pending = self._devbrute_log_pending[:]
                self._devbrute_log_pending.clear()
        if pending and self._devbrute_log_text and self._devbrute_log_window and self._devbrute_log_window.winfo_exists():
            try:
                self._devbrute_log_text.config(state=tk.NORMAL)
                for msg, tag in pending:
                    self._devbrute_log_text.insert(tk.END, msg + '\n', tag)
                self._devbrute_log_text.see(tk.END)
                self._devbrute_log_text.config(state=tk.DISABLED)
            except Exception:
                pass
        if self._devbrute_running or pending:
            self._devbrute_log_poll_scheduled = True
            self.root.after(100, self._db_flush_log)
        else:
            self._devbrute_log_poll_scheduled = False

    def _db_clear_log(self):
        with self._devbrute_log_lock:
            self._devbrute_log_buffer.clear()
            self._devbrute_log_pending.clear()
        if self._devbrute_log_text and self._devbrute_log_window and self._devbrute_log_window.winfo_exists():
            self._devbrute_log_text.config(state=tk.NORMAL)
            self._devbrute_log_text.delete(1.0, tk.END)
            self._devbrute_log_text.config(state=tk.DISABLED)

    def _db_export_log(self):
        with self._devbrute_log_lock:
            if not self._devbrute_log_buffer:
                messagebox.showinfo("Export Log", "Log is empty.")
                return
            content = "\n".join(m for m, _ in self._devbrute_log_buffer)
        path = filedialog.asksaveasfilename(defaultextension=".txt",
                                            filetypes=[("Text", "*.txt"), ("All", "*.*")])
        if path:
            try:
                with open(path, "w", encoding="utf-8") as f:
                    f.write(content)
                self.db_status_var.set(f"Saved: {os.path.basename(path)}")
            except Exception as e:
                messagebox.showerror("Export Error", str(e))

    def _db_open_log(self):
        if self._devbrute_log_window and self._devbrute_log_window.winfo_exists():
            self._devbrute_log_window.lift()
            self._devbrute_log_window.focus_force()
            return
        win = tk.Toplevel(self.root)
        win.title("Device Bruteforce Log")
        win.geometry("900x600")
        win.protocol("WM_DELETE_WINDOW", self._db_close_log)
        frame = ttk.Frame(win, padding="10")
        frame.pack(fill=tk.BOTH, expand=True)
        tb = ttk.Frame(frame)
        tb.pack(fill=tk.X, pady=(0, 6))
        ttk.Button(tb, text="🗑 Clear", command=self._db_clear_log).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="💾 Export", command=self._db_export_log).pack(side=tk.LEFT, padx=2)
        text = scrolledtext.ScrolledText(frame, wrap=tk.WORD, font=('Courier', 9), bg='white', fg='#333')
        text.pack(fill=tk.BOTH, expand=True)
        text.tag_configure('found', foreground='#006600', font=('Courier', 9, 'bold'))
        text.tag_configure('skip', foreground='#aaaaaa')
        text.tag_configure('error', foreground='#cc0000')
        text.tag_configure('retry', foreground='#cc6600')
        text.tag_configure('header', foreground='#004499', font=('Courier', 9, 'bold'))
        text.tag_configure('info', foreground='#333333')
        text.tag_configure('duplicate', foreground='#b8860b', font=('Courier', 9, 'bold'))
        with self._devbrute_log_lock:
            buf = list(self._devbrute_log_buffer)
        for msg, tag in buf:
            text.insert(tk.END, msg + '\n', tag)
        text.see(tk.END)
        text.config(state=tk.DISABLED)
        self._devbrute_log_window = win
        self._devbrute_log_text = text

    def _db_close_log(self):
        if self._devbrute_log_window:
            self._devbrute_log_window.destroy()
            self._devbrute_log_window = None
            self._devbrute_log_text = None

    def _db_pause(self):
        if not self._devbrute_running:
            return
        self._devbrute_pause_event.clear()
        self.db_pause_btn.config(state=tk.DISABLED)
        self.db_continue_btn.config(state=tk.NORMAL)
        self.db_status_var.set("⏸ Paused — press Continue to resume")

    def _db_continue(self):
        if not self._devbrute_running:
            return
        self._devbrute_pause_event.set()
        self.db_pause_btn.config(state=tk.NORMAL)
        self.db_continue_btn.config(state=tk.DISABLED)
        self.db_status_var.set("▶ Running…")

    def _db_visual_pause(self):
        if not self._devbrute_running:
            return
        self.db_pause_btn.config(state=tk.DISABLED)
        self.db_continue_btn.config(state=tk.NORMAL)
        self.db_status_var.set("⏸ Paused — found result, press Continue")

    def _db_stop(self):
        if not self._devbrute_running:
            return
        self._devbrute_stop_flag = True
        self._devbrute_pause_event.set()
        self.db_stop_btn.config(state=tk.DISABLED)
        self.db_status_var.set("Stopping…")

    def _db_finish(self, stop=False):
        self._devbrute_running = False
        self.db_speed_var.set("— req/s")
        self.db_start_btn.config(state=tk.NORMAL)
        self.db_pause_btn.config(state=tk.DISABLED)
        self.db_continue_btn.config(state=tk.DISABLED)
        self.db_stop_btn.config(state=tk.DISABLED)
        self._db_log("=" * 70, 'header')
        if stop:
            self._db_log("Device Bruteforce stopped by user.", 'header')
            self.db_status_var.set("Stopped by user.")
        else:
            self._db_log(
                f"Device Bruteforce finished. Found {self._devbrute_found_count}, "
                f"checked {self._devbrute_checked_count}.", 'header')
            self.db_status_var.set(
                f"Done — found {self._devbrute_found_count}, checked {self._devbrute_checked_count}.")

    def _db_monitor(self):
        if self._devbrute_stop_flag:
            self._db_finish(stop=True)
            return
        if self._devbrute_producer_thread and self._devbrute_producer_thread.is_alive():
            self.root.after(500, self._db_monitor)
            return
        if any(t.is_alive() for t in self._devbrute_worker_threads):
            self.root.after(500, self._db_monitor)
            return
        self._db_finish(stop=False)

    def _db_increment_progress(self):
        with self._devbrute_lock:
            self._devbrute_checked_count += 1
            self._devbrute_speed_count += 1
            checked = self._devbrute_checked_count
            total = self._devbrute_total
            found = self._devbrute_found_count
        self.root.after(0, lambda c=checked, t=total, f=found: self._db_update_progress_ui(c, t, f))

    def _db_update_progress_ui(self, checked, total, found):
        try:
            self.db_progress['value'] = checked
            if total > 0:
                self.db_status_var.set(f"[{checked}/{total}]  found={found}")
            else:
                self.db_status_var.set(f"[{checked}/?]  found={found}")
        except Exception:
            pass

    def _db_update_speed(self):
        if not self._devbrute_running:
            self.db_speed_var.set("— req/s")
            return
        now = time.monotonic()
        with self._devbrute_lock:
            elapsed = now - self._devbrute_speed_ts
            count = self._devbrute_speed_count
            self._devbrute_speed_count = 0
            self._devbrute_speed_ts = now
        if elapsed > 0:
            speed = count / elapsed
            if speed >= 1000:
                self.db_speed_var.set(f"{speed/1000:.1f}k req/s")
            else:
                self.db_speed_var.set(f"{speed:.1f} req/s")
        self.root.after(1000, self._db_update_speed)

    def _db_start(self):
        if self._devbrute_running:
            self._db_stop()
            return

        template = self.db_template_var.get().strip()
        if not template:
            messagebox.showerror("Device Bruteforce", "Enter a fingerprint template.")
            return

        use_wordlist = self.db_wordlist_enabled_var.get()
        wordlist_path = self.db_wordlist_path_var.get().strip() if use_wordlist else ""

        if use_wordlist and not wordlist_path:
            messagebox.showerror("Device Bruteforce", "Wordlist mode is enabled but no file is selected.")
            return

        charset = list(dict.fromkeys(self.db_charset_text.get("1.0", tk.END).strip()))
        if not use_wordlist and not charset:
            messagebox.showerror("Device Bruteforce", "Charset is empty.")
            return

        try:
            min_len = max(1, int(self.db_minlen_var.get()))
        except ValueError:
            messagebox.showerror("Device Bruteforce", "Invalid length value.")
            return

        fixed = self.db_fixed_var.get()
        if fixed:
            max_len = min_len
        else:
            try:
                max_len = max(min_len, int(self.db_maxlen_var.get()))
            except ValueError:
                max_len = min_len

        raw_keys = self.db_keys_text.get("1.0", tk.END).strip()
        key_list = [k.strip() for k in raw_keys.splitlines() if k.strip()]
        if not key_list:
            key_list = [""]

        prefix = ""
        suffix = ""
        locale = self.db_locale_var.get().strip() or "en-US"
        stop_on_find = self.db_stop_on_find_var.get()
        device_sn = self.db_sn_var.get().strip()
        imei = self.db_imei_var.get().strip()

        try:
            n_workers = max(1, int(self.db_workers_var.get()))
        except ValueError:
            n_workers = 10

        if use_wordlist:
            total = 0
        elif fixed:
            total = (len(charset) ** min_len) * len(key_list)
        else:
            total = sum(len(charset) ** l for l in range(min_len, max_len + 1)) * len(key_list)

        self._devbrute_stop_flag = False
        self._devbrute_pause_event.set()
        self._devbrute_found_count = 0
        self._devbrute_checked_count = 0
        self._devbrute_total = total
        self._devbrute_running = True
        self._devbrute_queue = queue.Queue(maxsize=10000)

        self._devbrute_speed = 0.0
        self._devbrute_speed_ts = time.monotonic()
        self._devbrute_speed_count = 0
        self.db_speed_var.set("0 req/s")

        self.db_progress['maximum'] = max(1, total) if total else 1
        self.db_progress['value'] = 0
        self.db_start_btn.config(state=tk.DISABLED)
        self.db_pause_btn.config(state=tk.NORMAL)
        self.db_stop_btn.config(state=tk.NORMAL)
        self.db_continue_btn.config(state=tk.DISABLED)
        self.db_status_var.set("▶ Running…")

        self._db_log("=" * 70, 'header')
        if use_wordlist:
            self._db_log(
                f"Device Bruteforce start | mode: WORDLIST | file: {os.path.basename(wordlist_path)} | "
                f"keys: {len(key_list)} | workers: {n_workers}", 'header')
        else:
            self._db_log(
                f"Device Bruteforce start | charset: {len(charset)} chars | "
                f"length: {'%d (fixed)' % min_len if fixed else '%d-%d' % (min_len, max_len)} | "
                f"keys: {len(key_list)} | total≈{total} | workers: {n_workers}", 'header')
        self._db_log(f"Template: {template}", 'header')
        if device_sn or imei:
            self._db_log(f"S/N: '{device_sn}'  IMEI: '{imei}'", 'header')
        self._db_log("-" * 70, 'header')

        if use_wordlist:
            self._devbrute_producer_thread = threading.Thread(
                target=self._db_producer_wordlist,
                args=(wordlist_path, key_list, n_workers),
                daemon=True)
        else:
            self._devbrute_producer_thread = threading.Thread(
                target=self._db_producer,
                args=(charset, min_len, max_len, fixed, key_list, prefix, suffix, n_workers, template),
                daemon=True)
        self._devbrute_producer_thread.start()

        self._devbrute_worker_threads = []
        for _ in range(n_workers):
            t = threading.Thread(
                target=self._db_worker,
                args=(template, locale, stop_on_find, device_sn, imei),
                daemon=True)
            t.start()
            self._devbrute_worker_threads.append(t)

        self.root.after(500, self._db_monitor)
        self.root.after(1000, self._db_update_speed)

    def _db_producer(self, charset, min_len, max_len, fixed, key_list, prefix, suffix, n_workers, template):
        lengths = [min_len] if fixed else range(min_len, max_len + 1)
        try:
            for length in lengths:
                for combo in _itertools.product(charset, repeat=length):
                    if self._devbrute_stop_flag:
                        break
                    self._devbrute_pause_event.wait()
                    if self._devbrute_stop_flag:
                        break
                    device = prefix + ''.join(combo) + suffix
                    for key in key_list:
                        self._devbrute_queue.put((device, key))
                if self._devbrute_stop_flag:
                    break
        finally:
            for _ in range(n_workers):
                self._devbrute_queue.put(None)

    def _db_producer_wordlist(self, wordlist_path, key_list, n_workers):
        try:
            for word in self._db_wordlist_iter(wordlist_path):
                if self._devbrute_stop_flag:
                    break
                self._devbrute_pause_event.wait()
                if self._devbrute_stop_flag:
                    break
                for key in key_list:
                    self._devbrute_queue.put((word, key))
                with self._devbrute_lock:
                    self._devbrute_total += len(key_list)
                self.root.after(0, lambda t=self._devbrute_total: self._db_set_progress_max(t))
        finally:
            for _ in range(n_workers):
                self._devbrute_queue.put(None)

    def _db_set_progress_max(self, total):
        try:
            self.db_progress['maximum'] = max(1, total)
        except Exception:
            pass

    def _db_worker(self, template, locale, stop_on_find, device_sn="", imei=""):
        tz = LOCALE_TZ_MAP.get(locale, 'America/New_York')
        _NETWORK_ERRS = ("handshake operation timed out", "read operation timed out",
                         "_ssl.c", "urlopen error", "timed out",
                         "connection reset", "connection refused", "remote end closed")
        max_hard_retries = 3

        while True:
            self._devbrute_pause_event.wait()
            if self._devbrute_stop_flag:
                break
            try:
                item = self._devbrute_queue.get(timeout=0.5)
            except queue.Empty:
                continue
            if item is None:
                break

            device, key = item

            fp = template
            if '{device}' in fp:
                fp = fp.replace('{device}', device)
            if '{key}' in fp:
                fp = fp.replace('{key}', key)

            hard_attempt = 0
            while True:
                if self._devbrute_stop_flag:
                    break
                self._devbrute_pause_event.wait()
                if self._devbrute_stop_flag:
                    break
                try:
                    _curl = getattr(self, 'checkin_url_var', None)
                    _curl = _curl.get().strip() if _curl else None
                    settings, raw_bytes, _req, _reqgz = perform_checkin(fp, locale=locale, timezone=tz,
                                                                       device_sn=device_sn, imei=imei, url=_curl)
                    if not settings:
                        hard_attempt += 1
                        if hard_attempt >= max_hard_retries:
                            self._db_log(
                                f"  DEVICE={device} KEY={key} → no response (after {max_hard_retries} retries)",
                                'skip')
                            self._db_increment_progress()
                            break
                        continue
                    ota = find_ota_link(settings)
                    label = f"DEVICE={device} KEY={key}"
                    if ota:
                        with self._devbrute_lock:
                            self._devbrute_found_count += 1
                            local_count = self._devbrute_found_count
                        url = ota.get('url', '') if isinstance(ota, dict) else str(ota)
                        title = ota.get('title', '') if isinstance(ota, dict) else ''
                        desc = ota.get('description', '') if isinstance(ota, dict) else ''
                        size = ota.get('size', '') if isinstance(ota, dict) else ''
                        block = [
                            ("", 'found'),
                            (f"  ★ FOUND #{local_count}  {label}", 'found'),
                            (f"    URL         : {url}", 'found'),
                        ]
                        if title:
                            block.append((f"    Title       : {title}", 'found'))
                        if desc:
                            block.append((f"    Description : {desc[:80]}{'...' if len(desc) > 80 else ''}", 'found'))
                        if size:
                            block.append((f"    Size        : {size}", 'found'))
                        block.append(("", 'found'))
                        for line, tag in block:
                            self._db_log(line, tag)
                        if stop_on_find:
                            self._devbrute_pause_event.clear()
                            self.root.after(0, self._db_visual_pause)
                    else:
                        if not self._db_hide_no_ota_var.get():
                            self._db_log(f"  {label} → no OTA", 'skip')
                    self._db_increment_progress()
                    break
                except Exception as e:
                    err_str = str(e).lower()
                    is_network = any(ne in err_str for ne in _NETWORK_ERRS)
                    if is_network:
                        continue
                    hard_attempt += 1
                    if hard_attempt >= max_hard_retries:
                        self._db_log(
                            f"  DEVICE={device} KEY={key} → ERROR: {e} (after {max_hard_retries} retries)",
                            'error')
                        self._db_increment_progress()
                        break

    def update_status(self, message, status_type='info'):
        self.status_var.set(message)
        if status_type == 'error':
            self.status_label.configure(foreground='#cc0000')
        elif status_type == 'success':
            self.status_label.configure(foreground='#006600')
        else:
            self.status_label.configure(foreground='#0066cc')
        self.root.update()

    def log_output(self, text, tag='info'):
        self.output_text.insert(tk.END, text + '\n', tag)
        self.output_text.see(tk.END)
        self.root.update()

    def log_link(self, display_text, url):
        link_id = f"link_{len(self.url_map)}"
        self.url_map[link_id] = url
        self.output_text.insert(tk.END, display_text, (link_id, 'link'))
        self.output_text.see(tk.END)
        self.root.update()

    def on_link_click(self, event):
        try:
            index = self.output_text.index(f"@{event.x},{event.y}")
            tags = self.output_text.tag_names(index)
            for tag in tags:
                if tag in self.url_map:
                    url = self.url_map[tag]
                    webbrowser.open(url)
                    return
        except Exception:
            pass

    def on_header_link_click(self, event):
        if self.current_ota_link:
            webbrowser.open(self.current_ota_link)

    def _flash_button(self, button, flash_text="✓ Copied", duration_ms=900):
        original_text = button.cget('text')
        pending_id = getattr(button, '_flash_after_id', None)
        if pending_id:
            try:
                self.root.after_cancel(pending_id)
            except Exception:
                pass
        else:
            button._flash_original_text = original_text
        button.config(text=flash_text)

        def _restore():
            button.config(text=getattr(button, '_flash_original_text', original_text))
            button._flash_after_id = None

        button._flash_after_id = self.root.after(duration_ms, _restore)

    def on_copy_link_click(self):
        if not self.current_ota_link:
            self.status_var.set("No link to copy yet")
            return
        self.root.clipboard_clear()
        self.root.clipboard_append(self.current_ota_link)
        self.status_var.set("Link copied to clipboard")
        self._flash_button(self.copy_link_button, "✓ Copied")

    def _os_label(self, os_kind):
        return {"android": "Android", "chromeos": "ChromeOS", "xiaomi": "Xiaomi", "playemu": "Play Games Emu"}.get(os_kind, os_kind)

    def _make_scrollable_frame(self, parent):
        canvas = tk.Canvas(parent, bg=self.APP_BG, highlightthickness=0)
        vscroll = ttk.Scrollbar(parent, orient=tk.VERTICAL, command=canvas.yview)
        inner = ttk.Frame(canvas)

        inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=inner, anchor="nw")
        canvas.configure(yscrollcommand=vscroll.set)

        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vscroll.pack(side=tk.RIGHT, fill=tk.Y)

        def _on_mousewheel(event):
            try:
                delta = -1 * (event.delta // 120) if event.delta else 0
                canvas.yview_scroll(delta, "units")
            except tk.TclError:
                try:
                    canvas.unbind_all("<MouseWheel>")
                except Exception:
                    pass
        canvas.bind_all("<MouseWheel>", _on_mousewheel)

        return canvas, inner

    def _record_matches_query(self, rec, query):
        if not query:
            return True
        q = query.lower()
        haystack = " ".join([
            rec.get("title", ""),
            rec.get("description", ""),
            rec.get("url", ""),
            rec.get("fingerprint", ""),
            rec.get("locale", ""),
            " ".join(rec.get("alt_filenames", []) or []),
        ]).lower()
        return q in haystack

    def _collection_entry_matches_query(self, url, entry, query):
        if not query:
            return True
        q = query.lower()
        variant_text = " ".join(
            " ".join([v.get("title", ""), v.get("description", ""), v.get("size", "")])
            for v in entry.get("variants", [])
        )
        haystack = " ".join([
            url,
            variant_text,
            " ".join(entry.get("alt_filenames", []) or []),
            " ".join(entry.get("locales", []) or []),
            " ".join(entry.get("fingerprints", []) or []),
        ]).lower()
        return q in haystack

    def open_additional_features_window(self):
        win = tk.Toplevel(self.root)
        win.title("Scan URLs")
        win.geometry("620x480")
        win.configure(bg=self.APP_BG)

        top = ttk.Frame(win, padding=12)
        top.pack(fill=tk.BOTH, expand=True)

        ttk.Label(top, text="Scan URLs", style='Header.TLabel').pack(anchor=tk.W, pady=(0, 10))

        desc = ttk.Label(
            top,
            text=("Scan URLs: import a .txt file containing a list of OTA links "
                  "(one per line). The app will check the metadata of every link "
                  "and write post-build / pre-build info to global.txt."),
            style='Normal.TLabel', wraplength=580, justify=tk.LEFT)
        desc.pack(anchor=tk.W, pady=(0, 10))

        options_row = ttk.Frame(top)
        options_row.pack(fill=tk.X, pady=(0, 10))

        ttk.Label(options_row, text="Parallel workers:", style='Normal.TLabel').pack(side=tk.LEFT)
        self.scan_urls_workers_var = tk.IntVar(value=1)
        workers_spin = ttk.Spinbox(options_row, from_=1, to=32, width=5,
                                   textvariable=self.scan_urls_workers_var)
        workers_spin.pack(side=tk.LEFT, padx=(8, 0))

        ttk.Button(options_row, text="🔍 Scan URLs", command=self.on_scan_urls_click).pack(side=tk.LEFT, padx=(20, 0))

        ttk.Separator(top, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=12)

        self.scan_urls_status_var = tk.StringVar(value="Ready.")
        ttk.Label(top, textvariable=self.scan_urls_status_var, style='Normal.TLabel',
                  wraplength=580, justify=tk.LEFT).pack(anchor=tk.W, pady=(0, 8))

        log_frame = ttk.Frame(top)
        log_frame.pack(fill=tk.BOTH, expand=True)
        self.scan_urls_log = scrolledtext.ScrolledText(log_frame, height=14, wrap=tk.WORD)
        self.scan_urls_log.pack(fill=tk.BOTH, expand=True)
        self.scan_urls_log.configure(state=tk.DISABLED)

        btn_row = ttk.Frame(top)
        btn_row.pack(fill=tk.X, pady=(8, 0))
        ttk.Button(btn_row, text="📂 Open global.txt",
                   command=self._open_global_txt).pack(side=tk.LEFT)
        ttk.Button(btn_row, text="Close", command=win.destroy).pack(side=tk.RIGHT)

        self._additional_features_win = win

    def _scan_urls_log_append(self, msg):
        try:
            self.scan_urls_log.configure(state=tk.NORMAL)
            self.scan_urls_log.insert(tk.END, msg + "\n")
            self.scan_urls_log.see(tk.END)
            self.scan_urls_log.configure(state=tk.DISABLED)
        except Exception:
            pass

    def _global_txt_path(self):
        try:
            base_dir = _get_storage_dir()
        except Exception:
            base_dir = os.getcwd()
        return os.path.join(base_dir, "global.txt")

    def _open_global_txt(self):
        path = self._global_txt_path()
        try:
            if not os.path.isfile(path):
                open(path, "a", encoding="utf-8").close()
            if sys.platform.startswith("win"):
                os.startfile(path)
            elif sys.platform == "darwin":
                os.system(f'open "{path}"')
            else:
                os.system(f'xdg-open "{path}"')
        except Exception as exc:
            messagebox.showerror("global.txt", f"Failed to open file:\n{exc}")

    def on_scan_urls_click(self):
        txt_path = filedialog.askopenfilename(
            title="Select a .txt file containing links",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")]
        )
        if not txt_path:
            return

        try:
            with open(txt_path, "r", encoding="utf-8", errors="replace") as f:
                raw_lines = f.readlines()
        except Exception as exc:
            messagebox.showerror("Scan URLs", f"Failed to read file:\n{exc}")
            return

        urls = []
        for line in raw_lines:
            u = line.strip()
            if not u or u.startswith('#'):
                continue
            urls.append(u)

        if not urls:
            messagebox.showinfo("Scan URLs", "No links were found in the file.")
            return

        try:
            worker_count = max(1, min(32, int(self.scan_urls_workers_var.get())))
        except Exception:
            worker_count = 1

        self.scan_urls_log.configure(state=tk.NORMAL)
        self.scan_urls_log.delete('1.0', tk.END)
        self.scan_urls_log.configure(state=tk.DISABLED)
        self.scan_urls_status_var.set(
            f"Found {len(urls)} link(s). Starting scan with {worker_count} worker(s)…")

        threading.Thread(target=self._scan_urls_dispatch, args=(urls, worker_count), daemon=True).start()

    def _scan_urls_dispatch(self, urls, worker_count):
        total = len(urls)
        work_queue = queue.Queue()
        for idx, url in enumerate(urls, start=1):
            work_queue.put((idx, url))

        global_txt_path = self._global_txt_path()
        file_lock = threading.Lock()
        counters = {'ok': 0, 'fail': 0, 'done': 0}
        counters_lock = threading.Lock()

        self._scan_urls_pending_log = []
        self._scan_urls_pending_log_lock = threading.Lock()
        self._scan_urls_latest_status = [None]
        self._scan_urls_active = True

        try:
            out_f = open(global_txt_path, "a", encoding="utf-8")
        except Exception as exc:
            self._scan_urls_queue_log(f"[Error] Failed to open {global_txt_path}: {exc}")
            self._scan_urls_active = False
            self.root.after(0, self.scan_urls_status_var.set, f"Failed to open global.txt: {exc}")
            return

        def buffer_log(msg):
            with self._scan_urls_pending_log_lock:
                self._scan_urls_pending_log.append(msg)

        def buffer_status(msg):
            self._scan_urls_latest_status[0] = msg

        RETRY_MAX_ATTEMPTS = 3
        RETRY_DELAY_SECONDS = 2.0

        def _is_404_error(exc_or_msg):
            code = getattr(exc_or_msg, 'code', None)
            if code == 404:
                return True
            text = str(exc_or_msg)
            return '404' in text

        def worker():
            while True:
                try:
                    idx, url = work_queue.get_nowait()
                except queue.Empty:
                    return

                filename = urlparse(url).path.rsplit('/', 1)[-1] or url
                buffer_log(f"[{idx}/{total}] {filename} — reading metadata…")

                post_build = ""
                pre_build = ""
                error_msg = ""
                is_404 = False

                attempt = 1
                while True:
                    post_build = ""
                    pre_build = ""
                    error_msg = ""
                    try:
                        status_cb = lambda m, i=idx, t=total: buffer_status(f"[{i}/{t}] {m}")
                        meta = fetch_payload_metadata(url, status_cb=status_cb, timeout=30)
                        fields = (meta or {}).get('fields', {}) or {}
                        post_build = fields.get('post-build', '') or ''
                        pre_build = fields.get('pre-build', '') or ''
                        if not meta.get('found'):
                            error_msg = meta.get('error') or "metadata not found"
                    except Exception as exc:
                        error_msg = str(exc)
                        if _is_404_error(exc):
                            is_404 = True

                    if post_build or pre_build:
                        break

                    if error_msg and _is_404_error(error_msg):
                        is_404 = True

                    if is_404:
                        break

                    if not error_msg:
                        break

                    if attempt >= RETRY_MAX_ATTEMPTS:
                        break

                    buffer_log(f"    ⟳ [{idx}/{total}] {filename} — attempt {attempt} failed "
                               f"({error_msg}), retrying…")
                    time.sleep(RETRY_DELAY_SECONDS)
                    attempt += 1

                if attempt > 1 and (post_build or pre_build):
                    buffer_log(f"    ↻ [{idx}/{total}] {filename} — succeeded on attempt {attempt}")

                entry_lines = [
                    f"filename: {filename}\n",
                    f"post-build: {post_build}\n",
                    f"pre-build: {pre_build}\n",
                ]
                if error_msg:
                    entry_lines.append(f"error: {error_msg}\n")
                entry_lines.append(f"url: {url}\n")
                entry_lines.append("\n")

                with file_lock:
                    try:
                        out_f.write("".join(entry_lines))
                        out_f.flush()
                    except Exception:
                        pass

                with counters_lock:
                    if post_build or pre_build:
                        counters['ok'] += 1
                    else:
                        counters['fail'] += 1
                    counters['done'] += 1
                    done_snapshot = counters['done']

                if post_build or pre_build:
                    buffer_log(f"    ✔ [{idx}/{total}] post-build: {post_build or '—'} | pre-build: {pre_build or '—'}")
                else:
                    buffer_log(f"    ✘ [{idx}/{total}] post-build/pre-build not found"
                               + (f" ({error_msg})" if error_msg else ""))

                buffer_status(f"Progress: {done_snapshot}/{total} link(s) processed…")

                work_queue.task_done()

        self.root.after(100, self._scan_urls_flush_ui)

        threads = []
        for _ in range(max(1, min(worker_count, total))):
            t = threading.Thread(target=worker, daemon=True)
            t.start()
            threads.append(t)

        for t in threads:
            t.join()

        try:
            out_f.close()
        except Exception:
            pass

        summary = (f"Done: {counters['ok']} succeeded, {counters['fail']} with no result. "
                   f"Written to global.txt ({global_txt_path})")
        buffer_log(summary)
        buffer_status(summary)
        self._scan_urls_active = False

    def _scan_urls_flush_ui(self):
        pending = None
        try:
            with self._scan_urls_pending_log_lock:
                if self._scan_urls_pending_log:
                    pending = self._scan_urls_pending_log
                    self._scan_urls_pending_log = []
        except Exception:
            pending = None

        if pending:
            try:
                self.scan_urls_log.configure(state=tk.NORMAL)
                self.scan_urls_log.insert(tk.END, "\n".join(pending) + "\n")
                self.scan_urls_log.see(tk.END)
                self.scan_urls_log.configure(state=tk.DISABLED)
            except Exception:
                pass

        latest_status = self._scan_urls_latest_status[0]
        if latest_status is not None:
            try:
                self.scan_urls_status_var.set(latest_status)
            except Exception:
                pass
            self._scan_urls_latest_status[0] = None

        if getattr(self, '_scan_urls_active', False):
            self.root.after(100, self._scan_urls_flush_ui)

    def _scan_urls_queue_log(self, msg):
        try:
            with self._scan_urls_pending_log_lock:
                self._scan_urls_pending_log.append(msg)
        except Exception:
            pass

    def open_scan_fingerprints_window(self):
        win = tk.Toplevel(self.root)
        win.title("Scan Fingerprints")
        win.geometry("680x620")
        win.configure(bg=self.APP_BG)

        top = ttk.Frame(win, padding=12)
        top.pack(fill=tk.BOTH, expand=True)

        ttk.Label(top, text="🧬 Scan Fingerprints", style='Header.TLabel').pack(anchor=tk.W, pady=(0, 10))

        desc = ttk.Label(
            top,
            text=("Import a .txt file with fingerprints (one per line). Each one is "
                  "checked-in against Google's servers, optionally across multiple "
                  "locales and/or all key/build types, and optionally with an IMEI "
                  "or Serial attached. Results are written to global2.txt."),
            style='Normal.TLabel', wraplength=640, justify=tk.LEFT)
        desc.pack(anchor=tk.W, pady=(0, 10))

        id_lf = ttk.LabelFrame(top, text="Device Identifier", padding=8)
        id_lf.pack(fill=tk.X, pady=(0, 10))

        ttk.Label(id_lf, text="IMEI:", style='Normal.TLabel').grid(row=0, column=0, sticky=tk.W)
        self.sf_imei_var = tk.StringVar()
        self.sf_imei_combo = ttk.Combobox(id_lf, textvariable=self.sf_imei_var, width=30)
        self.sf_imei_combo.grid(row=0, column=1, sticky=(tk.W, tk.E), padx=(6, 0))

        ttk.Label(id_lf, text="S/N:", style='Normal.TLabel').grid(row=1, column=0, sticky=tk.W, pady=(8, 0))
        self.sf_serial_var = tk.StringVar()
        self.sf_serial_combo = ttk.Combobox(id_lf, textvariable=self.sf_serial_var, width=30)
        self.sf_serial_combo.grid(row=1, column=1, sticky=(tk.W, tk.E), padx=(6, 0), pady=(8, 0))

        id_lf.columnconfigure(1, weight=1)

        loc_lf = ttk.LabelFrame(top, text="Locales", padding=8)
        loc_lf.pack(fill=tk.X, pady=(0, 10))
        ttk.Label(loc_lf, text="Locales (comma/space separated, blank = current app locale):",
                  style='Normal.TLabel').pack(anchor=tk.W)
        self.sf_locales_var = tk.StringVar(value="")
        ttk.Entry(loc_lf, textvariable=self.sf_locales_var, width=60).pack(fill=tk.X, pady=(4, 0))

        bt_lf = ttk.LabelFrame(top, text="Build Types", padding=8)
        bt_lf.pack(fill=tk.X, pady=(0, 10))
        self.sf_all_keytypes_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(bt_lf, text="Go through all key/build types for each fingerprint "
                                    "(user/eng/userdebug × release/dev/test-keys)",
                        variable=self.sf_all_keytypes_var).pack(anchor=tk.W)

        options_row = ttk.Frame(top)
        options_row.pack(fill=tk.X, pady=(0, 10))
        ttk.Label(options_row, text="Parallel workers:", style='Normal.TLabel').pack(side=tk.LEFT)
        self.sf_workers_var = tk.IntVar(value=1)
        ttk.Spinbox(options_row, from_=1, to=32, width=5, textvariable=self.sf_workers_var).pack(side=tk.LEFT, padx=(8, 0))
        ttk.Button(options_row, text="🔍 Scan Fingerprints", command=self.on_scan_fingerprints_click).pack(side=tk.LEFT, padx=(20, 0))

        ttk.Separator(top, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=8)

        self.sf_status_var = tk.StringVar(value="Ready.")
        ttk.Label(top, textvariable=self.sf_status_var, style='Normal.TLabel',
                  wraplength=640, justify=tk.LEFT).pack(anchor=tk.W, pady=(0, 8))

        log_frame = ttk.Frame(top)
        log_frame.pack(fill=tk.BOTH, expand=True)
        self.sf_log = scrolledtext.ScrolledText(log_frame, height=14, wrap=tk.WORD)
        self.sf_log.pack(fill=tk.BOTH, expand=True)
        self.sf_log.configure(state=tk.DISABLED)

        btn_row = ttk.Frame(top)
        btn_row.pack(fill=tk.X, pady=(8, 0))
        ttk.Button(btn_row, text="📂 Open global2.txt", command=self._open_global2_txt).pack(side=tk.LEFT)
        ttk.Button(btn_row, text="Close", command=win.destroy).pack(side=tk.RIGHT)

        self._scan_fingerprints_win = win
        self._sf_reload_id_values()

    def _sf_reload_id_values(self):
        try:
            data = _load_serials_data()
        except Exception:
            data = {"serials": [], "imeis": []}

        imei_values = [entry.get("value", "") for entry in data.get("imeis", []) if entry.get("value")]
        serial_values = [entry.get("value", "") for entry in data.get("serials", []) if entry.get("value")]

        self.sf_imei_combo['values'] = imei_values
        self.sf_serial_combo['values'] = serial_values

    def _global2_txt_path(self):
        try:
            base_dir = _get_storage_dir()
        except Exception:
            base_dir = os.getcwd()
        return os.path.join(base_dir, "global2.txt")

    def _open_global2_txt(self):
        path = self._global2_txt_path()
        try:
            if not os.path.isfile(path):
                open(path, "a", encoding="utf-8").close()
            if sys.platform.startswith("win"):
                os.startfile(path)
            elif sys.platform == "darwin":
                os.system(f'open "{path}"')
            else:
                os.system(f'xdg-open "{path}"')
        except Exception as exc:
            messagebox.showerror("global2.txt", f"Failed to open file:\n{exc}")

    def _sf_log_append(self, msg):
        try:
            self.sf_log.configure(state=tk.NORMAL)
            self.sf_log.insert(tk.END, msg + "\n")
            self.sf_log.see(tk.END)
            self.sf_log.configure(state=tk.DISABLED)
        except Exception:
            pass

    def on_scan_fingerprints_click(self):
        txt_path = filedialog.askopenfilename(
            title="Select a .txt file containing fingerprints",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")]
        )
        if not txt_path:
            return

        try:
            with open(txt_path, "r", encoding="utf-8", errors="replace") as f:
                raw_lines = f.readlines()
        except Exception as exc:
            messagebox.showerror("Scan Fingerprints", f"Failed to read file:\n{exc}")
            return

        fingerprints = []
        for line in raw_lines:
            fp = line.strip()
            if not fp or fp.startswith('#'):
                continue
            if ':' not in fp:
                continue
            fingerprints.append(fp)

        if not fingerprints:
            messagebox.showinfo("Scan Fingerprints", "No valid fingerprints were found in the file "
                                                    "(each line must contain at least one ':').")
            return

        locales_str = self.sf_locales_var.get().strip()
        if locales_str:
            locales = [loc.strip() for loc in re.split(r'[,\s\n]+', locales_str) if loc.strip()]
        else:
            locales = [self.locale_var.get().strip() or "en-US"]

        device_sn = self.sf_serial_var.get().strip()
        imei = self.sf_imei_var.get().strip()

        all_keytypes = bool(self.sf_all_keytypes_var.get())
        key_types = list(self.KEY_TYPES_ALL) if all_keytypes else [None]

        try:
            worker_count = max(1, min(32, int(self.sf_workers_var.get())))
        except Exception:
            worker_count = 1

        self.sf_log.configure(state=tk.NORMAL)
        self.sf_log.delete('1.0', tk.END)
        self.sf_log.configure(state=tk.DISABLED)

        total_jobs = len(fingerprints) * len(locales) * len(key_types)
        self.sf_status_var.set(
            f"Found {len(fingerprints)} fingerprint(s) × {len(locales)} locale(s)"
            f"{' × ' + str(len(key_types)) + ' key type(s)' if all_keytypes else ''}"
            f" = {total_jobs} job(s). Starting with {worker_count} worker(s)…"
        )

        threading.Thread(
            target=self._scan_fingerprints_dispatch,
            args=(fingerprints, locales, key_types, device_sn, imei, worker_count),
            daemon=True
        ).start()

    def _scan_fingerprints_dispatch(self, fingerprints, locales, key_types, device_sn, imei, worker_count):
        jobs = []
        idx = 0
        for fp in fingerprints:
            if ':' not in fp:
                continue
            prefix, own_key = fp.rsplit(':', 1)
            for loc in locales:
                for kt in key_types:
                    idx += 1
                    test_fp = f"{prefix}:{kt}" if kt else fp
                    key_label = kt or own_key
                    jobs.append((idx, fp, test_fp, loc, key_label))
        total = len(jobs)

        work_queue = queue.Queue()
        for job in jobs:
            work_queue.put(job)

        global2_txt_path = self._global2_txt_path()
        file_lock = threading.Lock()
        counters = {'ok': 0, 'fail': 0, 'done': 0, 'dupe': 0}
        counters_lock = threading.Lock()

        seen_urls = set()
        try:
            if os.path.isfile(global2_txt_path):
                with open(global2_txt_path, "r", encoding="utf-8", errors="replace") as ef:
                    for line in ef:
                        line = line.strip()
                        if line.startswith("ota_url:"):
                            u = line.split(":", 1)[1].strip()
                            if u:
                                seen_urls.add(u)
        except Exception:
            pass
        seen_urls_lock = threading.Lock()

        self._sf_pending_log = []
        self._sf_pending_log_lock = threading.Lock()
        self._sf_latest_status = [None]
        self._sf_active = True

        def buffer_log(msg):
            with self._sf_pending_log_lock:
                self._sf_pending_log.append(msg)

        def buffer_status(msg):
            self._sf_latest_status[0] = msg

        try:
            out_f = open(global2_txt_path, "a", encoding="utf-8")
        except Exception as exc:
            buffer_log(f"[Error] Failed to open {global2_txt_path}: {exc}")
            self._sf_active = False
            self.root.after(0, self.sf_status_var.set, f"Failed to open global2.txt: {exc}")
            return

        def worker():
            while True:
                try:
                    idx, orig_fp, test_fp, loc, key_label = work_queue.get_nowait()
                except queue.Empty:
                    return

                tz = LOCALE_TZ_MAP.get(loc, 'America/New_York')
                buffer_log(f"[{idx}/{total}] {test_fp}  (locale {loc})")
                buffer_status(f"[{idx}/{total}] Checking {test_fp} @ {loc}…")

                ota_url = ""
                ota_title = ""
                ota_size = ""
                error_msg = ""

                try:
                    _curl = getattr(self, 'checkin_url_var', None)
                    _curl = _curl.get().strip() if _curl else None
                    settings, raw_bytes, _req, _reqgz = perform_checkin(
                        test_fp, locale=loc, timezone=tz, device_sn=device_sn, imei=imei, url=_curl
                    )
                    if not settings:
                        error_msg = "No response from server"
                    else:
                        ota = find_ota_link(settings)
                        if ota and ota.get('url'):
                            ota_url = ota['url']
                            ota_title = ota.get('title', '') or ''
                            ota_size = ota.get('size', '') or ''
                        else:
                            error_msg = "No OTA found"
                except Exception as exc:
                    error_msg = str(exc)

                is_dupe = False
                if ota_url:
                    with seen_urls_lock:
                        if ota_url in seen_urls:
                            is_dupe = True
                        else:
                            seen_urls.add(ota_url)

                if ota_url and not is_dupe:
                    entry_lines = [
                        f"fingerprint: {test_fp}\n",
                        f"source_fingerprint: {orig_fp}\n",
                        f"key_type: {key_label}\n",
                        f"locale: {loc}\n",
                    ]
                    if device_sn:
                        entry_lines.append(f"serial: {device_sn}\n")
                    if imei:
                        entry_lines.append(f"imei: {imei}\n")
                    entry_lines.append(f"ota_url: {ota_url}\n")
                    if ota_title:
                        entry_lines.append(f"ota_title: {ota_title}\n")
                    if ota_size:
                        entry_lines.append(f"ota_size: {ota_size}\n")
                    entry_lines.append("\n")

                    with file_lock:
                        try:
                            out_f.write("".join(entry_lines))
                            out_f.flush()
                        except Exception:
                            pass

                with counters_lock:
                    if ota_url and not is_dupe:
                        counters['ok'] += 1
                    elif ota_url and is_dupe:
                        counters['dupe'] += 1
                    else:
                        counters['fail'] += 1
                    counters['done'] += 1
                    done_snapshot = counters['done']

                if ota_url and not is_dupe:
                    buffer_log(f"    ✔ [{idx}/{total}] OTA: {ota_url}")
                elif ota_url and is_dupe:
                    buffer_log(f"    ↷ [{idx}/{total}] Duplicate OTA, skipped: {ota_url}")
                else:
                    buffer_log(f"    ✘ [{idx}/{total}] No OTA — not written" + (f" ({error_msg})" if error_msg else ""))

                buffer_status(f"Progress: {done_snapshot}/{total} job(s) processed…")
                work_queue.task_done()

        self.root.after(100, self._sf_flush_ui)

        threads = []
        for _ in range(max(1, min(worker_count, total or 1))):
            t = threading.Thread(target=worker, daemon=True)
            t.start()
            threads.append(t)
        for t in threads:
            t.join()

        try:
            out_f.close()
        except Exception:
            pass

        summary = (f"Done: {counters['ok']} new OTA(s) written, {counters['dupe']} duplicate(s) skipped, "
                   f"{counters['fail']} with no result (not written). "
                   f"Written to global2.txt ({global2_txt_path})")
        buffer_log(summary)
        buffer_status(summary)
        self._sf_active = False

    def _sf_flush_ui(self):
        pending = None
        try:
            with self._sf_pending_log_lock:
                if self._sf_pending_log:
                    pending = self._sf_pending_log
                    self._sf_pending_log = []
        except Exception:
            pending = None

        if pending:
            try:
                self.sf_log.configure(state=tk.NORMAL)
                self.sf_log.insert(tk.END, "\n".join(pending) + "\n")
                self.sf_log.see(tk.END)
                self.sf_log.configure(state=tk.DISABLED)
            except Exception:
                pass

        latest_status = self._sf_latest_status[0]
        if latest_status is not None:
            try:
                self.sf_status_var.set(latest_status)
            except Exception:
                pass
            self._sf_latest_status[0] = None

        if getattr(self, '_sf_active', False):
            self.root.after(100, self._sf_flush_ui)

    def open_history_window(self):
        win = tk.Toplevel(self.root)
        win.title("OTA History")
        win.geometry("1000x680")
        win.configure(bg=self.APP_BG)

        top = ttk.Frame(win, padding=8)
        top.pack(fill=tk.X)
        ttk.Label(top, text="OTA History", style='Header.TLabel').pack(side=tk.LEFT)
        ttk.Button(top, text="🔄 Refresh", command=lambda: self._populate_history(nb, search_var.get())).pack(side=tk.RIGHT, padx=4)
        ttk.Button(top, text="🗑 Clear History", command=lambda: self._clear_history(nb, search_var)).pack(side=tk.RIGHT, padx=4)

        search_row = ttk.Frame(win, padding=(8, 0, 8, 8))
        search_row.pack(fill=tk.X)
        ttk.Label(search_row, text="🔎 Search device / title / URL / fingerprint:", style='Normal.TLabel').pack(side=tk.LEFT, padx=(0, 6))
        search_var = tk.StringVar(value="")
        search_entry = ttk.Entry(search_row, textvariable=search_var, width=50)
        search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        search_entry.bind('<KeyRelease>', lambda e: self._populate_history(nb, search_var.get()))
        ttk.Button(search_row, text="✕", width=3, command=lambda: (search_var.set(""), self._populate_history(nb, ""))).pack(side=tk.LEFT, padx=(6, 0))

        nb = NOTEBOOK_CLS(win)
        nb.pack(fill=tk.BOTH, expand=True, padx=8, pady=(0, 8))

        self._populate_history(nb, "")

    def _clear_history(self, nb, search_var):
        if not messagebox.askyesno("Clear History", "Are you sure you want to clear the entire OTA history?"):
            return
        with _ota_store_lock:
            _save_history([])
        self._populate_history(nb, search_var.get() if search_var else "")

    def _populate_history(self, nb, query=""):
        for tab_id in nb.tabs():
            nb.forget(tab_id)

        history = list(reversed(_load_history()))
        query = (query or "").strip()

        by_os = {"android": [], "chromeos": [], "xiaomi": []}
        for rec in history:
            if not self._record_matches_query(rec, query):
                continue
            by_os.setdefault(rec.get("os", "android"), []).append(rec)

        for os_kind in ("android", "chromeos", "xiaomi", "playemu"):
            recs = by_os.get(os_kind, [])
            tab = ttk.Frame(nb)
            nb.add(tab, text=f"{self._os_label(os_kind)} ({len(recs)})")
            self._build_paginated_tab(
                tab, recs,
                page_size=self.HISTORY_PAGE_SIZE,
                render_item=self._render_history_card,
            )

    def _build_paginated_tab(self, tab, items, page_size, render_item):
        state = {"page": 0}
        total = len(items)
        num_pages = max(1, (total + page_size - 1) // page_size)

        content_holder = ttk.Frame(tab)
        content_holder.pack(fill=tk.BOTH, expand=True)

        pager_holder = ttk.Frame(tab)
        pager_holder.pack(fill=tk.X, side=tk.BOTTOM)

        def render_page():
            for child in content_holder.winfo_children():
                child.destroy()
            for child in pager_holder.winfo_children():
                child.destroy()

            if not items:
                ttk.Label(content_holder, text="  No entries found.", style='Normal.TLabel').pack(anchor=tk.W, padx=10, pady=10)
                return

            canvas, inner = self._make_scrollable_frame(content_holder)
            start = state["page"] * page_size
            page_items = items[start:start + page_size]
            for it in page_items:
                render_item(inner, it)

            if num_pages > 1:
                self._build_pager_bar(pager_holder, state["page"], num_pages, go_to_page)

        def go_to_page(p):
            state["page"] = max(0, min(p, num_pages - 1))
            render_page()

        render_page()

    def _build_pager_bar(self, parent, current_page, num_pages, on_select):
        bar = ttk.Frame(parent, padding=(0, 6))
        bar.pack(anchor=tk.CENTER)

        def _btn(text, page, enabled=True):
            b = ttk.Button(bar, text=text, width=3 if text.isdigit() else 2,
                           command=(lambda: on_select(page)) if enabled else None)
            if not enabled:
                b.state(['disabled'])
            if enabled and text.isdigit() and page == current_page:
                b.state(['pressed'])
            b.pack(side=tk.LEFT, padx=1)

        _btn("«", 0, enabled=current_page > 0)
        _btn("‹", current_page - 1, enabled=current_page > 0)

        window = 2
        pages_to_show = set()
        pages_to_show.add(0)
        pages_to_show.add(num_pages - 1)
        for p in range(current_page - window, current_page + window + 1):
            if 0 <= p < num_pages:
                pages_to_show.add(p)
        sorted_pages = sorted(pages_to_show)

        last_shown = None
        for p in sorted_pages:
            if last_shown is not None and p - last_shown > 1:
                ttk.Label(bar, text="…", width=2, anchor=tk.CENTER).pack(side=tk.LEFT, padx=1)
            _btn(str(p + 1), p, enabled=True)
            last_shown = p

        _btn("›", current_page + 1, enabled=current_page < num_pages - 1)
        _btn("»", num_pages - 1, enabled=current_page < num_pages - 1)

    def _render_history_card(self, parent, rec):
        card = ttk.Frame(parent, relief=tk.GROOVE, borderwidth=1, padding=8)
        card.pack(fill=tk.X, padx=8, pady=4)

        head = ttk.Frame(card)
        head.pack(fill=tk.X)
        ttk.Label(head, text=f"🕘 {rec.get('timestamp', '')}", font=('Arial', 9, 'bold'),
                  foreground='#666666').pack(side=tk.LEFT)
        if rec.get("locale"):
            ttk.Label(head, text=f"   🌐 {rec['locale']}", font=('Arial', 9),
                      foreground='#666666').pack(side=tk.LEFT)

        title = rec.get("title") or "(no title)"
        title_lbl = ttk.Label(card, text=title, font=('Arial', 10, 'bold'), wraplength=880, justify=tk.LEFT)
        title_lbl.pack(anchor=tk.W, pady=(4, 0))

        url = rec.get("url", "")
        url_lbl = tk.Label(card, text=url, font=('Courier', 9), fg='#0066cc', bg=self.APP_BG,
                           wraplength=880, justify=tk.LEFT, cursor='hand2')
        url_lbl.pack(anchor=tk.W, pady=(2, 0))
        url_lbl.bind('<Button-1>', lambda e, u=url: webbrowser.open(u))

        desc = rec.get("description", "")
        if desc:
            desc_short = desc if len(desc) <= 220 else desc[:220] + "…"
            ttk.Label(card, text=desc_short, font=('Arial', 9), foreground='#333333',
                      wraplength=880, justify=tk.LEFT).pack(anchor=tk.W, pady=(2, 0))

        if rec.get("fingerprint"):
            fp = rec['fingerprint']
            fp_lbl = tk.Label(card, text=f"🔑 {fp}", font=('Courier', 8), fg='#666666', bg=self.APP_BG,
                              wraplength=880, justify=tk.LEFT)
            fp_lbl.pack(anchor=tk.W, pady=(2, 0))

        meta_bits = []
        if rec.get("size"):
            meta_bits.append(f"📦 {rec['size']}")
        if rec.get("alt_filenames"):
            meta_bits.append(f"🔀 {len(rec['alt_filenames'])} alternate filename(s)")
        if meta_bits:
            ttk.Label(card, text="   •   ".join(meta_bits), font=('Arial', 8),
                      foreground='#888888').pack(anchor=tk.W, pady=(2, 0))

    def open_collection_window(self):
        win = tk.Toplevel(self.root)
        win.title("OTA Collection")
        win.geometry("1050x700")
        win.configure(bg=self.APP_BG)

        top = ttk.Frame(win, padding=8)
        top.pack(fill=tk.X)
        ttk.Label(top, text="OTA Collection", style='Header.TLabel').pack(side=tk.LEFT)
        ttk.Button(top, text="🔄 Refresh", command=lambda: self._populate_collection(nb, search_var.get(), sort_var.get(), tag_filter_var.get())).pack(side=tk.RIGHT, padx=4)
        ttk.Button(top, text="🗑 Clear Collection", command=lambda: self._clear_collection(nb, search_var, sort_var, tag_filter_var)).pack(side=tk.RIGHT, padx=4)

        search_row = ttk.Frame(win, padding=(8, 0, 8, 4))
        search_row.pack(fill=tk.X)
        ttk.Label(search_row, text="🔎 Search device / title / URL / fingerprint / tag:", style='Normal.TLabel').pack(side=tk.LEFT, padx=(0, 6))
        search_var = tk.StringVar(value="")
        search_entry = ttk.Entry(search_row, textvariable=search_var, width=40)
        search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        search_entry.bind('<KeyRelease>', lambda e: self._populate_collection(nb, search_var.get(), sort_var.get(), tag_filter_var.get()))
        ttk.Button(search_row, text="✕", width=3, command=lambda: (search_var.set(""), self._populate_collection(nb, "", sort_var.get(), tag_filter_var.get()))).pack(side=tk.LEFT, padx=(6, 0))

        filter_row = ttk.Frame(win, padding=(8, 0, 8, 8))
        filter_row.pack(fill=tk.X)

        ttk.Label(filter_row, text="Sort by:", style='Normal.TLabel').pack(side=tk.LEFT, padx=(0, 6))
        sort_var = tk.StringVar(value=self.COLLECTION_SORT_OPTIONS[0][0])
        sort_combo = ttk.Combobox(filter_row, textvariable=sort_var, state="readonly", width=20,
                                  values=[label for label, _ in self.COLLECTION_SORT_OPTIONS])
        sort_combo.pack(side=tk.LEFT, padx=(0, 16))
        sort_combo.bind('<<ComboboxSelected>>', lambda e: self._populate_collection(nb, search_var.get(), sort_var.get(), tag_filter_var.get()))

        ttk.Label(filter_row, text="Tag:", style='Normal.TLabel').pack(side=tk.LEFT, padx=(0, 6))
        tag_filter_var = tk.StringVar(value="All tags")
        tag_filter_combo = ttk.Combobox(filter_row, textvariable=tag_filter_var, state="readonly", width=20,
                                        values=["All tags"] + get_all_collection_tags(_load_collection()))
        tag_filter_combo.pack(side=tk.LEFT)
        tag_filter_combo.bind('<<ComboboxSelected>>', lambda e: self._populate_collection(nb, search_var.get(), sort_var.get(), tag_filter_var.get()))
        self._collection_tag_filter_combo = tag_filter_combo

        nb = NOTEBOOK_CLS(win)
        nb.pack(fill=tk.BOTH, expand=True, padx=8, pady=(0, 8))

        self._populate_collection(nb, "", sort_var.get(), tag_filter_var.get())

    def _clear_collection(self, nb, search_var, sort_var=None, tag_filter_var=None):
        if not messagebox.askyesno("Clear Collection", "Are you sure you want to clear the entire OTA collection?"):
            return
        with _ota_store_lock:
            _save_collection({})
        self._populate_collection(
            nb,
            search_var.get() if search_var else "",
            sort_var.get() if sort_var else None,
            tag_filter_var.get() if tag_filter_var else None,
        )

    def _sort_collection_items(self, items, sort_label):
        sort_key = None
        for label, key in self.COLLECTION_SORT_OPTIONS:
            if label == sort_label:
                sort_key = key
                break
        if sort_key is None:
            sort_key = "last_seen_desc"

        def _title_of(entry):
            variants = entry.get("variants", [])
            t = variants[0].get("title") if variants else ""
            return (t or "").lower()

        def _size_bytes_of(entry):
            variants = entry.get("variants", [])
            size_str = variants[0].get("size") if variants else ""
            return self._parse_size_to_bytes(size_str)

        if sort_key == "last_seen_desc":
            return sorted(items, key=lambda kv: kv[1].get("last_seen", ""), reverse=True)
        elif sort_key == "last_seen_asc":
            return sorted(items, key=lambda kv: kv[1].get("last_seen", ""))
        elif sort_key == "first_seen_desc":
            return sorted(items, key=lambda kv: kv[1].get("first_seen", ""), reverse=True)
        elif sort_key == "first_seen_asc":
            return sorted(items, key=lambda kv: kv[1].get("first_seen", ""))
        elif sort_key == "title_asc":
            return sorted(items, key=lambda kv: _title_of(kv[1]))
        elif sort_key == "title_desc":
            return sorted(items, key=lambda kv: _title_of(kv[1]), reverse=True)
        elif sort_key == "size_desc":
            return sorted(items, key=lambda kv: _size_bytes_of(kv[1]), reverse=True)
        elif sort_key == "size_asc":
            return sorted(items, key=lambda kv: _size_bytes_of(kv[1]))
        return sorted(items, key=lambda kv: kv[1].get("last_seen", ""), reverse=True)

    @staticmethod
    def _parse_size_to_bytes(size_str):
        if not size_str:
            return 0
        m = re.search(r"([\d.,]+)\s*(KiB|MiB|GiB|KB|MB|GB|B)?", size_str, re.IGNORECASE)
        if not m:
            return 0
        try:
            num = float(m.group(1).replace(",", ""))
        except ValueError:
            return 0
        unit = (m.group(2) or "B").lower()
        mult = {
            "b": 1,
            "kb": 1024, "kib": 1024,
            "mb": 1024 ** 2, "mib": 1024 ** 2,
            "gb": 1024 ** 3, "gib": 1024 ** 3,
        }.get(unit, 1)
        return num * mult

    def _populate_collection(self, nb, query="", sort_label=None, tag_filter=None):
        for tab_id in nb.tabs():
            nb.forget(tab_id)

        coll = _load_collection()
        query = (query or "").strip()
        sort_label = sort_label or self.COLLECTION_SORT_OPTIONS[0][0]
        tag_filter = tag_filter or "All tags"

        for os_kind in ("android", "chromeos", "xiaomi", "playemu"):
            bucket = coll.get(os_kind, {})
            filtered = {
                u: e for u, e in bucket.items()
                if self._collection_entry_matches_query(u, e, query)
                and (tag_filter == "All tags" or tag_filter in (e.get("tags", []) or []))
            }

            items = self._sort_collection_items(list(filtered.items()), sort_label)

            tab = ttk.Frame(nb)
            nb.add(tab, text=f"{self._os_label(os_kind)} ({len(items)})")

            def render_item(parent, kv, os_kind=os_kind, nb=nb, query=query, sort_label=sort_label, tag_filter=tag_filter):
                url, entry = kv
                self._render_collection_card(parent, url, entry, os_kind, nb, query, sort_label, tag_filter)

            self._build_paginated_tab(
                tab, items,
                page_size=self.COLLECTION_PAGE_SIZE,
                render_item=render_item,
            )

    def _render_collection_card(self, parent, url, entry, os_kind=None, nb=None, query="", sort_label=None, tag_filter=None):
        card = ttk.Frame(parent, relief=tk.GROOVE, borderwidth=1, padding=8)
        card.pack(fill=tk.X, padx=8, pady=4)

        head = ttk.Frame(card)
        head.pack(fill=tk.X)
        ttk.Label(head, text=f"👁 first seen: {entry.get('first_seen', '?')}", font=('Arial', 8),
                  foreground='#888888').pack(side=tk.LEFT)
        ttk.Label(head, text=f"   🕘 last seen: {entry.get('last_seen', '?')}", font=('Arial', 8),
                  foreground='#888888').pack(side=tk.LEFT)

        if os_kind is not None:
            ttk.Button(
                head, text="🏷 Edit tags", width=12,
                command=lambda: self._edit_collection_tags(os_kind, url, entry, nb, query, sort_label, tag_filter)
            ).pack(side=tk.RIGHT)

        variants = entry.get("variants", [])

        main_variant = variants[0] if variants else {}
        title = main_variant.get("title") or "(no title)"
        ttk.Label(card, text=title, font=('Arial', 10, 'bold'), wraplength=880,
                  justify=tk.LEFT).pack(anchor=tk.W, pady=(4, 0))

        url_lbl = tk.Label(card, text=url, font=('Courier', 9), fg='#0066cc', bg=self.APP_BG,
                           wraplength=880, justify=tk.LEFT, cursor='hand2')
        url_lbl.pack(anchor=tk.W, pady=(2, 0))
        url_lbl.bind('<Button-1>', lambda e, u=url: webbrowser.open(u))

        desc = main_variant.get("description", "")
        if desc:
            desc_short = desc if len(desc) <= 220 else desc[:220] + "…"
            ttk.Label(card, text=desc_short, font=('Arial', 9), foreground='#333333',
                      wraplength=880, justify=tk.LEFT).pack(anchor=tk.W, pady=(2, 0))

        if main_variant.get("size"):
            ttk.Label(card, text=f"📦 {main_variant['size']}", font=('Arial', 8),
                      foreground='#888888').pack(anchor=tk.W, pady=(2, 0))

        if len(variants) > 1:
            extra = len(variants) - 1
            variants_frame = ttk.Frame(card)
            variants_frame.pack(anchor=tk.W, pady=(4, 0), fill=tk.X)
            toggle_btn = ttk.Button(
                variants_frame,
                text=f"📝 same OTA, {extra} more description variant(s) ▾",
            )
            details_holder = {"shown": False, "frame": None}

            def _toggle(v=variants, holder=details_holder, vf=variants_frame):
                if holder["shown"]:
                    if holder["frame"]:
                        holder["frame"].destroy()
                        holder["frame"] = None
                    holder["shown"] = False
                    toggle_btn.config(text=f"📝 same OTA, {extra} more description variant(s) ▾")
                else:
                    df = ttk.Frame(vf)
                    df.pack(fill=tk.X, pady=(4, 0))
                    for i, var in enumerate(v[1:], start=2):
                        sub = ttk.Frame(df, relief=tk.FLAT, padding=(10, 4))
                        sub.pack(fill=tk.X, anchor=tk.W)
                        vt = var.get("title") or "(no title)"
                        ttk.Label(sub, text=f"Variant {i}: {vt}", font=('Arial', 9, 'bold'),
                                  wraplength=850, justify=tk.LEFT).pack(anchor=tk.W)
                        vd = var.get("description", "")
                        if vd:
                            vd_short = vd if len(vd) <= 200 else vd[:200] + "…"
                            ttk.Label(sub, text=vd_short, font=('Arial', 8), foreground='#555555',
                                      wraplength=850, justify=tk.LEFT).pack(anchor=tk.W)
                        if var.get("size"):
                            ttk.Label(sub, text=f"📦 {var['size']}", font=('Arial', 8),
                                      foreground='#888888').pack(anchor=tk.W)
                    holder["frame"] = df
                    holder["shown"] = True
                    toggle_btn.config(text=f"📝 same OTA, {extra} more description variant(s) ▴")

            toggle_btn.config(command=_toggle)
            toggle_btn.pack(anchor=tk.W)

        alt_filenames = entry.get("alt_filenames", [])
        if alt_filenames:
            alt_text = ", ".join(alt_filenames[:6])
            if len(alt_filenames) > 6:
                alt_text += f"  (+{len(alt_filenames) - 6} more)"
            ttk.Label(card, text=f"🔀 Alternate filenames: {alt_text}", font=('Arial', 8),
                      foreground='#888888', wraplength=880, justify=tk.LEFT).pack(anchor=tk.W, pady=(4, 0))

        locales = entry.get("locales", [])
        if locales:
            loc_text = ", ".join(locales[:8])
            if len(locales) > 8:
                loc_text += f"  (+{len(locales) - 8} more)"
            ttk.Label(card, text=f"🌐 Locales: {loc_text}", font=('Arial', 8),
                      foreground='#888888', wraplength=880, justify=tk.LEFT).pack(anchor=tk.W, pady=(2, 0))

        tags = entry.get("tags", []) or []
        if tags:
            tags_frame = ttk.Frame(card)
            tags_frame.pack(anchor=tk.W, pady=(4, 0), fill=tk.X)
            ttk.Label(tags_frame, text="🏷", font=('Arial', 8), foreground='#888888').pack(side=tk.LEFT, padx=(0, 4))
            for t in tags:
                tk.Label(
                    tags_frame, text=t, font=('Arial', 8, 'bold'),
                    fg='#ffffff', bg='#4a90d9', padx=6, pady=1
                ).pack(side=tk.LEFT, padx=(0, 4))

        fingerprints = entry.get("fingerprints", [])
        if fingerprints:
            fp_frame = ttk.Frame(card)
            fp_frame.pack(anchor=tk.W, pady=(4, 0), fill=tk.X)
            if len(fingerprints) == 1:
                fp_lbl = tk.Label(fp_frame, text=f"🔑 {fingerprints[0]}", font=('Courier', 8),
                                  fg='#666666', bg=self.APP_BG, wraplength=880, justify=tk.LEFT)
                fp_lbl.pack(anchor=tk.W)
            else:
                toggle_btn = ttk.Button(fp_frame, text=f"🔑 {len(fingerprints)} fingerprint(s) ▾")
                holder = {"shown": False, "frame": None}

                def _toggle_fp(fps=fingerprints, holder=holder, ff=fp_frame):
                    if holder["shown"]:
                        if holder["frame"]:
                            holder["frame"].destroy()
                            holder["frame"] = None
                        holder["shown"] = False
                        toggle_btn.config(text=f"🔑 {len(fps)} fingerprint(s) ▾")
                    else:
                        df = ttk.Frame(ff)
                        df.pack(fill=tk.X, pady=(4, 0))
                        for fp in fps:
                            tk.Label(df, text=fp, font=('Courier', 8), fg='#666666', bg=self.APP_BG,
                                     wraplength=850, justify=tk.LEFT).pack(anchor=tk.W, padx=(10, 0))
                        holder["frame"] = df
                        holder["shown"] = True
                        toggle_btn.config(text=f"🔑 {len(fps)} fingerprint(s) ▴")

                toggle_btn.config(command=_toggle_fp)
                toggle_btn.pack(anchor=tk.W)

    def _edit_collection_tags(self, os_kind, url, entry, nb, query, sort_label, tag_filter):
        dlg = tk.Toplevel(self.root)
        dlg.title("Edit tags")
        dlg.geometry("480x180")
        dlg.configure(bg=self.APP_BG)
        dlg.transient(self.root)
        dlg.grab_set()

        ttk.Label(dlg, text=url, font=('Courier', 8), foreground='#666666',
                  wraplength=440, justify=tk.LEFT).pack(anchor=tk.W, padx=12, pady=(12, 4))

        ttk.Label(dlg, text="Tags:", style='Normal.TLabel').pack(anchor=tk.W, padx=12, pady=(6, 2))

        current_tags = ", ".join(entry.get("tags", []) or [])
        tags_var = tk.StringVar(value=current_tags)
        entry_box = ttk.Entry(dlg, textvariable=tags_var, width=55)
        entry_box.pack(fill=tk.X, padx=12)
        entry_box.focus_set()
        entry_box.icursor(tk.END)

        all_tags = get_all_collection_tags(_load_collection())
        if all_tags:
            hint = "Available tags: " + ", ".join(all_tags[:20])
            if len(all_tags) > 20:
                hint += f" (+{len(all_tags) - 20} more)"
            ttk.Label(dlg, text=hint, font=('Arial', 8), foreground='#888888',
                      wraplength=440, justify=tk.LEFT).pack(anchor=tk.W, padx=12, pady=(6, 0))

        btn_row = ttk.Frame(dlg)
        btn_row.pack(fill=tk.X, padx=12, pady=12, side=tk.BOTTOM)

        def _save():
            raw = tags_var.get()
            tags = [t.strip() for t in raw.split(",") if t.strip()]
            set_collection_tags(os_kind, url, tags)
            dlg.destroy()
            if hasattr(self, "_collection_tag_filter_combo") and self._collection_tag_filter_combo.winfo_exists():
                self._collection_tag_filter_combo.config(values=["All tags"] + get_all_collection_tags(_load_collection()))
            self._populate_collection(nb, query, sort_label, tag_filter)

        ttk.Button(btn_row, text="Save", command=_save).pack(side=tk.RIGHT, padx=(6, 0))
        ttk.Button(btn_row, text="Cancel", command=dlg.destroy).pack(side=tk.RIGHT)
        entry_box.bind('<Return>', lambda e: _save())

    def on_clear_click(self):
        self.output_text.delete(1.0, tk.END)
        if self.html_frame:
            self.html_frame.load_html("")
        elif self.desc_text:
            self.desc_text.delete(1.0, tk.END)
        self.raw_text.delete(1.0, tk.END)
        self._raw_human = ""
        self._raw_hex = ""
        self.status_icon_var.set("")
        self.ota_link_label.config(text="")
        self.current_ota_link = None
        self.copy_link_button.config(state=tk.DISABLED)
        self.dogfood_label.config(text="")

        if hasattr(self, 'hi_tree_metadata'):
            for ch in self.hi_tree_metadata.get_children():
                self.hi_tree_metadata.delete(ch)
            self.hi_tree_metadata.column("value", width=1000, stretch=False)
        if hasattr(self, 'hi_metadata_status_var'):
            self.hi_metadata_status_var.set("")

        if hasattr(self, 'hi_list_altnames'):
            self.hi_list_altnames.delete(0, tk.END)
        if hasattr(self, 'hi_altnames_status_var'):
            self.hi_altnames_status_var.set("")

        if hasattr(self, 'zip_tree'):
            for ch in self.zip_tree.get_children():
                self.zip_tree.delete(ch)
        if hasattr(self, 'zip_tree_cache'):
            self.zip_tree_cache = {
                'url': None,
                'tail_data': None,
                'tail_offset': 0,
                'total_size': 0,
                'entries': None,
            }
        if hasattr(self, 'zip_tree_status_var'):
            self.zip_tree_status_var.set("Press 'Scan ZIP Tree' to view contents.")

        self.update_status("Output cleared")

    def on_copy_click(self):
        try:
            content = self.output_text.get(1.0, tk.END)
            self.root.clipboard_clear()
            self.root.clipboard_append(content)
            self.update_status("Copied to clipboard", 'success')
            self._flash_button(self.copy_button, "✓ Copied")
        except Exception as e:
            self.update_status(f"Failed to copy: {e}", 'error')

    def _meta_autofill_url(self, url, token=""):
        self.httpinfo_url_var.set(url)
        if token:
            self.httpinfo_token_var.set(token)

    def _update_dogfood_label(self, detected):
        if detected:
            self.dogfood_label.config(text="🐶 Dogfood serial")
        else:
            self.dogfood_label.config(text="")

    def on_query_click(self):
        mode = self.os_mode_var.get()
        if mode == "playemu":
            self._playemu_send()
            return

        fingerprint = self.fingerprint_var.get().strip()
        if not fingerprint:
            messagebox.showerror("Error", "Please enter a fingerprint")
            return
        if '/' not in fingerprint:
            messagebox.showerror("Error", "Invalid fingerprint format")
            return

        self.query_button.config(state=tk.DISABLED)
        self.keyscan_button.config(state=tk.DISABLED)
        self.clear_button.config(state=tk.DISABLED)
        self.fingerprint_entry.config(state=tk.DISABLED)

        self.query_thread = threading.Thread(target=self.perform_query, args=(fingerprint,), daemon=True)
        self.query_thread.start()

    def perform_query(self, fingerprint):
        mode = self.os_mode_var.get()
        if mode == "chromeos":
            self.perform_query_chromeos(fingerprint)
            return
        if mode == "xiaomi":
            self.perform_query_xiaomi(fingerprint)
            return
        if mode == "playemu":
            self.perform_query_playemu()
            return
        try:
            self.output_text.delete(1.0, tk.END)
            self.raw_text.delete(1.0, tk.END)
            if self.html_frame:
                self.html_frame.load_html("")
            elif self.desc_text:
                self.desc_text.delete(1.0, tk.END)
            self.url_map.clear()
            self.current_ota_link = None
            self.copy_link_button.config(state=tk.DISABLED)
            self._update_dogfood_label(False)
            self.update_status("Parsing fingerprint...")

            parsed = parse_fingerprint(fingerprint)
            self.update_status("Sending check-in request...")

            locale = self.locale_var.get().strip()
            timezone = self.timezone_var.get().strip()
            device_sn = getattr(self, 'device_sn_var', tk.StringVar()).get().strip()
            imei = getattr(self, 'imei_var', tk.StringVar()).get().strip()

            checkin_url = getattr(self, 'checkin_url_var', None)
            checkin_url = checkin_url.get().strip() if checkin_url else None
            settings, raw_bytes, req_data, req_gz = perform_checkin(fingerprint, locale, timezone, device_sn, imei, url=checkin_url)
            self._last_query_token = settings.get('update_token', '') if settings else ''
            self._last_raw_bytes = raw_bytes
            self._last_request_data = req_data
            self._last_request_gz = req_gz
            self._raw_request_populate()

            dogfood = False
            if raw_bytes and (b'droidfood' in raw_bytes.lower() or b'platform_dogfood' in raw_bytes.lower()):
                dogfood = True
            self._update_dogfood_label(dogfood)

            if not settings:
                self.log_output("ERROR: Check-in failed - No response from server", 'error')
                self.status_icon_var.set("❌")
                self.update_status("Query failed", 'error')
            else:
                if raw_bytes:
                    human_dump, hex_dump = format_raw_response(raw_bytes)
                else:
                    fallback = json.dumps(settings, indent=2, sort_keys=True)
                    human_dump, hex_dump = fallback, fallback
                self._raw_populate(human_dump, hex_dump)

                build_info = extract_build_details(fingerprint, settings)
                ota_link = find_ota_link(settings)

                if self.json_var.get():
                    json_data = {
                        'fingerprint': fingerprint,
                        'build_info': build_info,
                        'ota_link': ota_link,
                        'total_settings': len(settings),
                        'locale': locale,
                        'timezone': timezone,
                        'dogfood': dogfood,
                    }
                    output_str = json.dumps(json_data, indent=2)
                    self.log_output(output_str)
                    if self.html_frame:
                        html_content = f"<pre>{output_str}</pre>"
                        self.html_frame.load_html(html_content)
                    elif self.desc_text:
                        self.desc_text.insert(tk.END, output_str)
                    if ota_link and ota_link.get('url'):
                        self.status_icon_var.set("✓")
                        self.status_icon_label.config(foreground='#006600')
                    else:
                        self.status_icon_var.set("❌")
                        self.status_icon_label.config(foreground='#cc0000')
                else:
                    self.format_and_log_output(fingerprint, settings, build_info, ota_link, dogfood)

                if self.save_var.get():
                    if self.json_var.get():
                        output_str = json.dumps({
                            'fingerprint': fingerprint,
                            'build_info': build_info,
                            'ota_link': ota_link,
                            'total_settings': len(settings),
                            'locale': locale,
                            'timezone': timezone,
                            'dogfood': dogfood,
                        }, indent=2)
                    else:
                        output_str = self.output_text.get(1.0, tk.END)
                    self.save_output(output_str, fingerprint)

                self.update_status("Query completed successfully", 'success')

        except ValueError as e:
            self.log_output(f"ERROR: {e}", 'error')
            self.status_icon_var.set("❌")
            self.update_status("Invalid fingerprint format", 'error')
        except Exception as e:
            self.log_output(f"ERROR: {e}", 'error')
            self.status_icon_var.set("❌")
            self.update_status(f"Error: {e}", 'error')
        finally:
            self.query_button.config(state=tk.NORMAL)
            self.keyscan_button.config(state=tk.NORMAL)
            self.clear_button.config(state=tk.NORMAL)
            self.fingerprint_entry.config(state=tk.NORMAL)

    def perform_query_chromeos(self, fingerprint):
        try:
            self.output_text.delete(1.0, tk.END)
            self.raw_text.delete(1.0, tk.END)
            if self.html_frame:
                self.html_frame.load_html("")
            elif self.desc_text:
                self.desc_text.delete(1.0, tk.END)
            self.url_map.clear()
            self.current_ota_link = None
            self.copy_link_button.config(state=tk.DISABLED)
            self._update_dogfood_label(False)
            self.update_status("Parsing ChromiumOS fingerprint...")

            parsed = parse_fingerprint_chromeos(fingerprint)
            app_id = self.cros_appid_var.get().strip()
            if not app_id:
                raise ValueError("App ID is required for ChromiumOS check-in")

            self.update_status("Sending Omaha check-in request...")
            response_text, raw_bytes = perform_checkin_chromeos(fingerprint, app_id, hardware_class=parsed['hwid'])
            self._last_query_token = ''
            cros_req_xml = build_checkin_request_chromeos(fingerprint, app_id, hardware_class=parsed['hwid'])
            self._last_request_data = cros_req_xml.encode('utf-8')
            self._last_request_gz = None
            self._raw_request_populate()

            dogfood = False
            if raw_bytes and (b'droidfood' in raw_bytes.lower() or b'platform_dogfood' in raw_bytes.lower()):
                dogfood = True
            self._update_dogfood_label(dogfood)

            if not response_text:
                self.log_output("ERROR: Check-in failed - No response from server", 'error')
                self.status_icon_var.set("❌")
                self.update_status("Query failed", 'error')
            else:
                human_dump = prettify_xml(response_text)
                hex_dump = format_hex_dump(raw_bytes, header_label="RAW OMAHA XML RESPONSE")
                self._last_raw_bytes = raw_bytes
                self._raw_populate(human_dump, hex_dump)

                ota_link = find_ota_link_chromeos(response_text)

                build_info = {
                    'device_codename': parsed['board'],
                    'android_version': f"ChromeOS {parsed['version']} ({parsed['track']})",
                    'build_tag': parsed['version'],
                    'build_number': '',
                    'build_flavor': parsed['track'],
                    'security_keys': '',
                    'android_id': '',
                    'device_country': '',
                }

                if self.json_var.get():
                    json_data = {
                        'fingerprint': fingerprint,
                        'build_info': build_info,
                        'ota_link': ota_link,
                        'app_id': app_id,
                        'dogfood': dogfood,
                    }
                    output_str = json.dumps(json_data, indent=2)
                    self.log_output(output_str)
                    if self.html_frame:
                        self.html_frame.load_html(f"<pre>{output_str}</pre>")
                    elif self.desc_text:
                        self.desc_text.insert(tk.END, output_str)
                    if ota_link and ota_link.get('url'):
                        self.status_icon_var.set("✓")
                        self.status_icon_label.config(foreground='#006600')
                    else:
                        self.status_icon_var.set("❌")
                        self.status_icon_label.config(foreground='#cc0000')
                else:
                    self.format_and_log_output(fingerprint, {}, build_info, ota_link, dogfood)

                if self.save_var.get():
                    if self.json_var.get():
                        output_str = json.dumps({
                            'fingerprint': fingerprint,
                            'build_info': build_info,
                            'ota_link': ota_link,
                            'app_id': app_id,
                            'dogfood': dogfood,
                        }, indent=2)
                    else:
                        output_str = self.output_text.get(1.0, tk.END)
                    self.save_output(output_str, fingerprint)

                self.update_status("Query completed successfully", 'success')

        except ValueError as e:
            self.log_output(f"ERROR: {e}", 'error')
            self.status_icon_var.set("❌")
            self.update_status("Invalid fingerprint format", 'error')
        except Exception as e:
            self.log_output(f"ERROR: {e}", 'error')
            self.status_icon_var.set("❌")
            self.update_status(f"Error: {e}", 'error')
        finally:
            self.query_button.config(state=tk.NORMAL)
            self.keyscan_button.config(state=tk.NORMAL)
            self.clear_button.config(state=tk.NORMAL)
            self.fingerprint_entry.config(state=tk.NORMAL)

    def perform_query_xiaomi(self, fingerprint):
        try:
            self.output_text.delete(1.0, tk.END)
            self.raw_text.delete(1.0, tk.END)
            if self.html_frame:
                self.html_frame.load_html("")
            elif self.desc_text:
                self.desc_text.delete(1.0, tk.END)
            self.url_map.clear()
            self.current_ota_link = None
            self.copy_link_button.config(state=tk.DISABLED)
            self._update_dogfood_label(False)
            self.update_status("Parsing Xiaomi fingerprint...")

            parsed = parse_fingerprint_xiaomi(fingerprint)

            if not XIAOMI_CRYPTO_AVAILABLE:
                raise RuntimeError(
                    "The 'pycryptodome' package is required for Xiaomi OTA checks.\n"
                    "Install it with: pip install pycryptodome"
                )

            self.update_status("Sending MIUI update-check request...")
            decrypted, raw_text, xiaomi_req_body = perform_checkin_xiaomi(
                parsed['codename'], parsed['rom_version'], parsed['android_version']
            )
            self._last_query_token = ''
            self._last_request_data = xiaomi_req_body
            self._last_request_gz = None
            self._raw_request_populate()

            dogfood = False
            raw_bytes = raw_text.encode('utf-8')
            if raw_bytes and (b'droidfood' in raw_bytes.lower() or b'platform_dogfood' in raw_bytes.lower()):
                dogfood = True
            self._update_dogfood_label(dogfood)

            if not decrypted:
                self.log_output("ERROR: Check-in failed - No response from server", 'error')
                self.status_icon_var.set("❌")
                self.update_status("Query failed", 'error')
            else:
                human_dump = json.dumps(decrypted, indent=2, ensure_ascii=False)
                decrypted_bytes = json.dumps(decrypted, ensure_ascii=False).encode('utf-8')
                hex_dump = format_hex_dump(decrypted_bytes, header_label="RAW DECRYPTED MIUI RESPONSE")
                self._last_raw_bytes = raw_bytes if raw_bytes else decrypted_bytes
                self._raw_populate(human_dump, hex_dump)

                details = extract_build_details_xiaomi(decrypted)

                ota_dict = None
                if details.get('found') and details.get('download_url'):
                    ota_dict = {
                        'url': details['download_url'],
                        'title': details.get('version', ''),
                        'description': '',
                        'size': details.get('filesize', ''),
                        'precondition': '',
                        'postcondition': '',
                    }
                    changelog = details.get('changelog')
                    if changelog:
                        if isinstance(changelog, dict):
                            for key, value in changelog.items():
                                if isinstance(value, dict) and 'txt' in value:
                                    txt_list = value.get('txt', [])
                                    if txt_list:
                                        ota_dict['description'] = '\n'.join(txt_list)
                                        break
                                elif isinstance(value, list):
                                    ota_dict['description'] = '\n'.join(str(item) for item in value)
                                    break
                        elif isinstance(changelog, list):
                            ota_dict['description'] = '\n'.join(str(item) for item in changelog)
                        elif isinstance(changelog, str):
                            ota_dict['description'] = changelog

                if not details.get('found'):
                    build_info = {
                        'device_codename': parsed['codename'],
                        'android_version': parsed['android_version'],
                        'build_tag': parsed['rom_version'],
                        'build_number': '',
                        'build_flavor': '',
                        'security_keys': '',
                        'android_id': '',
                        'device_country': '',
                    }
                    self.log_output(
                        "No ROM information returned for this device/version combination.\n"
                        "Double-check the codename, ROM version and Android version.",
                        'error'
                    )
                    self.status_icon_var.set("❌")
                    self.status_icon_label.config(foreground='#cc0000')
                else:
                    bigver = details.get('bigversion_label')
                    build_info = {
                        'device_codename': details.get('device', parsed['codename']),
                        'android_version': f"Android {details.get('codebase', parsed['android_version'])}"
                                           + (f" ({bigver})" if bigver else ""),
                        'build_tag': details.get('version', parsed['rom_version']),
                        'build_number': details.get('branch', ''),
                        'build_flavor': 'beta' if details.get('is_beta') and details.get('is_beta') != '0' else 'stable',
                        'security_keys': details.get('md5', ''),
                        'android_id': '',
                        'device_country': '',
                    }

                    if self.json_var.get():
                        json_data = {
                            'fingerprint': fingerprint,
                            'build_info': build_info,
                            'ota_link': ota_dict,
                            'filename': details.get('filename'),
                            'filesize': details.get('filesize'),
                            'md5': details.get('md5'),
                            'dogfood': dogfood,
                        }
                        output_str = json.dumps(json_data, indent=2)
                        self.log_output(output_str)
                        if self.html_frame:
                            self.html_frame.load_html(f"<pre>{output_str}</pre>")
                        elif self.desc_text:
                            self.desc_text.insert(tk.END, output_str)
                        if ota_dict and ota_dict.get('url'):
                            self.status_icon_var.set("✓")
                            self.status_icon_label.config(foreground='#006600')
                        else:
                            self.status_icon_var.set("❌")
                            self.status_icon_label.config(foreground='#cc0000')
                    else:
                        self.format_and_log_output(fingerprint, {}, build_info, ota_dict, dogfood)
                        if details.get('md5'):
                            self.log_output(f"    MD5: {details.get('md5')}")

                    if self.save_var.get():
                        if self.json_var.get():
                            output_str = json.dumps({
                                'fingerprint': fingerprint,
                                'build_info': build_info,
                                'ota_link': ota_dict,
                                'filename': details.get('filename'),
                                'filesize': details.get('filesize'),
                                'md5': details.get('md5'),
                                'dogfood': dogfood,
                            }, indent=2)
                        else:
                            output_str = self.output_text.get(1.0, tk.END)
                        self.save_output(output_str, fingerprint)

                self.update_status("Query completed successfully", 'success')

        except ValueError as e:
            self.log_output(f"ERROR: {e}", 'error')
            self.status_icon_var.set("❌")
            self.update_status("Invalid fingerprint format", 'error')
        except Exception as e:
            self.log_output(f"ERROR: {e}", 'error')
            self.status_icon_var.set("❌")
            self.update_status(f"Error: {e}", 'error')
        finally:
            self.query_button.config(state=tk.NORMAL)
            self.keyscan_button.config(state=tk.NORMAL)
            self.clear_button.config(state=tk.NORMAL)
            self.fingerprint_entry.config(state=tk.NORMAL)

    def perform_query_playemu(self):
        import uuid
        try:
            self.output_text.delete(1.0, tk.END)
            self.raw_text.delete(1.0, tk.END)
            if self.html_frame:
                self.html_frame.load_html("")
            elif self.desc_text:
                self.desc_text.delete(1.0, tk.END)
            self.current_ota_link = None
            self.copy_link_button.config(state=tk.DISABLED)
            self.update_status("Sending Omaha Play Games Emulator request...")

            req_uuid = "{" + str(uuid.uuid4()).upper() + "}"
            sess_uuid = "{" + str(uuid.uuid4()).upper() + "}"

            payload = {
                "request": {
                    "@os": self._pemu_os_var.get(),
                    "@updater": self._pemu_updater_var.get(),
                    "acceptformat": self._pemu_acceptformat_var.get(),
                    "apps": [
                        {
                            "ap": self._pemu_ap_var.get(),
                            "appid": self._pemu_appid_var.get(),
                            "enabled": self._pemu_enabled_var.get(),
                            "installdate": int(self._pemu_installdate_var.get()),
                            "installsource": self._pemu_installsource_var.get(),
                            "ping": {
                                "rd": int(self._pemu_ping_rd_var.get())
                            },
                            "updatecheck": {
                                "sameversionupdate": self._pemu_sameverupdate_var.get()
                            },
                            "version": self._pemu_version_var.get()
                        }
                    ],
                    "arch": self._pemu_arch_var.get(),
                    "dedup": self._pemu_dedup_var.get(),
                    "domainjoined": self._pemu_domainjoined_var.get(),
                    "hw": {
                        "avx": self._pemu_hw_avx_var.get(),
                        "physmemory": int(self._pemu_hw_physmem_var.get()),
                        "sse": self._pemu_hw_sse_var.get(),
                        "sse2": self._pemu_hw_sse2_var.get(),
                        "sse3": self._pemu_hw_sse3_var.get(),
                        "sse41": self._pemu_hw_sse41_var.get(),
                        "sse42": self._pemu_hw_sse42_var.get(),
                        "ssse3": self._pemu_hw_ssse3_var.get()
                    },
                    "ismachine": self._pemu_ismachine_var.get(),
                    "os": {
                        "arch": self._pemu_os_arch_var.get(),
                        "platform": self._pemu_os_platform_var.get(),
                        "version": self._pemu_os_version_var.get()
                    },
                    "prodversion": self._pemu_prodversion_var.get(),
                    "protocol": self._pemu_protocol_var.get(),
                    "requestid": req_uuid,
                    "sessionid": sess_uuid,
                    "updaterversion": self._pemu_updaterversion_var.get(),
                    "wow64": self._pemu_wow64_var.get()
                }
            }

            body = json.dumps(payload).encode('utf-8')
            self._last_request_data = body
            self._last_request_gz = None
            self._raw_request_populate()

            url = "https://update.googleapis.com/service/update2/json"
            headers = {
                "Content-Type": "application/json",
                "User-Agent": "GoogleUpdater/" + self._pemu_prodversion_var.get()
            }

            req_obj = urllib.request.Request(url, data=body, headers=headers, method="POST")
            ctx = ssl.create_default_context()
            with urllib.request.urlopen(req_obj, timeout=15, context=ctx) as resp:
                raw_bytes = resp.read()

            raw_text = raw_bytes.decode("utf-8", errors="replace")
            clean_text = raw_text
            if clean_text.startswith(")]}'"):
                clean_text = clean_text[4:].lstrip("\n")

            human_dump = json.dumps(json.loads(clean_text), indent=2, ensure_ascii=False)
            hex_dump = format_hex_dump(raw_bytes, header_label="RAW OMAHA JSON RESPONSE")
            self._last_raw_bytes = raw_bytes
            self._raw_populate(human_dump, hex_dump)

            resp_data = json.loads(clean_text)
            ota_url, ota_size, ota_sha256, next_version, description_lines, other_urls = \
                _parse_playemu_response(resp_data)

            if ota_url is not None:
                desc_full = "\n".join(description_lines)

                ota_link = {
                    "url": ota_url,
                    "title": "",
                    "description": desc_full,
                    "size": ota_size,
                    "precondition": "",
                    "postcondition": "",
                }
                self.current_ota_link = ota_link
                self.copy_link_button.config(state=tk.NORMAL)
                self._set_ota_link_header(ota_url)

                build_info = {
                    "device_codename": "Play Games Emulator",
                    "android_version": next_version or "",
                    "build_tag": next_version or "",
                    "build_number": "",
                    "build_flavor": self._pemu_ap_var.get(),
                    "security_keys": "",
                    "android_id": "",
                    "device_country": "",
                }
                if self.json_var.get():
                    json_data = {
                        "version": next_version or "",
                        "url": ota_url,
                        "size": ota_size,
                        "sha256": ota_sha256,
                        "description": desc_full,
                        "other_urls": other_urls,
                        "ap": self._pemu_ap_var.get(),
                    }
                    output_str = json.dumps(json_data, indent=2, ensure_ascii=False)
                    self.log_output(output_str)
                    if self.html_frame:
                        self.html_frame.load_html(f"<pre>{output_str}</pre>")
                    elif self.desc_text:
                        self.desc_text.insert(tk.END, output_str)
                    self.status_icon_var.set("✓")
                    self.status_icon_label.config(foreground="#006600")
                else:
                    self.format_and_log_output("", {}, build_info, ota_link, False)

                if self.save_var.get():
                    if self.json_var.get():
                        content = output_str
                    else:
                        content = self.output_text.get(1.0, tk.END)
                    self.save_output(content, "playemu")

                try:
                    add_ota_record(
                        os_kind="playemu",
                        url=ota_url,
                        title=ota_link["title"],
                        description=desc_full,
                        size=ota_size,
                        locale="",
                        fingerprint="",
                    )
                except Exception:
                    pass

                self.status_icon_var.set("✓")
                self.status_icon_label.config(foreground="#006600")
                self.update_status("Query completed successfully", "success")
            else:
                self.log_output("No update available for the specified version/channel.", "info")
                self.status_icon_var.set("❌")
                self.status_icon_label.config(foreground="#cc0000")
                self.update_status("Query completed successfully", "success")

        except Exception as e:
            self.log_output("ERROR: {}".format(e), "error")
            self.status_icon_var.set("❌")
            self.update_status("Error: {}".format(e), "error")
        finally:
            self.query_button.config(state=tk.NORMAL)
            self.keyscan_button.config(state=tk.NORMAL)
            self.clear_button.config(state=tk.NORMAL)
            self.fingerprint_entry.config(state=tk.NORMAL)

    def _build_playemu_editor(self, parent):
        def _cb(p, lbl, var, vals, w=14):
            ttk.Label(p, text=lbl).pack(side=tk.LEFT, padx=(0, 2))
            cb = ttk.Combobox(p, textvariable=var, values=vals, width=w)
            cb.pack(side=tk.LEFT, padx=(0, 8))

        def _entry(p, lbl, var, w=12):
            ttk.Label(p, text=lbl).pack(side=tk.LEFT, padx=(0, 2))
            ttk.Entry(p, textvariable=var, width=w).pack(side=tk.LEFT, padx=(0, 8))

        def _chk(p, lbl, var):
            ttk.Checkbutton(p, text=lbl, variable=var).pack(side=tk.LEFT, padx=(0, 8))

        self._pemu_os_var = tk.StringVar(value="win")
        self._pemu_updater_var = tk.StringVar(value="GoogleUpdater")
        self._pemu_acceptformat_var = tk.StringVar(value="crx3,download,puff,run,xz,zucc")
        self._pemu_protocol_var = tk.StringVar(value="4.0")
        self._pemu_prodversion_var = tk.StringVar(value="152.0.7933.0")
        self._pemu_updaterversion_var = tk.StringVar(value="152.0.7933.0")
        self._pemu_arch_var = tk.StringVar(value="x86")
        self._pemu_dedup_var = tk.StringVar(value="cr")
        self._pemu_domainjoined_var = tk.BooleanVar(value=False)
        self._pemu_ismachine_var = tk.BooleanVar(value=True)
        self._pemu_wow64_var = tk.BooleanVar(value=True)
        self._pemu_appid_var = tk.StringVar(value="{c601e9a4-03b0-4188-843e-80058bf16ef9}")
        self._pemu_ap_var = tk.StringVar(value="prod")
        self._pemu_version_var = tk.StringVar(value="0.0.0.0")
        self._pemu_enabled_var = tk.BooleanVar(value=True)
        self._pemu_installdate_var = tk.StringVar(value="-1")
        self._pemu_installsource_var = tk.StringVar(value="taggedmi")
        self._pemu_ping_rd_var = tk.StringVar(value="-1")
        self._pemu_sameverupdate_var = tk.BooleanVar(value=True)
        self._pemu_os_arch_var = tk.StringVar(value="x86_64")
        self._pemu_os_platform_var = tk.StringVar(value="Windows")
        self._pemu_os_version_var = tk.StringVar(value="10.0.22631.7376")
        self._pemu_hw_physmem_var = tk.StringVar(value="15")
        self._pemu_hw_avx_var = tk.BooleanVar(value=True)
        self._pemu_hw_sse_var = tk.BooleanVar(value=True)
        self._pemu_hw_sse2_var = tk.BooleanVar(value=True)
        self._pemu_hw_sse3_var = tk.BooleanVar(value=True)
        self._pemu_hw_sse41_var = tk.BooleanVar(value=True)
        self._pemu_hw_sse42_var = tk.BooleanVar(value=True)
        self._pemu_hw_ssse3_var = tk.BooleanVar(value=True)

        r1 = ttk.Frame(parent)
        r1.pack(fill=tk.X, pady=1)
        _cb(r1, "@os:", self._pemu_os_var, ["win", "mac", "linux", "cros", "android"], 6)
        _cb(r1, "@updater:", self._pemu_updater_var, ["GoogleUpdater", "Omaha", "Keystone"], 14)
        _cb(r1, "acceptformat:", self._pemu_acceptformat_var,
            ["crx3,download,puff,run,xz,zucc", "crx3,download,puff,run", "crx3,download"], 28)
        _cb(r1, "arch:", self._pemu_arch_var, ["x86", "x64", "arm64"], 6)
        _cb(r1, "dedup:", self._pemu_dedup_var, ["cr", "uid", "none"], 5)

        r2 = ttk.Frame(parent)
        r2.pack(fill=tk.X, pady=1)
        _entry(r2, "prodversion:", self._pemu_prodversion_var, 16)
        _entry(r2, "updaterversion:", self._pemu_updaterversion_var, 16)
        _cb(r2, "protocol:", self._pemu_protocol_var, ["4.0", "3.1", "3.0", "2.0"], 5)
        _chk(r2, "ismachine", self._pemu_ismachine_var)
        _chk(r2, "domainjoined", self._pemu_domainjoined_var)
        _chk(r2, "wow64", self._pemu_wow64_var)

        r3 = ttk.Frame(parent)
        r3.pack(fill=tk.X, pady=1)
        _cb(r3, "appid:", self._pemu_appid_var,
            ["{c601e9a4-03b0-4188-843e-80058bf16ef9}"], 36)
        _cb(r3, "ap:", self._pemu_ap_var, ["prod", "dogfood"], 8)
        _entry(r3, "version:", self._pemu_version_var, 10)
        _chk(r3, "enabled", self._pemu_enabled_var)
        _chk(r3, "sameversionupdate", self._pemu_sameverupdate_var)

        r4 = ttk.Frame(parent)
        r4.pack(fill=tk.X, pady=1)
        _cb(r4, "installdate:", self._pemu_installdate_var, ["-1", "0", "1"], 4)
        _cb(r4, "installsource:", self._pemu_installsource_var,
            ["taggedmi", "update", "ondemand", "scheduler"], 12)
        _cb(r4, "ping.rd:", self._pemu_ping_rd_var, ["-1", "0", "1"], 4)

        r5 = ttk.Frame(parent)
        r5.pack(fill=tk.X, pady=1)
        _cb(r5, "os.platform:", self._pemu_os_platform_var,
            ["Windows", "Mac", "Linux", "ChromeOS"], 10)
        _cb(r5, "os.arch:", self._pemu_os_arch_var,
            ["x86_64", "x86", "arm64", "aarch64"], 10)
        _entry(r5, "os.version:", self._pemu_os_version_var, 16)
        _cb(r5, "RAM (GB):", self._pemu_hw_physmem_var,
            ["4", "8", "15", "16", "32", "64"], 4)

        r6 = ttk.Frame(parent)
        r6.pack(fill=tk.X, pady=1)
        ttk.Label(r6, text="CPU caps:").pack(side=tk.LEFT, padx=(0, 4))
        for lbl, var in [("AVX", self._pemu_hw_avx_var), ("SSE", self._pemu_hw_sse_var),
                         ("SSE2", self._pemu_hw_sse2_var), ("SSE3", self._pemu_hw_sse3_var),
                         ("SSSE3", self._pemu_hw_ssse3_var), ("SSE4.1", self._pemu_hw_sse41_var),
                         ("SSE4.2", self._pemu_hw_sse42_var)]:
            _chk(r6, lbl, var)

        r7 = ttk.Frame(parent)
        r7.pack(fill=tk.X, pady=(3, 0))
        ttk.Button(r7, text="⟳ Reset", command=self._playemu_reset).pack(side=tk.RIGHT)

    def _build_playemu_tab(self):
        pass

    def _playemu_send(self):
        self.query_button.config(state=tk.DISABLED)
        self.keyscan_button.config(state=tk.DISABLED)
        self.clear_button.config(state=tk.DISABLED)
        self.fingerprint_entry.config(state=tk.DISABLED)
        t = threading.Thread(target=self.perform_query_playemu, daemon=True)
        t.start()

    def _playemu_reset(self):
        self._pemu_os_var.set("win")
        self._pemu_updater_var.set("GoogleUpdater")
        self._pemu_acceptformat_var.set("crx3,download,puff,run,xz,zucc")
        self._pemu_protocol_var.set("4.0")
        self._pemu_prodversion_var.set("152.0.7933.0")
        self._pemu_updaterversion_var.set("152.0.7933.0")
        self._pemu_arch_var.set("x86")
        self._pemu_dedup_var.set("cr")
        self._pemu_domainjoined_var.set(False)
        self._pemu_ismachine_var.set(True)
        self._pemu_wow64_var.set(True)
        self._pemu_appid_var.set("{c601e9a4-03b0-4188-843e-80058bf16ef9}")
        self._pemu_ap_var.set("prod")
        self._pemu_version_var.set("0.0.0.0")
        self._pemu_enabled_var.set(True)
        self._pemu_installdate_var.set("-1")
        self._pemu_installsource_var.set("taggedmi")
        self._pemu_ping_rd_var.set("-1")
        self._pemu_sameverupdate_var.set(True)
        self._pemu_os_arch_var.set("x86_64")
        self._pemu_os_platform_var.set("Windows")
        self._pemu_os_version_var.set("10.0.22631.7376")
        self._pemu_hw_physmem_var.set("15")
        self._pemu_hw_avx_var.set(True)
        self._pemu_hw_sse_var.set(True)
        self._pemu_hw_sse2_var.set(True)
        self._pemu_hw_sse3_var.set(True)
        self._pemu_hw_sse41_var.set(True)
        self._pemu_hw_sse42_var.set(True)
        self._pemu_hw_ssse3_var.set(True)

    def save_output(self, content, fingerprint):
        try:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            default_name = f"ota_report_{timestamp}.txt"

            file_path = filedialog.asksaveasfilename(
                defaultextension=".txt",
                initialfile=default_name,
                filetypes=[("Text files", "*.txt"), ("JSON files", "*.json"), ("All files", "*.*")]
            )

            if file_path:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(content)
                self.update_status(f"Saved to {file_path}", 'success')
        except Exception as e:
            self.update_status(f"Save failed: {e}", 'error')

    @staticmethod
    def _strip_simple_html(text):
        return (text.replace('<br>', '\n').replace('<p>', '').replace('</p>', '')
                .replace('<strong>', '').replace('</strong>', '')
                .replace('<a href="', '').replace('">', '').replace('</a>', ''))

    def format_and_log_output(self, fingerprint, settings, build_info, ota_link, dogfood=False):
        self.log_output("=" * 75, 'header')
        self.log_output("DEVICE & BUILD INFORMATION", 'header')
        self.log_output("=" * 75, 'header')

        self.log_output("\n[INPUT]", 'section')
        is_cros = self.os_mode_var.get() == "chromeos"
        self.log_output(f"  Device Codename:   {build_info['device_codename']}", 'info')
        self.log_output(f"  Android Version:   {build_info['android_version']}", 'info')
        self.log_output(f"  Build Tag:         {build_info['build_tag']}", 'info')
        if not is_cros:
            self.log_output(f"  Build Number:      {build_info['build_number']}", 'info')
        self.log_output(f"  Build Flavor:      {build_info['build_flavor']}", 'info')
        if not is_cros:
            self.log_output(f"  Security Keys:     {build_info['security_keys']}", 'info')

        self.log_output("\n[SERVER RESPONSE]", 'section')
        if settings:
            self.log_output(f"  Total Settings:    {len(settings)}", 'info')
        if build_info.get('android_id'):
            self.log_output(f"  Android ID:        {build_info['android_id']}", 'info')
        if build_info.get('device_country'):
            self.log_output(f"  Device Country:    {build_info['device_country']}", 'info')

        self.log_output("\n[OTA UPDATE]", 'section')
        if ota_link and ota_link.get('url'):
            self.status_icon_var.set("✓")
            self.status_icon_label.config(foreground='#006600')

            self.output_text.insert(tk.END, f"  Status:            ", 'info')
            self.output_text.insert(tk.END, "[OK] Update Available\n", 'success')

            if ota_link.get('title'):
                self.log_output(f"  Title:             {ota_link['title']}", 'info')

            self.log_output(f"\n  Target URL:", 'info')
            self.output_text.insert(tk.END, "    ", 'info')
            self.log_link(ota_link['url'], ota_link['url'])
            self.output_text.insert(tk.END, '\n', 'info')

            self.current_ota_link = ota_link['url']
            self.current_ota_precondition = ota_link.get('precondition', '')
            self.current_ota_postcondition = ota_link.get('postcondition', '')
            self._set_ota_link_header(ota_link['url'])
            self.copy_link_button.config(state=tk.NORMAL)
            self._meta_autofill_url(ota_link['url'], settings.get('update_token', ''))

            try:
                add_ota_record(
                    os_kind=self.os_mode_var.get(),
                    url=ota_link.get('url', ''),
                    title=ota_link.get('title', ''),
                    description=ota_link.get('description', ''),
                    size=ota_link.get('size', ''),
                    locale=self.locale_var.get().strip() if hasattr(self, 'locale_var') else '',
                    fingerprint=fingerprint,
                )
            except Exception:
                pass

            desc_parts = []
            if ota_link.get('title'):
                desc_parts.append(f"<strong>Title:</strong> {ota_link['title']}<br>")
            if ota_link.get('description'):
                desc_parts.append(ota_link['description'])
            if ota_link.get('size'):
                desc_parts.append(f"<br><strong>Size:</strong> {ota_link['size']}")
            desc_html = "".join(desc_parts) if desc_parts else "(No description available)"

            if self.html_frame:
                html_content = f"""
                <html>
                <head>
                    <style>
                        body {{ font-family: Arial, sans-serif; line-height: 1.6; padding: 20px; }}
                        strong {{ color: #333; }}
                        a {{ color: #0066cc; text-decoration: none; }}
                        a:hover {{ text-decoration: underline; }}
                        p {{ margin: 10px 0; }}
                        br {{ margin: 5px 0; }}
                    </style>
                </head>
                <body>
                {desc_html}
                </body>
                </html>
                """
                self.html_frame.load_html(html_content)
            elif self.desc_text:
                desc_plain = self._strip_simple_html(desc_html)
                self.desc_text.insert(tk.END, desc_plain)

            self.log_output(f"\n  Description:", 'info')
            if ota_link.get('title'):
                self.log_output(f"    Title: {ota_link['title']}", 'info')
            if ota_link.get('description'):
                desc_plain = self._strip_simple_html(ota_link['description'])
                if len(desc_plain) > 70:
                    words = desc_plain.split()
                    lines = []
                    current_line = []
                    for word in words:
                        if len(' '.join(current_line + [word])) <= 70:
                            current_line.append(word)
                        else:
                            if current_line:
                                lines.append('    ' + ' '.join(current_line))
                            current_line = [word]
                    if current_line:
                        lines.append('    ' + ' '.join(current_line))
                    for line in lines:
                        self.log_output(line, 'info')
                else:
                    self.log_output(f"    {desc_plain}", 'info')
            if ota_link.get('size'):
                self.log_output(f"    Size: {ota_link['size']}", 'info')

            if ota_link.get('precondition'):
                self.log_output(f"\n  Precondition:", 'info')
                self.log_output(f"    {ota_link['precondition']}", 'info')

            if ota_link.get('postcondition'):
                self.log_output(f"\n  Postcondition:", 'info')
                self.log_output(f"    {ota_link['postcondition']}", 'info')
        else:
            self.status_icon_var.set("❌")
            self.status_icon_label.config(foreground='#cc0000')
            self.output_text.insert(tk.END, f"  Status:            ", 'info')
            self.output_text.insert(tk.END, "[NONE] No Update Available\n", 'error')
            if self.html_frame:
                self.html_frame.load_html("<p>No OTA update available for this device.</p>")
            elif self.desc_text:
                self.desc_text.insert(tk.END, "No OTA update available for this device.")

        self.log_output("\n" + "=" * 75, 'header')

    def _build_rawreq_tab(self):
        outer = ttk.Frame(self.rawreq_frame)
        outer.pack(fill=tk.BOTH, expand=True)

        canvas = tk.Canvas(outer, highlightthickness=0)
        vsb = ttk.Scrollbar(outer, orient=tk.VERTICAL, command=canvas.yview)
        canvas.configure(yscrollcommand=vsb.set)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        inner = ttk.Frame(canvas, padding=10)
        inner_id = canvas.create_window((0, 0), window=inner, anchor='nw')

        def _on_inner_configure(e):
            canvas.configure(scrollregion=canvas.bbox('all'))

        def _on_canvas_configure(e):
            canvas.itemconfig(inner_id, width=e.width)
        inner.bind('<Configure>', _on_inner_configure)
        canvas.bind('<Configure>', _on_canvas_configure)

        def _on_mousewheel(e):
            canvas.yview_scroll(int(-1 * (e.delta / 120)), 'units')
        canvas.bind_all('<MouseWheel>', _on_mousewheel)

        proto_lf = ttk.LabelFrame(inner, text="Protocol", padding=6)
        proto_lf.pack(fill=tk.X, pady=(0, 6))
        self._rawreq_proto_var = tk.StringVar(value="checkin")
        ttk.Radiobutton(proto_lf, text="Android Checkin  (protobuf / gzip POST)",
                        variable=self._rawreq_proto_var, value="checkin",
                        command=self._rawreq_on_proto_change).pack(side=tk.LEFT, padx=(0, 20))
        ttk.Radiobutton(proto_lf, text="Omaha  (XML POST — ChromeOS / AOSP)",
                        variable=self._rawreq_proto_var, value="omaha",
                        command=self._rawreq_on_proto_change).pack(side=tk.LEFT)

        self._rawreq_url_var = tk.StringVar(value="http://android.googleapis.com/checkin")
        url_lf = ttk.LabelFrame(inner, text="Endpoint URL", padding=6)
        url_lf.pack(fill=tk.X, pady=(0, 6))
        url_entry_row = ttk.Frame(url_lf)
        url_entry_row.pack(fill=tk.X)
        ttk.Entry(url_entry_row, textvariable=self._rawreq_url_var, width=60,
                  font=('Courier', 9)).pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Button(url_entry_row, text="Use current checkin URL",
                   command=self._rawreq_use_current_url).pack(side=tk.LEFT, padx=(6, 0))
        ttk.Button(url_entry_row, text="Omaha default",
                   command=lambda: self._rawreq_url_var.set(CROS_AUSERVER)).pack(side=tk.LEFT, padx=(4, 0))

        mode_lf = ttk.LabelFrame(inner, text="Input mode", padding=6)
        mode_lf.pack(fill=tk.X, pady=(0, 6))
        self._rawreq_mode_var = tk.StringVar(value="text")
        ttk.Radiobutton(mode_lf, text="Type / paste bytes",
                        variable=self._rawreq_mode_var, value="text",
                        command=self._rawreq_toggle_mode).pack(side=tk.LEFT, padx=(0, 16))
        ttk.Radiobutton(mode_lf, text="Import file  (.gz / .bin / .xml / any)",
                        variable=self._rawreq_mode_var, value="file",
                        command=self._rawreq_toggle_mode).pack(side=tk.LEFT)

        self._rawreq_input_frame = ttk.LabelFrame(
            inner, text="Request body  (hex, base64, XML, or raw bytes)", padding=6)
        self._rawreq_input_frame.pack(fill=tk.X, pady=(0, 4))

        fmt_row = ttk.Frame(self._rawreq_input_frame)
        fmt_row.pack(fill=tk.X, pady=(0, 4))
        ttk.Label(fmt_row, text="Format:").pack(side=tk.LEFT, padx=(0, 6))
        self._rawreq_fmt_var = tk.StringVar(value="hex")
        ttk.Radiobutton(fmt_row, text="Hex", variable=self._rawreq_fmt_var, value="hex").pack(side=tk.LEFT, padx=(0, 8))
        ttk.Radiobutton(fmt_row, text="Base64", variable=self._rawreq_fmt_var, value="base64").pack(side=tk.LEFT, padx=(0, 8))
        ttk.Radiobutton(fmt_row, text="Raw bytes (already gz-compressed)",
                        variable=self._rawreq_fmt_var, value="raw").pack(side=tk.LEFT, padx=(0, 8))
        ttk.Radiobutton(fmt_row, text="XML text (Omaha)",
                        variable=self._rawreq_fmt_var, value="xml").pack(side=tk.LEFT)

        self._rawreq_text = scrolledtext.ScrolledText(
            self._rawreq_input_frame, width=90, height=7,
            font=('Courier', 9), wrap=tk.NONE)
        self._rawreq_text.pack(fill=tk.X)

        paste_row = ttk.Frame(self._rawreq_input_frame)
        paste_row.pack(fill=tk.X, pady=(4, 0))
        ttk.Button(paste_row, text="Paste from clipboard",
                   command=self._rawreq_paste).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(paste_row, text="Clear",
                   command=lambda: self._rawreq_text.delete(1.0, tk.END)).pack(side=tk.LEFT)

        self._rawreq_file_frame = ttk.LabelFrame(
            inner, text="Import file", padding=6)

        file_row = ttk.Frame(self._rawreq_file_frame)
        file_row.pack(fill=tk.X)
        self._rawreq_filepath_var = tk.StringVar(value="")
        ttk.Entry(file_row, textvariable=self._rawreq_filepath_var, width=60,
                  font=('Courier', 9), state='readonly').pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Button(file_row, text="Browse…",
                   command=self._rawreq_browse).pack(side=tk.LEFT, padx=(6, 0))
        self._rawreq_file_info_var = tk.StringVar(value="")
        ttk.Label(self._rawreq_file_frame, textvariable=self._rawreq_file_info_var,
                  foreground='#555555', font=('TkDefaultFont', 8)).pack(anchor='w', pady=(2, 0))

        send_lf = ttk.Frame(inner)
        send_lf.pack(fill=tk.X, pady=(6, 6))
        self._rawreq_send_btn = ttk.Button(send_lf, text="▶  Send Request",
                                           command=self._rawreq_send)
        self._rawreq_send_btn.pack(side=tk.LEFT, padx=(0, 12))
        self._rawreq_status_var = tk.StringVar(value="")
        ttk.Label(send_lf, textvariable=self._rawreq_status_var,
                  foreground='#0066cc').pack(side=tk.LEFT)

        resp_outer = ttk.LabelFrame(outer, text="Response", padding=6)
        resp_outer.pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))

        resp_btn_row = ttk.Frame(resp_outer)
        resp_btn_row.pack(fill=tk.X, pady=(0, 4))
        ttk.Button(resp_btn_row, text="Copy parsed",
                   command=self._rawreq_copy_parsed).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(resp_btn_row, text="Copy raw hex",
                   command=self._rawreq_copy_raw).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(resp_btn_row, text="Save response…",
                   command=self._rawreq_save_response).pack(side=tk.LEFT)

        self._rawreq_resp_nb = ttk.Notebook(resp_outer)
        self._rawreq_resp_nb.pack(fill=tk.BOTH, expand=True)

        parsed_frame = ttk.Frame(self._rawreq_resp_nb)
        self._rawreq_resp_nb.add(parsed_frame, text="Parsed / XML")
        self._rawreq_parsed_text = scrolledtext.ScrolledText(
            parsed_frame, font=('Courier', 9), wrap=tk.WORD,
            bg='white', fg='#222222')
        self._rawreq_parsed_text.pack(fill=tk.BOTH, expand=True)

        raw_frame = ttk.Frame(self._rawreq_resp_nb)
        self._rawreq_resp_nb.add(raw_frame, text="Raw bytes (hex dump)")
        self._rawreq_raw_text = scrolledtext.ScrolledText(
            raw_frame, font=('Courier', 9), wrap=tk.NONE,
            bg='#1e1e1e', fg='#d4d4d4')
        self._rawreq_raw_text.pack(fill=tk.BOTH, expand=True)

        self._rawreq_last_response_bytes = b''

    def _rawreq_on_proto_change(self):
        proto = self._rawreq_proto_var.get()
        if proto == "checkin":
            self._rawreq_url_var.set("http://android.googleapis.com/checkin")
            self._rawreq_fmt_var.set("hex")
        else:
            self._rawreq_url_var.set(CROS_AUSERVER)
            self._rawreq_fmt_var.set("xml")
            self._rawreq_mode_var.set("text")
            self._rawreq_toggle_mode()

    def _rawreq_toggle_mode(self):
        mode = self._rawreq_mode_var.get()
        if mode == "text":
            self._rawreq_file_frame.pack_forget()
            self._rawreq_input_frame.pack(fill=tk.X, pady=(0, 4))
        else:
            self._rawreq_input_frame.pack_forget()
            self._rawreq_file_frame.pack(fill=tk.X, pady=(0, 4))

    def _rawreq_use_current_url(self):
        try:
            url = self.checkin_url_var.get().strip()
            if url:
                self._rawreq_url_var.set(url)
        except Exception:
            pass

    def _rawreq_paste(self):
        try:
            self._rawreq_text.delete(1.0, tk.END)
            self._rawreq_text.insert(tk.END, self.root.clipboard_get())
        except Exception:
            pass

    def _rawreq_browse(self):
        path = filedialog.askopenfilename(
            title="Select request file",
            filetypes=[
                ("GZip files", "*.gz"),
                ("Binary files", "*.bin"),
                ("XML files", "*.xml"),
                ("All files", "*.*"),
            ])
        if not path:
            return
        self._rawreq_filepath_var.set(path)
        size = os.path.getsize(path)
        ext = os.path.splitext(path)[1].lower()
        hint = ""
        if ext == ".gz":
            hint = "  →  gzip-compressed protobuf (Checkin)"
        elif ext == ".xml":
            hint = "  →  XML (Omaha)"
        self._rawreq_file_info_var.set(f"{size:,} bytes{hint}")

    def _rawreq_copy_parsed(self):
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(self._rawreq_parsed_text.get(1.0, tk.END))
        except Exception:
            pass

    def _rawreq_copy_raw(self):
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(self._rawreq_raw_text.get(1.0, tk.END))
        except Exception:
            pass

    def _rawreq_save_response(self):
        if not self._rawreq_last_response_bytes:
            messagebox.showinfo("Save response", "No response data to save yet.")
            return
        path = filedialog.asksaveasfilename(
            title="Save response bytes",
            defaultextension=".bin",
            filetypes=[("Binary", "*.bin"), ("GZip", "*.gz"),
                       ("XML", "*.xml"), ("All files", "*.*")])
        if path:
            try:
                with open(path, 'wb') as f:
                    f.write(self._rawreq_last_response_bytes)
            except Exception as e:
                messagebox.showerror("Save error", str(e))

    def _rawreq_send(self):
        url = self._rawreq_url_var.get().strip()
        if not url:
            messagebox.showerror("Send Raw Request", "Please enter an endpoint URL.")
            return

        proto = self._rawreq_proto_var.get()
        mode = self._rawreq_mode_var.get()
        raw_bytes = None
        is_xml = False

        if mode == "file":
            path = self._rawreq_filepath_var.get().strip()
            if not path or not os.path.isfile(path):
                messagebox.showerror("Send Raw Request", "Please select a valid file.")
                return
            try:
                with open(path, 'rb') as f:
                    raw_bytes = f.read()
            except Exception as e:
                messagebox.showerror("Send Raw Request", f"Cannot read file: {e}")
                return
            ext = os.path.splitext(path)[1].lower()
            is_xml = (ext == ".xml") or (proto == "omaha")
        else:
            text = self._rawreq_text.get(1.0, tk.END).strip()
            if not text:
                messagebox.showerror("Send Raw Request", "Please enter request body.")
                return
            fmt = self._rawreq_fmt_var.get()
            if fmt == "xml":
                raw_bytes = text.encode('utf-8')
                is_xml = True
            elif fmt == "hex":
                try:
                    raw_bytes = bytes.fromhex(re.sub(r'\s+', '', text))
                except Exception as e:
                    messagebox.showerror("Send Raw Request", f"Invalid hex: {e}")
                    return
            elif fmt == "base64":
                try:
                    raw_bytes = base64.b64decode(text)
                except Exception as e:
                    messagebox.showerror("Send Raw Request", f"Invalid base64: {e}")
                    return
            else:
                raw_bytes = text.encode('latin-1')

        self._rawreq_send_btn.config(state=tk.DISABLED)
        self._rawreq_status_var.set("Sending…")
        self._rawreq_parsed_text.delete(1.0, tk.END)
        self._rawreq_raw_text.delete(1.0, tk.END)
        self._rawreq_last_response_bytes = b''

        threading.Thread(
            target=self._rawreq_worker,
            args=(url, raw_bytes, is_xml),
            daemon=True).start()

    def _rawreq_worker(self, url, raw_bytes, is_xml):
        try:
            if is_xml:
                send_bytes = raw_bytes
                headers = {
                    'Content-Type': 'application/xml',
                    'User-Agent': 'ChromeOSUpdateEngine/0.1.0.0',
                }
            else:
                if raw_bytes[:2] == b'\x1f\x8b':
                    send_bytes = raw_bytes
                else:
                    send_bytes = gzip.compress(raw_bytes)
                headers = {
                    'Accept-Encoding': 'gzip, deflate',
                    'Content-Encoding': 'gzip',
                    'Content-Type': 'application/x-protobuffer',
                    'User-Agent': 'Dalvik/2.1.0 (Linux; U; Android 14; Generic Build/UQ1A.000000.000)',
                }

            req = urllib.request.Request(url, data=send_bytes, headers=headers, method='POST')
            with urllib.request.urlopen(req, timeout=20) as resp:
                resp_bytes = resp.read()
                resp_headers = dict(resp.headers)

            self._rawreq_last_response_bytes = resp_bytes

            if is_xml:
                resp_text = resp_bytes.decode('utf-8', errors='replace')
                self.root.after(0, self._rawreq_display_xml,
                                resp_bytes, resp_text, resp_headers, len(send_bytes))
            else:
                try:
                    resp_decoded = gzip.decompress(resp_bytes)
                except Exception:
                    resp_decoded = resp_bytes
                try:
                    parsed = parse_protobuf_response(resp_decoded)
                except Exception as e:
                    parsed = {"parse_error": str(e)}
                self.root.after(0, self._rawreq_display_checkin,
                                resp_bytes, resp_decoded, parsed, resp_headers, len(send_bytes))
        except Exception as e:
            self.root.after(0, self._rawreq_error, str(e))

    def _rawreq_display_checkin(self, resp_bytes, resp_decoded, parsed, resp_headers, sent_bytes):
        self._rawreq_send_btn.config(state=tk.NORMAL)
        self._rawreq_status_var.set(
            f"✅  {len(resp_bytes)} bytes received  |  sent {sent_bytes} bytes")

        pt = self._rawreq_parsed_text
        pt.delete(1.0, tk.END)
        pt.tag_config('hdr', foreground='#005580', font=('Courier', 9, 'bold'))
        pt.tag_config('key', foreground='#0066cc')
        pt.tag_config('val', foreground='#222222')
        pt.tag_config('ota', foreground='#008800', font=('Courier', 9, 'bold'))

        pt.insert(tk.END, "=" * 62 + "\n  CHECKIN RESPONSE\n" + "=" * 62 + "\n", 'hdr')
        pt.insert(tk.END, "\nHTTP response headers:\n", 'key')
        for k, v in resp_headers.items():
            pt.insert(tk.END, f"  {k}: {v}\n", 'val')
        pt.insert(tk.END, "\nParsed protobuf fields:\n", 'key')
        if parsed:
            for k, v in sorted(parsed.items()):
                tag = 'ota' if k == 'update_url' else 'val'
                pt.insert(tk.END, f"  {k}: ", 'key')
                pt.insert(tk.END, f"{v}\n", tag)
            ota = find_ota_link(parsed)
            if ota and ota.get('url'):
                pt.insert(tk.END, "\n" + "─" * 62 + "\n", 'hdr')
                pt.insert(tk.END, "  ✅ OTA UPDATE FOUND\n", 'ota')
                pt.insert(tk.END, f"  URL   : {ota['url']}\n", 'ota')
                if ota.get('title'):
                    pt.insert(tk.END, f"  Title : {ota['title']}\n", 'val')
                if ota.get('size'):
                    pt.insert(tk.END, f"  Size  : {ota['size']}\n", 'val')
                pt.insert(tk.END, "─" * 62 + "\n", 'hdr')
        else:
            pt.insert(tk.END, "  (no fields decoded)\n", 'val')

        self._rawreq_fill_hex(resp_decoded)
        try:
            self._rawreq_resp_nb.select(0)
        except Exception:
            pass

    def _rawreq_display_xml(self, resp_bytes, resp_text, resp_headers, sent_bytes):
        self._rawreq_send_btn.config(state=tk.NORMAL)
        self._rawreq_status_var.set(
            f"✅  {len(resp_bytes)} bytes received  |  sent {sent_bytes} bytes")

        pt = self._rawreq_parsed_text
        pt.delete(1.0, tk.END)
        pt.tag_config('hdr', foreground='#005580', font=('Courier', 9, 'bold'))
        pt.tag_config('key', foreground='#0066cc')
        pt.tag_config('val', foreground='#222222')
        pt.tag_config('ota', foreground='#008800', font=('Courier', 9, 'bold'))

        pt.insert(tk.END, "=" * 62 + "\n  OMAHA RESPONSE\n" + "=" * 62 + "\n", 'hdr')
        pt.insert(tk.END, "\nHTTP response headers:\n", 'key')
        for k, v in resp_headers.items():
            pt.insert(tk.END, f"  {k}: {v}\n", 'val')
        pt.insert(tk.END, "\nXML body:\n", 'key')
        try:
            pretty = prettify_xml(resp_text)
        except Exception:
            pretty = resp_text
        pt.insert(tk.END, pretty + "\n", 'val')

        try:
            ota = find_ota_link_chromeos(resp_text)
            if ota and ota.get('url'):
                pt.insert(tk.END, "\n" + "─" * 62 + "\n", 'hdr')
                pt.insert(tk.END, "  ✅ OTA UPDATE FOUND\n", 'ota')
                pt.insert(tk.END, f"  URL   : {ota['url']}\n", 'ota')
                if ota.get('version'):
                    pt.insert(tk.END, f"  Version : {ota['version']}\n", 'val')
                pt.insert(tk.END, "─" * 62 + "\n", 'hdr')
        except Exception:
            pass

        self._rawreq_fill_hex(resp_bytes)
        try:
            self._rawreq_resp_nb.select(0)
        except Exception:
            pass

    def _rawreq_fill_hex(self, data):
        rt = self._rawreq_raw_text
        rt.delete(1.0, tk.END)
        lines = []
        for i in range(0, len(data), 16):
            chunk = data[i:i+16]
            hex_part = ' '.join(f'{b:02x}' for b in chunk)
            asc_part = ''.join(chr(b) if 32 <= b < 127 else '.' for b in chunk)
            lines.append(f"{i:08x}  {hex_part:<48}  |{asc_part}|")
        rt.insert(tk.END, '\n'.join(lines))

    def _rawreq_error(self, msg):
        self._rawreq_send_btn.config(state=tk.NORMAL)
        self._rawreq_status_var.set(f"❌  Error: {msg}")
        self._rawreq_parsed_text.delete(1.0, tk.END)
        self._rawreq_parsed_text.insert(tk.END, f"Request failed:\n\n{msg}")

    def on_keyscan_click(self):
        fingerprint = self.fingerprint_var.get().strip()
        if not fingerprint:
            messagebox.showerror("Error", "Please enter a fingerprint")
            return
        if '/' not in fingerprint:
            messagebox.showerror("Error", "Invalid fingerprint format")
            return

        self.query_button.config(state=tk.DISABLED)
        self.keyscan_button.config(state=tk.DISABLED)
        self.clear_button.config(state=tk.DISABLED)
        self.fingerprint_entry.config(state=tk.DISABLED)
        self.keyscan_stop_button.config(state=tk.NORMAL)
        self._keyscan_stop_event.clear()

        self.keyscan_thread = threading.Thread(target=self.perform_keyscan, args=(fingerprint,), daemon=True)
        self.keyscan_thread.start()

    def on_stop_scan_click(self):
        self._keyscan_stop_event.set()
        self._otachain_stop_event.set()
        self.keyscan_stop_button.config(state=tk.DISABLED)
        self.update_status("Stopping…")

    def perform_keyscan(self, fingerprint):
        try:
            self.output_text.delete(1.0, tk.END)
            self.raw_text.delete(1.0, tk.END)
            if self.html_frame:
                self.html_frame.load_html("")
            elif self.desc_text:
                self.desc_text.delete(1.0, tk.END)
            self.url_map.clear()
            self.current_ota_link = None
            self.copy_link_button.config(state=tk.DISABLED)
            self.status_icon_var.set("")
            self.ota_link_label.config(text="")
            self._update_dogfood_label(False)

            if ':' not in fingerprint:
                raise ValueError("Fingerprint must contain at least one ':' separator")
            prefix, original_key = fingerprint.rsplit(':', 1)

            key_types = [
                "user/release-keys",
                "userdebug/release-keys",
                "eng/release-keys",
                "user/dev-keys",
                "user/test-keys",
                "userdebug/dev-keys",
                "userdebug/test-keys",
                "eng/dev-keys",
                "eng/test-keys"
            ]

            scan_locales_str = self.scan_locales_var.get().strip()
            if scan_locales_str:
                locales = [loc.strip() for loc in re.split(r'[,\s\n]+', scan_locales_str) if loc.strip()]
            else:
                locales = [self.locale_var.get().strip()]

            device_sn = getattr(self, 'device_sn_var', tk.StringVar()).get().strip()
            imei = getattr(self, 'imei_var', tk.StringVar()).get().strip()

            self.log_output("=" * 75, 'header')
            self.log_output("KEY TYPE SCAN RESULTS", 'header')
            self.log_output("=" * 75, 'header')
            self.log_output(f"Fingerprint base: {prefix}:", 'info')
            self.log_output(f"Locales: {', '.join(locales)}", 'info')
            self.log_output("")

            found_links = []
            total = len(key_types) * len(locales)
            counter = 0

            stopped = False
            for loc in locales:
                if self._keyscan_stop_event.is_set():
                    stopped = True
                    break
                tz = LOCALE_TZ_MAP.get(loc, 'America/New_York')
                for key in key_types:
                    if self._keyscan_stop_event.is_set():
                        stopped = True
                        break
                    counter += 1
                    test_fp = f"{prefix}:{key}"
                    self.log_output(f"[{counter}/{total}] Locale: {loc}  Key: {key}", 'section')
                    self.log_output(f"  Fingerprint: {test_fp}", 'info')
                    self.update_status(f"Scanning {key} with {loc} ({counter}/{total})...")

                    try:
                        _curl = getattr(self, 'checkin_url_var', None)
                        _curl = _curl.get().strip() if _curl else None
                        settings, raw_bytes, _req, _reqgz = perform_checkin(test_fp, locale=loc, timezone=tz, device_sn=device_sn, imei=imei, url=_curl)
                        if not settings:
                            self.log_output("  Status: ❌ No response from server", 'error')
                            continue

                        ota = find_ota_link(settings)
                        if ota and ota.get('url'):
                            self.log_output("  Status: ✅ OTA found", 'success')
                            self.log_output(f"  URL: {ota['url']}", 'success')
                            if ota.get('title'):
                                self.log_output(f"  Title: {ota['title']}", 'info')
                            if ota.get('size'):
                                self.log_output(f"  Size: {ota['size']}", 'info')
                            found_links.append((key, loc, ota['url'], ota.get('title', ''), ota.get('size', '')))
                        else:
                            self.log_output("  Status: ❌ No OTA", 'error')
                    except Exception as e:
                        self.log_output(f"  Status: ❌ Error: {e}", 'error')

                    self.log_output("", 'info')

            self.log_output("=" * 75, 'header')
            if stopped:
                self.log_output(f"SCAN STOPPED by user after {counter}/{total} checked", 'error')
            if found_links:
                self.log_output(f"SUMMARY: Found {len(found_links)} OTA link(s)", 'success')
                for key, loc, url, title, size in found_links:
                    self.log_output(f"  - {key}  (locale {loc}) → {url}", 'success')
                    if title:
                        self.log_output(f"      Title: {title}", 'info')
                    if size:
                        self.log_output(f"      Size: {size}", 'info')
            else:
                self.log_output("SUMMARY: No OTA links found for any key type or locale", 'error')
            self.log_output("=" * 75, 'header')

            status_prefix = "Key scan stopped" if stopped else "Key scan completed"
            self.update_status(f"{status_prefix} – {len(found_links)} OTA(s) found", 'success' if found_links else 'error')
            self.status_icon_var.set("✓" if found_links else "❌")

        except ValueError as e:
            self.log_output(f"ERROR: {e}", 'error')
            self.update_status("Invalid fingerprint format", 'error')
        except Exception as e:
            self.log_output(f"ERROR: {e}", 'error')
            self.update_status(f"Error: {e}", 'error')
        finally:
            self.query_button.config(state=tk.NORMAL)
            self.keyscan_button.config(state=tk.NORMAL)
            self.clear_button.config(state=tk.NORMAL)
            self.fingerprint_entry.config(state=tk.NORMAL)
            self.keyscan_stop_button.config(state=tk.DISABLED)

    def on_otachain_click(self):
        fingerprint = self.fingerprint_var.get().strip()
        if not fingerprint:
            messagebox.showerror("Error", "Please enter a fingerprint")
            return
        if '/' not in fingerprint:
            messagebox.showerror("Error", "Invalid fingerprint format")
            return

        self.query_button.config(state=tk.DISABLED)
        self.keyscan_button.config(state=tk.DISABLED)
        self.otachain_button.config(state=tk.DISABLED)
        self.clear_button.config(state=tk.DISABLED)
        self.fingerprint_entry.config(state=tk.DISABLED)
        self.keyscan_stop_button.config(state=tk.NORMAL)
        self._otachain_stop_event.clear()

        self.otachain_thread = threading.Thread(
            target=self.perform_otachain, args=(fingerprint,), daemon=True)
        self.otachain_thread.start()

    def perform_otachain(self, start_fingerprint):
        try:
            self.output_text.delete(1.0, tk.END)
            self.raw_text.delete(1.0, tk.END)
            if self.html_frame:
                self.html_frame.load_html("")
            elif self.desc_text:
                self.desc_text.delete(1.0, tk.END)
            self.url_map.clear()
            self.current_ota_link = None
            self.copy_link_button.config(state=tk.DISABLED)
            self.status_icon_var.set("")
            self.ota_link_label.config(text="")
            self._update_dogfood_label(False)

            try:
                self.notebook.select(self.log_frame)
            except Exception:
                pass

            locale = self.locale_var.get().strip() or "en-US"
            tz = LOCALE_TZ_MAP.get(locale, 'America/New_York')
            device_sn = getattr(self, 'device_sn_var', tk.StringVar()).get().strip()
            imei = getattr(self, 'imei_var', tk.StringVar()).get().strip()
            _curl = getattr(self, 'checkin_url_var', None)
            checkin_url = _curl.get().strip() if _curl else None

            self.log_output("=" * 75, 'header')
            self.log_output("OTA CHAIN CHECK", 'header')
            self.log_output("=" * 75, 'header')
            self.log_output(f"Starting fingerprint : {start_fingerprint}", 'info')
            self.log_output(f"Locale               : {locale}  |  Timezone: {tz}", 'info')
            if device_sn:
                self.log_output(f"Serial Number        : {device_sn}", 'info')
            if imei:
                self.log_output(f"IMEI                 : {imei}", 'info')
            self.log_output("", 'info')

            visited_fingerprints = []
            visited_urls = set()
            chain_steps = []
            current_fp = start_fingerprint
            step = 0
            stopped = False
            termination_reason = None

            while True:
                if self._otachain_stop_event.is_set():
                    stopped = True
                    termination_reason = "stopped by user"
                    break

                step += 1
                self.log_output(f"── Step {step} ────────────────────────────────────────────────────────", 'section')
                self.log_output(f"  Fingerprint : {current_fp}", 'info')
                self.update_status(f"OTA Chain Check — step {step}: querying server…")

                if current_fp in visited_fingerprints:
                    self.log_output(f"  ⚠ Fingerprint already visited in this chain — loop detected, stopping.", 'error')
                    termination_reason = "fingerprint loop detected"
                    break
                visited_fingerprints.append(current_fp)

                try:
                    settings, raw_bytes, _req, _reqgz = perform_checkin(
                        current_fp, locale=locale, timezone=tz,
                        device_sn=device_sn, imei=imei, url=checkin_url)
                except Exception as e:
                    self.log_output(f"  ❌ Checkin error: {e}", 'error')
                    termination_reason = f"checkin error: {e}"
                    break

                if not settings:
                    self.log_output("  ❌ No response from server — chain ends here.", 'error')
                    termination_reason = "no response from server"
                    break

                ota = find_ota_link(settings)
                if not ota or not ota.get('url'):
                    self.log_output("  ❌ No OTA returned by server — chain ends here.", 'error')
                    termination_reason = "no OTA available for this fingerprint"
                    break

                ota_url = ota['url']
                self.log_output(f"  ✅ OTA found", 'success')
                self.log_output(f"     URL   : {ota_url}", 'success')
                if ota.get('title'):
                    self.log_output(f"     Title : {ota['title']}", 'info')
                if ota.get('size'):
                    self.log_output(f"     Size  : {ota['size']}", 'info')
                if ota.get('postcondition'):
                    self.log_output(f"     Post-condition : {ota['postcondition']}", 'info')

                if ota_url in visited_urls:
                    self.log_output(f"  ⚠ This OTA URL was already seen in this chain — loop detected, stopping.", 'error')
                    termination_reason = "OTA URL loop detected"
                    chain_steps.append((current_fp, ota_url, None))
                    break
                visited_urls.add(ota_url)

                if self._otachain_stop_event.is_set():
                    stopped = True
                    termination_reason = "stopped by user"
                    chain_steps.append((current_fp, ota_url, None))
                    break

                self.log_output(f"  🔍 Fetching payload metadata to extract post-build fingerprint…", 'info')
                self.update_status(f"OTA Chain Check — step {step}: fetching metadata…")

                post_build = None
                try:
                    meta = fetch_payload_metadata(
                        ota_url,
                        status_cb=lambda m: self.root.after(0, self.update_status, f"OTA Chain — metadata: {m}"),
                        timeout=30)
                    if meta and meta.get('found'):
                        fields = meta.get('fields', {})
                        post_build = fields.get('post-build') or ''
                        pre_build = fields.get('pre-build') or ''
                        if post_build:
                            self.log_output(f"     post-build  : {post_build}", 'success')
                        if pre_build:
                            self.log_output(f"     pre-build   : {pre_build}", 'info')
                        for k, v in fields.items():
                            if k not in ('post-build', 'pre-build') and v:
                                self.log_output(f"     {k:<20}: {v}", 'info')
                        if not post_build:
                            self.log_output(f"     ⚠ post-build field not found in metadata.", 'error')
                    else:
                        self.log_output(f"     ⚠ Could not retrieve payload metadata (OTA might not be a ZIP or server blocked partial ranges).", 'error')
                except Exception as e:
                    self.log_output(f"     ⚠ Metadata fetch error: {e}", 'error')

                chain_steps.append((current_fp, ota_url, post_build))

                if not post_build:
                    self.log_output(f"  ⛔ No post-build fingerprint available — cannot continue chain.", 'error')
                    termination_reason = "post-build fingerprint unavailable"
                    break

                self.log_output(f"  ➡ Next fingerprint  : {post_build}", 'info')
                self.log_output("", 'info')
                current_fp = post_build

            self.log_output("", 'info')
            self.log_output("=" * 75, 'header')
            if stopped:
                self.log_output("OTA CHAIN CHECK — STOPPED BY USER", 'error')
            else:
                self.log_output("OTA CHAIN CHECK — COMPLETE", 'header')
            self.log_output(f"Total steps completed : {len(chain_steps)}", 'info')
            self.log_output(f"Termination reason    : {termination_reason or 'unknown'}", 'info')
            self.log_output("", 'info')

            if chain_steps:
                self.log_output("Chain summary:", 'section')
                for i, (fp, url, pb) in enumerate(chain_steps, 1):
                    self.log_output(f"  [{i}] FP  : {fp}", 'info')
                    self.log_output(f"       URL : {url}", 'success')
                    if pb:
                        self.log_output(f"       ↓ post-build → next step", 'info')
                    self.log_output("", 'info')
            else:
                self.log_output("  No OTA found at any step.", 'error')

            self.log_output("=" * 75, 'header')

            found_count = len(chain_steps)
            status_text = f"OTA chain {'stopped' if stopped else 'done'} — {found_count} step(s) with OTA"
            self.update_status(status_text, 'success' if found_count else 'error')
            self.status_icon_var.set("✓" if found_count else "❌")

        except Exception as e:
            self.log_output(f"ERROR: {e}", 'error')
            self.update_status(f"OTA Chain error: {e}", 'error')
        finally:
            self.query_button.config(state=tk.NORMAL)
            self.keyscan_button.config(state=tk.NORMAL)
            self.otachain_button.config(state=tk.NORMAL)
            self.clear_button.config(state=tk.NORMAL)
            self.fingerprint_entry.config(state=tk.NORMAL)
            self.keyscan_stop_button.config(state=tk.DISABLED)

    def open_serials_imeis_window(self):
        win = tk.Toplevel(self.root)
        win.title("Serials / IMEIs / Other")
        win.geometry("900x650")
        win.configure(bg=self.APP_BG)
        win.transient(self.root)

        top = ttk.Frame(win, padding=12)
        top.pack(fill=tk.X)
        ttk.Label(top, text="🔢 Serials / IMEIs / Other", style='Header.TLabel').pack(side=tk.LEFT)

        btn_frame = ttk.Frame(top)
        btn_frame.pack(side=tk.RIGHT)
        ttk.Button(btn_frame, text="🔄 Refresh", command=self._refresh_all_serials_tabs).pack(side=tk.LEFT, padx=3)
        ttk.Button(btn_frame, text="📥 Import", command=self._import_serials).pack(side=tk.LEFT, padx=3)
        ttk.Button(btn_frame, text="📤 Export", command=self._export_serials).pack(side=tk.LEFT, padx=3)

        search_row = ttk.Frame(win, padding=(12, 4, 12, 8))
        search_row.pack(fill=tk.X)
        ttk.Label(search_row, text="🔎 Search:", style='Normal.TLabel').pack(side=tk.LEFT, padx=(0, 6))
        self._ser_search_var = tk.StringVar(value="")
        search_entry = ttk.Entry(search_row, textvariable=self._ser_search_var, width=40)
        search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        search_entry.bind('<KeyRelease>', lambda e: self._refresh_all_serials_tabs())
        ttk.Button(search_row, text="✕", width=3,
                   command=lambda: (self._ser_search_var.set(""), self._refresh_all_serials_tabs())).pack(side=tk.LEFT, padx=(6, 0))

        self._ser_nb = NOTEBOOK_CLS(win)
        self._ser_nb.pack(fill=tk.BOTH, expand=True, padx=12, pady=(0, 12))

        self._ser_serials_tab = ttk.Frame(self._ser_nb)
        self._ser_nb.add(self._ser_serials_tab, text="Serials")
        self._build_serials_tab(self._ser_serials_tab, "serials", "Serial Number")

        self._ser_imeis_tab = ttk.Frame(self._ser_nb)
        self._ser_nb.add(self._ser_imeis_tab, text="IMEIs")
        self._build_serials_tab(self._ser_imeis_tab, "imeis", "IMEI")

        self._ser_other_tab = ttk.Frame(self._ser_nb)
        self._ser_nb.add(self._ser_other_tab, text="Other")
        self._build_serials_tab(self._ser_other_tab, "other", "Value")

        self._ser_status_var = tk.StringVar(value="Ready.")
        ttk.Label(win, textvariable=self._ser_status_var,
                  foreground='#0066cc', style='Normal.TLabel').pack(anchor=tk.W, padx=12, pady=(0, 8))

        self._ser_win = win
        self._refresh_all_serials_tabs()

    def _build_serials_tab(self, parent, category, value_label):
        toolbar = ttk.Frame(parent, padding=(0, 4))
        toolbar.pack(fill=tk.X, side=tk.TOP)
        ttk.Button(toolbar, text="➕ Add", command=lambda: self._add_note_dialog(category)).pack(side=tk.LEFT, padx=3)
        ttk.Button(toolbar, text="🗑 Clear All", command=lambda: self._clear_all_notes(category)).pack(side=tk.LEFT, padx=3)

        pager_frame = ttk.Frame(parent, padding=(4, 6))

        page_info = ttk.Label(pager_frame, text="", font=('Arial', 9))
        page_info.pack(side=tk.LEFT, padx=(8, 0))
        setattr(self, f"_ser_pageinfo_{category}", page_info)

        nav_frame = ttk.Frame(pager_frame)
        nav_frame.pack(side=tk.LEFT, expand=True)

        first_btn = ttk.Button(nav_frame, text="⏮ First", width=7, command=lambda: self._go_to_page(category, 0))
        first_btn.pack(side=tk.LEFT, padx=1)

        prev_btn = ttk.Button(nav_frame, text="◀ Prev", width=7, command=lambda: self._prev_page(category))
        prev_btn.pack(side=tk.LEFT, padx=1)

        page_entry_var = tk.StringVar(value="1")
        page_entry = ttk.Entry(nav_frame, textvariable=page_entry_var, width=6, justify=tk.CENTER)
        page_entry.pack(side=tk.LEFT, padx=4)
        setattr(self, f"_ser_pageentry_{category}", page_entry_var)

        go_btn = ttk.Button(nav_frame, text="Go", width=4, command=lambda: self._jump_to_page(category))
        go_btn.pack(side=tk.LEFT, padx=1)

        next_btn = ttk.Button(nav_frame, text="Next ▶", width=7, command=lambda: self._next_page(category))
        next_btn.pack(side=tk.LEFT, padx=1)

        last_btn = ttk.Button(nav_frame, text="Last ⏭", width=7, command=lambda: self._go_to_last_page(category))
        last_btn.pack(side=tk.LEFT, padx=1)

        setattr(self, f"_ser_firstbtn_{category}", first_btn)
        setattr(self, f"_ser_prevbtn_{category}", prev_btn)
        setattr(self, f"_ser_nextbtn_{category}", next_btn)
        setattr(self, f"_ser_lastbtn_{category}", last_btn)

        size_frame = ttk.Frame(pager_frame)
        size_frame.pack(side=tk.RIGHT, padx=(0, 8))
        ttk.Label(size_frame, text="Per page:", font=('Arial', 8)).pack(side=tk.LEFT)
        size_var = tk.StringVar(value="500")
        size_combo = ttk.Combobox(size_frame, textvariable=size_var, width=6,
                                  values=["50", "100", "250", "500", "1000"], state="readonly")
        size_combo.pack(side=tk.LEFT, padx=(4, 0))
        size_combo.bind('<<ComboboxSelected>>', lambda e, c=category: self._change_page_size(c))
        setattr(self, f"_ser_pagesizevar_{category}", size_var)

        tree_frame = ttk.Frame(parent)
        tree_frame.pack(fill=tk.BOTH, expand=True, side=tk.TOP)

        cols = ("value", "note", "tags", "modified")
        tree = ttk.Treeview(tree_frame, columns=cols, show="headings")

        tree.heading("value", text=value_label, command=lambda: self._sort_serials(category, "value"))
        tree.heading("note", text="Note / Description", command=lambda: self._sort_serials(category, "note"))
        tree.heading("tags", text="Tags", command=lambda: self._sort_serials(category, "tags"))
        tree.heading("modified", text="Modified", command=lambda: self._sort_serials(category, "modified"))

        tree.column("value", width=180, stretch=False)
        tree.column("note", width=400, stretch=True)
        tree.column("tags", width=150, stretch=False)
        tree.column("modified", width=130, stretch=False)

        vsb = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=tree.yview)
        tree.configure(yscrollcommand=vsb.set)
        tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)

        pager_frame.pack(fill=tk.X, side=tk.BOTTOM)

        menu = tk.Menu(tree, tearoff=0)
        menu.add_command(label="📋 Copy value", command=lambda: self._copy_note_value(tree))
        menu.add_command(label="📋 Copy row", command=lambda: self._copy_note_row(tree))
        menu.add_separator()
        menu.add_command(label="✏️ Edit", command=lambda: self._edit_note_dialog(tree, category))
        menu.add_command(label="🗑 Delete", command=lambda: self._delete_note(tree, category))
        menu.add_separator()

        if category == "imeis":
            menu.add_command(label="➡️ Set as IMEI", command=lambda: self._set_as_imei(tree))
        elif category == "serials":
            menu.add_command(label="➡️ Set as Device SN", command=lambda: self._set_as_serial(tree))
        else:
            menu.add_command(label="➡️ Set as IMEI", command=lambda: self._set_as_imei(tree))
            menu.add_command(label="➡️ Set as Device SN", command=lambda: self._set_as_serial(tree))

        def _on_right_click(event):
            item = tree.identify_row(event.y)
            if item:
                tree.selection_set(item)
                menu.post(event.x_root, event.y_root)

        tree.bind('<Button-3>', _on_right_click)
        tree.bind('<Double-Button-1>', lambda e: self._edit_note_dialog(tree, category))

        setattr(self, f"_ser_tree_{category}", tree)

    def _refresh_all_serials_tabs(self):
        query = (self._ser_search_var.get() or "").strip().lower()
        data = _load_serials_data()

        for category in ("serials", "imeis", "other"):
            tree = getattr(self, f"_ser_tree_{category}", None)
            if tree is None:
                continue

            for ch in tree.get_children():
                tree.delete(ch)

            all_entries = []
            for idx, entry in enumerate(data.get(category, [])):
                value = entry.get("value", "")
                note = entry.get("note", "")
                tags = ", ".join(entry.get("tags", []) or [])
                modified = entry.get("modified", "")
                if query:
                    haystack = f"{value} {note} {tags}".lower()
                    if query not in haystack:
                        continue
                all_entries.append({
                    "idx": idx,
                    "value": value,
                    "note": note,
                    "tags": tags,
                    "modified": modified,
                    "created": entry.get("created", ""),
                })

            sort_col = self._ser_sort_col.get(category, "value")
            sort_dir = self._ser_sort_dir.get(category, "asc")
            reverse = (sort_dir == "desc")

            if sort_col == "value":
                all_entries.sort(key=lambda x: x["value"].lower(), reverse=reverse)
            elif sort_col == "note":
                all_entries.sort(key=lambda x: x["note"].lower(), reverse=reverse)
            elif sort_col == "tags":
                all_entries.sort(key=lambda x: x["tags"].lower(), reverse=reverse)
            elif sort_col == "modified":
                all_entries.sort(key=lambda x: x["modified"], reverse=reverse)

            self._ser_total_items[category] = len(all_entries)

            page_size = self._ser_page_size
            total_pages = max(1, (len(all_entries) + page_size - 1) // page_size)
            current_page = min(self._ser_pages.get(category, 0), total_pages - 1)
            self._ser_pages[category] = current_page

            start = current_page * page_size
            end = min(start + page_size, len(all_entries))
            page_entries = all_entries[start:end]

            for entry in page_entries:
                tree.insert("", tk.END, iid=str(entry["idx"]), values=(
                    entry["value"], entry["note"], entry["tags"], entry["modified"]
                ))

            page_info = getattr(self, f"_ser_pageinfo_{category}", None)
            if page_info:
                showing = len(page_entries)
                total = len(all_entries)
                page_info.config(text=f"Page {current_page + 1} of {total_pages}  |  Showing {showing} of {total} entries")

            page_entry_var = getattr(self, f"_ser_pageentry_{category}", None)
            if page_entry_var:
                page_entry_var.set(str(current_page + 1))

            first_btn = getattr(self, f"_ser_firstbtn_{category}", None)
            prev_btn = getattr(self, f"_ser_prevbtn_{category}", None)
            next_btn = getattr(self, f"_ser_nextbtn_{category}", None)
            last_btn = getattr(self, f"_ser_lastbtn_{category}", None)

            if first_btn:
                first_btn.config(state=tk.DISABLED if current_page == 0 else tk.NORMAL)
            if prev_btn:
                prev_btn.config(state=tk.DISABLED if current_page == 0 else tk.NORMAL)
            if next_btn:
                next_btn.config(state=tk.DISABLED if current_page >= total_pages - 1 else tk.NORMAL)
            if last_btn:
                last_btn.config(state=tk.DISABLED if current_page >= total_pages - 1 else tk.NORMAL)

        total = sum(len(data.get(c, [])) for c in ("serials", "imeis", "other"))
        self._ser_status_var.set(f"Total entries: {total}  •  Click right mouse button on row for actions  •  Click column header to sort")

    def _sort_serials(self, category, column):
        current_col = self._ser_sort_col.get(category, "value")
        current_dir = self._ser_sort_dir.get(category, "asc")

        if current_col == column:
            self._ser_sort_dir[category] = "desc" if current_dir == "asc" else "asc"
        else:
            self._ser_sort_col[category] = column
            self._ser_sort_dir[category] = "asc"

        self._ser_pages[category] = 0
        self._refresh_all_serials_tabs()

    def _go_to_page(self, category, page):
        self._ser_pages[category] = page
        self._refresh_all_serials_tabs()

    def _prev_page(self, category):
        current = self._ser_pages.get(category, 0)
        if current > 0:
            self._ser_pages[category] = current - 1
            self._refresh_all_serials_tabs()

    def _next_page(self, category):
        current = self._ser_pages.get(category, 0)
        self._ser_pages[category] = current + 1
        self._refresh_all_serials_tabs()

    def _go_to_last_page(self, category):
        total = self._ser_total_items.get(category, 0)
        page_size = self._ser_page_size
        last_page = max(0, (total + page_size - 1) // page_size - 1)
        self._ser_pages[category] = last_page
        self._refresh_all_serials_tabs()

    def _jump_to_page(self, category):
        page_entry_var = getattr(self, f"_ser_pageentry_{category}", None)
        if page_entry_var is None:
            return
        try:
            page = int(page_entry_var.get()) - 1
            total = self._ser_total_items.get(category, 0)
            page_size = self._ser_page_size
            total_pages = max(1, (total + page_size - 1) // page_size)
            page = max(0, min(page, total_pages - 1))
            self._ser_pages[category] = page
            self._refresh_all_serials_tabs()
        except ValueError:
            pass

    def _change_page_size(self, category):
        size_var = getattr(self, f"_ser_pagesizevar_{category}", None)
        if size_var is None:
            return
        try:
            new_size = int(size_var.get())
            if new_size > 0:
                self._ser_page_size = new_size
                self._ser_pages[category] = 0
                self._refresh_all_serials_tabs()
        except ValueError:
            pass

    def _add_note_dialog(self, category):
        titles = {"serials": "Add Serial Number", "imeis": "Add IMEI", "other": "Add Note"}
        labels = {"serials": "Serial:", "imeis": "IMEI:", "other": "Value:"}
        dlg = tk.Toplevel(self.root)
        dlg.title(titles.get(category, "Add"))
        dlg.geometry("520x420")
        dlg.configure(bg=self.APP_BG)
        dlg.transient(self.root)
        dlg.grab_set()

        mode_frame = ttk.LabelFrame(dlg, text="Input Mode", padding=6)
        mode_frame.pack(fill=tk.X, padx=12, pady=(8, 4))

        self._add_mode_var = tk.StringVar(value="single")
        ttk.Radiobutton(mode_frame, text="Single value", variable=self._add_mode_var,
                        value="single", command=lambda: self._toggle_add_mode(dlg)).pack(side=tk.LEFT, padx=8)
        ttk.Radiobutton(mode_frame, text="Batch (multiple values)", variable=self._add_mode_var,
                        value="batch", command=lambda: self._toggle_add_mode(dlg)).pack(side=tk.LEFT, padx=8)

        self._add_value_frame = ttk.Frame(dlg)
        self._add_value_frame.pack(fill=tk.X, padx=12, pady=(8, 2))

        self._add_value_label = ttk.Label(self._add_value_frame, text=labels.get(category, "Value:") + " *", style='Normal.TLabel')
        self._add_value_label.pack(anchor=tk.W)

        self._add_single_entry = ttk.Entry(self._add_value_frame, width=50)
        self._add_single_entry.pack(fill=tk.X, pady=(2, 0))

        self._add_batch_text = tk.Text(self._add_value_frame, height=6, width=50, font=('Courier', 9))
        self._add_batch_text.insert(tk.END, "# Enter one value per line\n# Lines starting with # are ignored")
        self._add_batch_status = ttk.Label(dlg, text="", foreground='#666666')
        self._add_batch_text.pack_forget()

        ttk.Label(dlg, text="Note / Description (shared for all):", style='Normal.TLabel').pack(anchor=tk.W, padx=12, pady=(8, 2))
        note_var = tk.StringVar()
        ttk.Entry(dlg, textvariable=note_var, width=50).pack(fill=tk.X, padx=12)

        ttk.Label(dlg, text="Tags (comma separated, shared for all):", style='Normal.TLabel').pack(anchor=tk.W, padx=12, pady=(8, 2))
        tags_var = tk.StringVar()
        ttk.Entry(dlg, textvariable=tags_var, width=50).pack(fill=tk.X, padx=12)

        self._add_batch_status.pack(anchor=tk.W, padx=12, pady=(4, 0), fill=tk.X)

        btn_row = ttk.Frame(dlg)
        btn_row.pack(fill=tk.X, padx=12, pady=16, side=tk.BOTTOM)

        def _save():
            mode = self._add_mode_var.get()
            note = note_var.get().strip()
            tags = [t.strip() for t in tags_var.get().split(",") if t.strip()]

            if mode == "single":
                val = self._add_single_entry.get().strip()
                if not val:
                    messagebox.showwarning("Required", "Value cannot be empty.", parent=dlg)
                    return
                _add_serial_note(category, val, note, tags)
                self._refresh_all_serials_tabs()
                dlg.destroy()
            else:
                raw = self._add_batch_text.get("1.0", tk.END)
                lines = []
                for line in raw.splitlines():
                    line = line.strip()
                    if not line or line.startswith('#'):
                        continue
                    lines.append(line)

                if not lines:
                    messagebox.showwarning("Required", "No valid values found. Enter one per line.", parent=dlg)
                    return

                added = 0
                skipped = 0
                for val in lines:
                    val = val.strip()
                    if not val:
                        skipped += 1
                        continue
                    existing = _load_serials_data().get(category, [])
                    if any(e.get("value") == val for e in existing):
                        skipped += 1
                        continue
                    _add_serial_note(category, val, note, tags)
                    added += 1

                self._refresh_all_serials_tabs()
                msg = f"Added {added} entries."
                if skipped:
                    msg += f" Skipped {skipped} (empty or duplicate)."
                self._ser_status_var.set(msg)
                dlg.destroy()

        ttk.Button(btn_row, text="Save", command=_save).pack(side=tk.RIGHT, padx=(6, 0))
        ttk.Button(btn_row, text="Cancel", command=dlg.destroy).pack(side=tk.RIGHT)

        self._add_single_entry.focus_set()
        dlg.bind('<Return>', lambda e: _save())

    def _toggle_add_mode(self, dlg=None):
        mode = self._add_mode_var.get()
        if mode == "single":
            self._add_single_entry.pack(fill=tk.X, pady=(2, 0))
            self._add_batch_text.pack_forget()
            self._add_batch_status.config(text="")
            self._add_single_entry.focus_set()
        else:
            self._add_single_entry.pack_forget()
            self._add_batch_text.pack(fill=tk.BOTH, expand=True, pady=(2, 0))
            self._add_batch_status.config(text="Enter one value per line. Lines starting with # are ignored.")
            self._add_batch_text.focus_set()
            self._add_batch_text.tag_add(tk.SEL, "1.0", tk.END)

    def _edit_note_dialog(self, tree, category):
        sel = tree.selection()
        if not sel:
            return
        idx = int(sel[0])
        data = _load_serials_data()
        entries = data.get(category, [])
        if idx < 0 or idx >= len(entries):
            return
        entry = entries[idx]

        titles = {"serials": "Edit Serial", "imeis": "Edit IMEI", "other": "Edit Note"}
        dlg = tk.Toplevel(self.root)
        dlg.title(titles.get(category, "Edit"))
        dlg.geometry("480x280")
        dlg.configure(bg=self.APP_BG)
        dlg.transient(self.root)
        dlg.grab_set()

        ttk.Label(dlg, text="Value:", style='Normal.TLabel').pack(anchor=tk.W, padx=12, pady=(12, 2))
        val_var = tk.StringVar(value=entry.get("value", ""))
        ttk.Entry(dlg, textvariable=val_var, width=50).pack(fill=tk.X, padx=12)

        ttk.Label(dlg, text="Note:", style='Normal.TLabel').pack(anchor=tk.W, padx=12, pady=(8, 2))
        note_var = tk.StringVar(value=entry.get("note", ""))
        ttk.Entry(dlg, textvariable=note_var, width=50).pack(fill=tk.X, padx=12)

        ttk.Label(dlg, text="Tags (comma separated):", style='Normal.TLabel').pack(anchor=tk.W, padx=12, pady=(8, 2))
        tags_var = tk.StringVar(value=", ".join(entry.get("tags", []) or []))
        ttk.Entry(dlg, textvariable=tags_var, width=50).pack(fill=tk.X, padx=12)

        btn_row = ttk.Frame(dlg)
        btn_row.pack(fill=tk.X, padx=12, pady=16, side=tk.BOTTOM)

        def _save():
            val = val_var.get().strip()
            if not val:
                messagebox.showwarning("Required", "Value cannot be empty.", parent=dlg)
                return
            note = note_var.get().strip()
            tags = [t.strip() for t in tags_var.get().split(",") if t.strip()]
            _update_serial_note(category, idx, val, note, tags)
            self._refresh_all_serials_tabs()
            dlg.destroy()

        ttk.Button(btn_row, text="Save", command=_save).pack(side=tk.RIGHT, padx=(6, 0))
        ttk.Button(btn_row, text="Cancel", command=dlg.destroy).pack(side=tk.RIGHT)
        dlg.bind('<Return>', lambda e: _save())

    def _delete_note(self, tree, category):
        sel = tree.selection()
        if not sel:
            return
        idx = int(sel[0])
        if not messagebox.askyesno("Delete", "Are you sure you want to delete this entry?", parent=self._ser_win):
            return
        _delete_serial_note(category, idx)
        self._refresh_all_serials_tabs()

    def _clear_all_notes(self, category):
        names = {"serials": "Serials", "imeis": "IMEIs", "other": "Other"}
        if not messagebox.askyesno("Clear All", f"Are you sure you want to clear ALL {names.get(category, category)}?", parent=self._ser_win):
            return
        with _ser_data_lock:
            data = _load_serials_data()
            data[category] = []
            _save_serials_data(data)
        self._refresh_all_serials_tabs()

    def _copy_note_value(self, tree):
        sel = tree.selection()
        if not sel:
            return
        val = tree.item(sel[0], 'values')[0]
        self.root.clipboard_clear()
        self.root.clipboard_append(val)
        self._ser_status_var.set(f"Copied value: {val}")

    def _copy_note_row(self, tree):
        sel = tree.selection()
        if not sel:
            return
        vals = tree.item(sel[0], 'values')
        text = "  •  ".join(str(v) for v in vals)
        self.root.clipboard_clear()
        self.root.clipboard_append(text)
        self._ser_status_var.set("Copied full row")

    def _set_as_imei(self, tree):
        sel = tree.selection()
        if not sel:
            return
        val = tree.item(sel[0], 'values')[0]
        self.imei_var.set(val)
        self._ser_status_var.set(f"Set IMEI to: {val}")
        self.imei_entry.focus_set()
        self.imei_entry.selection_range(0, tk.END)

    def _set_as_serial(self, tree):
        sel = tree.selection()
        if not sel:
            return
        val = tree.item(sel[0], 'values')[0]
        self.device_sn_var.set(val)
        self._ser_status_var.set(f"Set Device SN to: {val}")
        self.device_sn_entry.focus_set()
        self.device_sn_entry.selection_range(0, tk.END)

    def _import_serials(self):
        path = filedialog.askopenfilename(
            title="Import Serials/IMEIs",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                imported = json.load(f)
            if not isinstance(imported, dict):
                raise ValueError("Invalid format: expected JSON object")
            with _ser_data_lock:
                data = _load_serials_data()
                for cat in ("serials", "imeis", "other"):
                    items = imported.get(cat, [])
                    if isinstance(items, list):
                        data[cat].extend(items)
                _save_serials_data(data)
            self._refresh_all_serials_tabs()
            self._ser_status_var.set(f"Imported from {os.path.basename(path)}")
        except Exception as e:
            messagebox.showerror("Import Error", str(e), parent=self._ser_win)

    def _export_serials(self):
        path = filedialog.asksaveasfilename(
            title="Export Serials/IMEIs",
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        if not path:
            return
        try:
            data = _load_serials_data()
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            self._ser_status_var.set(f"Exported to {os.path.basename(path)}")
        except Exception as e:
            messagebox.showerror("Export Error", str(e), parent=self._ser_win)

    def open_download_ota_window(self):
        if self._download_ota_window is not None and self._download_ota_window.winfo_exists():
            self._download_ota_window.lift()
            self._download_ota_window.focus_force()
            return

        win = tk.Toplevel(self.root)
        win.title("Download OTA")
        win.geometry("620x420")
        win.configure(bg=self.APP_BG)
        win.transient(self.root)

        top = ttk.Frame(win, padding=12)
        top.pack(fill=tk.BOTH, expand=True)

        ttk.Label(top, text="⬇️ Download OTA", style='Header.TLabel').pack(anchor=tk.W, pady=(0, 10))

        url_frame = ttk.Frame(top)
        url_frame.pack(fill=tk.X, pady=(0, 6))
        ttk.Label(url_frame, text="OTA URL:", style='Normal.TLabel', width=12).pack(side=tk.LEFT)
        self._download_url_var = tk.StringVar()
        ttk.Entry(url_frame, textvariable=self._download_url_var, font=('Courier', 9)).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(6, 0))

        token_frame = ttk.Frame(top)
        token_frame.pack(fill=tk.X, pady=(0, 6))
        ttk.Label(token_frame, text="Auth Token:", style='Normal.TLabel', width=12).pack(side=tk.LEFT)
        self._download_token_var = tk.StringVar()
        ttk.Entry(token_frame, textvariable=self._download_token_var, font=('Courier', 9)).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(6, 0))

        path_frame = ttk.Frame(top)
        path_frame.pack(fill=tk.X, pady=(0, 10))
        ttk.Label(path_frame, text="Save to:", style='Normal.TLabel', width=12).pack(side=tk.LEFT)
        self._download_path_var = tk.StringVar()
        ttk.Entry(path_frame, textvariable=self._download_path_var, font=('Courier', 9)).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(6, 0))
        ttk.Button(path_frame, text="📂 Browse…", command=self._download_browse_path).pack(side=tk.LEFT, padx=(6, 0))

        prog_lf = ttk.LabelFrame(top, text="Progress", padding=8)
        prog_lf.pack(fill=tk.X, pady=(0, 10))

        self._download_progress_var = tk.DoubleVar(value=0)
        self._download_progress = ttk.Progressbar(prog_lf, variable=self._download_progress_var, maximum=100, mode='determinate')
        self._download_progress.pack(fill=tk.X, pady=(0, 6))

        info_frame = ttk.Frame(prog_lf)
        info_frame.pack(fill=tk.X)
        self._download_status_var = tk.StringVar(value="Ready")
        ttk.Label(info_frame, textvariable=self._download_status_var, foreground='#0066cc', font=('Arial', 9)).pack(side=tk.LEFT)
        self._download_speed_var = tk.StringVar(value="")
        ttk.Label(info_frame, textvariable=self._download_speed_var, foreground='#666666', font=('Arial', 9)).pack(side=tk.RIGHT)

        btn_row = ttk.Frame(top)
        btn_row.pack(fill=tk.X, pady=(8, 0))
        self._download_start_btn = ttk.Button(btn_row, text="▶  Start Download", command=self._download_ota_start)
        self._download_start_btn.pack(side=tk.LEFT, padx=(0, 6))
        self._download_stop_btn = ttk.Button(btn_row, text="⏹  Stop", command=self._download_ota_stop, state=tk.DISABLED)
        self._download_stop_btn.pack(side=tk.LEFT, padx=(0, 6))
        self._download_save256_btn = ttk.Button(btn_row, text="💾  Save 256 KB", command=self._download_ota_save_256kb)
        self._download_save256_btn.pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(btn_row, text="Close", command=win.destroy).pack(side=tk.RIGHT)

        log_frame = ttk.Frame(top)
        log_frame.pack(fill=tk.BOTH, expand=True, pady=(8, 0))
        self._download_log = scrolledtext.ScrolledText(log_frame, height=6, wrap=tk.WORD, font=('Courier', 8))
        self._download_log.pack(fill=tk.BOTH, expand=True)
        self._download_log.configure(state=tk.DISABLED)

        self._download_ota_window = win
        self._download_stop_event.clear()

        if self.current_ota_link:
            self._download_url_var.set(self.current_ota_link)
            parsed = urlparse(self.current_ota_link)
            fname = parsed.path.rsplit('/', 1)[-1] or 'ota_package.zip'
            self._download_path_var.set(os.path.join(os.path.expanduser('~'), 'Downloads', fname))
        if hasattr(self, '_last_query_token') and self._last_query_token:
            self._download_token_var.set(self._last_query_token)

    def _download_browse_path(self):
        url = self._download_url_var.get().strip()
        default_name = 'ota_package.zip'
        if url:
            parsed = urlparse(url)
            fname = parsed.path.rsplit('/', 1)[-1]
            if fname:
                default_name = fname
        path = filedialog.asksaveasfilename(
            title="Save OTA as",
            initialfile=default_name,
            defaultextension=".zip",
            filetypes=[("ZIP files", "*.zip"), ("OTA files", "*.bin"), ("All files", "*.*")]
        )
        if path:
            self._download_path_var.set(path)

    def _download_log_append(self, msg):
        def _do_append():
            try:
                self._download_log.configure(state=tk.NORMAL)
                self._download_log.insert(tk.END, msg + "\n")
                self._download_log.see(tk.END)
                self._download_log.configure(state=tk.DISABLED)
            except Exception:
                pass
        if self._download_ota_window and self._download_ota_window.winfo_exists():
            self._download_ota_window.after(0, _do_append)

    def _download_ota_start(self):
        url = self._download_url_var.get().strip()
        if not url:
            messagebox.showwarning("Download OTA", "Please enter an OTA URL.", parent=self._download_ota_window)
            return
        path = self._download_path_var.get().strip()
        if not path:
            messagebox.showwarning("Download OTA", "Please choose where to save the file.", parent=self._download_ota_window)
            return

        token = self._download_token_var.get().strip()

        self._download_start_btn.config(state=tk.DISABLED)
        self._download_stop_btn.config(state=tk.NORMAL)
        self._download_progress_var.set(0)
        self._download_status_var.set("Starting download…")
        self._download_speed_var.set("")
        self._download_stop_event.clear()

        self._download_log_append(f"URL: {url}")
        self._download_log_append(f"Save to: {path}")
        if token:
            self._download_log_append("Authorization token is set.")
        else:
            self._download_log_append("No authorization token (public download).")
        self._download_log_append("—" * 50)

        self._download_thread = threading.Thread(
            target=self._download_ota_worker,
            args=(url, path, token),
            daemon=True
        )
        self._download_thread.start()

    def _download_ota_stop(self):
        self._download_stop_event.set()
        self._download_status_var.set("Stopping…")
        self._download_stop_btn.config(state=tk.DISABLED)

    def _download_ota_save_256kb(self):
        url = self._download_url_var.get().strip()
        if not url:
            messagebox.showwarning("Download OTA", "Please enter an OTA URL.", parent=self._download_ota_window)
            return
        path = self._download_path_var.get().strip()
        if not path:
            messagebox.showwarning("Download OTA", "Please choose where to save the file.", parent=self._download_ota_window)
            return

        base, ext = os.path.splitext(path)
        partial_path = f"{base}.first256kb{ext or '.bin'}"

        token = self._download_token_var.get().strip()

        self._download_start_btn.config(state=tk.DISABLED)
        self._download_save256_btn.config(state=tk.DISABLED)
        self._download_stop_btn.config(state=tk.NORMAL)
        self._download_progress_var.set(0)
        self._download_status_var.set("Starting partial download…")
        self._download_speed_var.set("")
        self._download_stop_event.clear()

        self._download_log_append(f"URL: {url}")
        self._download_log_append(f"Save first 256 KB to: {partial_path}")
        if token:
            self._download_log_append("Authorization token is set.")
        self._download_log_append("—" * 50)

        self._download_thread = threading.Thread(
            target=self._download_ota_worker_256kb,
            args=(url, partial_path, token),
            daemon=True
        )
        self._download_thread.start()

    def _download_ota_worker_256kb(self, url, save_path, token):
        RANGE_BYTES = 256 * 1024

        def _update_ui(progress_pct, status_msg, speed_msg):
            def _do():
                try:
                    self._download_progress_var.set(progress_pct)
                    self._download_status_var.set(status_msg)
                    self._download_speed_var.set(speed_msg)
                except Exception:
                    pass
            if self._download_ota_window and self._download_ota_window.winfo_exists():
                self._download_ota_window.after(0, _do)

        def _reset_buttons():
            self._download_ota_window.after(0, lambda: (
                self._download_start_btn.config(state=tk.NORMAL),
                self._download_save256_btn.config(state=tk.NORMAL),
                self._download_stop_btn.config(state=tk.DISABLED)
            ))

        try:
            headers = {
                'User-Agent': 'AndroidDownloadManager/14 (Linux; U; Android 14; sdk_gphone64_x86_64 Build/UE1A.230829.036)',
                'Accept-Encoding': 'identity',
                'Range': f'bytes=0-{RANGE_BYTES - 1}',
            }
            if token:
                headers['Authorization'] = token

            req = urllib.request.Request(url, headers=headers, method='GET')
            ctx = ssl.create_default_context()

            _update_ui(0, "Connecting…", "")
            self._download_log_append("Connecting to server (Range request)…")

            t_start = time.time()
            with urllib.request.urlopen(req, timeout=30, context=ctx) as resp:
                status = getattr(resp, 'status', 200)
                content_range = resp.headers.get('Content-Range', '')
                accept_ranges = resp.headers.get('Accept-Ranges', '')

                if status == 206:
                    self._download_log_append(f"Server honored Range request (HTTP 206). Content-Range: {content_range or 'n/a'}")
                elif status == 200:
                    self._download_log_append("⚠️ Server returned HTTP 200 (Range not supported) — "
                                              "response may contain the full file; only 256 KB will be read/saved.")
                else:
                    self._download_log_append(f"Server responded HTTP {status}.")

                os.makedirs(os.path.dirname(os.path.abspath(save_path)), exist_ok=True)

                downloaded = 0
                CHUNK_SIZE = 32 * 1024
                last_report_time = t_start
                last_report_bytes = 0

                with open(save_path, 'wb') as f:
                    while downloaded < RANGE_BYTES:
                        if self._download_stop_event.is_set():
                            self._download_log_append("Partial download stopped by user.")
                            _update_ui(0, "Stopped", "")
                            try:
                                f.close()
                                os.remove(save_path)
                            except Exception:
                                pass
                            _reset_buttons()
                            return

                        to_read = min(CHUNK_SIZE, RANGE_BYTES - downloaded)
                        chunk = resp.read(to_read)
                        if not chunk:
                            break

                        f.write(chunk)
                        downloaded += len(chunk)

                        now = time.time()
                        elapsed = now - t_start
                        interval = now - last_report_time
                        if interval >= 0.25:
                            instant_speed = (downloaded - last_report_bytes) / interval if interval > 0 else 0
                            last_report_time = now
                            last_report_bytes = downloaded
                            if instant_speed >= 1_048_576:
                                speed_str = f"{instant_speed/1_048_576:.1f} MiB/s"
                            elif instant_speed >= 1024:
                                speed_str = f"{instant_speed/1024:.1f} KiB/s"
                            else:
                                speed_str = f"{instant_speed:.0f} B/s"
                            pct = min(100.0, (downloaded / RANGE_BYTES) * 100)
                            _update_ui(pct, f"Saving first 256 KB… {pct:.1f}%", speed_str)

                elapsed_total = time.time() - t_start
                self._download_log_append("—" * 50)
                self._download_log_append(f"✅ Saved first {downloaded:,} bytes to: {save_path}")
                self._download_log_append(f"   Elapsed: {elapsed_total:.1f}s")
                _update_ui(100, "Complete (256 KB)", "")
                _reset_buttons()

        except urllib.error.HTTPError as e:
            self._download_log_append(f"❌ HTTP error: {e.code} {e.reason}")
            _update_ui(0, f"Error: HTTP {e.code}", "")
            _reset_buttons()
        except Exception as e:
            self._download_log_append(f"❌ Error: {e}")
            _update_ui(0, f"Error: {e}", "")
            _reset_buttons()

    def _download_ota_worker(self, url, save_path, token):
        CHUNK_SIZE = 256 * 1024

        def _update_ui(progress_pct, status_msg, speed_msg):
            def _do():
                try:
                    self._download_progress_var.set(progress_pct)
                    self._download_status_var.set(status_msg)
                    self._download_speed_var.set(speed_msg)
                except Exception:
                    pass
            if self._download_ota_window and self._download_ota_window.winfo_exists():
                self._download_ota_window.after(0, _do)

        def _reset_buttons():
            self._download_ota_window.after(0, lambda: (
                self._download_start_btn.config(state=tk.NORMAL),
                self._download_stop_btn.config(state=tk.DISABLED)
            ))

        try:
            headers = {
                'User-Agent': 'AndroidDownloadManager/14 (Linux; U; Android 14; sdk_gphone64_x86_64 Build/UE1A.230829.036)',
                'Accept-Encoding': 'identity',
            }
            if token:
                headers['Authorization'] = token

            req = urllib.request.Request(url, headers=headers, method='GET')
            ctx = ssl.create_default_context()

            _update_ui(0, "Connecting…", "")
            self._download_log_append("Connecting to server…")

            t_start = time.time()
            with urllib.request.urlopen(req, timeout=30, context=ctx) as resp:
                total_size = int(resp.headers.get('Content-Length', 0) or 0)
                downloaded = 0
                last_report_time = t_start
                last_report_bytes = 0

                size_human = ""
                if total_size > 0:
                    if total_size >= 1_073_741_824:
                        size_human = f"{total_size/1_073_741_824:.2f} GiB"
                    elif total_size >= 1_048_576:
                        size_human = f"{total_size/1_048_576:.2f} MiB"
                    else:
                        size_human = f"{total_size/1024:.1f} KiB"
                    self._download_log_append(f"File size: {size_human} ({total_size:,} bytes)")
                else:
                    self._download_log_append("File size: unknown (streaming)")

                os.makedirs(os.path.dirname(os.path.abspath(save_path)), exist_ok=True)

                with open(save_path, 'wb') as f:
                    while True:
                        if self._download_stop_event.is_set():
                            self._download_log_append("Download stopped by user.")
                            _update_ui(0, "Stopped", "")
                            try:
                                f.close()
                                os.remove(save_path)
                            except Exception:
                                pass
                            _reset_buttons()
                            return

                        chunk = resp.read(CHUNK_SIZE)
                        if not chunk:
                            break

                        f.write(chunk)
                        downloaded += len(chunk)

                        now = time.time()
                        elapsed = now - t_start
                        avg_speed = downloaded / elapsed if elapsed > 0 else 0

                        interval = now - last_report_time
                        if interval >= 0.5:
                            instant_speed = (downloaded - last_report_bytes) / interval
                            last_report_time = now
                            last_report_bytes = downloaded

                            if instant_speed >= 1_048_576:
                                speed_str = f"{instant_speed/1_048_576:.1f} MiB/s"
                            elif instant_speed >= 1024:
                                speed_str = f"{instant_speed/1024:.1f} KiB/s"
                            else:
                                speed_str = f"{instant_speed:.0f} B/s"

                            if total_size > 0:
                                pct = min(100.0, (downloaded / total_size) * 100)
                                _update_ui(pct, f"Downloading… {pct:.1f}%", speed_str)
                            else:
                                dl_human = f"{downloaded/1_048_576:.1f} MiB" if downloaded >= 1_048_576 else f"{downloaded/1024:.1f} KiB"
                                _update_ui(0, f"Downloading… {dl_human}", speed_str)

                elapsed_total = time.time() - t_start
                if elapsed_total > 0:
                    avg_speed = downloaded / elapsed_total
                    if avg_speed >= 1_048_576:
                        avg_str = f"{avg_speed/1_048_576:.1f} MiB/s"
                    elif avg_speed >= 1024:
                        avg_str = f"{avg_speed/1024:.1f} KiB/s"
                    else:
                        avg_str = f"{avg_speed:.0f} B/s"
                else:
                    avg_str = "N/A"

                self._download_log_append("—" * 50)
                self._download_log_append(f"✅ Download complete: {save_path}")
                self._download_log_append(f"   Total: {downloaded:,} bytes in {elapsed_total:.1f}s")
                self._download_log_append(f"   Average speed: {avg_str}")
                _update_ui(100, "Complete", avg_str)

                _reset_buttons()

        except Exception as e:
            self._download_log_append(f"❌ Error: {e}")
            _update_ui(0, f"Error: {e}", "")
            _reset_buttons()


def main():
    root = tk.Tk()
    app = OTAProberGUI(root)
    root.mainloop()


if __name__ == '__main__':
    main()
