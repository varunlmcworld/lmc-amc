#!/usr/bin/env python3
"""LMC World AMC Manager — local and Render cloud with Guest Check."""
from __future__ import annotations

import csv
import datetime as dt
import hashlib
import hmac
import html
import ipaddress
import io
import json
import os
from pathlib import Path
from contextlib import contextmanager
import re
import secrets
import sqlite3
import tempfile
import threading
import time
from email import policy
from email.parser import BytesParser
from http import HTTPStatus
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, quote, urlencode, urlparse

BASE = Path(__file__).resolve().parent
DB_PATH = Path(os.environ.get("AMC_DB_PATH", str(BASE / "data" / "amc.db")))
HOST = os.environ.get("AMC_HOST", "127.0.0.1")
PORT = int(os.environ.get("PORT", os.environ.get("AMC_PORT", "8765")))
CLOUD = os.environ.get("AMC_CLOUD") == "1"
MAX_UPLOAD = 2 * 1024 * 1024
SESSIONS: dict[str, dict] = {}
GUEST_SESSIONS: dict[str, dict] = {}
LOGIN_FAILURES: dict[str, list[float]] = {}
LOCK = threading.RLock()
TYPES = {"AMC", "LMC Warranty", "No Coverage"}
RATE_WINDOW_SECONDS = 15 * 60


def h(value) -> str:
    return html.escape(str(value if value is not None else ""), quote=True)


def normalize_serial(value: str) -> str:
    return re.sub(r"\s+", "", value or "").upper()


def parse_date(value: str, required: bool = True) -> str | None:
    value = (value or "").strip()
    if not value:
        if required:
            raise ValueError("A date is required.")
        return None
    for fmt in ("%Y-%m-%d", "%d/%m/%Y"):
        try:
            return dt.datetime.strptime(value, fmt).date().isoformat()
        except ValueError:
            continue
    raise ValueError(f"Invalid date '{value}'. Use YYYY-MM-DD or DD/MM/YYYY.")


def coverage_status(row, today: dt.date | None = None) -> tuple[str, int | None, str]:
    today = today or dt.date.today()
    if row["coverage_type"] == "No Coverage" or not row["coverage_end"]:
        return "Not covered", None, "neutral"
    start = dt.date.fromisoformat(row["coverage_start"])
    end = dt.date.fromisoformat(row["coverage_end"])
    days = (end - today).days
    if today < start:
        return "Scheduled", days, "blue"
    if days < 0:
        return "Expired", days, "red"
    if days <= 30:
        return "Expiring soon", days, "amber"
    return "Covered", days, "green"


def human_date(value: str | None) -> str:
    return dt.date.fromisoformat(value).strftime("%d %b %Y") if value else "—"


def remaining_text(status: str, days: int | None) -> str:
    if days is None:
        return "No LMC coverage"
    if status == "Scheduled":
        return "Starts on coverage start date"
    if days == 0:
        return "Ends today"
    if days < 0:
        return f"Expired {abs(days)} day{'s' if abs(days) != 1 else ''} ago"
    return f"{days} day{'s' if days != 1 else ''} remaining"


@contextmanager
def db_connect():
    """One SQLite connection per operation; commit/rollback and close reliably."""
    DB_PATH.parent.mkdir(parents=True, exist_ok=True)
    db = sqlite3.connect(DB_PATH, timeout=10)
    try:
        db.row_factory = sqlite3.Row
        db.execute("PRAGMA busy_timeout=10000")
        db.execute("PRAGMA foreign_keys=ON")
        yield db
        db.commit()
    except Exception:
        db.rollback()
        raise
    finally:
        db.close()


def init_db() -> None:
    with db_connect() as db:
        db.execute("PRAGMA journal_mode=WAL")
        db.executescript("""
        CREATE TABLE IF NOT EXISTS settings (
            key TEXT PRIMARY KEY, value TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS assets (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            client_name TEXT NOT NULL,
            manufacturer TEXT NOT NULL DEFAULT 'Dell',
            model TEXT NOT NULL,
            serial_number TEXT NOT NULL,
            serial_key TEXT NOT NULL UNIQUE,
            purchase_date TEXT NOT NULL,
            coverage_type TEXT NOT NULL DEFAULT 'AMC',
            coverage_start TEXT,
            coverage_end TEXT,
            invoice_number TEXT NOT NULL DEFAULT '',
            notes TEXT NOT NULL DEFAULT '',
            created_at TEXT NOT NULL DEFAULT (datetime('now')),
            updated_at TEXT NOT NULL DEFAULT (datetime('now'))
        );
        CREATE INDEX IF NOT EXISTS idx_assets_client ON assets(client_name);
        CREATE INDEX IF NOT EXISTS idx_assets_expiry ON assets(coverage_end);
        CREATE TABLE IF NOT EXISTS history (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            asset_id INTEGER NOT NULL REFERENCES assets(id),
            action TEXT NOT NULL,
            detail TEXT NOT NULL,
            created_at TEXT NOT NULL DEFAULT (datetime('now'))
        );
        -- Counters survive Render redeploys on the existing persistent disk.
        -- Hashed identifiers; no raw visitor IP or serial numbers are stored.
        CREATE TABLE IF NOT EXISTS request_limits (
            bucket TEXT PRIMARY KEY,
            window_start INTEGER NOT NULL,
            count INTEGER NOT NULL
        );
        """)


def consume_lookup_allowance(session_token: str, client_ip: str, now: float | None = None) -> bool:
    """Atomically allow a lookup within session, IP and site-wide budgets.

    Using the existing SQLite disk ensures new sessions or a service restart
    cannot evade the shared budgets. A 15-minute fixed window is intentionally
    simple; it is a basic abuse limit, not a full bot/WAF solution.
    """
    timestamp = int(time.time() if now is None else now)
    window = (timestamp // RATE_WINDOW_SECONDS) * RATE_WINDOW_SECONDS
    with db_connect() as db:
        db.execute('BEGIN IMMEDIATE')
        row = db.execute("SELECT value FROM settings WHERE key='rate_limit_salt'").fetchone()
        if row is None:
            salt = secrets.token_hex(32)
            db.execute("INSERT INTO settings(key,value) VALUES('rate_limit_salt',?)", (salt,))
        else:
            salt = row['value']

        def bucket(kind: str, identifier: str) -> str:
            fingerprint = hmac.new(bytes.fromhex(salt), f'{kind}:{identifier}'.encode(), hashlib.sha256).hexdigest()
            return f'{kind}:{fingerprint}'

        limits = ((bucket('session', session_token), 15),
                  (bucket('ip', client_ip), 45),
                  ('global', 600))
        for key, limit in limits:
            old = db.execute('SELECT count, window_start FROM request_limits WHERE bucket=?', (key,)).fetchone()
            if old is not None and old['window_start'] == window and old['count'] >= limit:
                return False
        for key, _ in limits:
            db.execute('''INSERT INTO request_limits(bucket, window_start, count)
                          VALUES (?, ?, 1)
                          ON CONFLICT(bucket) DO UPDATE SET
                          count=CASE WHEN window_start=excluded.window_start THEN count+1 ELSE 1 END,
                          window_start=excluded.window_start''', (key, window))
        # Periodic pruning keeps the table small even with many abandoned sessions.
        if db.execute("SELECT count FROM request_limits WHERE bucket='global'").fetchone()['count'] % 64 == 0:
            db.execute('DELETE FROM request_limits WHERE window_start < ?', (window,))
    return True


def bootstrap_cloud_admin() -> None:
    """One-time cloud admin setup. Never publish a first-user registration form."""
    if not CLOUD:
        return
    pw = os.environ.get("AMC_BOOTSTRAP_PASSWORD", "")
    with db_connect() as db:
        existing = db.execute("SELECT 1 FROM settings WHERE key='admin_password'").fetchone()
        if existing:
            return  # A redeploy must never reset the existing admin password.
        if not 14 <= len(pw) <= 200:
            raise RuntimeError("Set AMC_BOOTSTRAP_PASSWORD (14-200 chars) as a private Render environment variable before first deployment.")
        db.execute("INSERT INTO settings(key,value) VALUES('admin_password',?)", (password_hash(pw),))


def validate_cloud_configuration() -> None:
    if not CLOUD:
        return
    if HOST != "0.0.0.0" or os.environ.get("AMC_HTTPS") != "1":
        raise RuntimeError("Cloud deployment requires AMC_HOST=0.0.0.0 and AMC_HTTPS=1 behind HTTPS proxy.")
    if not DB_PATH.is_absolute() or not DB_PATH.is_relative_to(Path("/var/data")):
        raise RuntimeError("Cloud deployment requires AMC_DB_PATH on the persistent /var/data disk.")
    if not Path("/var/data").is_dir():
        raise RuntimeError("Persistent disk /var/data was not mounted; refusing to create a disposable database.")


def password_hash(password: str) -> str:
    """PBKDF2 is available on supported Python/macOS builds where scrypt isn't."""
    salt = secrets.token_bytes(16)
    rounds = 600_000
    digest = hashlib.pbkdf2_hmac("sha256", password.encode(), salt, rounds)
    return f"pbkdf2_sha256${rounds}${salt.hex()}${digest.hex()}"


def verify_password(password: str, stored: str) -> bool:
    try:
        if stored.startswith("pbkdf2_sha256$"):
            algorithm, rounds_text, salt_hex, hash_hex = stored.split("$", 3)
            rounds = int(rounds_text)
            # Limit work if a damaged database contains an unreasonable value.
            if rounds < 100_000 or rounds > 2_000_000:
                return False
            expected = bytes.fromhex(hash_hex)
            if len(expected) != 32:
                return False
            actual = hashlib.pbkdf2_hmac("sha256", password.encode(), bytes.fromhex(salt_hex), rounds)
            return hmac.compare_digest(actual, expected)
        # Backwards compatibility for users who completed setup with v1 on
        # a Python installation exposing scrypt. Newly created hashes use PBKDF2.
        salt_hex, hash_hex = stored.split("$", 1)
        scrypt = getattr(hashlib, "scrypt", None)
        if not callable(scrypt):
            return False
        expected = bytes.fromhex(hash_hex)
        actual = scrypt(password.encode(), salt=bytes.fromhex(salt_hex), n=2**14, r=8, p=1)
        return hmac.compare_digest(actual, expected)
    except (ValueError, TypeError, OverflowError):
        return False


def validate_asset(form: dict) -> dict:
    def field(key: str, limit: int = 255) -> str:
        value = str(form.get(key, "") or "").strip()
        if len(value) > limit:
            raise ValueError(f"{key.replace('_',' ').title()} is too long (max {limit} characters).")
        return value

    client = field("client_name")
    model = field("model")
    manufacturer = field("manufacturer", 80) or "Dell"
    serial = field("serial_number", 100)
    key = normalize_serial(serial)
    invoice = field("invoice_number", 100)
    notes = field("notes", 2000)
    if not client or not model or not serial:
        raise ValueError("Client name, model and serial number are required.")
    if len(key) < 3:
        raise ValueError("The serial number must have at least 3 characters.")
    coverage_type = field("coverage_type", 40) or "AMC"
    if coverage_type not in TYPES:
        raise ValueError("Choose a valid LMC coverage type.")
    purchase = parse_date(field("purchase_date", 20))
    start = parse_date(field("coverage_start", 20), required=coverage_type != "No Coverage")
    end = parse_date(field("coverage_end", 20), required=coverage_type != "No Coverage")
    if coverage_type == "No Coverage":
        start = end = None
    if start and end and end < start:
        raise ValueError("Coverage end date cannot be before its start date.")
    return dict(client_name=client, manufacturer=manufacturer, model=model,
                serial_number=serial, serial_key=key, purchase_date=purchase,
                coverage_type=coverage_type, coverage_start=start, coverage_end=end,
                invoice_number=invoice, notes=notes)


CSS = r"""
:root{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;color:#15233d;background:#f5f7fb;font-synthesis:none}
*{box-sizing:border-box}body{margin:0}a{color:#2454cb;text-decoration:none}a:hover{text-decoration:underline}
.container{max-width:1190px;margin:auto;padding:30px 26px 65px}.top{background:#0e1d3a;color:white;border-bottom:3px solid #476af5}
.nav{max-width:1190px;margin:auto;display:flex;gap:22px;align-items:center;min-height:76px;padding:13px 26px;flex-wrap:wrap}
.brand{font-size:19px;font-weight:800;letter-spacing:-.6px;color:white!important}.brand small{display:block;color:#aebede;font-size:11px;letter-spacing:2px;margin-top:2px}
.links{display:flex;align-items:center;gap:17px;margin-left:auto;flex-wrap:wrap}.links a{color:#d2dbef;font-size:13px;font-weight:650}.links a.current{color:white}
.nav-logout{background:#25375b;color:white;border:0;border-radius:9px;padding:9px 14px;font-weight:700;cursor:pointer}
h1{font-size:31px;line-height:1.2;letter-spacing:-1.1px;margin:5px 0 7px}h2{font-size:20px;letter-spacing:-.4px;margin:0 0 18px}
p{line-height:1.52}.muted{color:#697790}.subtitle{font-size:14px;margin:0 0 22px}.eyebrow{font-size:11px;letter-spacing:1.5px;font-weight:850;color:#5268ab;text-transform:uppercase}
.hero{display:flex;align-items:flex-start;justify-content:space-between;gap:15px;margin-bottom:25px;flex-wrap:wrap}
.btn{display:inline-flex;gap:8px;align-items:center;justify-content:center;padding:12px 16px;border-radius:10px;background:#3459db;color:white!important;border:1px solid #3459db;font-size:13px;font-weight:750;cursor:pointer;white-space:nowrap;text-decoration:none!important}
.btn.secondary{background:white;color:#1f355c!important;border-color:#d9e1ef}.btn.danger{background:#b42335;border-color:#b42335}.btn.small{padding:9px 12px;font-size:12px}.btn:hover{filter:brightness(.96)}
.cards{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:14px;margin-bottom:21px}
.card,.panel{background:white;border:1px solid #e4e9f2;border-radius:15px;box-shadow:0 3px 11px rgba(29,43,78,.025)}
.card{padding:19px 20px}.card .value{font-size:32px;font-weight:850;letter-spacing:-1px;margin:10px 0 4px}.card .label{color:#6a7790;font-size:12px;font-weight:750}.card .foot{font-size:11px;color:#8290a6}
.panel{padding:22px 23px;margin-bottom:19px}.search{display:flex;gap:10px}.input,select,textarea{width:100%;padding:12px 13px;background:white;color:#1d2b46;border:1px solid #d7dfed;border-radius:10px;font:inherit;font-size:14px;outline:none}
.input:focus,select:focus,textarea:focus{border-color:#4569e7;box-shadow:0 0 0 3px #4569e71c}.search .input{font-size:16px}
.tablewrap{overflow:auto}table{width:100%;border-collapse:collapse;white-space:nowrap}th{text-align:left;font-size:11px;text-transform:uppercase;letter-spacing:.8px;color:#8190a5;padding:12px 11px;border-bottom:1px solid #e8edf4}td{padding:14px 11px;border-bottom:1px solid #eef1f6;font-size:13px}tr:last-child td{border-bottom:0}
strong{font-weight:750}.serial{font-weight:850;letter-spacing:.3px;color:#244bc0}.tiny{font-size:11px;color:#77869b;margin-top:4px}
.badge{display:inline-block;padding:6px 9px;border-radius:7px;font-size:11px;font-weight:850;white-space:nowrap}.green{color:#08764e;background:#dbf7e8}.red{color:#af3344;background:#ffe5e8}.amber{color:#916215;background:#fff1ca}.blue{color:#2756a5;background:#e6efff}.neutral{color:#637086;background:#ecf0f5}
.split{display:flex;gap:11px;justify-content:space-between;align-items:center;flex-wrap:wrap}.formgrid,.details{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:16px 20px}
.formgrid label{font-size:12px;color:#596981;font-weight:750;display:block;margin-bottom:7px}.field{min-width:0}.wide{grid-column:1/-1}.required{color:#c63b52}
.detail{border-bottom:1px solid #edf0f5;padding-bottom:14px}.detail .name{font-size:12px;color:#7b899b;margin-bottom:7px}.detail .answer{font-size:15px;font-weight:700;word-break:break-word}
.statusbox{border-radius:14px;background:#eef5ff;padding:21px;margin:19px 0;border:1px solid #dbe7fd}.statusbox.green{background:#e9faf1;border-color:#cbf1da}.statusbox.red{background:#fff0f1;border-color:#ffdade}.statusbox.amber{background:#fff7e4;border-color:#f8e7b3}.statusbox.neutral{background:#f1f3f7;border-color:#e2e6ee}
.statusbox .big{font-size:29px;font-weight:850;letter-spacing:-.8px;margin:10px 0 3px;color:#172844}
.notice{padding:12px 15px;border:1px solid #d9e5f9;background:#edf4ff;color:#254778;border-radius:10px;font-size:13px;margin-bottom:18px}.notice.error{background:#fff1f1;color:#9b2034;border-color:#ffd7dc}
.footer{font-size:12px;color:#8e99aa;padding-top:20px;text-align:center}.helper{font-size:12px;color:#728097;margin:7px 0 0}.actions{display:flex;align-items:center;gap:9px;flex-wrap:wrap}.empty{padding:33px 10px;text-align:center;color:#7a879a}.number{font-variant-numeric:tabular-nums}.pagination{display:flex;justify-content:flex-end;align-items:center;gap:12px;padding-top:15px;font-size:12px}
.login{max-width:470px;margin:52px auto}.login h1{font-size:26px}.login .panel{padding:30px}.login .field{margin-bottom:18px}
.guest-result{margin-top:14px}.guest-result .details{margin-top:21px}
.landing-shell{max-width:1060px;margin:28px auto}.landing-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:19px;align-items:stretch}
.landing-grid .panel{padding:27px;min-height:260px;display:flex;flex-direction:column}.landing-grid form{flex:1;display:flex;flex-direction:column}.landing-grid .field label{display:block;font-size:12px;color:#596981;font-weight:750;margin-bottom:9px}.landing-grid form .btn{align-self:stretch;width:100%;margin-top:auto!important}.landing-shell .guest-result{padding:30px}.landing-intro{margin-bottom:19px}
@media(max-width:760px){.landing-grid{grid-template-columns:1fr}.landing-grid .panel{padding:20px}.landing-shell .guest-result{padding:20px}}
@media(max-width:760px){.container{padding:24px 15px 55px}.nav{padding:12px 15px}.links{margin-left:0;width:100%;gap:14px}.cards{grid-template-columns:repeat(2,1fr)}.panel{padding:17px}.formgrid,.details{grid-template-columns:1fr}.search{flex-direction:column}.hero h1{font-size:27px}.card{padding:15px}.card .value{font-size:26px}}
"""


def document(content: str, title: str, session: dict | None = None, active: str = "", guest: bool = False) -> str:
    nav = ""
    if session:
        nav = f'''<div class="links"><a class="{'current' if active == 'dashboard' else ''}" href="/">Dashboard</a><a href="/guest">Coverage lookup</a><a class="{'current' if active == 'import' else ''}" href="/import">Import</a><a href="/export.csv">Export CSV</a><a href="/backup.db">DB Backup</a><form action="/logout" method="post" style="margin:0">{csrf_field(session)}<button class="nav-logout">Log out</button></form></div>'''
    elif guest:
        nav = ''
    brand_target = '/'
    footer = 'LMC World · End User coverage check' if guest else 'LMC World · Internal service coverage register · Manufacturer warranty is not verified by this system'
    return f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="robots" content="noindex,nofollow"><title>{h(title)} · LMC World</title><style>{CSS}</style></head><body><header class="top"><nav class="nav"><a class="brand" href="{brand_target}">LMC WORLD</a>{nav}</nav></header><main class="container">{content}<footer class="footer">{footer}</footer></main></body></html>'''


def csrf_field(session: dict) -> str:
    return f'<input type="hidden" name="csrf" value="{h(session["csrf"])}">'


def asset_form(session: dict, asset=None, error: str = "", form: dict | None = None) -> str:
    edit = asset is not None
    data = dict(asset) if asset else {}
    if form:
        data.update(form)
    def val(key: str, default: str = "") -> str:
        return h(data.get(key) if data.get(key) is not None else default)
    mode = "Edit laptop" if edit else "Register laptop"
    action = f'/asset/{asset["id"]}/edit' if edit else "/asset/create"
    types = "".join(f'<option value="{h(t)}" {"selected" if data.get("coverage_type", "AMC") == t else ""}>{h(t)}</option>' for t in ("AMC", "LMC Warranty", "No Coverage"))
    fields = [
        ('client_name','Client / business name','text',True,'e.g. ABC Technologies Pvt Ltd'),
        ('manufacturer','Manufacturer','text',False,'Dell'),
        ('model','Laptop model','text',True,'e.g. Latitude 7490'),
        ('serial_number','Serial number / service tag','text',True,'Unique serial number'),
        ('purchase_date','Purchase date','date',True,''),
        ('invoice_number','Invoice reference','text',False,'e.g. INV-2026-0105'),
    ]
    html_fields = ""
    for key, label, kind, req, placeholder in fields:
        default = 'Dell' if key == 'manufacturer' else ''
        html_fields += f'''<div class="field"><label for="{key}">{label} {'<span class="required">*</span>' if req else ''}</label><input class="input" id="{key}" name="{key}" type="{kind}" value="{val(key,default)}" placeholder="{h(placeholder)}" {'required' if req else ''}></div>'''
    html_fields += f'''<div class="field"><label for="coverage_type">LMC coverage type <span class="required">*</span></label><select name="coverage_type" id="coverage_type">{types}</select></div><div class="field"><label for="coverage_start">LMC coverage start</label><input class="input" id="coverage_start" type="date" name="coverage_start" value="{val('coverage_start')}"></div><div class="field"><label for="coverage_end">LMC coverage end (inclusive)</label><input class="input" id="coverage_end" type="date" name="coverage_end" value="{val('coverage_end')}"></div><div class="field wide"><label for="notes">AMC terms / service notes</label><textarea class="input" id="notes" name="notes" rows="3" placeholder="Coverage exclusions, contract details, internal notes">{val('notes')}</textarea></div>'''
    error_block = f'<div class="notice error">{h(error)}</div>' if error else ''
    return document(f'''<div class="hero"><div><div class="eyebrow">LAPTOP REGISTER</div><h1>{mode}</h1><p class="subtitle muted">Record the client's laptop and the exact dates of LMC-provided coverage.</p></div><a class="btn secondary" href="{'/asset/'+str(asset['id']) if edit else '/'}">← Back</a></div>{error_block}<form action="{action}" method="post" class="panel">{csrf_field(session)}<div class="formgrid">{html_fields}</div><p class="helper" style="margin-top:18px">For manufacturer warranty, verify separately with Dell, HP or Lenovo. This register tracks LMC World commitments.</p><div class="actions" style="margin-top:22px"><button class="btn" type="submit">{'Save changes' if edit else 'Save laptop'}</button></div></form>''', mode, session)


def row_html(row: sqlite3.Row) -> str:
    status, days, color = coverage_status(row)
    sub = f"{h(row['manufacturer'])} {h(row['model'])}"
    return f'''<tr><td><a class="serial" href="/asset/{row['id']}">{h(row['serial_number'])}</a><div class="tiny">{sub}</div></td><td><strong>{h(row['client_name'])}</strong></td><td>{human_date(row['purchase_date'])}</td><td>{h(row['coverage_type'])}</td><td class="number">{human_date(row['coverage_end'])}</td><td><span class="badge {color}">{h(status)}</span><div class="tiny">{h(remaining_text(status,days))}</div></td><td><a href="/asset/{row['id']}">View →</a></td></tr>'''


def dashboard(session: dict, query: str = "", page: int = 1, msg: str = "", status_filter: str = "") -> str:
    today = dt.date.today().isoformat()
    in30 = (dt.date.today() + dt.timedelta(days=30)).isoformat()
    with db_connect() as db:
        total = db.execute("SELECT COUNT(*) FROM assets").fetchone()[0]
        clients = db.execute("SELECT COUNT(DISTINCT client_name) FROM assets").fetchone()[0]
        covered = db.execute("SELECT COUNT(*) FROM assets WHERE coverage_type != 'No Coverage' AND coverage_start <= ? AND coverage_end >= ?",(today,today)).fetchone()[0]
        expiring = db.execute("SELECT COUNT(*) FROM assets WHERE coverage_type != 'No Coverage' AND coverage_start <= ? AND coverage_end BETWEEN ? AND ?", (today,today,in30)).fetchone()[0]
        terms: list[str] = []
        params: list = []
        if query.strip():
            key = normalize_serial(query)
            if key:
                terms.append("(serial_key LIKE ? OR client_name LIKE ? OR model LIKE ? OR invoice_number LIKE ?)")
                params.extend([f"%{key}%",f"%{query.strip()}%",f"%{query.strip()}%",f"%{query.strip()}%"])
        filters = {
            "covered": "coverage_type != 'No Coverage' AND coverage_start <= ? AND coverage_end >= ?",
            "expiring": "coverage_type != 'No Coverage' AND coverage_start <= ? AND coverage_end BETWEEN ? AND ?",
            "expired": "coverage_type != 'No Coverage' AND coverage_end < ?",
            "none": "coverage_type = 'No Coverage'",
        }
        if status_filter in filters:
            terms.append("("+filters[status_filter]+")")
            params.extend(([today,today] if status_filter=='covered' else [today,today,in30] if status_filter=='expiring' else [today] if status_filter=='expired' else []))
        where = " WHERE " + " AND ".join(terms) if terms else ""
        matched = db.execute("SELECT COUNT(*) FROM assets"+where,params).fetchone()[0]
        page = max(1,min(page, max(1,(matched+49)//50)))
        rows = db.execute("SELECT * FROM assets"+where+" ORDER BY CASE WHEN coverage_end IS NULL THEN 1 ELSE 0 END, coverage_end ASC, id DESC LIMIT 50 OFFSET ?",[*params,(page-1)*50]).fetchall()
    metrics = [('Registered laptops',total,'Complete laptop register',''),('Currently covered',covered,'Active LMC coverage','covered'),('Expiring ≤ 30 days',expiring,'Follow up for renewals','expiring'),('B2B clients',clients,'Distinct client names','')]
    cards = ''.join(f'<a class="card" href="/{"?status="+m[3] if m[3] else ""}" style="text-decoration:none;color:inherit"><div class="label">{m[0]}</div><div class="value number">{m[1]}</div><div class="foot">{m[2]}</div></a>' for m in metrics)
    rows_html = ''.join(row_html(row) for row in rows) if rows else '<tr><td colspan="7"><div class="empty">No matching laptops. Register a laptop or try another serial number.</div></td></tr>'
    pre = f'<div class="notice">{h(msg)}</div>' if msg else ''
    search = f'''<form class="search" action="/" method="get"><input class="input" name="q" value="{h(query)}" placeholder="Enter serial number, client, model or invoice..." autofocus><button class="btn" type="submit">Find laptop →</button></form>'''
    title = "Matching laptops" if query or status_filter else "Laptop register"
    pg = ''
    def pgurl(p):
        return '/?'+urlencode(dict(q=query,status=status_filter,page=p))
    if matched>50:
        pg = f'''<div class="pagination">{'<a class="btn secondary small" href="'+h(pgurl(page-1))+'">← Previous</a>' if page>1 else ''}<span>Page {page} of {(matched+49)//50}</span>{'<a class="btn secondary small" href="'+h(pgurl(page+1))+'">Next →</a>' if page*50<matched else ''}</div>'''
    return document(f'''<div class="hero"><div><div class="eyebrow">SERVICE COVERAGE CONTROL</div><h1>AMC dashboard</h1><p class="subtitle muted">One reliable place to verify every refurbished laptop sold by LMC World.</p></div><a class="btn" href="/asset/new">＋ Register laptop</a></div>{pre}<section class="cards">{cards}</section><section class="panel"><div class="eyebrow" style="margin-bottom:8px">QUICK SERIAL SEARCH</div><h2>Find a laptop in seconds</h2>{search}<p class="helper">Type the full Dell service tag or part of a client's name. Search is case-insensitive.</p></section><section class="panel"><div class="split"><h2>{title} <span class="muted" style="font-size:14px;font-weight:500">({matched})</span></h2><div class="actions"><a class="btn secondary small" href="/import">↑ Import CSV</a><a class="btn secondary small" href="/export.csv">↓ Export</a>{'<a href="/" class="btn secondary small">Clear filter</a>' if query or status_filter else ''}</div></div><div class="tablewrap"><table><thead><tr><th>Serial / model</th><th>Client</th><th>Purchase</th><th>LMC plan</th><th>Ends</th><th>Coverage status</th><th></th></tr></thead><tbody>{rows_html}</tbody></table></div>{pg}</section>''', 'AMC Dashboard',session,'dashboard')


def asset_detail(session: dict, asset: sqlite3.Row, msg: str = "", error: str = "") -> str:
    status, days, color = coverage_status(asset)
    pairs = [('Client / business',asset['client_name']),('Manufacturer',asset['manufacturer']),('Model',asset['model']),('Serial number',asset['serial_number']),('Purchase date',human_date(asset['purchase_date'])),('Invoice reference',asset['invoice_number'] or '—'),('LMC coverage type',asset['coverage_type']),('Coverage start',human_date(asset['coverage_start'])),('Coverage end (inclusive)',human_date(asset['coverage_end']))]
    details = ''.join(f'<div class="detail"><div class="name">{h(k)}</div><div class="answer">{h(v)}</div></div>' for k,v in pairs)
    with db_connect() as db:
        history = db.execute("SELECT * FROM history WHERE asset_id=? ORDER BY id DESC LIMIT 30",(asset['id'],)).fetchall()
    history_html = ''.join(f'<tr><td>{h(x["created_at"][:16])} UTC</td><td>{h(x["action"])}</td><td style="white-space:normal;min-width:220px">{h(x["detail"])}</td></tr>' for x in history) if history else '<tr><td colspan="3">No events yet.</td></tr>'
    notice = f'<div class="notice {"error" if error else ""}">{h(error or msg)}</div>' if error or msg else ''
    renew = '' if asset['coverage_type']=='No Coverage' else f'''<section class="panel"><h2>Renew / extend LMC coverage</h2><p class="subtitle muted">Updates the current plan and keeps the previous dates in the activity history.</p><form method="post" action="/asset/{asset['id']}/renew">{csrf_field(session)}<div class="formgrid"><div class="field"><label>New coverage start</label><input class="input" type="date" name="coverage_start" value="{h(asset['coverage_start'] or '')}" required></div><div class="field"><label>New coverage end (inclusive)</label><input class="input" type="date" name="coverage_end" min="{h(asset['coverage_start'] or '')}" value="{h(asset['coverage_end'] or '')}" required></div><div class="field wide"><label>Renewal invoice / comment (optional)</label><input class="input" name="comment" maxlength="250" placeholder="e.g. AMC renewed; INV-2027-001"></div></div><div class="actions" style="margin-top:18px"><button class="btn" type="submit">Save renewal</button></div></form></section>'''
    return document(f'''<div class="hero"><div><div class="eyebrow">LAPTOP LOOKUP RESULT</div><h1>{h(asset['manufacturer'])} {h(asset['model'])}</h1><p class="subtitle muted">Serial: <strong>{h(asset['serial_number'])}</strong> · {h(asset['client_name'])}</p></div><div class="actions"><a class="btn secondary" href="/">← Dashboard</a><a class="btn" href="/asset/{asset['id']}/edit">Edit record</a></div></div>{notice}<section class="statusbox {color}"><span class="badge {color}">{h(status.upper())}</span><div class="big">{h(remaining_text(status,days))}</div><div class="muted">{h(asset['coverage_type'])} · Coverage ends {human_date(asset['coverage_end'])}</div></section><section class="panel"><h2>Customer &amp; coverage details</h2><div class="details">{details}<div class="detail wide"><div class="name">AMC terms / service notes</div><div class="answer" style="font-weight:500;white-space:pre-wrap">{h(asset['notes'] or 'No additional notes recorded.')}</div></div></div></section>{renew}<section class="panel"><h2>Record activity</h2><div class="tablewrap"><table><thead><tr><th>When</th><th>Action</th><th>Details</th></tr></thead><tbody>{history_html}</tbody></table></div></section>''','Laptop details',session)


def import_page(session: dict, message: str = "", error: bool = False) -> str:
    notice = f'<div class="notice {"error" if error else ""}">{h(message)}</div>' if message else ''
    return document(f'''<div class="hero"><div><div class="eyebrow">BULK ONBOARDING</div><h1>Import laptop records</h1><p class="subtitle muted">Move your historical invoice records into the AMC register with a CSV file.</p></div><a class="btn secondary" href="/">← Dashboard</a></div>{notice}<section class="panel"><h2>1. Prepare your CSV</h2><p class="muted">Download the template, fill one row per laptop, and save as UTF-8 CSV. Purchase and coverage dates can be YYYY-MM-DD or DD/MM/YYYY.</p><a class="btn secondary" href="/template.csv">↓ Download blank template</a><p class="helper">Required columns: client_name, model, serial_number, purchase_date, coverage_type. For AMC/LMC Warranty, coverage_start and coverage_end are also required.</p></section><section class="panel"><h2>2. Upload and import</h2><form action="/import" method="post" enctype="multipart/form-data">{csrf_field(session)}<div class="field" style="margin-bottom:19px"><label for="file">CSV file (maximum 2 MB)</label><input id="file" class="input" type="file" name="file" accept=".csv,text/csv" required></div><button class="btn" type="submit">Import laptop records</button></form><p class="helper" style="margin-top:14px">Existing serial numbers are skipped, never silently overwritten. Invalid rows are reported. Export a backup before large imports.</p></section>''','Import CSV',session,'import')


def guest_page(session: dict, asset: sqlite3.Row | None = None, error: str = "", serial: str = "", login_error: str = "") -> str:
    # Unified public landing: read-only exact-serial lookup and separate admin authentication.
    notice = f'<div class="notice error" role="alert">{h(error)}</div>' if error else ''
    login_notice = f'<div class="notice error" role="alert">{h(login_error)}</div>' if login_error else ''
    result = ''
    if asset is not None:
        status, days, color = coverage_status(asset)
        # The business owner is deliberately public on exact-serial matches.
        # Never expose purchase dates, invoice references, internal notes,
        # asset IDs or history in this response.
        fields = [('Owner / B2B client', asset['client_name']),
                  ('Manufacturer', asset['manufacturer']), ('Model', asset['model']),
                  ('Serial number', asset['serial_number']),
                  ('Coverage starts', human_date(asset['coverage_start'])),
                  ('Coverage ends (inclusive)', human_date(asset['coverage_end']))]
        details = ''.join(f'<div class="detail"><div class="name">{h(label)}</div><div class="answer">{h(value)}</div></div>' for label, value in fields)
        result = f'''<section class="panel guest-result" aria-label="Coverage result"><h2 style="margin-top:0">{h(asset['manufacturer'])} {h(asset['model'])}</h2><div class="statusbox {color}"><span class="badge {color}">{h(status.upper())}</span><div class="big">{h(remaining_text(status, days))}</div></div><div class="details">{details}</div></section>'''
    # Always render a single public landing. Results precede both forms.
    # Avoid autofocus after a result so the browser doesn't scroll away from it.
    focus = '' if asset is not None or login_error else ' autofocus'
    content = f'''<div class="landing-shell"><div class="landing-intro"><h1>AMC Portal</h1></div>{result}<div class="landing-grid"><section class="panel" id="coverage" aria-label="Coverage lookup"><h2>Check Coverage</h2>{notice}<form method="post" action="/guest/lookup">{csrf_field(session)}<div class="field"><label for="serial_number">Enter Serial Number</label><input class="input" id="serial_number" name="serial_number" value="{h(serial)}" placeholder="e.g. XHDHDJDJ" minlength="3" maxlength="100" required{focus} autocomplete="off"></div><button class="btn" type="submit">Submit</button></form></section><section class="panel" id="admin"><h2>Admin Login</h2>{login_notice}<form action="/login" method="post"><div class="field"><label for="admin_password">Enter password</label><input class="input" id="admin_password" type="password" name="password" required autocomplete="current-password"></div><button class="btn" type="submit">Log In</button></form></section></div></div>'''
    return document(content, 'AMC Portal', guest=True)


class AppHandler(BaseHTTPRequestHandler):
    server_version = "LMCAMC/1.8.5"

    def log_message(self, fmt, *args):
        print(f"[{self.log_date_time_string()}] {self.address_string()} {fmt % args}")

    def send(self, body: str | bytes, status: int = 200, content_type: str = "text/html; charset=utf-8", headers: dict | None = None):
        raw = body.encode("utf-8") if isinstance(body,str) else body
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(raw)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("X-Frame-Options", "DENY")
        self.send_header("Referrer-Policy", "no-referrer")
        if CLOUD:
            self.send_header("Strict-Transport-Security", "max-age=31536000")
        self.send_header("Content-Security-Policy", "default-src 'none'; style-src 'unsafe-inline'; form-action 'self'; base-uri 'none'; frame-ancestors 'none'")
        for key, value in (headers or {}).items():
            self.send_header(key, value)
        self.end_headers()
        self.wfile.write(raw)

    def redirect(self, path: str, cookie: str | None = None):
        self.send("",303,headers={**{"Location":path}, **({"Set-Cookie":cookie} if cookie else {})})

    def fail(self, status: int, message: str):
        self.send(document(f'<div class="panel"><h1>{status}</h1><p>{h(message)}</p><a href="/" class="btn secondary">Go to dashboard</a></div>',"Error"),status)

    def session(self) -> dict | None:
        cookie = SimpleCookie()
        try:
            cookie.load(self.headers.get("Cookie", ""))
            token = cookie["lmc_session"].value if "lmc_session" in cookie else ""
        except Exception:
            return None
        with LOCK:
            session = SESSIONS.get(token)
            if not session:
                return None
            if time.time() - session["last"] > 8 * 3600:
                SESSIONS.pop(token,None)
                return None
            session["last"] = time.time()
            return session

    def guest_session(self) -> dict | None:
        cookie = SimpleCookie()
        try:
            cookie.load(self.headers.get('Cookie', ''))
            token = cookie['lmc_guest'].value if 'lmc_guest' in cookie else ''
        except Exception:
            return None
        with LOCK:
            session = GUEST_SESSIONS.get(token)
            if session is None:
                return None
            if time.time() - session['last'] > 2 * 3600:
                GUEST_SESSIONS.pop(token, None)
                return None
            session['last'] = time.time()
            return session

    def ensure_guest_session(self) -> tuple[dict, str | None]:
        session = self.guest_session()
        if session is not None:
            return session, None
        token = secrets.token_urlsafe(32)
        session = {'csrf': secrets.token_urlsafe(32), 'last': time.time(), 'token': token}
        with LOCK:
            now = time.time()
            for key, old in list(GUEST_SESSIONS.items()):
                if now - old['last'] > 2 * 3600:
                    GUEST_SESSIONS.pop(key, None)
            GUEST_SESSIONS[token] = session
        cookie = f'lmc_guest={token}; HttpOnly; SameSite=Strict; Path=/' + ('; Secure' if os.environ.get('AMC_HTTPS') == '1' else '')
        return session, cookie

    def guest_entry(self, login_error: str = '', status: int = 200):
        session, cookie = self.ensure_guest_session()
        headers = {'Set-Cookie': cookie} if cookie else None
        return self.send(guest_page(session, login_error=login_error), status, headers=headers)

    def guest_rate_limited(self, token: str) -> bool:
        return not consume_lookup_allowance(token, self.visitor_ip())

    def visitor_ip(self) -> str:
        """On Render use the forwarded client IP; locally ignore spoofed headers.

        Prefer the last address instead of the leftmost user-supplied XFF item:
        a caller cannot change an existing trusted proxy-appended address by
        prepending a fake value. If the header is absent or invalid, fall back
        to the socket IP; a site-wide ceiling still applies either way.
        """
        if CLOUD:
            forwarded = self.headers.get('X-Forwarded-For', '')
            if forwarded:
                candidate = forwarded.split(',')[-1].strip()
                try:
                    return str(ipaddress.ip_address(candidate))
                except ValueError:
                    pass
        return self.client_address[0]

    def form(self) -> dict:
        length = int(self.headers.get("Content-Length", "0"))
        if length < 0 or length > MAX_UPLOAD:
            raise ValueError("Request too large (maximum 2 MB).")
        raw = self.rfile.read(length)
        kind = self.headers.get("Content-Type", "")
        if kind.startswith("multipart/form-data"):
            wire = ("Content-Type: " + kind + "\r\nMIME-Version: 1.0\r\n\r\n").encode() + raw
            message = BytesParser(policy=policy.default).parsebytes(wire)
            result = {}
            for part in message.iter_parts():
                if part.get_content_disposition() != "form-data":
                    continue
                name = part.get_param("name",header="content-disposition")
                if name == 'file':
                    result["file"] = part.get_payload(decode=True)
                    result["filename"] = part.get_filename() or ""
                elif name:
                    result[name] = part.get_payload(decode=True).decode("utf-8",errors="replace")
            return result
        if not kind.startswith("application/x-www-form-urlencoded"):
            raise ValueError("Expected a form submission.")
        return {k:v[0] for k,v in parse_qs(raw.decode('utf-8'),keep_blank_values=True).items()}

    def setup_done(self) -> bool:
        with db_connect() as db:
            return db.execute("SELECT value FROM settings WHERE key='admin_password'").fetchone() is not None

    def do_GET(self):
        try:
            self.handle_get()
        except (BrokenPipeError,ConnectionResetError):
            pass
        except Exception as exc:
            print("GET error:",repr(exc))
            self.fail(500,"Unexpected server error. Please check the terminal log.")

    def handle_get(self):
        path = urlparse(self.path).path
        if path == '/healthz':
            ready = self.setup_done()
            return self.send('ok' if ready else 'not ready', 200 if ready else 503, 'text/plain; charset=utf-8')
        qs = parse_qs(urlparse(self.path).query)
        arg = lambda x: (qs.get(x) or [""])[0]
        if not self.setup_done():
            if CLOUD:
                return self.fail(503, 'Administrator setup is not complete. Check deployment configuration.')
            if path != '/setup':
                return self.redirect('/setup')
            return self.send(self.setup_page())
        if path in ('/', '/login'):
            session = self.session()
            if session is None:
                return self.guest_entry()
            if path == '/login':
                return self.redirect('/')
        if path == '/guest':
            return self.guest_entry()
        session = self.session()
        if not session:
            return self.redirect('/login')
        if path == '/':
            try: page = int(arg('page') or '1')
            except ValueError: page = 1
            return self.send(dashboard(session,arg('q'),page,arg('msg'),arg('status')))
        if path == '/asset/new':
            return self.send(asset_form(session))
        match = re.fullmatch(r'/asset/(\d+)(/edit)?',path)
        if match:
            with db_connect() as db:
                asset = db.execute("SELECT * FROM assets WHERE id=?",(int(match[1]),)).fetchone()
            if not asset: return self.fail(404,"Laptop not found.")
            return self.send(asset_form(session,asset) if match[2] else asset_detail(session,asset,arg('msg')))
        if path == '/import':
            return self.send(import_page(session))
        if path == '/template.csv':
            out=io.StringIO()
            csv.writer(out).writerow(['client_name','manufacturer','model','serial_number','purchase_date','coverage_type','coverage_start','coverage_end','invoice_number','notes'])
            return self.send(out.getvalue(),content_type='text/csv; charset=utf-8',headers={'Content-Disposition':'attachment; filename="LMC_AMC_import_template.csv"'})
        if path == '/export.csv':
            with db_connect() as db:
                assets = db.execute('SELECT * FROM assets ORDER BY client_name, serial_key').fetchall()
            out=io.StringIO()
            fields=['client_name','manufacturer','model','serial_number','purchase_date','coverage_type','coverage_start','coverage_end','invoice_number','notes']
            writer=csv.writer(out)
            writer.writerow(fields + ['current_status','days_to_expiry'])
            for asset in assets:
                status,days,_=coverage_status(asset)
                def safe(v):
                    s=str(v or '')
                    return "'"+s if s.lstrip().startswith(('=','+','-','@')) else s
                writer.writerow([safe(asset[f]) for f in fields]+[status,days if days is not None else ''])
            return self.send(out.getvalue(),content_type='text/csv; charset=utf-8',headers={'Content-Disposition':'attachment; filename="LMC_AMC_export.csv"'})
        if path == '/backup.db':
            with tempfile.TemporaryDirectory() as folder:
                snapshot = Path(folder) / 'backup.db'
                with db_connect() as source:
                    target = sqlite3.connect(snapshot)
                    try:
                        source.backup(target)
                    finally:
                        target.close()
                data = snapshot.read_bytes()
            return self.send(data,content_type='application/octet-stream',headers={'Content-Disposition':'attachment; filename="LMC_AMC_backup.db"'})
        return self.fail(404,'Page not found.')

    def setup_page(self,error=''):
        notice=f'<div class="notice error">{h(error)}</div>' if error else ''
        return document(f'''<div class="login"><div class="panel"><div class="eyebrow">WELCOME TO LMC WORLD</div><h1>Set up AMC Manager</h1><p class="subtitle muted">Create an administrator password. Your laptop database will be stored locally in the <strong>data</strong> folder.</p>{notice}<form action="/setup" method="post"><div class="field"><label>Choose password (minimum 10 characters)</label><input class="input" type="password" name="password" minlength="10" required autocomplete="new-password"></div><div class="field"><label>Confirm password</label><input class="input" type="password" name="confirm" minlength="10" required autocomplete="new-password"></div><button class="btn" type="submit">Create secure account</button></form><p class="helper">First-time setup is only allowed from this computer. Back up your database regularly.</p></div></div>''','Setup')


    def do_POST(self):
        try:
            self.handle_post()
        except (BrokenPipeError,ConnectionResetError):
            pass
        except ValueError as exc:
            self.fail(400,str(exc))
        except Exception as exc:
            print('POST error:',repr(exc))
            self.fail(500,"Unexpected server error. Please check the terminal log.")

    def handle_post(self):
        path=urlparse(self.path).path
        form=self.form()
        if not self.setup_done():
            if CLOUD:
                return self.fail(503, 'Administrator setup is not complete. Check deployment configuration.')
            if path!='/setup': return self.redirect('/setup')
            if self.client_address[0] not in ('127.0.0.1','::1'):
                return self.fail(403,'First-time setup must be completed on the server computer.')
            pw=str(form.get('password',''))
            if len(pw)<10 or len(pw)>200 or pw!=form.get('confirm'):
                return self.send(self.setup_page('Use matching passwords of at least 10 characters (maximum 200).'),400)
            with db_connect() as db:
                db.execute("INSERT INTO settings(key,value) VALUES('admin_password',?)",(password_hash(pw),))
            return self.redirect('/login')
        if path=='/login':
            ip=self.visitor_ip()
            now=time.time()
            with LOCK:
                failures=[t for t in LOGIN_FAILURES.get(ip,[]) if now-t<900]
                LOGIN_FAILURES[ip]=failures
                if len(failures)>=8:
                    return self.guest_entry(login_error='Too many attempts. Try again in 15 minutes.', status=429)
            with db_connect() as db:
                stored=db.execute("SELECT value FROM settings WHERE key='admin_password'").fetchone()['value']
            if not verify_password(str(form.get('password','')),stored):
                with LOCK: LOGIN_FAILURES.setdefault(ip,[]).append(now)
                return self.guest_entry(login_error='Incorrect password.', status=401)
            token=secrets.token_urlsafe(32)
            with LOCK:
                LOGIN_FAILURES.pop(ip,None)
                SESSIONS[token]={'csrf':secrets.token_urlsafe(32),'last':time.time()}
            cookie=f'lmc_session={token}; HttpOnly; SameSite=Strict; Path=/'+('; Secure' if os.environ.get('AMC_HTTPS')=='1' else '')
            return self.redirect('/',cookie)
        if path == '/guest/lookup':
            guest = self.guest_session()
            if guest is None:
                return self.redirect('/')
            if not hmac.compare_digest(str(form.get('csrf', '')), guest['csrf']):
                return self.fail(403, 'Guest session verification failed. Reload Guest Check and try again.')
            if self.guest_rate_limited(guest['token']):
                return self.send(guest_page(guest, error='Too many searches. Please try again in 15 minutes.'),
                                 429, headers={'Retry-After': str(RATE_WINDOW_SECONDS)})
            serial = str(form.get('serial_number', ''))
            key = normalize_serial(serial)
            if len(serial) > 100 or len(key) < 3 or len(key) > 100:
                return self.send(guest_page(guest, error='Enter the complete serial number (3–100 characters).'), 400)
            with db_connect() as db:
                # Exact match only. Public fields are explicitly allowlisted.
                asset = db.execute('SELECT client_name, manufacturer, model, serial_number, coverage_type, coverage_start, coverage_end FROM assets WHERE serial_key=?', (key,)).fetchone()
            if asset is None:
                return self.send(guest_page(guest, error='No matching coverage record found. Check the full serial number or contact LMC World.'), 200)
            return self.send(guest_page(guest, asset=asset))
        session=self.session()
        if not session:
            return self.redirect('/login')
        if not hmac.compare_digest(str(form.get('csrf','')),session['csrf']):
            return self.fail(403,'Session verification failed. Reload the form and try again.')
        if path=='/logout':
            cookie=SimpleCookie()
            cookie.load(self.headers.get('Cookie',''))
            with LOCK:
                if 'lmc_session' in cookie: SESSIONS.pop(cookie['lmc_session'].value,None)
            return self.redirect('/login','lmc_session=; Max-Age=0; HttpOnly; SameSite=Strict; Path=/' + ('; Secure' if os.environ.get('AMC_HTTPS') == '1' else ''))
        if path=='/asset/create':
            try: data=validate_asset(form)
            except ValueError as exc:
                return self.send(asset_form(session,error=str(exc),form=form),400)
            try:
                with db_connect() as db:
                    cols=list(data)
                    cur=db.execute(f"INSERT INTO assets({','.join(cols)}) VALUES ({','.join('?' for _ in cols)})",list(data.values()))
                    db.execute("INSERT INTO history(asset_id,action,detail) VALUES (?, ?, ?)",(cur.lastrowid,'Created','Initial laptop and coverage record registered.'))
                    new_id=cur.lastrowid
            except sqlite3.IntegrityError:
                return self.send(asset_form(session,error='Serial number already exists. Search for it and edit the existing record.',form=form),409)
            return self.redirect(f'/asset/{new_id}?msg='+quote('Laptop successfully registered.'))
        edit=re.fullmatch(r'/asset/(\d+)/edit',path)
        if edit:
            aid=int(edit[1])
            with db_connect() as db: old=db.execute('SELECT * FROM assets WHERE id=?',(aid,)).fetchone()
            if not old: return self.fail(404,'Laptop not found.')
            try: data=validate_asset(form)
            except ValueError as exc:
                return self.send(asset_form(session,old,error=str(exc),form=form),400)
            changes=[key for key in data if old[key]!=data[key]]
            if changes:
                try:
                    with db_connect() as db:
                        db.execute('UPDATE assets SET '+','.join(f'{k}=?' for k in data)+",updated_at=datetime('now') WHERE id=?",list(data.values())+[aid])
                        change_text='Updated: '+', '.join(k.replace('_',' ') for k in changes)
                        if any(k in changes for k in ('coverage_type','coverage_start','coverage_end')):
                            change_text+=f". Previous coverage: {old['coverage_type']} {old['coverage_start'] or '—'} to {old['coverage_end'] or '—'}."
                        db.execute('INSERT INTO history(asset_id,action,detail) VALUES (?,?,?)',(aid,'Edited',change_text))
                except sqlite3.IntegrityError:
                    return self.send(asset_form(session,old,error='Serial number already belongs to another record.',form=form),409)
            return self.redirect(f'/asset/{aid}?msg='+quote('Record saved.'))
        renew=re.fullmatch(r'/asset/(\d+)/renew',path)
        if renew:
            aid=int(renew[1])
            with db_connect() as db: old=db.execute('SELECT * FROM assets WHERE id=?',(aid,)).fetchone()
            if not old:return self.fail(404,'Laptop not found.')
            if old['coverage_type']=='No Coverage':return self.fail(400,'Edit this laptop to add a coverage plan first.')
            try:
                start=parse_date(str(form.get('coverage_start','')))
                end=parse_date(str(form.get('coverage_end','')))
                if end<start:raise ValueError('Coverage end date cannot be before the start.')
                comment=str(form.get('comment','')).strip()
                if len(comment)>250:raise ValueError('Comment must be 250 characters or fewer.')
            except ValueError as exc:
                return self.send(asset_detail(session,old,error=str(exc)),400)
            with db_connect() as db:
                db.execute("UPDATE assets SET coverage_start=?,coverage_end=?,updated_at=datetime('now') WHERE id=?",(start,end,aid))
                detail=f"Previous: {old['coverage_start']} to {old['coverage_end']}. New: {start} to {end}."+(f' Note: {comment}' if comment else '')
                db.execute("INSERT INTO history(asset_id,action,detail) VALUES (?,?,?)",(aid,'Renewed',detail))
            return self.redirect(f'/asset/{aid}?msg='+quote('Coverage dates updated; previous dates preserved in activity.'))
        if path=='/import':
            try:
                blob=form.get('file',b'')
                if not isinstance(blob,bytes) or not blob:
                    raise ValueError('Choose a non-empty CSV file.')
                if len(blob)>MAX_UPLOAD:
                    raise ValueError('File too large.')
                if not str(form.get('filename','')).lower().endswith('.csv'):
                    raise ValueError('Please select a .csv file.')
                content=blob.decode('utf-8-sig')
                reader=csv.DictReader(io.StringIO(content))
                if not reader.fieldnames:
                    raise ValueError('CSV does not contain column headers.')
                reader.fieldnames=[(name or '').strip() for name in reader.fieldnames]
                required={'client_name','model','serial_number','purchase_date','coverage_type','coverage_start','coverage_end'}
                if not required.issubset(reader.fieldnames):
                    raise ValueError('Missing columns: '+', '.join(sorted(required-set(reader.fieldnames))))
                added=0; duplicates=0; invalid=[]
                with db_connect() as db:
                    for rowno,row in enumerate(reader,2):
                        if rowno>5001:
                            invalid.append('Only the first 5,000 rows were processed.');break
                        try:
                            if None in row: raise ValueError('Extra columns found; check commas and quoting.')
                            data=validate_asset(row)
                            cols=list(data)
                            cur=db.execute(f"INSERT OR IGNORE INTO assets({','.join(cols)}) VALUES ({','.join('?' for _ in cols)})",list(data.values()))
                            if cur.rowcount==0: duplicates+=1
                            else:
                                added+=1
                                db.execute('INSERT INTO history(asset_id,action,detail) VALUES (?,?,?)',(cur.lastrowid,'Imported','Imported from CSV.'))
                        except (ValueError, TypeError) as exc:
                            if len(invalid)<10:invalid.append(f'Row {rowno}: {str(exc)}')
                message=f'Import finished: {added} added, {duplicates} duplicates skipped, {len(invalid)} row errors shown.'
                if invalid:message+=' '+ ' | '.join(invalid)
                return self.send(import_page(session,message,bool(invalid)))
            except (ValueError,UnicodeError,csv.Error) as exc:
                return self.send(import_page(session,str(exc),True),400)
        return self.fail(404,'Page not found.')


def run():
    validate_cloud_configuration()
    init_db()
    bootstrap_cloud_admin()
    if HOST not in ('127.0.0.1','localhost','::1'):
        print('SECURITY NOTE: Network access enabled. Use the Render HTTPS proxy and public lookup abuse controls. Do not expose the server port directly.')
    print(f'LMC AMC Manager running at http://{HOST}:{PORT}')
    print(f'Database: {DB_PATH}')
    httpd=ThreadingHTTPServer((HOST,PORT),AppHandler)
    try:httpd.serve_forever()
    except KeyboardInterrupt:print('\nStopping LMC AMC Manager.')
    finally:httpd.server_close()


if __name__ == '__main__':
    run()
