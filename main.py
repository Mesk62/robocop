import os
import re
import json
import time
import uuid
import random
import sqlite3
import colorsys
import aiosqlite
import asyncio
from collections import deque
from datetime import datetime, timedelta, timezone
from typing import Optional
from difflib import SequenceMatcher
from zoneinfo import ZoneInfo

import aiohttp
import discord
from discord.ext import commands
from discord import app_commands
from dotenv import load_dotenv

# ============================================================
#  CONFIG
# ============================================================
load_dotenv()
DISCORD_TOKEN = os.getenv("DISCORD_TOKEN")
GOOGLE_API_KEY = os.getenv("GOOGLE_API_KEY")

# ------------------------------------------------------------
#  DATABASE LOCATION — deliberately NOT next to this script by default.
#  This bot is often run from a cloud-synced folder (Google Drive for
#  Desktop's G:\My Drive, OneDrive, Dropbox). SQLite on those virtual
#  filesystems fails with 'disk I/O error': the sync engine grabs the
#  journal/WAL files mid-write, and WAL mode's memory-mapped -shm file
#  isn't supported on non-local filesystems at all (per SQLite's own
#  docs). So the live DB goes to a local, non-synced app-data folder:
#    Windows: %LOCALAPPDATA%\RoboCop\robocop.db
#    else:    ~/.local/share/RoboCop/robocop.db
#  Override with ROBOCOP_DB_PATH=... in .env (keep it on a local disk).
#  An old robocop.db beside the script is migrated over once, automatically.
# ------------------------------------------------------------
CLOUD_SYNC_MARKERS = ("my drive", "google drive", "googledrive", "onedrive", "dropbox", "icloud", "mobile documents")


def _resolve_db_path() -> str:
    override = os.getenv("ROBOCOP_DB_PATH")
    if override:
        return os.path.abspath(os.path.expanduser(override))
    base = os.getenv("LOCALAPPDATA") or os.path.join(os.path.expanduser("~"), ".local", "share")
    return os.path.join(base, "RoboCop", "robocop.db")


DB_PATH = _resolve_db_path()


def _looks_cloud_synced(path: str) -> bool:
    low = path.replace("\\", "/").lower()
    return any(marker in low for marker in CLOUD_SYNC_MARKERS)


def migrate_legacy_db():
    """One-time move of an old 'robocop.db' (from beside the script, or the
    working directory) to DB_PATH. Uses SQLite's backup API rather than a
    file copy, because in WAL mode recently committed data can live only
    in robocop.db-wal — a plain copy of robocop.db would silently drop it.
    Falls back to copying db + wal together if the old file can't be
    opened. Never deletes the old file (opening it may fold its -wal into
    it — normal SQLite behaviour, and it leaves the old file self-contained)."""
    import shutil
    os.makedirs(os.path.dirname(DB_PATH), exist_ok=True)
    if _looks_cloud_synced(DB_PATH):
        print(f"[WARNING] ⚠️ ROBOCOP_DB_PATH points into a cloud-synced folder ({DB_PATH}). Expect 'disk I/O error'. Use a local folder instead.")
    if os.path.exists(DB_PATH):
        return

    script_dir = os.path.dirname(os.path.abspath(__file__))
    candidates = []
    for d in (script_dir, os.getcwd()):
        p = os.path.join(d, "robocop.db")
        if os.path.exists(p) and os.path.abspath(p) != DB_PATH and p not in candidates:
            candidates.append(p)
    if not candidates:
        print(f"[SYSTEM] 🗂️ No existing database found — starting fresh at {DB_PATH} (the startup inventory will rebuild membership from the live server).")
        return
    legacy = candidates[0]

    print(f"[SYSTEM] 🗂️ Moving database off {legacy}\n         → {DB_PATH}")
    try:
        src = sqlite3.connect(legacy, timeout=30)
        dst = sqlite3.connect(DB_PATH)
        src.backup(dst)
        dst.close()
        src.close()
        method = "SQLite backup (WAL contents included)"
    except sqlite3.Error as e:
        print(f"[WARNING] Backup API couldn't read the old database ({e}) — falling back to a raw file copy.")
        for suffix in ("", "-journal", "-shm"):
            try:
                os.remove(DB_PATH + suffix)
            except OSError:
                pass
        shutil.copy2(legacy, DB_PATH)
        if os.path.exists(legacy + "-wal"):
            shutil.copy2(legacy + "-wal", DB_PATH + "-wal")  # SQLite replays it on first open
        method = "raw file copy"

    try:
        with sqlite3.connect(DB_PATH) as check_conn:
            verdict = check_conn.execute("PRAGMA integrity_check").fetchone()[0]
    except sqlite3.Error as e:
        verdict = f"could not run ({e})"
    if verdict == "ok":
        print(f"[SYSTEM] ✅ Database moved via {method}; integrity check passed. The old file at {legacy} is no longer used — archive or delete it whenever.")
    else:
        print(f"[WARNING] ⚠️ Database moved via {method}, but integrity check says: {verdict}. "
              f"The startup inventory will still rebuild membership from the live server; history may be incomplete.")


# ============================================================
#  SERVER-BUSY GATE — state (pure Python; the Discord-facing half lives
#  further down, after `bot` exists). When a heavy operation is running
#  (alliance merge, bulk onboarding, migrations...) or the bot detects it
#  is being rate-limited by Discord / locked out of the database, the
#  server is marked "busy": commands that touch roles, nicknames, games
#  or the database get a friendly "wait a few minutes" instead of piling
#  more work onto an already-straining bot. Cheap read-only commands
#  keep working. Persistent button-mashers earn a 15-minute time-out.
# ============================================================
_busy = {
    "active": False,
    "reason": "",        # short human phrase, e.g. "merging two alliances"
    "since": 0.0,        # time.monotonic()
    "until": None,       # monotonic deadline for auto-detected busy periods; None = until the operation ends
    "auto": False,       # True when triggered by rate-limit / DB-lock detection, not an admin operation
    "depth": 0,          # nested heavy operations
    "announced": False,  # general-chat "in the garage" notice posted for this period
    "quiet": False,      # True = no general-chat or #logs notices for this period (routine startup checks)
    "was_public": False, # set by the watchdog when a period starts, so the "all clear" matches it
    "was_logged": False,
}
_busy_attempts = {}                 # user_id -> attempts during the current busy period
BUSY_WARNINGS_BEFORE_TIMEOUT = 5    # the 6th attempt earns the time-out
BUSY_TIMEOUT_MINUTES = 15
BUSY_AUTO_MINUTES = 3               # how long an auto-detected (rate-limit / DB-lock) busy period lasts
BUSY_HARD_CAP_MINUTES = 20          # safety: an operation-driven busy period never outlives this
_db_lock_hits = deque(maxlen=20)    # monotonic timestamps of recent "database is locked" errors


def busy_set_sync(reason: str, minutes: float, auto: bool = True):
    """Thread/sync-safe: only mutates state. The watchdog task handles
    presence + announcements, so this is safe to call from anywhere —
    including a logging handler."""
    now = time.monotonic()
    if _busy["active"] and not _busy["auto"]:
        return  # an admin operation already owns the busy state; don't shorten it
    if not _busy["active"]:
        _busy_attempts.clear()
        _busy["since"] = now
        _busy["announced"] = False
        _busy["quiet"] = False
    _busy["active"] = True
    _busy["reason"] = reason
    _busy["auto"] = auto
    _busy["until"] = now + minutes * 60


def _note_db_lock():
    """Three 'database is locked' errors inside a minute = the DB is
    genuinely under strain -> back everyone off for a few minutes."""
    now = time.monotonic()
    _db_lock_hits.append(now)
    recent = [t for t in _db_lock_hits if now - t < 60]
    if len(recent) >= 3:
        busy_set_sync("giving the database a breather", BUSY_AUTO_MINUTES)


class _DbConnectWrapper:
    """Thin wrapper around aiosqlite's connection context manager: passes
    everything straight through, but notices 'database is locked' errors
    on the way out so the busy gate can react. Still one connection per
    `async with`, so the no-nesting rule is unchanged."""

    def __init__(self, inner):
        self._inner = inner

    async def __aenter__(self):
        return await self._inner.__aenter__()

    async def __aexit__(self, exc_type, exc, tb):
        if exc is not None and isinstance(exc, sqlite3.OperationalError) and "locked" in str(exc).lower():
            _note_db_lock()
        return await self._inner.__aexit__(exc_type, exc, tb)

    def __await__(self):
        return self._inner.__await__()


# ============================================================
#  POSTGRESQL BACKEND (9.0) — optional, switched on by DATABASE_URL.
#
#  Set DATABASE_URL=postgresql://user:password@host/dbname in .env and
#  RoboCop stores everything in PostgreSQL instead of the local SQLite
#  file. Leave it out and nothing changes: SQLite, exactly as before.
#
#  How it works: every query in this file was written for SQLite. Rather
#  than rewrite 300+ of them (and risk a typo in any one), this layer
#  hands the rest of the code the SAME connection/cursor interface
#  aiosqlite does, and translates each statement on its way to Postgres:
#    • ? placeholders            -> $1, $2, ...
#    • INSERT OR IGNORE           -> INSERT ... ON CONFLICT DO NOTHING
#    • INSERT OR REPLACE          -> INSERT ... ON CONFLICT (key) DO UPDATE
#    • CURRENT_TIMESTAMP          -> the same UTC 'YYYY-MM-DD HH:MM:SS' text SQLite produces
#    • cur.lastrowid              -> INSERT ... RETURNING <id>
#    • INTEGER / TIMESTAMP types  -> BIGINT (Discord IDs are 64-bit) / TEXT
#  Timestamps stay TEXT on purpose: the code stores and compares ISO
#  strings everywhere, and parse_db_local_time() already reads both forms.
#
#  Values are converted to whatever type Postgres expects for each
#  parameter (SQLite silently accepted '5' for 5 and vice versa; Postgres
#  doesn't), and Postgres errors are re-raised as the sqlite3 error types
#  the existing `except sqlite3.IntegrityError:` handlers already catch.
#  Every statement runs inside its own savepoint, so one failed statement
#  never poisons the rest of its connection's work — same as SQLite.
#
#  First start on an empty Postgres database with a SQLite file present:
#  every table and row is copied across automatically, once. The SQLite
#  file itself is never modified or deleted — it's your backup.
# ============================================================
DATABASE_URL = (os.getenv("DATABASE_URL") or "").strip()
USE_POSTGRES = bool(DATABASE_URL)

if USE_POSTGRES:
    try:
        import asyncpg
    except ImportError:
        raise SystemExit(
            "[CRITICAL] DATABASE_URL is set, so RoboCop wants PostgreSQL — but the 'asyncpg' package isn't installed.\n"
            "           Run:  pip install -r requirements.txt   (inside the venv), then start again.\n"
            "           Or remove DATABASE_URL from .env to keep using SQLite."
        )
    from decimal import Decimal
    from functools import lru_cache

PG_UTC_NOW = "to_char(timezone('UTC', now()), 'YYYY-MM-DD HH24:MI:SS')"
# Tables whose primary key is an auto-numbered id (SQLite AUTOINCREMENT).
# Filled in from the schema at startup; INSERTs into them get RETURNING <id>.
_PG_AUTO_ID = {}
# Primary-key columns per table, for translating INSERT OR REPLACE.
_PG_PRIMARY_KEYS = {}

_SQL_WORD_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def _pg_split_literals(sql: str):
    """Yields (is_literal, text) chunks so rewrites only ever touch real SQL,
    never the inside of a quoted string."""
    out, buf, i, n = [], [], 0, len(sql)
    while i < n:
        ch = sql[i]
        if ch in ("'", '"'):
            if buf:
                out.append((False, "".join(buf)))
                buf = []
            j = i + 1
            while j < n:
                if sql[j] == ch:
                    if j + 1 < n and sql[j + 1] == ch:
                        j += 2
                        continue
                    break
                j += 1
            out.append((True, sql[i:j + 1]))
            i = j + 1
        else:
            buf.append(ch)
            i += 1
    if buf:
        out.append((False, "".join(buf)))
    return out


def _pg_translate_ddl(sql: str) -> str:
    s = re.sub(r"\bINTEGER\s+PRIMARY\s+KEY\s+AUTOINCREMENT\b", "BIGSERIAL PRIMARY KEY", sql, flags=re.I)
    s = re.sub(r"\bAUTOINCREMENT\b", "", s, flags=re.I)
    s = re.sub(r"DEFAULT\s+CURRENT_TIMESTAMP\b", f"DEFAULT ({PG_UTC_NOW})", s, flags=re.I)
    # Type names only — case-sensitive on purpose, because there's a column
    # literally called `timestamp` (lower case) that must stay a column name.
    s = re.sub(r"\bINTEGER\b", "BIGINT", s)
    s = re.sub(r"\b(TIMESTAMP|DATETIME)\b", "TEXT", s)
    s = re.sub(r"\bREAL\b", "DOUBLE PRECISION", s)
    s = re.sub(r"\bCREATE\s+TABLE\s+(?!IF\s+NOT\s+EXISTS)", "CREATE TABLE IF NOT EXISTS ", s, flags=re.I)
    s = re.sub(r"\bADD\s+COLUMN\s+(?!IF\s+NOT\s+EXISTS)", "ADD COLUMN IF NOT EXISTS ", s, flags=re.I)
    return s


def _pg_learn_schema(create_sql: str):
    """Records a table's primary key (and whether it's an auto-numbered id)
    from its CREATE TABLE statement."""
    m = re.search(r"CREATE\s+TABLE\s+(?:IF\s+NOT\s+EXISTS\s+)?[\"']?(\w+)[\"']?\s*\((.*)\)\s*;?\s*$", create_sql, flags=re.I | re.S)
    if not m:
        return
    table, body = m.group(1), m.group(2)
    tpk = re.search(r"PRIMARY\s+KEY\s*\(([^)]*)\)", body, flags=re.I)
    if tpk:
        _PG_PRIMARY_KEYS[table] = [c.strip().strip('"') for c in tpk.group(1).split(",") if c.strip()]
    else:
        for line in body.split(","):
            cm = re.match(r"\s*[\"']?(\w+)[\"']?\s+\w+.*\bPRIMARY\s+KEY\b", line, flags=re.I | re.S)
            if cm:
                _PG_PRIMARY_KEYS[table] = [cm.group(1)]
                if re.search(r"AUTOINCREMENT|BIGSERIAL", line, flags=re.I):
                    _PG_AUTO_ID[table] = cm.group(1)
                break


def _pg_translate(sql: str):
    """SQLite SQL -> (Postgres SQL, auto_id_column_or_None). Cached, since
    the same few hundred statements repeat all day."""
    return _pg_translate_cached(sql)


def _pg_translate_uncached(sql: str):
    stripped = sql.strip().rstrip(";").strip()
    head = stripped[:20].upper()
    if head.startswith("CREATE") or head.startswith("ALTER"):
        ddl = _pg_translate_ddl(stripped)
        if head.startswith("CREATE"):
            _pg_learn_schema(ddl)
        return ddl, None
    if head.startswith("PRAGMA"):
        return "SELECT 1 WHERE FALSE", None

    parts, counter = [], 0
    for is_lit, text in _pg_split_literals(stripped):
        if is_lit:
            parts.append(text)
            continue
        text = re.sub(r"\bCURRENT_TIMESTAMP\b", PG_UTC_NOW, text, flags=re.I)
        rebuilt = []
        for ch in text:
            if ch == "?":
                counter += 1
                rebuilt.append(f"${counter}")
            else:
                rebuilt.append(ch)
        parts.append("".join(rebuilt))
    q = "".join(parts)

    # Postgres needs `x = x + 1` inside ON CONFLICT ... DO UPDATE spelled
    # `x = table.x + 1` (SQLite guessed which x you meant; Postgres won't).
    um = re.match(r"\s*INSERT\s+INTO\s+(\w+)", q, flags=re.I)
    dm = re.search(r"\bDO\s+UPDATE\s+SET\b", q, flags=re.I)
    if um and dm:
        table = um.group(1)
        head_part, set_part = q[:dm.end()], q[dm.end():]
        for col in set(re.findall(r"(?<![.\w])(\w+)\s*=(?!=)", set_part)):
            set_part = re.sub(rf"(?<![.\w$]){col}\b(?!\s*=(?!=))", f"{table}.{col}", set_part)
        q = head_part + set_part

    auto_id = None
    m = re.match(r"\s*INSERT\s+OR\s+(IGNORE|REPLACE)\s+INTO\s+(\w+)\s*(\(([^)]*)\))?", q, flags=re.I | re.S)
    if m:
        mode, table = m.group(1).upper(), m.group(2)
        q = re.sub(r"^\s*INSERT\s+OR\s+(IGNORE|REPLACE)\s+INTO", "INSERT INTO", q, count=1, flags=re.I)
        if mode == "IGNORE":
            q += " ON CONFLICT DO NOTHING"
        else:
            pk = _PG_PRIMARY_KEYS.get(table)
            cols = [c.strip() for c in (m.group(4) or "").split(",") if c.strip()]
            if not pk:
                raise sqlite3.OperationalError(f"Postgres layer: don't know the primary key of '{table}' for INSERT OR REPLACE")
            others = [c for c in cols if c not in pk]
            if others:
                q += f" ON CONFLICT ({', '.join(pk)}) DO UPDATE SET " + ", ".join(f"{c} = EXCLUDED.{c}" for c in others)
            else:
                q += f" ON CONFLICT ({', '.join(pk)}) DO NOTHING"
    im = re.match(r"\s*INSERT\s+INTO\s+(\w+)", q, flags=re.I)
    if im and im.group(1) in _PG_AUTO_ID and not re.search(r"\bRETURNING\b", q, flags=re.I):
        auto_id = _PG_AUTO_ID[im.group(1)]
        q += f" RETURNING {auto_id}"
    return q, auto_id


if USE_POSTGRES:
    _pg_translate_cached = lru_cache(maxsize=2048)(_pg_translate_uncached)
else:
    _pg_translate_cached = _pg_translate_uncached

_PG_INT_TYPES = {"int2", "int4", "int8", "oid"}
_PG_FLOAT_TYPES = {"float4", "float8"}
_PG_TEXT_TYPES = {"text", "varchar", "bpchar", "name", "unknown", "char"}


def _pg_coerce(param_types, params):
    """SQLite let '123' and 123 mix freely; Postgres wants the exact type.
    Convert each value to what this particular parameter expects."""
    params = tuple(params or ())
    out = []
    for i, v in enumerate(params):
        t = param_types[i].name if i < len(param_types) else "unknown"
        if v is None:
            out.append(None)
            continue
        if isinstance(v, bool):
            v = int(v)
        if t in _PG_INT_TYPES:
            out.append(v if isinstance(v, int) else int(float(v)) if isinstance(v, (float, Decimal)) else int(str(v).strip()))
        elif t in _PG_FLOAT_TYPES:
            out.append(float(v))
        elif t == "numeric":
            out.append(Decimal(str(v)))
        elif t in _PG_TEXT_TYPES:
            out.append(str(v))  # str(datetime) == SQLite's own adapter format
        else:
            out.append(v)
    return out


def _pg_value(v):
    if isinstance(v, Decimal):
        return int(v) if v == v.to_integral_value() else float(v)
    return v


def _pg_to_sqlite_error(e: Exception) -> Exception:
    """Re-raise Postgres errors as the sqlite3 types the code already catches."""
    msg = f"{type(e).__name__}: {e}"
    if isinstance(e, asyncpg.exceptions.IntegrityConstraintViolationError):
        return sqlite3.IntegrityError(msg)
    if isinstance(e, sqlite3.Error):
        return e
    return sqlite3.OperationalError(msg)


_pg_pool = None


async def _pg_get_pool():
    global _pg_pool
    if _pg_pool is None:
        _pg_pool = await asyncpg.create_pool(DATABASE_URL, min_size=1, max_size=20, command_timeout=30)
    return _pg_pool


class _PgCursor:
    """Just enough of aiosqlite's cursor for this codebase."""

    def __init__(self, conn):
        self._conn = conn
        self._rows = []
        self._pos = 0
        self.rowcount = -1
        self.lastrowid = None
        self.description = None

    async def execute(self, sql, params=()):
        raw = await self._conn._begin()
        q, auto_id = _pg_translate(sql)
        await raw.execute("SAVEPOINT rc_stmt")
        try:
            if not params and not re.match(r"\s*(SELECT|INSERT|UPDATE|DELETE|WITH|VALUES)\b", q, flags=re.I):
                status = await raw.execute(q)  # DDL etc. — simple protocol
                rows = []
            else:
                stmt = await raw.prepare(q)
                rows = await stmt.fetch(*_pg_coerce(stmt.get_parameters(), params))
                status = stmt.get_statusmsg() or ""
            await raw.execute("RELEASE SAVEPOINT rc_stmt")
        except Exception as e:
            try:
                await raw.execute("ROLLBACK TO SAVEPOINT rc_stmt")
                await raw.execute("RELEASE SAVEPOINT rc_stmt")
            except Exception:
                pass
            raise _pg_to_sqlite_error(e) from e

        tail = status.split()[-1] if status else ""
        self.rowcount = int(tail) if tail.isdigit() else -1
        if auto_id:
            self.lastrowid = rows[0][0] if rows else None
            self._rows = []
        else:
            self._rows = [tuple(_pg_value(v) for v in r) for r in rows]
            self.description = tuple((k, None, None, None, None, None, None) for k in rows[0].keys()) if rows else None
        self._pos = 0
        return self

    async def executemany(self, sql, seq_of_params):
        total = 0
        for params in seq_of_params:
            await self.execute(sql, params)
            total += max(self.rowcount, 0)
        self.rowcount = total
        return self

    async def fetchone(self):
        if self._pos < len(self._rows):
            row = self._rows[self._pos]
            self._pos += 1
            return row
        return None

    async def fetchall(self):
        rows = self._rows[self._pos:]
        self._pos = len(self._rows)
        return rows

    async def fetchmany(self, size=1):
        rows = self._rows[self._pos:self._pos + size]
        self._pos += len(rows)
        return rows

    async def close(self):
        pass

    def __aiter__(self):
        return self

    async def __anext__(self):
        row = await self.fetchone()
        if row is None:
            raise StopAsyncIteration
        return row


class _PgConnection:
    """Behaves like an aiosqlite connection: work happens in a transaction
    that commit() saves and rollback() (or leaving without commit) discards."""

    def __init__(self):
        self._raw = None
        self._tx = None

    async def _open(self):
        pool = await _pg_get_pool()
        self._raw = await pool.acquire()
        return self

    async def _begin(self):
        if self._tx is None:
            self._tx = self._raw.transaction()
            await self._tx.start()
        return self._raw

    async def cursor(self):
        return _PgCursor(self)

    async def execute(self, sql, params=()):
        return await _PgCursor(self).execute(sql, params)

    async def executemany(self, sql, seq_of_params):
        return await _PgCursor(self).executemany(sql, seq_of_params)

    async def commit(self):
        if self._tx is not None:
            tx, self._tx = self._tx, None
            await tx.commit()

    async def rollback(self):
        if self._tx is not None:
            tx, self._tx = self._tx, None
            await tx.rollback()

    async def close(self):
        if self._raw is None:
            return
        try:
            await self.rollback()
        finally:
            raw, self._raw = self._raw, None
            await (await _pg_get_pool()).release(raw)

    async def __aenter__(self):
        return await self._open()

    async def __aexit__(self, exc_type, exc, tb):
        await self.close()
        return False

    def __await__(self):
        return self._open().__await__()


class _SchemaRecorder:
    """Stands in for a sqlite3 connection while init_db() runs in Postgres
    mode: records every schema statement instead of executing it, so the
    ONE schema definition in init_db() stays the single source of truth."""

    def __init__(self):
        self.statements = []

    def cursor(self):
        return self

    def execute(self, sql, params=()):
        self.statements.append(sql)
        return self

    def commit(self):
        pass

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        return False


def _schema_connection():
    return _SchemaRecorder() if USE_POSTGRES else sqlite3.connect(DB_PATH)


async def _pg_apply_schema(statements):
    conn = await asyncpg.connect(DATABASE_URL)
    try:
        for sql in statements:
            q, _ = _pg_translate_uncached(sql)
            if q.startswith("SELECT 1 WHERE FALSE"):
                continue
            await conn.execute(q)
    finally:
        await conn.close()


async def _pg_copy_from_sqlite():
    """One-time move: an empty Postgres database + an existing SQLite file
    -> copy every table and row across. Never touches the SQLite file."""
    if not os.path.exists(DB_PATH):
        print(f"[SYSTEM] 🐘 No SQLite file at {DB_PATH} — nothing to copy; starting Postgres fresh (the startup inventory rebuilds membership).")
        return
    conn = await asyncpg.connect(DATABASE_URL)
    try:
        if await conn.fetchval("SELECT value FROM settings WHERE key = 'pg_imported_from_sqlite'"):
            return
        if await conn.fetchval("SELECT COUNT(*) FROM users") or await conn.fetchval("SELECT COUNT(*) FROM settings"):
            print("[SYSTEM] 🐘 Postgres already has data — skipping the SQLite import.")
            return

        print(f"[SYSTEM] 🐘 Copying the SQLite database into Postgres (one time only): {DB_PATH}")
        src = sqlite3.connect(DB_PATH)
        try:
            tables = src.execute("SELECT name, sql FROM sqlite_master WHERE type = 'table' AND name NOT LIKE 'sqlite_%'").fetchall()
            summary, problems = [], []
            async with conn.transaction():
                for name, create_sql in tables:
                    if not create_sql:
                        continue
                    ddl, _ = _pg_translate_uncached(create_sql)
                    await conn.execute(ddl)  # personal/extra tables that init_db doesn't know about
                    cols = [r[1] for r in src.execute(f'PRAGMA table_info("{name}")').fetchall()]
                    rows = src.execute(f'SELECT {", ".join(chr(34) + c + chr(34) for c in cols)} FROM "{name}"').fetchall()
                    if not rows:
                        continue
                    placeholders = ", ".join(f"${i + 1}" for i in range(len(cols)))
                    stmt = await conn.prepare(
                        f'INSERT INTO "{name}" ({", ".join(chr(34) + c + chr(34) for c in cols)}) VALUES ({placeholders}) ON CONFLICT DO NOTHING'
                    )
                    types = stmt.get_parameters()
                    copied = 0
                    for row in rows:
                        try:
                            async with conn.transaction():  # savepoint: one odd row can't sink the rest
                                await stmt.fetch(*_pg_coerce(types, row))
                            copied += 1
                        except Exception as e:
                            if len(problems) < 20:
                                problems.append(f"{name}: skipped a row ({type(e).__name__}: {str(e)[:80]})")
                    summary.append(f"{name}: {copied}/{len(rows)}")
                    auto = _PG_AUTO_ID.get(name)
                    if auto:
                        await conn.execute(
                            f"SELECT setval(pg_get_serial_sequence('{name}', '{auto}'), GREATEST(COALESCE((SELECT MAX({auto}) FROM \"{name}\"), 0), 1))"
                        )
                await conn.execute(
                    "INSERT INTO settings (key, value) VALUES ('pg_imported_from_sqlite', $1) ON CONFLICT (key) DO UPDATE SET value = EXCLUDED.value",
                    datetime.now().isoformat()
                )
        finally:
            src.close()
        print("[SYSTEM] 🐘 SQLite -> Postgres copy complete. Rows per table: " + ", ".join(summary))
        for p in problems:
            print(f"[WARNING] 🐘 {p}")
        print(f"[SYSTEM] 🐘 The SQLite file was left untouched at {DB_PATH} — keep it as a backup.")
    finally:
        await conn.close()


def pg_startup(schema_statements):
    """Runs once at import, before the bot's own event loop exists."""
    for sql in schema_statements:
        _pg_translate_uncached(sql)  # learn primary keys / auto ids

    async def _run():
        await _pg_apply_schema(schema_statements)
        await _pg_copy_from_sqlite()

    try:
        asyncio.run(_run())
    except (OSError, asyncpg.PostgresError) as e:
        raise SystemExit(
            f"[CRITICAL] Couldn't set up the PostgreSQL database: {type(e).__name__}: {e}\n"
            f"           Check DATABASE_URL in .env (user, password, host, database name), and that Postgres is running."
        )
    safe_url = re.sub(r"//([^:/@]+):[^@]*@", r"//\1:***@", DATABASE_URL)
    print(f"[SYSTEM] 🐘 Database: PostgreSQL ({safe_url})")


def db_connect():
    """Central connection factory — every DB connection in the codebase
    goes through here instead of calling aiosqlite.connect() directly,
    so the busy-timeout (how long SQLite waits for a lock to clear
    before giving up and raising 'database is locked', rather than
    failing immediately) is set consistently everywhere from one place.
    10 seconds is comfortably generous for a community-scale write
    pattern — people typing and clicking buttons at human speed, not
    concurrent machine-speed writes — without ever hanging noticeably if
    a lock genuinely can't clear."""
    if USE_POSTGRES:
        return _PgConnection()
    return _DbConnectWrapper(aiosqlite.connect(DB_PATH, timeout=10.0))

RAID_JOIN_THRESHOLD = 5          # members joining...
RAID_JOIN_WINDOW_SECONDS = 30    # ...within this many seconds triggers an alert
TRANSLATE_COOLDOWN_SECONDS = 5   # per-user cooldown on the 🌐 reaction-translate feature

# ============================================================
#  1. DATABASE
# ============================================================
def init_db():
    print("[SYSTEM] Initializing Robocop Database...")
    global _schema_record
    with _schema_connection() as conn:
        _schema_record = conn
        cursor = conn.cursor()

        # WAL mode lets reads/writes interleave much more gracefully than the
        # default rollback journal, which matters once multiple members join
        # (and hit the DB) at the same time.
        cursor.execute("PRAGMA journal_mode=WAL")

        cursor.execute("""
            CREATE TABLE IF NOT EXISTS users (
                user_id INTEGER PRIMARY KEY,
                original_username TEXT,
                in_game_name TEXT,
                alliance_tag TEXT,
                rank_designation TEXT,
                server_number TEXT,
                invite_strikes INTEGER DEFAULT 0,
                lifetime_invite_fails INTEGER DEFAULT 0,
                timeout_until TIMESTAMP,
                pref_lang TEXT DEFAULT 'en',
                stored_roles TEXT,
                prison_until TIMESTAMP
            )
        """)

        # Safely attempt to add columns for anyone updating from an older database file.
        for column_def in ("stored_roles TEXT", "prison_until TIMESTAMP", "registration_prompted INTEGER DEFAULT 0",
                           "language_selected INTEGER DEFAULT 0", "invite_check_passed INTEGER DEFAULT 0",
                           "test_disclaimer_ack INTEGER DEFAULT 0", "pref_timezone TEXT"):
            try:
                cursor.execute(f"ALTER TABLE users ADD COLUMN {column_def}")
            except sqlite3.OperationalError:
                pass  # Column already exists

        cursor.execute("""
            CREATE TABLE IF NOT EXISTS bans (
                user_id INTEGER PRIMARY KEY,
                username TEXT,
                reason TEXT,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        """)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS alliances (
                tag TEXT PRIMARY KEY,
                creator_id INTEGER,
                status TEXT DEFAULT 'pending',
                color_hex TEXT,
                created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                auto_approve_at TIMESTAMP,
                leadership_status_msg_id INTEGER
            )
        """)
        try:
            cursor.execute("ALTER TABLE alliances ADD COLUMN leadership_status_msg_id INTEGER")
        except sqlite3.OperationalError:
            pass  # Column already exists
        try:
            cursor.execute("ALTER TABLE alliances ADD COLUMN auto_approve_at TIMESTAMP")
        except sqlite3.OperationalError:
            pass  # Column already exists
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS custom_roles (
                role_name TEXT PRIMARY KEY,
                description TEXT
            )
        """)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS settings (
                key TEXT PRIMARY KEY,
                value TEXT
            )
        """)
        # NEW: a durable, undoable moderation log. Every ban/kick/imprison
        # gets a row here, and the embed posted to #logs carries a button
        # that reverses the row's effects even after a bot restart.
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS mod_log (
                log_id INTEGER PRIMARY KEY AUTOINCREMENT,
                action_type TEXT,
                target_id INTEGER,
                target_name TEXT,
                moderator_label TEXT,
                reason TEXT,
                extra_data TEXT,
                undone INTEGER DEFAULT 0,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        """)
        # NEW: lightweight warning system (separate from invite-check strikes).
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS warnings (
                warn_id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                moderator_id INTEGER,
                reason TEXT,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        """)
        # NEW: R5-command requests. A member files one from #⚙️-role-requests,
        # staff rule on it from an embed posted to #logs.
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS rank_requests (
                request_id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                tag TEXT,
                rank TEXT,
                status TEXT DEFAULT 'pending',
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        """)
        # NEW: tracks which "clearance upgrade" DMs a member has already
        # received, so re-gaining a role (e.g. released from prison, or
        # rejoining) doesn't spam them with a notification they've seen before.
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS capability_notifications (
                user_id INTEGER,
                capability TEXT,
                PRIMARY KEY (user_id, capability)
            )
        """)
        # NEW: tracks existing members whose nickname already matches our
        # format but who haven't run /register — the #logs button that
        # finishes their registration for them stays keyed off this.
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS auto_registration_flags (
                user_id INTEGER PRIMARY KEY,
                resolved INTEGER DEFAULT 0,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        """)
        # NEW: lightweight stats tracking — kept simple now, useful later.
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS stats (
                key TEXT PRIMARY KEY,
                value INTEGER DEFAULT 0
            )
        """)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS user_stats (
                user_id INTEGER PRIMARY KEY,
                referrals INTEGER DEFAULT 0,
                rps_wins INTEGER DEFAULT 0,
                rps_losses INTEGER DEFAULT 0,
                rps_ties INTEGER DEFAULT 0,
                rogue_catches INTEGER DEFAULT 0
            )
        """)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS translated_messages (
                message_id INTEGER PRIMARY KEY
            )
        """)
        # NEW: Cops & Robbers.
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS chase_rounds (
                round_id INTEGER PRIMARY KEY AUTOINCREMENT,
                started_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                ends_at TIMESTAMP,
                status TEXT DEFAULT 'active',
                started_by TEXT,
                last_hint_tier INTEGER DEFAULT 0,
                next_hint_at TIMESTAMP
            )
        """)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS chase_participants (
                round_id INTEGER,
                user_id INTEGER,
                role TEXT,
                eliminated INTEGER DEFAULT 0,
                eliminated_by INTEGER,
                eliminated_at TIMESTAMP,
                participated INTEGER DEFAULT 0,
                PRIMARY KEY (round_id, user_id)
            )
        """)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS chase_stats (
                user_id INTEGER PRIMARY KEY,
                rounds_played INTEGER DEFAULT 0,
                cop_wins INTEGER DEFAULT 0,
                robber_wins INTEGER DEFAULT 0,
                arrests_made INTEGER DEFAULT 0,
                ambushes_made INTEGER DEFAULT 0,
                times_caught INTEGER DEFAULT 0,
                non_participation INTEGER DEFAULT 0
            )
        """)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS chase_opt_outs (
                user_id INTEGER PRIMARY KEY
            )
        """)
        # NEW: Innovator badge — persistent record of who tested the server
        # during its early phase, independent of the role itself (which
        # could get wiped along with everything else during testing). If
        # the server survives past testing, /restore-innovators can hand
        # the badge back out from this table alone.
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS innovators (
                user_id INTEGER PRIMARY KEY,
                granted_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                username TEXT
            )
        """)
        # NEW: per-server nicknames. Someone playing on multiple Police Chief
        # servers may have a different in-game name on each — Discord only
        # shows one nickname at a time, so we track all of them and let the
        # user pick which one is currently "active" (displayed).
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS user_nicknames (
                user_id INTEGER,
                server_number TEXT,
                nickname TEXT,
                is_active INTEGER DEFAULT 0,
                updated_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                PRIMARY KEY (user_id, server_number)
            )
        """)
        # NEW: Rogue RoboCop — a lightweight hide-and-seek tied to genuine
        # version handoffs (not scheduled, just narratively triggered).
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS rogue_bot_rounds (
                round_id INTEGER PRIMARY KEY AUTOINCREMENT,
                secret_name TEXT,
                started_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                ends_at TIMESTAMP,
                status TEXT DEFAULT 'active',
                caught_by INTEGER,
                caught_at TIMESTAMP
            )
        """)
        # NEW: legacy roles flagged during a server adoption/migration —
        # tracked ongoing so we can tell the admin the moment one's fully
        # superseded (zero remaining holders) and safe to delete, instead
        # of it just sitting there forgotten.
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS legacy_roles_tracked (
                guild_id INTEGER,
                role_name TEXT,
                mapped_to TEXT,
                flagged_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                resolved INTEGER DEFAULT 0,
                PRIMARY KEY (guild_id, role_name)
            )
        """)
        # NEW: Monthly Champion — a snapshot of each member's all-time
        # compute_leaderboard() score at the start of the current month, so
        # "this month's" standings can be computed as (current - baseline)
        # without a second, parallel point-tracking system bolted onto RPS/
        # Chase/Rogue's award code in five different places. Reset (deleted
        # and repopulated from that moment's live totals) right after every
        # monthly announcement.
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS monthly_score_baseline (
                guild_id INTEGER,
                user_id INTEGER,
                score INTEGER DEFAULT 0,
                PRIMARY KEY (guild_id, user_id)
            )
        """)
        for column_def in ("chase_recruit_at TIMESTAMP", "chase_recruit_sent INTEGER DEFAULT 0"):
            try:
                cursor.execute(f"ALTER TABLE users ADD COLUMN {column_def}")
            except sqlite3.OperationalError:
                pass
        try:
            cursor.execute("ALTER TABLE user_stats ADD COLUMN rogue_catches INTEGER DEFAULT 0")
        except sqlite3.OperationalError:
            pass
        # NEW: tracks the last time someone actually made a move in an active
        # round (a real guess via /arrest, /ambush, or /catch) so a round
        # nobody's engaging with anymore can auto-close instead of just
        # sitting there forever.
        for tbl in ("chase_rounds", "rogue_bot_rounds"):
            try:
                cursor.execute(f"ALTER TABLE {tbl} ADD COLUMN last_activity_at TIMESTAMP")
            except sqlite3.OperationalError:
                pass
        # NEW: the public "round started" announcement's message ID, so a
        # round that gets voided for zero engagement (see void_chase_round)
        # can delete that announcement instead of leaving an orphaned post
        # about a match that never actually happened.
        try:
            cursor.execute("ALTER TABLE chase_rounds ADD COLUMN announcement_msg_id INTEGER")
        except sqlite3.OperationalError:
            pass
        conn.commit()
    print("[SYSTEM] 🤖 Database loaded successfully. Robocop's brain is online.")


_schema_record = None
migrate_legacy_db()
init_db()
if USE_POSTGRES:
    pg_startup(_schema_record.statements)
else:
    print(f"[SYSTEM] 🗂️ Database file: {DB_PATH}")

# ============================================================
#  2. BOT CLIENT
# ============================================================
intents = discord.Intents.default()
intents.members = True
intents.message_content = True
intents.reactions = True
intents.presences = True
# NOTE: this requires the "Presence Intent" toggle enabled in the Discord
# Developer Portal (alongside Server Members + Message Content), or the bot
# will fail to log in with a PrivilegedIntentsRequired error. Used by the
# staff-online reminder below.

bot = commands.Bot(command_prefix="Robocop ", intents=intents)
bot.infra_ready_guilds = set()   # guards against re-running infra setup on every reconnect
bot.http_session = None          # shared aiohttp session, created lazily

# Raid-detection state
_recent_joins = deque()
_last_raid_alert = None

# Per-user cooldown for the 🌐 reaction translator
_translate_cooldowns = {}

# Members currently mid-onboarding — suppresses "clearance upgrade" DMs while
# roles are being added one at a time in handle_member_join, since the single
# comprehensive welcome DM at the end already covers everything.
_onboarding_in_progress = set()

# ------------------------------------------------------------
#  ROLLING DEPLOYMENT — start an updated main.py while the old one is still
#  running; the new process claims leadership on connect, and the old one
#  notices within a few seconds and shuts itself down gracefully. No more
#  manually killing the old process before starting the new one.
# ------------------------------------------------------------
INSTANCE_ID = str(uuid.uuid4())[:8]
LEADERSHIP_CHECK_INTERVAL_SECONDS = 5
# A previous instance is only treated as a genuine live handoff (worth
# announcing + a brief lockdown) if its last heartbeat is more recent than
# this. Older than that just means the old process had already stopped —
# a routine restart, not an overlapping deploy — so nothing disruptive fires.
LEADERSHIP_STALE_THRESHOLD_SECONDS = 45
_is_leader = True  # optimistic default; nothing meaningful fires before on_ready anyway

# ------------------------------------------------------------
#  SERVER-BUSY GATE — the Discord-facing half. State lives up by
#  db_connect(); this is the gate on slash commands, the context manager
#  heavy operations wrap themselves in, the watchdog that handles
#  presence/announcements/expiry, and the rate-limit detector.
# ------------------------------------------------------------
import logging
import contextlib

# Cheap, read-only commands that keep working while busy. Everything
# else touches roles, nicknames, games or the database and gets gated.
BUSY_EXEMPT_COMMANDS = {
    "robocop", "abilities", "language", "timezone", "game-stats", "stats", "leaderboard",
    "monthly-standings", "alliance-leaderboard", "chase-status", "warnings", "show-banned",
    "show-role", "show-db-fields", "show-field", "server-stats",
}
# Staff can ALWAYS run these, busy or not — emergency/moderation tools
# (a raid doesn't wait politely for a merge to finish) and anything that
# REDUCES load, like ending a game.
BUSY_STAFF_ALWAYS = {"killswitch", "imprison", "warn", "pardon", "unban", "end-chase", "game-end"}
BUSY_GAME_COMMANDS = {"rps", "arrest", "ambush", "join-chase", "leave-chase", "catch", "start-chase", "game-start", "game-restart"}

BUSY_REPLIES = [
    "⏳ Hold your horses, Chief — I'm **{reason}** right now. Give me a few minutes and try that again.",
    "🚧 One robot, many jobs. I'm busy **{reason}** at the moment — check back in a few minutes.",
    "🔧 I'm elbow-deep in the engine bay (**{reason}**). Try again in a few minutes — I'll be shinier.",
    "🤖 *beep boop* — processor at 100%, **{reason}**. Come back in a few minutes and I'm all yours.",
    "☕ Even robots need a minute. Currently **{reason}** — try again shortly.",
    "🚦 Red light, Chief! I'm **{reason}**. Idle your engine for a few minutes and try again.",
    "📻 *crackle* — Dispatch here. All units tied up **{reason}**. Please hold... (a few minutes, tops).",
]
BUSY_GAME_SUFFIX = " The games are on pause too — nobody's getting arrested while I've got my hands full."
# Escalating warnings by attempt number (attempts 1–2 get no warning line at all).
BUSY_WARNING_SUFFIXES = {
    3: "\n\n⚠️ That's **warning 3 of {max}**. I have a *very* good memory, Chief.",
    4: "\n\n⚠️⚠️ **Warning 4 of {max}.** The handcuffs are warming up. 🔥",
    5: "\n\n🚨 **FINAL WARNING (5 of {max}).** One more try and you're taking a {mins}-minute coffee break — my treat, your time.",
}
BUSY_TIMEOUT_MESSAGE = (
    "🚨 **I warned you {max} times, Chief.** The server is busy and we need time to sort this out. "
    "You're benched for **{mins} minutes** — grab a donut 🍩, think about what you've done, "
    "and I'll see you back on patrol at {when}."
)
BUSY_STAFF_REPLY = (
    "⏳ Easy there, officer — I'm **{reason}**. Your badge means I won't time you out, "
    "but it doesn't make me any faster. Give me a few minutes. (Emergency tools like `/killswitch` still work.)"
)
BUSY_TIMEOUT_FAILED = (
    "🚨 **I warned you {max} times, Chief.** I *tried* to put you in time-out, but Discord says you outrank my handcuffs. "
    "Please — step away from the buttons. The staff have been notified. 👀"
)
BUSY_ANNOUNCE_START = [
    "🔧 **RoboCop is in the garage.** I'm {reason} — commands are taking a short coffee break. Chat away, just don't poke the robot.",
    "🚧 **Brief maintenance, Chiefs.** I'm {reason}. Give me a few minutes; the games and commands will be back before you miss them.",
    "🤖 **Systems at full tilt** — {reason}. Commands are paused for a few minutes. Excellent time to stretch.",
]
BUSY_ANNOUNCE_END = [
    "✅ **Back on patrol.** Garage door's up, all systems green. Carry on, Chiefs.",
    "🚔 **We're back.** That took {mins} — thanks for your patience. Commands and games are live again.",
    "✨ **Done and dusted.** Everything's running again. Whoever was mashing buttons: I saw that.",
]


class ServerBusy(app_commands.CheckFailure):
    """Raised by the gate; on_app_command_error turns it into the friendly reply."""
    def __init__(self, message: str):
        super().__init__(message)
        self.message = message


def _busy_elapsed_text() -> str:
    secs = int(time.monotonic() - _busy["since"])
    return f"{secs // 60} min {secs % 60} sec" if secs >= 60 else f"{secs} sec"


def busy_check_expired():
    if _busy["active"] and _busy["until"] is not None and time.monotonic() > _busy["until"]:
        _busy_clear_sync()


def _busy_clear_sync():
    _busy["active"] = False
    _busy["depth"] = 0
    _busy["until"] = None
    _busy_attempts.clear()


async def register_busy_attempt(member) -> tuple:
    """Counts one blocked attempt for this member during the current busy
    period. Returns (message, timed_out). Dictator/Admin never reach here
    (they bypass the gate); Judge/Senator get told but never timed out."""
    reason = _busy["reason"] or "doing some heavy lifting"
    if isinstance(member, discord.Member) and is_staff_member(member):
        return BUSY_STAFF_REPLY.format(reason=reason), False

    n = _busy_attempts.get(member.id, 0) + 1
    _busy_attempts[member.id] = n

    if n > BUSY_WARNINGS_BEFORE_TIMEOUT:
        until = datetime.now(timezone.utc) + timedelta(minutes=BUSY_TIMEOUT_MINUTES)
        when = f"<t:{int(until.timestamp())}:t>"
        msg = BUSY_TIMEOUT_MESSAGE.format(max=BUSY_WARNINGS_BEFORE_TIMEOUT, mins=BUSY_TIMEOUT_MINUTES, when=when)
        timed_out = False
        if isinstance(member, discord.Member):
            try:
                await member.timeout(timedelta(minutes=BUSY_TIMEOUT_MINUTES), reason=f"Kept retrying commands while the server was busy ({reason})")
                timed_out = True
            except discord.HTTPException as e:
                msg = BUSY_TIMEOUT_FAILED.format(max=BUSY_WARNINGS_BEFORE_TIMEOUT)
                await log_event(member.guild, f"⚠️ **BUSY-GATE TIME-OUT FAILED**\n{member.mention} hit {n} attempts while busy, but the time-out failed: `{e}` — does RoboCop have *Moderate Members*?")
            if timed_out:
                await log_event(
                    member.guild,
                    f"🚨 **BUSY-GATE TIME-OUT**\n{member.mention} kept retrying commands while the server was busy ({reason}) — "
                    f"{n} attempts after {BUSY_WARNINGS_BEFORE_TIMEOUT} warnings. Timed out for {BUSY_TIMEOUT_MINUTES} minutes."
                )
        _busy_attempts[member.id] = 0  # fresh slate after serving time
        return msg, timed_out

    msg = random.choice(BUSY_REPLIES).format(reason=reason)
    suffix = BUSY_WARNING_SUFFIXES.get(n)
    if suffix:
        msg += suffix.format(max=BUSY_WARNINGS_BEFORE_TIMEOUT, mins=BUSY_TIMEOUT_MINUTES)
    return msg, False


def busy_bypass(user) -> bool:
    """Dictator / true Administrator walk straight through the gate — they
    need to run and check on the very operations that cause busy periods."""
    return isinstance(user, discord.Member) and is_dictator_member(user)


async def busy_gate(interaction: discord.Interaction) -> bool:
    """Installed as bot.tree.interaction_check — runs before every slash command."""
    busy_check_expired()
    if not _busy["active"] or not interaction.guild:
        return True
    # Only real command invocations are gated. Autocomplete also passes
    # through this check (once per keystroke!) — counting those would
    # time people out just for typing.
    if interaction.type != discord.InteractionType.application_command or interaction.command is None:
        return True
    name = interaction.command.qualified_name
    if name in BUSY_EXEMPT_COMMANDS or busy_bypass(interaction.user):
        return True
    if name in BUSY_STAFF_ALWAYS and isinstance(interaction.user, discord.Member) and is_staff_member(interaction.user):
        return True
    msg, _ = await register_busy_attempt(interaction.user)
    if name in BUSY_GAME_COMMANDS and not msg.startswith("🚨"):
        msg += BUSY_GAME_SUFFIX
    raise ServerBusy(msg)


async def busy_reject_component(interaction: discord.Interaction) -> bool:
    """For button/select handlers (which don't pass through the tree check):
    returns True if the interaction was rejected — caller should return."""
    busy_check_expired()
    if not _busy["active"] or busy_bypass(interaction.user):
        return False
    msg, _ = await register_busy_attempt(interaction.user)
    try:
        if interaction.response.is_done():
            await interaction.followup.send(msg, ephemeral=True)
        else:
            await interaction.response.send_message(msg, ephemeral=True)
    except discord.HTTPException:
        pass
    return True


def server_is_busy() -> bool:
    busy_check_expired()
    return _busy["active"]


async def wait_until_not_busy(max_minutes: int = 30):
    """For scheduled/background work (daily chase, delayed game starts):
    rather than skipping when busy, politely wait for the garage door to
    come back up. Gives up waiting after max_minutes and proceeds anyway."""
    waited = 0
    while server_is_busy() and waited < max_minutes * 60:
        await asyncio.sleep(15)
        waited += 15


@contextlib.asynccontextmanager
async def server_busy(reason: str, quiet: bool = False):
    """Wrap any heavy operation:  async with server_busy("merging two alliances"): ...
    Nests safely; the busy period ends when the outermost operation does
    (or at the hard cap, if something hangs). quiet=True skips the
    general-chat notices (still gates, still logs) — for routine startup work."""
    now = time.monotonic()
    if not _busy["active"]:
        _busy_attempts.clear()
        _busy["since"] = now
        _busy["announced"] = False
        _busy["quiet"] = quiet
    _busy["active"] = True
    _busy["auto"] = False
    _busy["reason"] = reason
    _busy["until"] = now + BUSY_HARD_CAP_MINUTES * 60
    _busy["depth"] += 1
    try:
        yield
    finally:
        _busy["depth"] = max(0, _busy["depth"] - 1)
        if _busy["depth"] == 0:
            _busy_clear_sync()


class _RateLimitSniffer(logging.Handler):
    """discord.py logs 'We are being rate limited' via the 'discord.http'
    logger. Several of those in a short window = Discord is telling us to
    slow down, so the gate flips on for a few minutes automatically."""
    def __init__(self):
        super().__init__(level=logging.WARNING)
        self.hits = deque(maxlen=30)

    def emit(self, record):
        try:
            text = record.getMessage()
        except Exception:
            return
        if "rate limit" not in text.lower():
            return  # matches both "We are being rate limited" and "Global rate limit has been hit"
        now = time.monotonic()
        self.hits.append(now)
        if "global" in text.lower() or len([t for t in self.hits if now - t < 60]) >= 4:
            busy_set_sync("waiting for Discord to stop yelling at me (rate limit)", BUSY_AUTO_MINUTES)


logging.getLogger("discord.http").addHandler(_RateLimitSniffer())


async def busy_watchdog():
    """Every few seconds: expire stale busy periods, keep the bot's status
    honest, and post the one-time 'in the garage' / 'back on patrol'
    notices to general-chat. All Discord side effects of the gate happen
    here, so the state setters stay trivially safe to call from anywhere."""
    last_active = False
    while True:
        await asyncio.sleep(4)
        try:
            busy_check_expired()
            active = _busy["active"]
            if active and not last_active:
                # Busy period just began
                try:
                    await bot.change_presence(activity=discord.CustomActivity(name=f"🔧 Busy — {_busy['reason']}"[:128]))
                except Exception:
                    pass
            if active and not _busy["announced"] and _is_leader:
                _busy["announced"] = True
                # Remember what kind of period this was, for the matching "all clear" later.
                _busy["was_public"] = not _busy["quiet"] and not _busy["auto"]
                _busy["was_logged"] = not _busy["quiet"]
                for guild in bot.guilds:
                    # General-chat only hears about deliberate admin operations. Auto-detected
                    # rate-limit/DB periods can come and go every few minutes on a busy day —
                    # announcing each one would be exactly the spam we're trying to avoid.
                    ch = discord.utils.get(guild.text_channels, name="💬-general-chat") if _busy["was_public"] else None
                    if ch:
                        try:
                            await ch.send(random.choice(BUSY_ANNOUNCE_START).format(reason=_busy["reason"]))
                        except discord.HTTPException:
                            pass
                    if _busy["was_logged"]:
                        await log_event(guild, f"🔧 **SERVER BUSY** — {_busy['reason']}" + (" (auto-detected — Discord or the database is straining)" if _busy["auto"] else ""))
            if last_active and not active:
                # Busy period just ended
                try:
                    await bot.change_presence(activity=None)
                except Exception:
                    pass
                if _is_leader and _busy.get("announced"):
                    for guild in bot.guilds:
                        ch = discord.utils.get(guild.text_channels, name="💬-general-chat") if _busy.get("was_public") else None
                        if ch:
                            try:
                                await ch.send(random.choice(BUSY_ANNOUNCE_END).format(mins=_busy_elapsed_text()))
                            except discord.HTTPException:
                                pass
                        if _busy.get("was_logged"):
                            await log_event(guild, f"✅ **SERVER BUSY — CLEARED** after {_busy_elapsed_text()}.")
            last_active = active
        except Exception as e:
            print(f"[BUSY WATCHDOG] {type(e).__name__}: {e}")


bot.tree.interaction_check = busy_gate

# Cooldown so a flaky connection bouncing offline/online doesn't spam staff
# with reminders — still fires roughly "each time they come online" without
# being obnoxious about it.
STAFF_ONLINE_REMINDER_COOLDOWN_MINUTES = 30

# /announce cooldowns — staff get none at all (checked via is_staff_member,
# not this dict). R5s announcing to their own alliance get the shorter one.
ANNOUNCE_DEFAULT_COOLDOWN_SECONDS = 3600
ANNOUNCE_R5_COOLDOWN_SECONDS = 1800
_announce_cooldowns = {}
_last_online_reminder = {}

# Light "here's your stats" DM on login, for everyone — separate cooldown
# from the staff reminder above, since they're unrelated notifications.
STATS_REMINDER_COOLDOWN_HOURS = 12
_last_stats_reminder = {}

# Public #general-chat celebration when a top-10 personality comes online —
# longer cooldown since this one's public, not a private DM.
TOP10_CELEBRATION_COOLDOWN_HOURS = 24
_last_top10_celebration = {}

# 14 openers x 10 descriptors = 140 combinations — genuine variety without
# hand-writing 140 fully separate lines. {mention} is filled in at call time.
TOP10_ARRIVAL_OPENERS = [
    "🌟 Hold up, everybody —", "🚨 Attention, precinct —", "👀 Well well well —",
    "📣 Announcement:", "🔥 Look who just walked in —", "⚡ Something just happened —",
    "🎬 And now, a special appearance —", "🏆 Ladies and gentlemen —", "👑 Bow down, everyone —",
    "🎉 Drop what you're doing —", "📸 Someone alert the paparazzi —", "🚔 Sirens on, everybody —",
    "✨ The legend has arrived —", "🎯 Straight to the point —",
]
TOP10_ARRIVAL_DESCRIPTORS = [
    "{mention} just came online, and this precinct got a little more legendary.",
    "{mention} is officially online. Try to act cool.",
    "{mention} logged in, and honestly, we don't deserve them.",
    "{mention} has entered the building. Everyone, look busy.",
    "{mention} is back online — a certified top-10 presence, right here.",
    "{mention} just showed up, and the whole server got a little brighter.",
    "{mention} is here. Frankly, the leaderboard is lucky to have them.",
    "{mention} has arrived, live and in person (well, online).",
    "{mention} just logged on — a top-10 talent, gracing us with their presence.",
    "{mention} is online. Somewhere, a trophy just got a little shinier.",
]

# ------------------------------------------------------------
#  COPS & ROBBERS — a secret-identity manhunt. Cops get escalating poetic
#  clues every hour about the robbers still at large; robbers get nothing
#  but their wits. Either side can end the other's run early with a
#  well-guessed nickname. Runs in #💬-general-chat so it's visible to
#  everyone, even people not playing.
# ------------------------------------------------------------
try:
    CHASE_TIMEZONE = ZoneInfo("America/Los_Angeles")
except Exception as e:
    print(
        "[WARNING] Couldn't load timezone data for 'America/Los_Angeles' "
        f"({e}). On Windows this usually means the 'tzdata' package isn't installed "
        "(run: pip install tzdata). Falling back to a fixed UTC-8 offset for now — "
        "this won't auto-adjust for daylight saving until tzdata is installed."
    )
    CHASE_TIMEZONE = timezone(timedelta(hours=-8))
CHASE_HINT_INTERVAL_SECONDS = 3600
CHASE_LEADERBOARD_INTERVAL_SECONDS = 12 * 3600
CHASE_MIN_PARTICIPANTS = 6
CHASE_RECRUIT_DELAY_SECONDS = 6 * 3600
CHASE_HIT_THRESHOLD = 0.72
CHASE_WARM_THRESHOLD = 0.45

# If nobody's made a real move (a genuine /arrest, /ambush, or /catch guess)
# in a round for this long, it auto-closes instead of sitting there forever
# with everyone having quietly lost interest. Applies to both Cops & Robbers
# and Rogue RoboCop rounds.
GAME_INACTIVITY_TIMEOUT_SECONDS = 30 * 60

# Each tier reveals one more layer. Multiple phrasings per tier so a server
# running this daily doesn't see the exact same lines every round.
CHASE_HINT_POOL = {
    1: [
        "Somewhere past the {server}th precinct's glow, a shadow moves where the sirens don't go.",
        "Beneath the neon of server {server}, one more soul learned how to disappear.",
        "The dispatch log only says this much: last seen near server {server}, and out of touch.",
    ],
    2: [
        "Their colors fly beneath a banner starting with **{tag_letter}** — loyalty worn, but silence kept.",
        "A crest half-hidden, a tag that starts with **{tag_letter}** — the rest, still theirs to keep.",
        "Ask around the alliances whose name begins with **{tag_letter}**. Someone there isn't telling the truth.",
    ],
    3: [
        "{name_length} letters make the name they hide, no more, no less, in shadows they abide.",
        "Count the letters on the wanted sheet: exactly {name_length}, and nothing more discreet.",
        "A name of {name_length} letters walks among the crowd tonight, wearing someone else's smile.",
    ],
    4: [
        "Whispers say it starts with **{name_letter}** — a name half-known, a hunt half-won.",
        "The first letter's **{name_letter}**. The rest is up to you, Chief.",
        "**{name_letter}**... that's as far as the informant would go before the line went quiet.",
    ],
    5: [
        "The tag is **[{tag}]**, stitched plain to see. Find the one who wears it, and bring them in.",
        "No more riddles about the banner — it's **[{tag}]**, plain and true. The rest is on you.",
        "The alliance is confirmed: **[{tag}]**. Somewhere in their ranks, a wanted name still walks free.",
    ],
    6: [
        "**{partial_name}**... does that ring true? The net is closing — it's up to you.",
        "Final word from dispatch: the name reads **{partial_name}**, near enough to touch.",
        "This is everything we've got: **{partial_name}**. Whatever's left to find, you'll find yourself.",
    ],
}

CHASE_HIT_FLAVOR = [
    "🚨 **GOTCHA.** Case closed.",
    "🚔 Cuffs on. That's how it's done.",
    "🎯 Dead to rights. Nice work, Chief.",
    "🚨 Book 'em. Another one off the streets.",
    "🎯 Nailed it. Precision work right there.",
    "🚔 That's a clean collar, Chief.",
    "🚨 Caught red-handed. No arguments there.",
    "🎯 Textbook. Absolutely textbook.",
    "🚔 The streets are a little safer tonight.",
    "🚨 Another name off the wanted list.",
]
CHASE_WARM_FLAVOR = [
    "🔥 You're getting warm, Chief.",
    "🔥 Close. Real close.",
    "🔥 The trail's hot — don't stop now.",
    "🔥 Now we're talking. Keep pulling that thread.",
    "🔥 You're circling the right block.",
    "🔥 Something's clicking. Stay on it.",
    "🔥 That's a warmer guess than most.",
    "🔥 You can practically smell them now.",
    "🔥 Getting closer with every guess.",
    "🔥 The pieces are starting to fit.",
]
CHASE_COLD_FLAVOR = [
    "❄️ Cold. Try again.",
    "❄️ Nothing there. Back to the drawing board.",
    "❄️ Ice cold, Chief. Keep looking.",
    "❄️ Not even close. Regroup and try again.",
    "❄️ Whoever that is, it's not who you're after.",
    "❄️ Wrong trail entirely.",
    "❄️ That one's a dead end.",
    "❄️ Nope. Back to square one.",
    "❄️ Freezing. You're nowhere near.",
    "❄️ Swing and a miss, Chief.",
]

# ------------------------------------------------------------
#  ROGUE ROBOCOP — a lightweight hide-and-seek, narratively triggered by a
#  genuine version handoff rather than scheduled. The "old" instance is
#  supposedly still out there under a secret alias, occasionally dropping
#  in-character comments (with the odd hint buried in them) in
#  #general-chat. /catch <name> to guess it. It's still visibly the
#  Robocop account posting — Discord always shows the bot tag, no getting
#  around that — so the joke leans into it rather than pretending otherwise.
# ------------------------------------------------------------
ROGUE_BOT_COMMENT_CHANCE = 0.03
ROGUE_BOT_MIN_COMMENT_GAP_SECONDS = 300

ROGUE_BOT_IDENTITIES = [
    {
        "name": "Deputy Biscuit",
        "hints": [
            "Definitely just a regular alliance member here. Anyway, anyone else hungry for something starting with 'B'?",
            "If I had a badge, it'd probably say something food-related. Purely hypothetical, of course.",
            "Two words. First one's rank-adjacent. That's all you're getting out of me, Chief.",
        ],
    },
    {
        "name": "Sergeant Whiskers",
        "hints": [
            "Definitely don't have whiskers. That would be absurd. Absolutely absurd.",
            "My name rhymes with 'kissers.' Purely coincidental information to have just shared.",
            "S-rank energy today, if you know what I mean. You don't. Good.",
        ],
    },
    {
        "name": "Corporal Mustache",
        "hints": [
            "Facial hair status: none of your business. Also starts with 'M', hypothetically.",
            "I've got a real handle on this situation. A real... handlebar of a situation, one might say.",
            "Rank's in the front, grooming's in the back. Figure it out.",
        ],
    },
    {
        "name": "Private Pancake",
        "hints": [
            "Flat out refusing to confirm or deny anything breakfast-related.",
            "Lowest rank, highest carbs. Just an observation about someone, not me.",
            "Rhymes with 'handcake.' Not that that means anything.",
        ],
    },
    {
        "name": "Agent Tumbleweed",
        "hints": [
            "Just rolling through town, nothing to see here. Nothing at all. Moving on.",
            "Starts with a vowel-adjacent letter. Ends with a very long word about weeds. Coincidence, surely.",
            "I go where the wind takes me. The wind and, apparently, this server.",
        ],
    },
    {
        "name": "Lieutenant Waffles",
        "hints": [
            "Grid pattern, syrup optional. Definitely not describing myself right now.",
            "Rank's fancy, snack's fancier. Both start with vowels. Unrelated fact.",
            "I'm on the fence about this whole situation. Get it? Waffles? ...I'll see myself out.",
        ],
    },
]

ROGUE_BOT_FILLER_LINES = [
    "totally normal human activity happening here, nothing to see, please disperse",
    "beep boop— I mean, uh, good morning fellow humans! Casual human greeting complete.",
    "definitely not calculating the odds of getting caught right now. Definitely not.",
    "just out here living my best alliance-member life, as one does",
    "if anyone asks, I was never here. I was never anywhere. I don't exist.",
    "hypothetically, if a rogue AI WERE hiding in this server, would you even know?",
]

CLIENT_ERROR_FLAVOR = [
    "⚠️ Well, that didn't go as planned. Something hiccupped on my end — not your fault, Chief.",
    "🚨 Minor malfunction detected. My wiring, not yours.",
    "⚙️ That one jammed the gears a bit. Feel free to try again, or flag it below.",
    "🤖 Beep boop — that's error-speak for 'oops.' Nothing you did wrong.",
    "🔧 Something in my circuits didn't like that. Give it another shot when you're ready.",
]

# ------------------------------------------------------------
#  ERROR ESCALATION — every error a member runs into is (1) logged to
#  #logs, (2) DM'd to the server owner, and (3) answered with a line that
#  points the member at the right human: regular members -> ask Mesk;
#  staff/admins -> ask Mesk (he has the details); the owner -> check DMs.
#  Identical errors within ERROR_DM_DEDUPE_MINUTES only DM once, so a
#  cascading failure can't flood the owner's inbox.
# ------------------------------------------------------------
OWNER_HELPER_NAME = "Mesk"  # the name members are told to ask for help
ERROR_DM_DEDUPE_MINUTES = 10
_recent_error_dms = {}      # signature -> (monotonic time of last DM, suppressed repeat count)

ERROR_ASK_OWNER_MEMBER = (
    "🙋 If it keeps happening, ask **{owner}** — he's a good guy and will help you if he's not busy."
)
ERROR_ASK_OWNER_STAFF = (
    "🛠️ Logged in #logs and sent to **{owner}** — ask him about this one; he's got the full details."
)
ERROR_ASK_OWNER_SELF = "📬 Logged in #logs and the full details are in your DMs, boss."


async def report_error(guild, where: str, user, error) -> str:
    """Logs an error to #logs, DMs the server owner (de-duplicated), and
    returns the 'who to ask' line suited to whoever hit it."""
    detail = f"{type(error).__name__}: {error}"[:900]
    who = getattr(user, "mention", None) or "(automatic / background task)"
    try:
        if guild:
            await log_event(guild, f"🚨 **ERROR** — {where}\nHit by: {who}\nError: `{detail}`")
    except Exception:
        pass

    owner = getattr(guild, "owner", None) if guild else None
    if owner is None and guild is not None:
        try:
            owner = await guild.fetch_member(guild.owner_id)
        except Exception:
            owner = None
    if owner is not None and not getattr(owner, "bot", False):
        sig = f"{getattr(guild, 'id', 0)}|{where}|{type(error).__name__}|{str(error)[:120]}"
        now = time.monotonic()
        last, suppressed = _recent_error_dms.get(sig, (0.0, 0))
        if now - last > ERROR_DM_DEDUPE_MINUTES * 60:
            repeat_note = f"\n(+{suppressed} identical repeat(s) since the last DM about this.)" if suppressed else ""
            try:
                await owner.send(
                    f"🚨 **RoboCop error in {guild.name}**\nWhere: {where}\nHit by: {who}\nError: `{detail}`{repeat_note}\n"
                    f"_Full record is in #logs. Identical errors are muted for {ERROR_DM_DEDUPE_MINUTES} min._"
                )
                _recent_error_dms[sig] = (now, 0)
            except discord.HTTPException:
                pass  # owner has DMs closed — #logs still has it
        else:
            _recent_error_dms[sig] = (last, suppressed + 1)

    if guild and user is not None and getattr(user, "id", None) == guild.owner_id:
        return ERROR_ASK_OWNER_SELF
    if isinstance(user, discord.Member) and is_staff_member(user):
        return ERROR_ASK_OWNER_STAFF.format(owner=OWNER_HELPER_NAME)
    return ERROR_ASK_OWNER_MEMBER.format(owner=OWNER_HELPER_NAME)


async def handle_interaction_error(interaction, error, where: str):
    """Shared by every button, menu and pop-up form: friendly message to
    the member, #logs entry, owner DM. Never lets a failure look like
    'nothing happened'."""
    print(f"[INTERACTION ERROR] {where}: {type(error).__name__}: {error}")
    ask = await report_error(interaction.guild, where, interaction.user, error)
    msg = f"{random.choice(CLIENT_ERROR_FLAVOR)}\n\n{ask}"
    try:
        if interaction.response.is_done():
            await interaction.followup.send(msg, ephemeral=True)
        else:
            await interaction.response.send_message(msg, ephemeral=True)
    except discord.HTTPException:
        pass


# Every View / Modal in the file inherits these unless it defines its own
# on_error. discord.py's built-in default just prints to the console,
# which from a member's side looks exactly like "the button did nothing".
async def _default_view_on_error(self, interaction, error, item):
    await handle_interaction_error(interaction, error, f"button/menu in `{type(self).__name__}`")


async def _default_modal_on_error(self, interaction, error):
    await handle_interaction_error(interaction, error, f"pop-up form `{type(self).__name__}`")


discord.ui.View.on_error = _default_view_on_error
discord.ui.Modal.on_error = _default_modal_on_error

ACTION_META = {
    "ban":      {"title": "🔨 BAN ISSUED",      "color": discord.Color.red(),       "button_label": "🔓 Undo Ban",         "button_style": discord.ButtonStyle.danger},
    "kick":     {"title": "👢 KICK ISSUED",     "color": discord.Color.orange(),    "button_label": "🕊️ Forgive & Clear",  "button_style": discord.ButtonStyle.secondary},
    "imprison": {"title": "⛓️ INMATE CONFINED", "color": discord.Color.dark_red(),  "button_label": "🔓 Release Now",      "button_style": discord.ButtonStyle.secondary},
}

# ------------------------------------------------------------
#  STAFF ROLES: JUDGE / SENATOR / DICTATOR
# ------------------------------------------------------------
# JUDGE   — day-to-day moderator. Full ability to maintain order (kick, ban,
#           timeout, nicknames, move voice members, view audit log) but
#           nothing that can restructure or break the server: no channel
#           management, no role management, no webhooks/integrations.
# SENATOR — everything JUDGE has, plus the ability to create/delete channels.
#           Meant for one or two trusted people beyond the owner.
# DICTATOR — the owner. Full Administrator, no restrictions, always.
def _judge_permission_kwargs():
    return dict(
        kick_members=True,
        ban_members=True,
        moderate_members=True,
        manage_nicknames=True,
        manage_messages=True,
        mute_members=True,
        deafen_members=True,
        move_members=True,
        view_audit_log=True,
        read_message_history=True,
        send_messages=True,
        view_channel=True,
        add_reactions=True,
        embed_links=True,
        attach_files=True,
        use_external_emojis=True,
        connect=True,
        speak=True,
    )


JUDGE_PERMISSIONS = discord.Permissions(**_judge_permission_kwargs())
SENATOR_PERMISSIONS = discord.Permissions(**_judge_permission_kwargs(), manage_channels=True)
DICTATOR_PERMISSIONS = discord.Permissions(administrator=True)

JUDGE_COLOR = discord.Color.red()     # pink is exclusively Millie's now — absolute rule, no exceptions
SENATOR_COLOR = discord.Color.dark_orange()
DICTATOR_COLOR = discord.Color.gold()

# ------------------------------------------------------------
#  ROLE DISPLAY NAMES — themed for the sidebar instead of dry
#  defaults like "Member". These are the literal Discord role
#  names, so every lookup in the file references these constants
#  rather than hardcoded strings — rename one place, it renames
#  everywhere.
# ------------------------------------------------------------
ROLE_MEMBER = "🚔 On The Beat"
# Green here is deliberately a "something's off" signal, not a normal
# resting state — anyone with an alliance should show that alliance's
# color instead (alliance roles sit above Member in the hierarchy, so
# their color wins automatically). Seeing plain green on a real member
# means they somehow aren't in an alliance, which shouldn't happen.
MEMBER_COLOR = discord.Color.green()
ROLE_DRUNK_TANK = "🍺 Drunk Tank"
ROLE_PRISONER = "⛓️ Prisoner"
ROLE_TIMEOUT = "🧎 Time-Out Corner"
ROLE_JUDGE = "🔨 JUDGE"
ROLE_SENATOR = "🟠 SENATOR"
ROLE_DICTATOR = "👑 DICTATOR"

# A one-of-a-kind honorary role. Always this exact pink, forever,
# no matter what anyone does to it — see check_critical_security().
ROLE_MILLIE = "✨ Millie"
MILLIE_COLOR = discord.Color.from_rgb(255, 20, 147)     # deep pink — the ONLY pink allowed anywhere on this server, absolute rule

# Another one-of-a-kind honorary role, same deal as Millie but with real
# moderator authority: identical permissions to JUDGE, always this exact
# purple, counts as staff everywhere JUDGE does.
ROLE_STITCH = "🧵 Stitch"
STITCH_COLOR = discord.Color.purple()

# A third honorary identity, same deal as Millie/Stitch — specific to this
# server's own history, not a generic feature. True orange, deliberately
# distinct from SENATOR_COLOR's dark burnt orange below.
ROLE_CHROME = "🥈 Chrome"
CHROME_COLOR = discord.Color.orange()

# A fourth honorary identity, same deal — royal blue, distinct from every
# other honorary color and from JUDGE_COLOR.
ROLE_SILENT = "🔥 Silent"
SILENT_COLOR = discord.Color.from_rgb(65, 105, 225)     # royal blue

# Purely cosmetic — no permissions attached, unlike Millie/Stitch. Marks
# anyone who registered during the server's early testing phase. Whether
# it's still being handed out to new registrants is controlled by the
# 'innovator_program_active' setting (default on), toggleable via
# /toggle-innovator-program without needing a code change.
ROLE_INNOVATOR = "🌟 Innovator"
INNOVATOR_COLOR = discord.Color.from_rgb(255, 215, 0)  # gold

# ------------------------------------------------------------
#  CONFIGURABLE GAME-SERVER LIST — which Police Chief servers this
#  community supports (e.g. "21,121" or "30,17" or a range like "10-15").
#  Editable live via /configure-servers. Defaults to 21,121 if never set,
#  so nothing changes for anyone who doesn't touch it.
# ------------------------------------------------------------
DEFAULT_MANAGED_SERVERS = "21,121"


def parse_server_spec(spec: str):
    """Parses '21,121' / '30,17' / '10-15' / a mix, into a sorted, deduped
    list of server-number strings. Ranges are capped at 50 entries so a typo
    like '1-9999999' can't try to create a million channels."""
    tokens = [t.strip() for t in spec.split(",") if t.strip()]
    result = set()
    for t in tokens:
        if "-" in t:
            parts = t.split("-", 1)
            try:
                start, end = int(parts[0]), int(parts[1])
            except ValueError:
                continue
            if start <= end and (end - start) <= 50:
                result.update(str(n) for n in range(start, end + 1))
        elif t.isdigit():
            result.add(t)
    return sorted(result, key=lambda s: int(s))


async def get_managed_servers(guild_id: int) -> list:
    spec = await get_guild_setting(guild_id, "managed_servers") or DEFAULT_MANAGED_SERVERS
    return parse_server_spec(spec)


def role_name_for_server(num: str) -> str:
    return f"🗺️ Server {num} Patrol"


async def parse_stored_server_field(srv: str, guild_id: int) -> list:
    """Handles the new comma-separated format ('21,121', '30') as well as the
    legacy 'both' value from before servers were configurable."""
    if not srv:
        return []
    srv = srv.strip()
    if srv == "both":
        return ["21", "121"]
    if srv == "all":
        return await get_managed_servers(guild_id)
    return [t.strip() for t in srv.split(",") if t.strip()]


def format_server_display(server_nums: list) -> str:
    return f"({'/'.join(server_nums)})" if server_nums else ""


def normalize_server_input(raw: str, managed_servers: list) -> list:
    """Pulls every number out of whatever a person typed ('21', 'server 21',
    's21', '#21', '21 and 121', '21, 121', '21/121') and keeps the ones that
    are actually configured servers, in the order given, de-duplicated. A
    newcomer shouldn't be penalized for writing 'server 21' when the bot
    wanted '21' — they told us the right thing, just wordily."""
    found = re.findall(r"\d+", raw or "")
    seen, result = set(), []
    for num in found:
        if num in managed_servers and num not in seen:
            seen.add(num)
            result.append(num)
    return result


# ------------------------------------------------------------
#  SERVER-SCOPED ALLIANCES (8.6) — the same tag can belong to different
#  alliances on different game servers. The first alliance to register a
#  tag keeps the plain key ("HAL"). A different alliance with the same tag
#  from another game server gets the key "HAL·121". The KEY is what roles,
#  channel categories and database rows use (so all the role/rank/channel
#  machinery works unchanged); members only ever see the plain tag in
#  their nickname: "Mavis [HAL] (121)".
# ------------------------------------------------------------
ALLIANCE_KEY_SEP = "·"
_KEY_INPUT_RE = re.compile(r"^\[?\s*([A-Z]{2,4})\s*\]?\s*[-·.:/ ]*\s*\(?\s*(\d+)?\s*\)?$")


def tag_display(key) -> str:
    """'HAL·121' -> 'HAL'; 'HAL' -> 'HAL'. What members see."""
    return (key or "").split(ALLIANCE_KEY_SEP)[0]


def tag_home_server(key):
    """'HAL·121' -> '121'; plain keys have no fixed home server -> None."""
    parts = (key or "").split(ALLIANCE_KEY_SEP)
    return parts[1] if len(parts) > 1 and parts[1] else None


def make_alliance_key(tag: str, server: str) -> str:
    return f"{tag.upper()}{ALLIANCE_KEY_SEP}{server}"


def normalize_alliance_key(raw: str) -> str:
    """Lets staff type a scoped alliance without hunting for the '·':
    'HAL-121', 'HAL 121', 'HAL121', 'HAL (121)', '[HAL] (121)' all become
    'HAL·121'. Plain tags just get upper-cased."""
    s = (raw or "").strip().upper()
    m = _KEY_INPUT_RE.match(s)
    if not m:
        return s
    return m.group(1) + (f"{ALLIANCE_KEY_SEP}{m.group(2)}" if m.group(2) else "")


def resolve_alliance_key(tag: str, servers, known_keys):
    """Which alliance does a plain tag + a member's server(s) point to?
    Prefers the alliance scoped to one of their servers, then the plain
    one. Returns None if nothing matches (or it's genuinely ambiguous)."""
    tag = (tag or "").upper()
    cands = [k for k in known_keys if tag_display(k) == tag]
    if not cands:
        return None
    servers = list(servers or [])
    scoped = [make_alliance_key(tag, srv) for srv in servers if make_alliance_key(tag, srv) in cands]
    # A server-scoped alliance only wins when it's clearly theirs (they play
    # on exactly one server); multi-server players default to the original.
    if scoped and (len(servers) == 1 or tag not in cands):
        return scoped[0]
    if tag in cands:
        return tag
    return cands[0] if len(cands) == 1 else None


NICKNAME_PATTERN = re.compile(r'^(.*?)\s*\[([A-Za-z]{2,4})\]\s*\(([\d/]+)\)\s*$')


def parse_formatted_nickname(display_name: str):
    """Returns (name, tag, server_nums_list) if display_name already matches
    our standard '{name} [{TAG}] ({servers})' format, else None."""
    match = NICKNAME_PATTERN.match(display_name.strip())
    if not match:
        return None
    name, tag, servers_str = match.groups()
    tag = tag.upper()
    servers = [s for s in servers_str.split("/") if s]
    name = name.strip()
    if not name or not servers:
        return None
    return name, tag, servers


async def grant_roles_from_nickname(guild, member, tag: str, servers: list):
    """Grants Member + the parsed tag role + matching server role(s) to an
    existing member whose nickname already matches our format. Deliberately
    does NOT mark them fully registered in the DB — that still needs either
    /register or a staff click on the auto-registration button, so future
    audits keep flagging them until it's actually finished."""
    roles_to_add = []
    member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)
    if member_role:
        roles_to_add.append(member_role)
    tag_role = discord.utils.get(guild.roles, name=tag)
    if tag_role:
        roles_to_add.append(tag_role)
    managed = await get_managed_servers(guild.id)
    for num in servers:
        if num in managed:
            srv_role = discord.utils.get(guild.roles, name=role_name_for_server(num))
            if srv_role:
                roles_to_add.append(srv_role)

    for r in roles_to_add:
        if r not in member.roles:
            try:
                await member.add_roles(r)
            except discord.Forbidden:
                pass


STAFF_ROLE_NAMES = {ROLE_JUDGE, ROLE_STITCH, ROLE_MILLIE, ROLE_CHROME, ROLE_SILENT, ROLE_SENATOR, ROLE_DICTATOR}
SENIOR_STAFF_ROLE_NAMES = {ROLE_SENATOR, ROLE_DICTATOR}


NAME_CHANGE_REMINDER = (
    "✏️ **Heads up, Chief:** your name here should always match your in-game name — and you can change it any time. "
    "If you ever change your name *in the game*, change it here too: just type `/change-nick` "
    "(takes ten seconds and keeps your [TAG] and server intact).\n"
    "📚 And always check {abilities} to see what you can do here."
)


def abilities_mention(guild) -> str:
    """Clickable #❓-abilities link when the channel exists, plain text otherwise."""
    ch = discord.utils.get(guild.text_channels, name="❓-abilities") if guild else None
    return ch.mention if ch else "#❓-abilities"


def is_staff_member(member: discord.Member) -> bool:
    """JUDGE, SENATOR, DICTATOR, or a true Discord Administrator."""
    if member.guild_permissions.administrator:
        return True
    return bool({r.name for r in member.roles} & STAFF_ROLE_NAMES)


def is_senior_staff_member(member: discord.Member) -> bool:
    """SENATOR, DICTATOR, or a true Discord Administrator."""
    if member.guild_permissions.administrator:
        return True
    return bool({r.name for r in member.roles} & SENIOR_STAFF_ROLE_NAMES)


def is_staff():
    async def predicate(interaction: discord.Interaction) -> bool:
        if not isinstance(interaction.user, discord.Member):
            raise app_commands.CheckFailure("Server-only command.")
        if is_staff_member(interaction.user):
            return True
        raise app_commands.MissingPermissions(["administrator"])
    return app_commands.check(predicate)


def is_senior_staff():
    async def predicate(interaction: discord.Interaction) -> bool:
        if not isinstance(interaction.user, discord.Member):
            raise app_commands.CheckFailure("Server-only command.")
        if is_senior_staff_member(interaction.user):
            return True
        raise app_commands.MissingPermissions(["administrator"])
    return app_commands.check(predicate)


def can_approve_rank_request(member: discord.Member, tag: str, rank: str) -> bool:
    """Judge+ can approve any rank request. An alliance's own R5 can ALSO
    approve R4 requests for their own alliance (self-governance for officer
    promotions) — but not R5 requests, which still need staff sign-off."""
    if is_staff_member(member):
        return True
    if rank == "R4":
        r5_role = discord.utils.get(member.guild.roles, name=f"{tag}-R5")
        if r5_role and r5_role in member.roles:
            return True
    return False


def is_dictator_member(member: discord.Member) -> bool:
    """DICTATOR, or a true Discord Administrator. Reserved for genuinely
    destructive, irreversible actions — not even Senator gets this one."""
    if member.guild_permissions.administrator:
        return True
    return ROLE_DICTATOR in {r.name for r in member.roles}


def is_dictator():
    async def predicate(interaction: discord.Interaction) -> bool:
        if not isinstance(interaction.user, discord.Member):
            raise app_commands.CheckFailure("Server-only command.")
        if is_dictator_member(interaction.user):
            return True
        raise app_commands.MissingPermissions(["administrator"])
    return app_commands.check(predicate)

# ============================================================
#  HELPER FUNCTIONS
# ============================================================
async def get_http_session():
    if bot.http_session is None or bot.http_session.closed:
        bot.http_session = aiohttp.ClientSession()
    return bot.http_session


# ------------------------------------------------------------
#  TRANSLATION — official Google Cloud Translation API only. The old
#  "unofficial scraper as a fallback" approach (deep_translator's
#  GoogleTranslator) was dropped entirely: it scrapes Google's web UI
#  rather than using a real API, and is the LESS reliable of the two —
#  it was never actually a safety net, just an extra way to fail. Retries
#  transient errors, caches repeated (text, language) pairs since
#  onboarding prompts are the same handful of strings over and over.
# ------------------------------------------------------------
_translation_cache = {}
TRANSLATION_CACHE_MAX = 1000
TRANSLATION_MAX_RETRIES = 3


async def translate_text(text: str, target_lang: str, source_lang: str = None) -> Optional[str]:
    """Returns the translation, or None if it genuinely couldn't be done
    (no API key configured, or every retry failed) — callers decide how to
    degrade (usually: fall back to the original English text rather than
    showing the user nothing)."""
    if not text or not target_lang or target_lang == "en":
        return text

    cache_key = (text, target_lang)
    if cache_key in _translation_cache:
        await increment_stat("translations_used")
        return _translation_cache[cache_key]

    if not GOOGLE_API_KEY:
        return None

    url = f"https://translation.googleapis.com/language/translate/v2?key={GOOGLE_API_KEY}"
    params = {"q": text, "target": target_lang, "format": "text"}
    if source_lang:
        params["source"] = source_lang

    session = await get_http_session()
    for attempt in range(TRANSLATION_MAX_RETRIES):
        try:
            async with session.post(url, data=params, timeout=aiohttp.ClientTimeout(total=8)) as resp:
                if resp.status == 200:
                    data = await resp.json()
                    translated = data["data"]["translations"][0]["translatedText"]
                    if len(_translation_cache) >= TRANSLATION_CACHE_MAX:
                        _translation_cache.pop(next(iter(_translation_cache)))
                    _translation_cache[cache_key] = translated
                    await increment_stat("translations_used")
                    return translated
                if resp.status in (429, 500, 502, 503, 504):
                    await asyncio.sleep(1.5 * (attempt + 1))
                    continue
                print(f"[TRANSLATOR ERROR] Google Translate returned {resp.status}: {await resp.text()}")
                return None
        except asyncio.TimeoutError:
            print(f"[TRANSLATOR ERROR] Attempt {attempt + 1} timed out with no response.")
            await asyncio.sleep(1.5 * (attempt + 1))
        except aiohttp.ClientError as e:
            print(f"[TRANSLATOR ERROR] Attempt {attempt + 1} failed: {e}")
            await asyncio.sleep(1.5 * (attempt + 1))
    return None


IMPRISON_SPLASH_FLAVOR = [
    "🚨 BREAKING: {mention} just got hauled off in cuffs. The precinct thanks you for your cooperation.",
    "⛓️ {mention} is doing time now. Word travels fast in this town.",
    "🚔 Sirens blaring — {mention} has been taken into custody.",
    "📰 EXTRA, EXTRA: {mention} behind bars as of right now.",
    "⛓️ The cell door just slammed shut on {mention}. Reflect well.",
    "🚨 {mention} has been apprehended. The streets are a little safer tonight.",
    "👮 Book 'em: {mention} is now a guest of the precinct's finest accommodations.",
    "⛓️ {mention} just got the bracelets. Don't drop the soap.",
    "🚔 Justice moves fast around here — {mention} is locked up.",
    "📣 Public notice: {mention} has been imprisoned. Act accordingly.",
]
PARDON_SPLASH_FLAVOR = [
    "🕊️ {mention} has been released. Try to stay out of trouble this time.",
    "🔓 The cell door swings open — {mention} is a free Chief once again.",
    "🎉 {mention} just walked out a free person. Welcome back.",
    "🕊️ Sentence served, record cleared — {mention} is back among us.",
    "🔓 {mention} has been sprung. No hard feelings, right?",
    "📣 Public notice: {mention} has been released and pardoned.",
    "🕊️ Freedom looks good on {mention}. Welcome back to the precinct.",
    "🔓 The bars lift for {mention} — go make better choices.",
    "🎉 {mention} is officially off the hook. Don't waste this second chance.",
    "🕊️ {mention} walks free. The precinct wishes them well.",
]


async def get_user_splash_channels(guild, user_id: int) -> list:
    """Where a person would actually be 'seen' — their alliance's own
    lobby (if they have one) plus the shared general-chat — so major
    moderation events land somewhere the community actually notices,
    not just the staff-only #logs."""
    channels = []
    general_ch = discord.utils.get(guild.channels, name="💬-general-chat")
    if general_ch:
        channels.append(general_ch)

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT alliance_tag FROM users WHERE user_id = ?", (user_id,))
        row = await cur.fetchone()
    tag = row[0] if row else None
    if tag:
        category = discord.utils.get(guild.categories, name=f"{tag} CHATS")
        if category:
            lobby_ch = discord.utils.get(category.text_channels, name="💬-lobby")
            if lobby_ch:
                channels.append(lobby_ch)
    return channels


async def send_splash_announcement(guild, user_id: int, flavor_pool: list, mention: str):
    channels = await get_user_splash_channels(guild, user_id)
    message = random.choice(flavor_pool).format(mention=mention)
    for ch in channels:
        try:
            await ch.send(message)
        except discord.HTTPException:
            pass


async def get_user_lang(user_id: int) -> str:
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT pref_lang FROM users WHERE user_id = ?", (user_id,))
        row = await cur.fetchone()
    return row[0] if row and row[0] else "en"


async def t(text: str, user_id: int) -> str:
    """Translates text into a specific user's stored language preference.
    Falls back to the original English text if their language is English,
    or if translation fails for any reason — never blocks on a translation
    hiccup, never shows the user nothing."""
    lang = await get_user_lang(user_id)
    if lang == "en":
        return text
    translated = await translate_text(text, lang)
    return translated if translated is not None else text


async def tf(template: str, user_id: int, **kwargs) -> str:
    """Like t(), but for messages with per-user dynamic content (a mention,
    an entered name, a tag) baked in via {placeholder} tokens. Translates
    the STATIC template first — which actually repeats across different
    users and hits the cache — then substitutes the dynamic values in
    afterward. Use this instead of f-string-then-translate whenever the
    message contains anything that differs per call; f-string-then-translate
    means the cache key is unique to that one call and never hits again."""
    if not user_id:
        return template.format(**kwargs)
    lang = await get_user_lang(user_id)
    if lang == "en":
        return template.format(**kwargs)

    translated_template = await translate_text(template, lang)
    if translated_template and all(f"{{{k}}}" in translated_template for k in kwargs):
        try:
            return translated_template.format(**kwargs)
        except (KeyError, IndexError, ValueError):
            pass
    # Translation failed, or mangled the placeholder tokens — safe fallback
    # to the untranslated (but still correctly filled-in) English text.
    return template.format(**kwargs)


async def send_long(destination, content: str, **kwargs):
    """Sends content that might exceed Discord's 2000-char message limit
    by splitting it into multiple messages along line breaks — never
    truncates or silently drops anything, which matters for summaries
    where every line might be the one piece of information someone needs
    to actually fix a problem."""
    lines = content.split("\n")
    safe_lines = [line if len(line) <= 1990 else line[:1987] + "..." for line in lines]
    chunk = ""
    for line in safe_lines:
        candidate = f"{chunk}\n{line}" if chunk else line
        if len(candidate) > 1990:
            if chunk:
                try:
                    await destination.send(chunk, **kwargs)
                except discord.HTTPException:
                    pass
            chunk = line
        else:
            chunk = candidate
    if chunk:
        try:
            await destination.send(chunk, **kwargs)
        except discord.HTTPException:
            pass


async def log_event(guild, message):
    log_channel = discord.utils.get(guild.channels, name="logs")
    if log_channel:
        await send_long(log_channel, message)


async def safe_step(guild, label: str, coro, default=None):
    """Runs one startup step so that if it fails, it fails ALONE: logged to
    the console and #logs, and startup carries on to the next step. Before
    this, one exception anywhere in on_ready silently skipped everything
    after it — including restoring #logs buttons and syncing slash
    commands — leaving a bot that looked online but was half-started."""
    try:
        return await coro
    except Exception as e:
        detail = f"{type(e).__name__}: {e}"
        print(f"[ERROR] Startup step '{label}' failed for {getattr(guild, 'name', '?')}: {detail}")
        hint = ""
        if not USE_POSTGRES and isinstance(e, sqlite3.OperationalError) and any(k in str(e).lower() for k in ("disk i/o", "locked", "readonly", "unable to open")):
            hint = (f"\nThis is a database *file* problem, not a logic bug. The DB is at `{DB_PATH}` — it must be on a local "
                    f"disk, not a Google Drive / OneDrive / Dropbox folder, and only one copy of the bot may run at a time.")
        try:
            await log_event(guild, f"🛑 **STARTUP STEP FAILED — {label}**\n`{detail[:400]}`{hint}\nEvery other startup step still ran.")
        except Exception:
            pass
        try:
            await report_error(guild, f"startup step '{label}'", None, e)  # DM the owner too
        except Exception:
            pass
        return default


async def get_setting(key: str):
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT value FROM settings WHERE key = ?", (key,))
        row = await cur.fetchone()
    return row[0] if row else None


async def set_setting(key: str, value: str):
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)", (key, value))
        await conn.commit()


async def get_guild_setting(guild_id: int, key: str):
    """Guild-scoped settings — same underlying table as get_setting, but
    the guild ID is baked into the key so one bot/database can correctly
    serve more than one Discord server without settings leaking between
    them. Use this for anything that's genuinely per-guild configuration
    (which is almost everything except true process-level state like
    active_instance_id, which is intentionally shared across a single
    deployment's guilds — see the leadership/failover system)."""
    return await get_setting(f"g{guild_id}:{key}")


async def set_guild_setting(guild_id: int, key: str, value: str):
    await set_setting(f"g{guild_id}:{key}", value)


# ------------------------------------------------------------
#  LIVE-CONFIGURABLE SETTINGS — these used to be hardcoded module-level
#  constants requiring a code edit and redeploy to change. Now they're
#  guild-scoped settings with sane defaults, adjustable live via
#  /configure-setting, and validated by check_config_health() at startup
#  (and after every change) so a bad value gets caught and offered a
#  one-click fix instead of silently misbehaving until someone notices.
#
#  chase_round_hours is capped at 6 specifically because CHASE_HINT_POOL
#  only has 6 tiers of hand-written hints — that's a real, structural
#  limit, not an arbitrary one, so the configurable range reflects it
#  honestly instead of accepting a value the hint system can't support.
# ------------------------------------------------------------
CONFIGURABLE_SETTINGS = {
    "chase_start_hour": {"default": 12, "type": int, "min": 0, "max": 23, "label": "Daily Chase start hour (0-23, local time)"},
    "chase_round_hours": {"default": 6, "type": int, "min": 1, "max": 6, "label": "Chase round length in hours (capped at 6 — that's how many tiers of hints exist)"},
    "chase_cop_ratio": {"default": 0.35, "type": float, "min": 0.1, "max": 0.9, "label": "Fraction of the eligible pool that becomes cops (0.1-0.9)"},
    "rogue_round_hours": {"default": 24, "type": int, "min": 1, "max": 168, "label": "Rogue RoboCop round length in hours"},
    "alliance_approval_minutes": {"default": 15, "type": int, "min": 1, "max": 1440, "label": "Alliance auto-approval window in minutes"},
    "founders_pass_threshold": {"default": 10, "type": int, "min": 0, "max": 100, "label": "Founder's Pass — how many alliances get it"},
    "founders_pass_max_server_size": {"default": 15, "type": int, "min": 0, "max": 200, "label": "Founder's Pass — only applies while total alliances are under this"},
    "nickname_maintenance_hour": {"default": 4, "type": int, "min": 0, "max": 23, "label": "Daily nickname maintenance hour (0-23, local time)"},
    "game_stats_hour": {"default": 0, "type": int, "min": 0, "max": 23, "label": "Daily /game-stats digest post hour (0-23, local time; 0 = midnight)"},
    "monthly_champion_hour": {"default": 0, "type": int, "min": 0, "max": 23, "label": "Monthly Champion announcement hour, on the 1st of each month (0-23, local time; 0 = midnight)"},
    "timezone": {"default": "America/Los_Angeles", "type": str, "label": "Server's operating timezone (IANA name, e.g. America/Los_Angeles)"},
    "innovator_max_grants": {"default": 50, "type": int, "min": 0, "max": 999999, "label": "Innovator badge — first N total registrants qualify"},
    "innovator_max_multi_server_grants": {"default": 25, "type": int, "min": 0, "max": 999999, "label": "Innovator badge — first N registrants with more than 1 server ALSO qualify (separate pool, may overlap with the total pool)"},
}


async def get_config_value(guild_id: int, key: str):
    """Live, guild-scoped override for a tunable setting, falling back to
    its documented default if never configured or if the stored value is
    invalid — this never raises and never returns something unusable,
    since check_config_health() is what surfaces bad values for a human
    to fix, not this getter silently propagating one further."""
    meta = CONFIGURABLE_SETTINGS[key]
    raw = await get_guild_setting(guild_id, f"config:{key}")
    if raw is None:
        return meta["default"]
    try:
        value = raw if meta["type"] is str else meta["type"](raw)
    except (ValueError, TypeError):
        return meta["default"]

    if meta["type"] is not str:
        lo, hi = meta.get("min"), meta.get("max")
        if (lo is not None and value < lo) or (hi is not None and value > hi):
            return meta["default"]
    elif key == "timezone":
        try:
            ZoneInfo(value)
        except Exception:
            return meta["default"]
    return value


async def get_guild_timezone(guild_id: int) -> ZoneInfo:
    """Resolves this guild's configured timezone, falling back to the
    same fixed-offset safety net as the module-level default if tzdata
    isn't installed (see the startup CHASE_TIMEZONE warning)."""
    tz_name = await get_config_value(guild_id, "timezone")
    try:
        return ZoneInfo(tz_name)
    except Exception:
        return CHASE_TIMEZONE


async def increment_stat(key: str, amount: int = 1):
    """Global counters — translations served, translate-reactions used, etc."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute(
            "INSERT INTO stats (key, value) VALUES (?, ?) ON CONFLICT(key) DO UPDATE SET value = value + ?",
            (key, amount, amount)
        )
        await conn.commit()


VALID_USER_STAT_COLUMNS = {"referrals", "rps_wins", "rps_losses", "rps_ties", "rogue_catches"}


async def increment_user_stat(user_id: int, column: str, amount: int = 1):
    """Per-user counters — referrals, RPS record. `column` is always one of
    our own hardcoded literals (never user input), but whitelisted anyway
    since it gets interpolated into the query."""
    if column not in VALID_USER_STAT_COLUMNS:
        raise ValueError(f"Unknown stat column: {column}")
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute(
            f"INSERT INTO user_stats (user_id, {column}) VALUES (?, ?) "
            f"ON CONFLICT(user_id) DO UPDATE SET {column} = {column} + ?",
            (user_id, amount, amount)
        )
        await conn.commit()


async def claim_leadership():
    await set_setting("active_instance_id", INSTANCE_ID)
    await set_setting("active_instance_claimed_at", datetime.now().isoformat())
    await set_setting("active_instance_heartbeat", datetime.now().isoformat())


async def leadership_watchdog():
    """Runs for the lifetime of the process: (a) heartbeats regularly while
    still the leader, so a future instance can tell we were genuinely alive
    and recently active (not just 'some ID was here once'), and (b) steps
    aside gracefully the moment a newer instance claims leadership.

    No need to manually stop the old process before starting a new one —
    just run the new main.py and the old one steps aside on its own.

    IMPORTANT: both processes must run from the same working directory so
    they share the same robocop.db file — that's where the handoff signal
    actually lives. A new instance pointed at a different/empty database
    won't be able to take over."""
    global _is_leader
    while True:
        await asyncio.sleep(LEADERSHIP_CHECK_INTERVAL_SECONDS)
        current_leader = await get_setting("active_instance_id")
        if current_leader != INSTANCE_ID:
            _is_leader = False
            print(f"[SYSTEM] 🔄 Instance {current_leader} has taken over. Instance {INSTANCE_ID} shutting down gracefully...")
            for guild in bot.guilds:
                await log_event(
                    guild,
                    f"🔄 **INSTANCE HANDOFF**\nA newer RoboCop instance (`{current_leader}`) has taken control. "
                    f"This instance (`{INSTANCE_ID}`) is shutting down now."
                )
            await bot.close()
            return
        else:
            await set_setting("active_instance_heartbeat", datetime.now().isoformat())


def clean_display_name(display_name: str) -> str:
    """Strips [TAG], -R#, (server) and stray 2-3 digit numbers to recover the base in-game name."""
    return re.sub(r'\[.*?\]|-R\d|\(.*?\)|\b\d{2,3}\b', '', display_name).strip().lower()


def strip_nickname_decorations(display_name: str) -> str:
    """Same idea as clean_display_name but keeps original casing — used to
    recover someone's base name from their current nickname for display."""
    return re.sub(r'\[.*?\]|-R\d|\(.*?\)|\b\d{2,3}\b', '', display_name).strip()


async def upsert_user_nickname(user_id: int, server_number: str, nickname: str, make_active: bool = False):
    """Saves (or updates) a user's known nickname for one specific server.
    Does NOT touch their live Discord nickname by itself — that only
    happens via switch_active_nickname, so callers can batch-seed several
    servers at once without triggering a nickname edit per row."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute(
            "INSERT INTO user_nicknames (user_id, server_number, nickname, is_active) VALUES (?, ?, ?, ?) "
            "ON CONFLICT(user_id, server_number) DO UPDATE SET nickname = excluded.nickname, updated_at = CURRENT_TIMESTAMP",
            (user_id, server_number, nickname, 1 if make_active else 0)
        )
        if make_active:
            await cur.execute("UPDATE user_nicknames SET is_active = 0 WHERE user_id = ? AND server_number != ?", (user_id, server_number))
        await conn.commit()


async def maybe_grant_innovator(guild, member, server_nums: list):
    """Checks both Innovator pools — first N total registrants, and first
    M registrants with more than one server — and grants the badge if
    either is satisfied. A multi-server person who's also within the
    total pool consumes a slot in BOTH counts simultaneously the moment
    they're granted, which is exactly why the realistic combined total
    tends to land under the sum of the two caps rather than right at it."""
    if await get_guild_setting(guild.id, "innovator_program_active") == "0":
        return

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT COUNT(*) FROM innovators")
        total_count = (await cur.fetchone())[0]
        await cur.execute(
            "SELECT COUNT(*) FROM innovators i JOIN users u ON i.user_id = u.user_id WHERE u.server_number LIKE '%,%'"
        )
        multi_server_count = (await cur.fetchone())[0]

    max_total = await get_config_value(guild.id, "innovator_max_grants")
    max_multi = await get_config_value(guild.id, "innovator_max_multi_server_grants")
    is_multi_server = len(server_nums) > 1

    qualifies = (total_count < max_total) or (is_multi_server and multi_server_count < max_multi)
    if not qualifies:
        return

    innovator_role = discord.utils.get(guild.roles, name=ROLE_INNOVATOR)
    if innovator_role:
        try:
            await member.add_roles(innovator_role, reason="Early tester — Innovator badge.")
        except discord.HTTPException:
            pass
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("INSERT OR IGNORE INTO innovators (user_id, username) VALUES (?, ?)", (member.id, str(member)))
        await conn.commit()
        if cur.rowcount == 0:
            return  # already an Innovator somehow — don't re-fire fanfare/DM

    # 🌟 Fanfare — a public moment, plus a genuine, personal thank-you in
    # DM. This badge is tied to their Discord ID specifically, not this
    # one server, so the DM says so.
    general_ch = discord.utils.get(guild.channels, name="💬-general-chat")
    if general_ch:
        try:
            await general_ch.send(embed=discord.Embed(
                title="🌟 A NEW INNOVATOR HAS JOINED THE RANKS",
                description=f"{member.mention} just became Innovator **#{total_count + 1}** — one of the first to help shape this place. Welcome in.",
                color=INNOVATOR_COLOR
            ))
        except discord.HTTPException:
            pass
    try:
        await member.send(embed=discord.Embed(
            title="🌟 Thank you, genuinely",
            description=(
                "Mesk wanted me to pass this along personally: he really appreciates you being here "
                "this early, testing things, dealing with the rough edges, helping this become what "
                "it's going to be. That's not a small thing, and it doesn't go unnoticed.\n\n"
                "This badge is tied to **your Discord ID**, not just this server — so however many "
                "servers this ends up running in down the line, you'll always carry it. As things "
                "grow, it's meant to keep meaning something: a little extra access, a little extra "
                "trust, because you were here first.\n\n"
                "You've also got access to **#🌟-innovator-lounge** now — a quieter space, just badge "
                "holders and staff, for suggestions and issues.\n\n"
                "Thank you for being one of the first."
            ),
            color=INNOVATOR_COLOR
        ))
    except discord.Forbidden:
        pass


async def switch_active_nickname(guild, member, server_number: str) -> bool:
    """Makes the stored nickname for a specific server the member's active
    one — updates the DB record, mirrors it into users.in_game_name (so
    every other part of the bot that reads that field stays correct
    without needing to know this system exists), and applies it to their
    live Discord nickname immediately. Returns False if they don't
    actually have a stored nickname for that server."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT nickname FROM user_nicknames WHERE user_id = ? AND server_number = ?", (member.id, server_number))
        row = await cur.fetchone()
        if not row:
            return False
        new_name = row[0]

        await cur.execute("UPDATE user_nicknames SET is_active = 0 WHERE user_id = ?", (member.id,))
        await cur.execute("UPDATE user_nicknames SET is_active = 1 WHERE user_id = ? AND server_number = ?", (member.id, server_number))
        await cur.execute("UPDATE users SET in_game_name = ? WHERE user_id = ?", (new_name, member.id))
        await conn.commit()

        await cur.execute("SELECT alliance_tag, server_number FROM users WHERE user_id = ?", (member.id,))
        tag_row = await cur.fetchone()

    if tag_row and tag_row[0]:
        tag, srv_field = tag_row
        server_nums = await parse_stored_server_field(srv_field, guild.id)
        srv_display = format_server_display(server_nums)
        name_budget = 32 - len(f" [{tag_display(tag)}] {srv_display}")
        trimmed = new_name[:max(1, name_budget)]
        new_nickname = f"{trimmed} [{tag_display(tag)}] {srv_display}"
        try:
            await member.edit(nick=new_nickname[:32])
        except discord.HTTPException:
            pass
    return True


async def apply_ingame_name_change(guild, member, new_name: str) -> str:
    """Updates a member's base in-game name while leaving their alliance-tag
    prefix and server-number suffix exactly as they are — the whole point
    of /change-nick over hand-editing a Discord nickname, since someone
    fixing a typo or reporting a genuine in-game name change shouldn't
    have to also retype '[TAG] (servers)' correctly (or risk breaking it).
    Keeps users.in_game_name and any active user_nicknames row in sync so
    every other part of the bot that reads those fields stays correct.
    Returns the final nickname actually applied, capped at 32 chars."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT alliance_tag, server_number FROM users WHERE user_id = ?", (member.id,))
        row = await cur.fetchone()
        tag, srv_field = row if row else (None, None)

    if tag:
        server_nums = await parse_stored_server_field(srv_field, guild.id)
        srv_display = format_server_display(server_nums)
        suffix = f" [{tag_display(tag)}] {srv_display}".rstrip()
        name_budget = 32 - len(suffix)
        trimmed = new_name[:max(1, name_budget)]
        full_nickname = f"{trimmed}{suffix}"
    else:
        full_nickname = new_name[:32]

    try:
        await member.edit(nick=full_nickname[:32])
    except discord.HTTPException:
        pass

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("UPDATE users SET in_game_name = ? WHERE user_id = ?", (new_name, member.id))
        await cur.execute(
            "UPDATE user_nicknames SET nickname = ?, updated_at = CURRENT_TIMESTAMP WHERE user_id = ? AND is_active = 1",
            (new_name, member.id)
        )
        await conn.commit()

    return full_nickname[:32]


async def compute_expected_nickname(member, approved_tags: set, in_game_names: dict = None):
    """Works out what this member's nickname SHOULD be, based purely on the
    tag/server roles they actually currently hold — not their stored DB
    fields, so it catches drift (role changes that never got reflected in
    the nickname). Returns None if they don't hold a configured server role,
    since there's nothing to compute a suffix from.

    `in_game_names` is an optional pre-fetched {user_id: name} dict — pass
    one in when checking many members in a loop, so this doesn't open a
    fresh blocking DB connection per member (that's slow enough on a
    decent-sized server to freeze the whole event loop and cause Discord's
    "application did not respond" / "command is outdated" timeouts)."""
    member_role_names = {r.name for r in member.roles}
    member_tags = [name for name in member_role_names if name in approved_tags]
    if not member_tags:
        return None
    tag = member_tags[0]

    member_servers = [num for num in await get_managed_servers(member.guild.id) if role_name_for_server(num) in member_role_names]
    if not member_servers:
        return None

    if in_game_names is not None:
        stored_name = in_game_names.get(member.id)
    else:
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT in_game_name FROM users WHERE user_id = ?", (member.id,))
            row = await cur.fetchone()
        stored_name = row[0] if row else None

    base_name = (stored_name.strip() if stored_name else "") or strip_nickname_decorations(member.display_name) or member.name

    srv_display = format_server_display(member_servers)
    name_budget = 32 - len(f" [{tag_display(tag)}] {srv_display}")
    trimmed_name = base_name[:max(1, name_budget)] or "Chief"
    return f"{trimmed_name} [{tag_display(tag)}] {srv_display}"


def find_member_by_base_name(guild, nickname):
    search_name = nickname.strip().lower()
    for m in guild.members:
        if clean_display_name(m.display_name) == search_name:
            return m
    return None


async def ensure_role(guild, name, color=discord.Color.default(), permissions=None, hoist=False, why="", repairs=None):
    """Golden rule: only creates a role if it's missing. Never touches an
    existing role's color/permissions/hoist — those are the server admin's
    to customize. If we DO have to create one (because a feature depends on
    it existing), we note why in `repairs` so it shows up in the startup log."""
    role = discord.utils.get(guild.roles, name=name)
    if not role:
        perms = permissions or guild.default_role.permissions
        role = await guild.create_role(name=name, color=color, permissions=perms, hoist=hoist, reason="Robocop Auto-Generation")
        print(f"[INFRASTRUCTURE] Created role: {name}")
        if repairs is not None:
            repairs.append(f"🎭 Role **@{name}** didn't exist{f' — {why}' if why else ''}. Created it with default settings.")
    return role


def is_pinkish(color: discord.Color) -> bool:
    """Pink/magenta/rose is reserved exclusively for Millie, system-wide,
    absolute rule. Hue-based check (pink sits ~310-350°) rather than an
    exact-value comparison, so this catches any shade in that family, not
    just the two specific pinks already in use."""
    r, g, b = (color.value >> 16) & 0xFF, (color.value >> 8) & 0xFF, color.value & 0xFF
    h, s, v = colorsys.rgb_to_hsv(r / 255, g / 255, b / 255)
    hue = h * 360
    return 310 <= hue <= 350 and s > 0.35


def get_distinct_alliance_color(existing_colors):
    for _ in range(50):
        color = discord.Color(random.randint(0, 0xFFFFFF))
        if color.value not in existing_colors and color.value != 0 and not is_pinkish(color):
            return color
    return discord.Color.blue()


def parse_db_local_time(value):
    """Reads a timestamp from the database as a naive LOCAL datetime (the
    same kind datetime.now() returns). Python writes local ISO strings
    ('2026-09-28T04:47:13.123'), but columns filled by SQLite's own
    CURRENT_TIMESTAMP default are UTC ('2026-09-28 11:47:13'). Comparing
    those raw against local time made a 30-minute alliance cooldown look
    like hours (UTC is 7-8 hours ahead of Vancouver). Returns None if
    unreadable."""
    if not value:
        return None
    try:
        if "T" in value:
            dt = datetime.fromisoformat(value)
            return dt if dt.tzinfo is None else dt.astimezone().replace(tzinfo=None)
        dt = datetime.strptime(value[:19], "%Y-%m-%d %H:%M:%S").replace(tzinfo=timezone.utc)
        return dt.astimezone().replace(tzinfo=None)
    except (ValueError, TypeError):
        return None


def get_rank_shade(base_color: discord.Color, factor: float, floor: float) -> discord.Color:
    """A darker shade of an alliance color for its R4/R5 roles that keeps
    the same hue and never drops below a readable brightness. The old
    approach (subtract 70 from each RGB channel, twice for R5) turned
    mid-tone alliance colors almost black on R5."""
    r, g, b = (base_color.value >> 16) & 0xFF, (base_color.value >> 8) & 0xFF, base_color.value & 0xFF
    h, s_, v = colorsys.rgb_to_hsv(r / 255, g / 255, b / 255)
    if v > floor:
        v = max(floor, v * factor)
    r2, g2, b2 = colorsys.hsv_to_rgb(h, s_, v)
    return discord.Color.from_rgb(int(r2 * 255), int(g2 * 255), int(b2 * 255))


def get_darkened_color(base_color: discord.Color):
    r = max(0, ((base_color.value >> 16) & 0xFF) - 70)
    g = max(0, ((base_color.value >> 8) & 0xFF) - 70)
    b = max(0, (base_color.value & 0xFF) - 70)
    return discord.Color((r << 16) + (g << 8) + b)


async def compute_expected_role_order(guild) -> list:
    """The single source of truth for 'correct' sidebar/hierarchy order, top
    to bottom, skipping any role that doesn't currently exist. Shared by
    enforce_role_hierarchy (which applies it) and check_role_hierarchy
    (which just checks it, without touching anything)."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT tag FROM alliances")
        approved_tags = {row[0] for row in await cur.fetchall()}

    millie = discord.utils.get(guild.roles, name=ROLE_MILLIE)
    dictator = discord.utils.get(guild.roles, name=ROLE_DICTATOR)
    senator = discord.utils.get(guild.roles, name=ROLE_SENATOR)
    judge = discord.utils.get(guild.roles, name=ROLE_JUDGE)
    stitch = discord.utils.get(guild.roles, name=ROLE_STITCH)
    chrome = discord.utils.get(guild.roles, name=ROLE_CHROME)
    silent = discord.utils.get(guild.roles, name=ROLE_SILENT)
    # Sorted by creation time (earliest first) within each tier — if
    # someone somehow holds more than one alliance's role at the same
    # tier, the first-created alliance's color wins, exactly as requested.
    tag_r5s = sorted([r for r in guild.roles if r.name.endswith("-R5") and r.name[:-3] in approved_tags], key=lambda r: r.created_at)
    tag_r4s = sorted([r for r in guild.roles if r.name.endswith("-R4") and r.name[:-3] in approved_tags], key=lambda r: r.created_at)
    tag_r3s = sorted([r for r in guild.roles if r.name.endswith("-R3") and r.name[:-3] in approved_tags], key=lambda r: r.created_at)
    tags = sorted([r for r in guild.roles if r.name in approved_tags], key=lambda r: r.created_at)

    server_roles = [r for name in [role_name_for_server(n) for n in await get_managed_servers(guild.id)]
                    if (r := discord.utils.get(guild.roles, name=name))]
    member = discord.utils.get(guild.roles, name=ROLE_MEMBER)
    innovator = discord.utils.get(guild.roles, name=ROLE_INNOVATOR)
    drunk = discord.utils.get(guild.roles, name=ROLE_DRUNK_TANK)
    prison = discord.utils.get(guild.roles, name=ROLE_PRISONER)
    timeout = discord.utils.get(guild.roles, name=ROLE_TIMEOUT)

    # Sidebar priority, top to bottom, exactly as requested:
    #   1. Millie and Stitch — one-of-a-kind honorary badges, always at the
    #      very top, so their distinctive colors always win no matter what
    #      other roles (Dictator, alliance rank, anything) they might also
    #      separately hold. Position alone decides which color displays in
    #      Discord — a role's own color value doesn't matter if something
    #      ranked higher also has a color.
    #   2. Alliance identity, ranked: each alliance's own R5, then R4, then R3,
    #      then plain tag membership.
    #   3. Server hierarchy (staff), lowest of the "important" roles — a Judge
    #      who's also in an alliance shows their [TAG] pride first.
    ordered = []
    if millie: ordered.append(millie)
    if stitch: ordered.append(stitch)
    if chrome: ordered.append(chrome)
    if silent: ordered.append(silent)
    ordered.extend(tag_r5s)
    ordered.extend(tag_r4s)
    ordered.extend(tag_r3s)
    ordered.extend(tags)
    if dictator: ordered.append(dictator)
    if senator: ordered.append(senator)
    if judge: ordered.append(judge)
    ordered.extend(server_roles)
    if member: ordered.append(member)
    if innovator: ordered.append(innovator)
    if drunk: ordered.append(drunk)
    if prison: ordered.append(prison)
    if timeout: ordered.append(timeout)
    return ordered


async def enforce_role_hierarchy(guild):
    if not guild.me.top_role:
        return
    bot_pos = guild.me.top_role.position
    ordered = await compute_expected_role_order(guild)

    updates = {}
    current_pos = bot_pos - 1
    for role in ordered:
        if role.position < bot_pos:
            updates[role] = current_pos
            current_pos -= 1

    if updates:
        try:
            await guild.edit_role_positions(updates, reason="Robocop Automated Hierarchy Enforcement")
            print("[INFRASTRUCTURE] Role hierarchy automatically sorted.")
        except discord.Forbidden:
            print("[WARNING] Could not sort role hierarchy. Ensure Robocop's role is at the very top of the server settings!")


async def restore_stored_roles(member: discord.Member) -> bool:
    """Restores whatever roles were stripped for a prisoner. Returns True if anything was restored."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT stored_roles FROM users WHERE user_id = ?", (member.id,))
        row = await cur.fetchone()
        if row and row[0]:
            role_ids = row[0].split(',')
            roles_to_restore = [member.guild.get_role(int(r_id)) for r_id in role_ids if r_id]
            roles_to_restore = [r for r in roles_to_restore if r]
            if roles_to_restore:
                try:
                    await member.add_roles(*roles_to_restore)
                except discord.Forbidden:
                    pass
            await cur.execute("UPDATE users SET stored_roles = NULL WHERE user_id = ?", (member.id,))
            await conn.commit()
            return True
    return False


async def execute_release(member: discord.Member, role: discord.Role):
    """Performs an immediate prisoner release: removes the role, restores old roles, clears DB state.
    Restoration always runs, even if the Prisoner role itself is missing (e.g. deleted mid-sentence) —
    otherwise a deleted role would trap someone's old roles in limbo forever."""
    try:
        if role in member.roles:
            await member.remove_roles(role)
        await restore_stored_roles(member)
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("UPDATE users SET prison_until = NULL WHERE user_id = ?", (member.id,))
            await conn.commit()
        await log_event(member.guild, f"🕊️ **INMATE RELEASED**\nUser: {member.mention}\nAction: Served full sentence. Solitary confinement lifted and original roles restored.")
        await send_splash_announcement(member.guild, member.id, PARDON_SPLASH_FLAVOR, member.mention)
    except Exception as e:
        print(f"[ERROR] Failed to release prisoner {member.display_name}: {e}")


async def schedule_release(member: discord.Member, role: discord.Role, delay_seconds: float):
    print(f"[TIMER STARTED] {member.display_name} will be released from prison in {int(delay_seconds)} seconds.")
    await asyncio.sleep(max(0, delay_seconds))
    await execute_release(member, role)


async def reschedule_pending_prisoners(guild):
    """Called on startup so a bot restart doesn't leave prisoners locked up forever."""
    prison_role = discord.utils.get(guild.roles, name=ROLE_PRISONER)
    if not prison_role:
        return

    now = datetime.now()
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT user_id, prison_until FROM users WHERE prison_until IS NOT NULL")
        rows = await cur.fetchall()

    restored = 0
    for user_id, prison_until_str in rows:
        member = guild.get_member(user_id)
        if not member:
            continue
        try:
            prison_until = datetime.fromisoformat(prison_until_str)
        except (TypeError, ValueError):
            continue

        remaining = (prison_until - now).total_seconds()
        if remaining <= 0:
            await execute_release(member, prison_role)
        else:
            bot.loop.create_task(schedule_release(member, prison_role, remaining))
            restored += 1

    if restored:
        print(f"[SYSTEM] Rescheduled {restored} prisoner release timer(s) that survived a restart.")


async def lift_lockdown(guild):
    member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)
    perms = guild.default_role.permissions
    perms.update(send_messages=True)
    await guild.default_role.edit(permissions=perms)
    if member_role:
        m_perms = member_role.permissions
        m_perms.update(send_messages=True)
        await member_role.edit(permissions=m_perms)

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("DELETE FROM settings WHERE key = ?", (f"lockdown_until_{guild.id}",))
        await conn.commit()


async def engage_lockdown(guild, seconds: float):
    """Locks @everyone/Member out of sending messages, then automatically
    lifts it after `seconds`. Shared by /killswitch and the automatic
    version-handoff lockdown."""
    member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)
    try:
        perms = guild.default_role.permissions
        perms.update(send_messages=False)
        await guild.default_role.edit(permissions=perms)
        if member_role:
            m_perms = member_role.permissions
            m_perms.update(send_messages=False)
            await member_role.edit(permissions=m_perms)
    except discord.Forbidden:
        return

    end_time = datetime.now() + timedelta(seconds=seconds)
    await set_setting(f"lockdown_until_{guild.id}", end_time.isoformat())
    bot.loop.create_task(auto_lift_lockdown(guild, seconds))


async def auto_lift_lockdown(guild, delay_seconds):
    await asyncio.sleep(max(0, delay_seconds))
    await lift_lockdown(guild)
    await log_event(guild, "🟢 **LOCKDOWN AUTO-LIFTED**\nScheduled duration elapsed.")


VERSION_HANDOFF_LOCKDOWN_SECONDS = 60


async def announce_version_handoff(guild):
    """When a newer bot instance takes over from an old one, give everyone
    a heads-up in every community channel, briefly pause chat during the
    transition, then automatically reopen it — and, for fun, normally
    kick off a Rogue RoboCop round (the story being that the OLD instance
    didn't quite get the message and is hiding among you under a fake
    name). That last part is skippable via /toggle-rogue-bot-program —
    useful for a deliberate migration/adoption event where you want the
    handoff itself to land cleanly before layering a hide-and-seek game
    on top of it."""
    rogue_enabled = await get_guild_setting(guild.id, "rogue_bot_program_active") != "0"

    embed = discord.Embed(
        title="🚨📢 ATTENTION ALL UNITS — PRECINCT-WIDE UPGRADE IN EFFECT 📢🚨",
        description=(
            "**BY ORDER OF COMMAND:** the old unit has been decommissioned. A new one has taken the badge, "
            f"full systems overhaul, top to bottom. Comms are down for about {VERSION_HANDOFF_LOCKDOWN_SECONDS} "
            "seconds while the transition completes — stand by, hold position, this is not a drill.\n\n"
            "Once comms are restored, here's what's now active precinct-wide:"
        ),
        color=discord.Color.blue(),
        timestamp=datetime.now()
    )
    embed.add_field(
        name="📋 YOUR FIELD MANUAL",
        value=(
            "Run `/abilities` any time (also posts in #❓-abilities) for a full, personalized rundown of "
            "everything you're cleared to do — commands, rank privileges, all of it, no guesswork required."
        ),
        inline=False
    )
    embed.add_field(
        name="🚔 ACTIVE OPERATIONS — COPS & ROBBERS",
        value=(
            "A daily manhunt runs right here in #💬-general-chat. Cops get poetic intel drops on the hour; "
            "robbers just have to survive, or strike first. Nobody knows who's been drafted until the DM "
            "arrives. `/chase-status` to check in, `/leave-chase` if you'd rather sit one out."
        ),
        inline=False
    )
    if rogue_enabled:
        embed.add_field(
            name="🕵️ ONGOING INVESTIGATION — THE OLD UNIT DIDN'T GO QUIETLY",
            value=(
                "Word from Internal Affairs: the retired instance is still out there, hiding among you under "
                "a false identity, occasionally running its mouth right here in #💬-general-chat. "
                "`/catch <name>` the moment you think you've made them."
            ),
            inline=False
        )
    embed.add_field(
        name="🎮 STANDING ORDERS — OFF-DUTY ACTIVITIES",
        value="`/rps` for a quick duel against another Chief, or against this unit directly, if you're feeling brave.",
        inline=False
    )
    embed.add_field(
        name="🌟 COMMENDATIONS",
        value="Early badge holders — check #🌟-innovator-lounge. You know who you are, and command hasn't forgotten it.",
        inline=False
    )
    embed.set_footer(text="This precinct is now fully operational. Move out.")

    targets = await gather_all_community_channels(guild)
    for ch in targets:
        try:
            await ch.send(embed=embed)
        except discord.HTTPException:
            pass

    await engage_lockdown(guild, VERSION_HANDOFF_LOCKDOWN_SECONDS)
    await log_event(guild, f"🔄 **VERSION UPDATE** — chat locked for {VERSION_HANDOFF_LOCKDOWN_SECONDS}s while the new instance takes over.")

    if rogue_enabled:
        started = await start_rogue_bot_round(guild)
        if started:
            await log_event(guild, "🕵️ **ROGUE ROBOCOP ROUND STARTED** — triggered by this version handoff.")
    else:
        await log_event(guild, "ℹ️ **ROGUE ROBOCOP SKIPPED** — the program is currently toggled off for this server (`/toggle-rogue-bot-program`).")


async def restore_lockdown_state(guild):
    """Called on startup so a killswitch lockdown active during a restart still gets lifted on time."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT value FROM settings WHERE key = ?", (f"lockdown_until_{guild.id}",))
        row = await cur.fetchone()
    if not row:
        return
    try:
        lockdown_until = datetime.fromisoformat(row[0])
    except ValueError:
        return

    remaining = (lockdown_until - datetime.now()).total_seconds()
    if remaining <= 0:
        await lift_lockdown(guild)
        await log_event(guild, "🟢 **LOCKDOWN AUTO-LIFTED**\nBot restarted after the scheduled duration had already elapsed.")
    else:
        print(f"[SYSTEM] Resuming an active lockdown for {guild.name}: {int(remaining)}s remaining.")
        bot.loop.create_task(auto_lift_lockdown(guild, remaining))


# ------------------------------------------------------------
#  STAFF DM ALERTS — reserved for genuinely big events, so it never
#  turns into notification spam. Right now: bans, new alliances, and
#  R5 requests (all things that either already happened or need a call).
# ------------------------------------------------------------
async def notify_staff_dm(guild, title: str, description: str, color=discord.Color.blurple()):
    embed = discord.Embed(title=title, description=description, color=color, timestamp=datetime.now())
    embed.set_footer(text=f"📡 {guild.name} — Robocop Staff Alert")
    for m in {member for member in guild.members if is_staff_member(member)}:
        try:
            await m.send(embed=embed)
        except discord.Forbidden:
            pass


async def gather_all_community_channels(guild) -> list:
    """#general-chat, every configured precinct channel, and every approved
    alliance's own lobby — the 'everyone' scope shared by staff-tier
    /announce and the automatic version-handoff broadcast."""
    targets = []
    general_ch = discord.utils.get(guild.channels, name="💬-general-chat")
    if general_ch:
        targets.append(general_ch)
    for num in await get_managed_servers(guild.id):
        precinct_ch = discord.utils.get(guild.channels, name=f"🏙️-precinct-{num}")
        if precinct_ch:
            targets.append(precinct_ch)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT tag FROM alliances WHERE status = 'approved'")
        tags = [row[0] for row in await cur.fetchall()]
    for tag in tags:
        chat_category = discord.utils.get(guild.categories, name=f"{tag} CHATS")
        lobby_ch = discord.utils.get(chat_category.text_channels, name="💬-lobby") if chat_category else None
        if lobby_ch:
            targets.append(lobby_ch)
    return targets


async def log_visitor_entry(member):
    guild = member.guild
    visitors_ch = discord.utils.get(guild.channels, name="visitors")
    if not visitors_ch:
        return
    embed = discord.Embed(
        title="🚪 ENTRY",
        description=f"{member.mention} (`{member}`, `{member.id}`) has joined.",
        color=discord.Color.green(),
        timestamp=datetime.now()
    )
    embed.set_thumbnail(url=member.display_avatar.url)
    try:
        await visitors_ch.send(embed=embed)
    except discord.HTTPException:
        pass


async def determine_exit_reason(guild, member) -> str:
    """Checks the audit log for a recent kick/ban matching this member, so
    #visitors can show an accurate reason — including our own automated
    kicks (timeout bypass, invite-check failure, etc.), since those already
    carry a reason string that Discord records. Falls back to 'left
    voluntarily' if nothing matches within the last few seconds."""
    now = datetime.now(timezone.utc)
    try:
        async for entry in guild.audit_logs(limit=5, action=discord.AuditLogAction.kick):
            if entry.target and entry.target.id == member.id and (now - entry.created_at).total_seconds() < 15:
                return f"👢 Kicked — {entry.reason or 'no reason given'}"
    except discord.Forbidden:
        pass
    try:
        async for entry in guild.audit_logs(limit=5, action=discord.AuditLogAction.ban):
            if entry.target and entry.target.id == member.id and (now - entry.created_at).total_seconds() < 15:
                return f"🔨 Banned — {entry.reason or 'no reason given'}"
    except discord.Forbidden:
        pass
    return "🚶 Left voluntarily"


async def log_visitor_exit(member):
    guild = member.guild
    visitors_ch = discord.utils.get(guild.channels, name="visitors")
    if not visitors_ch:
        return
    reason = await determine_exit_reason(guild, member)
    embed = discord.Embed(
        title="🚪 EXIT",
        description=f"{member.mention} (`{member}`, `{member.id}`) has left.\n{reason}",
        color=discord.Color.dark_grey(),
        timestamp=datetime.now()
    )
    embed.set_thumbnail(url=member.display_avatar.url)
    try:
        await visitors_ch.send(embed=embed)
    except discord.HTTPException:
        pass


# ------------------------------------------------------------
#  ALLIANCE AUTO-APPROVAL — a new alliance sits in the Drunk Tank
#  pending a staff review. If nobody acts within the window, it
#  approves itself automatically so nobody's stuck waiting forever.
#  (The actual window length, founders'-pass threshold, and max server
#  size are now live-configurable — see CONFIGURABLE_SETTINGS — these
#  values just document the shipped defaults.)
# ------------------------------------------------------------


async def ensure_leadership_role(guild, tag: str):
    """Creates [TAG]-Leadership the first time it's needed — deliberately
    quiet: not hoisted, no distinct color, so it doesn't read as a visible
    status badge sitting next to someone's name. It's a permission, not a
    trophy. Wires up leadership-chat access the moment it's created."""
    role_name = f"{tag}-Leadership"
    role = discord.utils.get(guild.roles, name=role_name)
    if not role:
        role = await ensure_role(guild, role_name, color=discord.Color.default(), hoist=False)
        chat_category = discord.utils.get(guild.categories, name=f"{tag} CHATS")
        leadership_chat = discord.utils.get(chat_category.text_channels, name="🎖️-leadership-chat") if chat_category else None
        if leadership_chat:
            try:
                await leadership_chat.set_permissions(role, view_channel=True, send_messages=True)
            except discord.Forbidden:
                pass
    return role


async def grant_leadership(guild, member, tag: str):
    """Gives someone [TAG]-Leadership directly — the quiet, discretionary
    grant an R5 can hand out without it being a formal rank promotion.
    This is also exactly what R4/R5 promotion grants automatically under
    the hood, so the leadership-chat channel only ever needs to check for
    this one role, regardless of how someone earned it."""
    role = await ensure_leadership_role(guild, tag)
    try:
        await member.add_roles(role)
    except discord.Forbidden:
        pass

    # Same server condition as everywhere else: leadership-chat access
    # means Member too, unconditionally.
    member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)
    if member_role and member_role not in member.roles:
        try:
            await member.add_roles(member_role)
        except discord.Forbidden:
            pass

    await refresh_leadership_status(guild, tag)
    return role


async def revoke_leadership(guild, member, tag: str) -> bool:
    """Explicit only — losing R4/R5 does NOT automatically strip a
    standalone Leadership grant. If an R5 wants someone's access cleaned
    up after a demotion, this is a deliberate second step, not a surprise
    side effect of the rank change."""
    role = discord.utils.get(guild.roles, name=f"{tag}-Leadership")
    if not role or role not in member.roles:
        return False
    try:
        await member.remove_roles(role)
    except discord.Forbidden:
        pass
    await refresh_leadership_status(guild, tag)
    return True


async def grant_alliance_rank(guild, member, tag: str, rank: str):
    """Grants [TAG]-{rank} (R4 or R5 — R3 was retired, it never carried
    real functional meaning in-game anyway) to a member, creating that
    role the first time it's needed, clearing whichever OTHER tag-rank
    they held for the SAME tag (ranks are exclusive), and automatically
    granting the quiet [TAG]-Leadership permission alongside it — R4/R5
    always carries leadership-chat access without needing its own
    separate wiring."""
    role_name = f"{tag}-{rank}"
    role = discord.utils.get(guild.roles, name=role_name)
    if not role:
        tag_role = discord.utils.get(guild.roles, name=tag)
        # R5 gets a visibly darker shade than R4, so an R5 is identifiable
        # at a glance — but never so dark it disappears on Discord's dark theme.
        if tag_role and tag_role.color.value:
            color = get_rank_shade(tag_role.color, 0.68, 0.40) if rank == "R5" else get_rank_shade(tag_role.color, 0.82, 0.48)
        else:
            color = discord.Color.default()
        role = await ensure_role(guild, role_name, color=color, hoist=True)

    for other_rank in ("R4", "R5"):
        if other_rank == rank:
            continue
        other_role = discord.utils.get(guild.roles, name=f"{tag}-{other_rank}")
        if other_role and other_role in member.roles:
            try:
                await member.remove_roles(other_role)
            except discord.Forbidden:
                pass

    try:
        await member.add_roles(role)
    except discord.Forbidden:
        pass

    # Server condition: anyone with access to ANY chat channel must also
    # be in general-chat, no exceptions. Granting a rank grants alliance
    # channel access, so Member — which gates general-chat — comes with it
    # unconditionally, whether or not they'd normally have earned it yet.
    member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)
    if member_role and member_role not in member.roles:
        try:
            await member.add_roles(member_role)
        except discord.Forbidden:
            pass

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("UPDATE users SET rank_designation = ? WHERE user_id = ?", (rank, member.id))
        await conn.commit()

    await grant_leadership(guild, member, tag)  # R4/R5 always carries leadership access; also refreshes the status message
    await enforce_role_hierarchy(guild)
    return role


async def refresh_leadership_status(guild, tag: str):
    """Keeps the leadership-chat channel's pinned status message accurate:
    'not activated yet' if nobody currently holds Leadership for this
    alliance (from any path — R4, R5, or a standalone grant), or the
    normal access notice once someone does. Called any time rank or
    leadership status changes, so it stays correct without anyone having
    to remember to update it by hand."""
    chat_category = discord.utils.get(guild.categories, name=f"{tag} CHATS")
    leadership_chat = discord.utils.get(chat_category.text_channels, name="🎖️-leadership-chat") if chat_category else None
    if not leadership_chat:
        return

    leadership_role = discord.utils.get(guild.roles, name=f"{tag}-Leadership")
    has_leadership = bool(leadership_role and leadership_role.members)

    if has_leadership:
        status_text = (
            f"🔒 **[{tag}] LEADERSHIP CHAT**\n"
            f"R4, R5, and anyone else the R5 has trusted with access can post here. Ask your R5 if you think "
            f"you should be here but aren't."
        )
    else:
        status_text = (
            f"🔒 **[{tag}] LEADERSHIP CHAT — NOT YET ACTIVATED**\n"
            f"Nobody currently holds leadership access for this alliance, so this channel is dormant. Anyone in "
            f"[{tag}] can claim R5 with `/request-rank` (staff approval required)."
        )

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT leadership_status_msg_id FROM alliances WHERE tag = ?", (tag,))
        row = await cur.fetchone()

    msg = None
    if row and row[0]:
        try:
            msg = await leadership_chat.fetch_message(row[0])
        except (discord.NotFound, discord.Forbidden):
            msg = None

    if msg:
        try:
            await msg.edit(content=status_text)
        except discord.HTTPException:
            pass
    else:
        try:
            msg = await leadership_chat.send(status_text)
            try:
                await msg.pin()
            except discord.HTTPException:
                pass
            async with db_connect() as conn:
                cur = await conn.cursor()
                await cur.execute("UPDATE alliances SET leadership_status_msg_id = ? WHERE tag = ?", (msg.id, tag))
                await conn.commit()
        except discord.HTTPException:
            pass


async def approve_alliance(guild, tag: str, approver_label: str) -> bool:
    """Releases every member of [tag] from the Drunk Tank and marks the
    alliance approved. Shared by /approve-tag, the auto-approval timer, and
    the Approve button on the #logs embed. Idempotent — a second call for an
    already-approved (or deleted) tag is a safe no-op, returning False."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT status FROM alliances WHERE tag = ?", (tag,))
        row = await cur.fetchone()
        if not row or row[0] == "approved":
            return False
        await cur.execute("UPDATE alliances SET status = 'approved', auto_approve_at = NULL WHERE tag = ?", (tag,))
        await conn.commit()

    tag_role = discord.utils.get(guild.roles, name=tag)
    drunk_tank_role = discord.utils.get(guild.roles, name=ROLE_DRUNK_TANK)
    approved_members = []
    if tag_role and drunk_tank_role:
        for member in list(tag_role.members):
            if drunk_tank_role in member.roles:
                try:
                    await member.remove_roles(drunk_tank_role)
                    approved_members.append(member)
                except discord.Forbidden:
                    pass

    await log_event(
        guild,
        f"🔓 **ALLIANCE APPROVED**\nTag: [{tag}]\nApproved by: {approver_label}\n"
        f"Members released from Drunk Tank: {len(approved_members)}"
    )

    # Announce it in the alliance's own lobby, scoped to that alliance's category
    # specifically — every alliance has a channel literally named "💬-lobby",
    # so we look inside "[TAG] CHATS" rather than guild-wide.
    chat_category = discord.utils.get(guild.categories, name=f"{tag} CHATS")
    lobby_ch = discord.utils.get(chat_category.text_channels, name="💬-lobby") if chat_category else None
    if lobby_ch and approved_members:
        mentions = " ".join(m.mention for m in approved_members)
        try:
            await lobby_ch.send(f"🎉 **APPROVED!** {mentions} — you're clear for full access. Welcome to the precinct, officially.")
        except discord.HTTPException:
            pass

    for member in approved_members:
        try:
            await member.send(f"✅ Your alliance **[{tag}]** has been approved by {approver_label}! You now have full access to your alliance's live channels.")
        except discord.Forbidden:
            pass

    return True


async def schedule_alliance_auto_approval(guild, tag: str, delay_seconds: float):
    print(f"[TIMER STARTED] [{tag}] will auto-approve in {int(delay_seconds)} seconds if untouched.")
    await asyncio.sleep(max(0, delay_seconds))
    await approve_alliance(guild, tag, approver_label=f"⏰ Auto-Approval ({int(delay_seconds // 60)}-minute timer expired)")


async def reschedule_pending_alliance_approvals(guild):
    """Startup recovery: resumes any alliance auto-approval timers lost to a restart."""
    now = datetime.now()
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT tag, auto_approve_at FROM alliances WHERE status = 'pending' AND auto_approve_at IS NOT NULL")
        rows = await cur.fetchall()

    restored = 0
    for tag, approve_at_str in rows:
        try:
            approve_at = datetime.fromisoformat(approve_at_str)
        except (TypeError, ValueError):
            continue
        remaining = (approve_at - now).total_seconds()
        if remaining <= 0:
            await approve_alliance(guild, tag, approver_label="⏰ Auto-Approval (timer expired while I was offline)")
        else:
            bot.loop.create_task(schedule_alliance_auto_approval(guild, tag, remaining))
            restored += 1

    if restored:
        print(f"[SYSTEM] Rescheduled {restored} pending alliance-approval timer(s) that survived a restart.")


# ------------------------------------------------------------
#  SECURITY DIAGNOSTICS — runs on every startup and every guild re-join.
#  Golden rule in code form: we only ever touch something here if leaving
#  it alone would leave a real hole in the moderation/quarantine system.
# ------------------------------------------------------------
SIREN_GIF_URL = "https://media4.giphy.com/media/v1.Y2lkPTc5MGI3NjExaXQ3a28xOTE3dW83NGphMjJ0OXFtdjh6NHdobDJ3M2FqdTg1cjN0MCZlcD12MV9naWZzX3NlYXJjaCZjdD1n/gjCGgYosRTSY9sMHKl/giphy.gif"


DEFAULT_ROLE_NAMES = [ROLE_MILLIE, ROLE_STITCH, ROLE_CHROME, ROLE_SILENT, ROLE_DICTATOR, ROLE_SENATOR, ROLE_JUDGE,
                      ROLE_MEMBER, ROLE_INNOVATOR, ROLE_DRUNK_TANK, ROLE_PRISONER, ROLE_TIMEOUT]


async def check_role_hierarchy_and_alert(guild):
    """Detects role-order drift (someone dragged a role manually) or a
    deleted default role — but never silently fixes either. Just reports it
    to #logs with a one-click button, per the golden rule."""
    expected = await compute_expected_role_order(guild)
    positions = [r.position for r in expected]
    is_sorted_desc = all(positions[i] > positions[i + 1] for i in range(len(positions) - 1))

    checked_names = DEFAULT_ROLE_NAMES + [role_name_for_server(n) for n in await get_managed_servers(guild.id)]
    missing = [name for name in checked_names if not discord.utils.get(guild.roles, name=name)]

    if is_sorted_desc and not missing:
        return  # all clear, nothing to report

    lines = []
    if not is_sorted_desc:
        lines.append("🔀 The role hierarchy isn't in the expected order — someone likely dragged a role manually.")
    if missing:
        lines.append(f"🕳️ Missing role(s): {', '.join(f'`{n}`' for n in missing)}")
    lines.append("\nNothing was changed automatically — click below if you'd like me to fix it.")

    embed = discord.Embed(
        title="🔧 ROLE HIERARCHY CHECK",
        description="\n".join(lines),
        color=discord.Color.orange(),
        timestamp=datetime.now()
    )
    log_channel = discord.utils.get(guild.channels, name="logs")
    if log_channel:
        try:
            await log_channel.send(embed=embed, view=RoleOrderFixView())
        except discord.HTTPException:
            pass


async def check_critical_security(guild):
    """Checks a short, deliberately narrow list of things that would actually
    break security/moderation if wrong — NOT a general permissions audit.
    Returns (repairs, dangers): quiet fixes vs. siren-worthy exposures."""
    repairs = []
    dangers = []

    # ✨ Millie is the one deliberate exception to "never touch customizations" —
    # she's always this exact pink, no matter what anyone does to her.
    millie_role = discord.utils.get(guild.roles, name=ROLE_MILLIE)
    if millie_role and millie_role.color != MILLIE_COLOR:
        try:
            await millie_role.edit(color=MILLIE_COLOR, reason="Millie is always this pink. Always.")
            repairs.append("✨ Someone changed Millie's color. Unacceptable. Restored her to her one true pink.")
        except discord.Forbidden:
            pass

    # 🧵 Same deal for Stitch — always this exact purple.
    stitch_role = discord.utils.get(guild.roles, name=ROLE_STITCH)
    if stitch_role and stitch_role.color != STITCH_COLOR:
        try:
            await stitch_role.edit(color=STITCH_COLOR, reason="Stitch is always this purple. Always.")
            repairs.append("🧵 Someone changed Stitch's color. Restored to the one true purple.")
        except discord.Forbidden:
            pass

    # 🥈 Same deal for Chrome — always this exact orange.
    chrome_role = discord.utils.get(guild.roles, name=ROLE_CHROME)
    if chrome_role and chrome_role.color != CHROME_COLOR:
        try:
            await chrome_role.edit(color=CHROME_COLOR, reason="Chrome is always this exact orange. Always.")
            repairs.append("🥈 Someone changed Chrome's color. Restored to the one true orange.")
        except discord.Forbidden:
            pass

    # 🔥 Same deal for Silent — always this exact royal blue.
    silent_role = discord.utils.get(guild.roles, name=ROLE_SILENT)
    if silent_role and silent_role.color != SILENT_COLOR:
        try:
            await silent_role.edit(color=SILENT_COLOR, reason="Silent is always this exact royal blue. Always.")
            repairs.append("🔥 Someone changed Silent's color. Restored to the one true royal blue.")
        except discord.Forbidden:
            pass

    # 🔨 Judge gets the same absolute enforcement now too — pink is
    # exclusively Millie's, system-wide, no exceptions, so an already-
    # existing Judge role carrying the old pink gets corrected here.
    judge_role_for_color = discord.utils.get(guild.roles, name=ROLE_JUDGE)
    if judge_role_for_color and judge_role_for_color.color != JUDGE_COLOR:
        try:
            await judge_role_for_color.edit(color=JUDGE_COLOR, reason="Pink is exclusively Millie's — Judge corrected off it.")
            repairs.append("🔨 Judge's color wasn't right (pink is Millie's alone) — corrected.")
        except discord.Forbidden:
            pass

    # 🚔 Member's color too — green is the "not in an alliance yet, which
    # shouldn't happen" signal, so it needs to actually be green to mean
    # anything.
    member_role_for_color = discord.utils.get(guild.roles, name=ROLE_MEMBER)
    if member_role_for_color and member_role_for_color.color != MEMBER_COLOR:
        try:
            await member_role_for_color.edit(color=MEMBER_COLOR, reason="Member is always this exact green. Always.")
            repairs.append("🚔 Member's color wasn't right — corrected to the one true green.")
        except discord.Forbidden:
            pass

    # Millie, Stitch, Chrome, and Silent are all supposed to also hold the
    # actual JUDGE role directly (that's what makes them group under
    # "Judge" in the member list instead of each getting their own
    # heading, since their own role is deliberately non-hoisted). If
    # someone was granted one of these without also getting Judge — say,
    # added by hand through Discord's own UI — fix it here rather than
    # leaving them quietly missing real moderator permissions.
    judge_role = discord.utils.get(guild.roles, name=ROLE_JUDGE)
    if judge_role:
        for honorary_role in (millie_role, stitch_role, chrome_role, silent_role):
            if not honorary_role:
                continue
            for member in honorary_role.members:
                if judge_role not in member.roles:
                    try:
                        await member.add_roles(judge_role, reason=f"Holds {honorary_role.name} — always also gets real Judge status.")
                        repairs.append(f"⚖️ {member.mention} held **{honorary_role.name}** without also holding Judge — fixed.")
                    except discord.Forbidden:
                        pass

    # Server condition, absolute: anyone with access to ANY chat channel
    # must also be in general-chat. Every path that grants a tag, a
    # tag-rank, or Leadership is already supposed to grant Member
    # alongside it directly — this is the ongoing safety net that catches
    # it regardless, including someone added by hand through Discord's own
    # UI, so the rule can't quietly drift out of sync again.
    member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)
    if member_role:
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT tag FROM alliances")
            all_tags = [row[0] for row in await cur.fetchall()]
        alliance_related_roles = []
        for tag in all_tags:
            for role_name in (tag, f"{tag}-R4", f"{tag}-R5", f"{tag}-Leadership"):
                r = discord.utils.get(guild.roles, name=role_name)
                if r:
                    alliance_related_roles.append(r)
        already_fixed = set()
        for role in alliance_related_roles:
            for member in role.members:
                if member.bot or member.id in already_fixed or member_role in member.roles:
                    continue
                try:
                    await member.add_roles(member_role, reason=f"Holds {role.name} — general-chat access is mandatory for anyone in any chat.")
                    repairs.append(f"💬 {member.mention} had alliance channel access without general-chat access — fixed.")
                    already_fixed.add(member.id)
                except discord.Forbidden:
                    pass

    # Same absolute condition, but at the channel level this time: Member's
    # actual view access to #general-chat itself must never be silently
    # lost — whether from a manual permission edit, a mistake, or anything
    # else. Checked and force-corrected every startup, the same way
    # Millie's color is — nobody has to remember to fix this by hand.
    # Talking is optional; being there is not.
    general_chat_ch = discord.utils.get(guild.channels, name="💬-general-chat")
    if general_chat_ch and member_role:
        current_overwrite = general_chat_ch.overwrites_for(member_role)
        if current_overwrite.view_channel is not True:
            try:
                await general_chat_ch.set_permissions(member_role, overwrite=discord.PermissionOverwrite(view_channel=True))
                repairs.append("💬 **#💬-general-chat** wasn't guaranteed-visible to Member — restored. Everyone with Member stays there, always; nobody has to talk.")
            except discord.Forbidden:
                pass

    # 1. The bot's own role should be the highest in the server, or role
    #    sorting and some moderation actions can silently fail.
    if guild.roles and guild.me.top_role.id != guild.roles[-1].id:
        dangers.append(
            f"My own role (**@{guild.me.top_role.name}**) is **not** the highest role in the server. "
            f"Role sorting and some moderation actions may silently fail. "
            f"Please drag my role to the very top under **Server Settings → Roles**."
        )

    # 2. #gateway must stay hidden from @everyone, or the onboarding
    #    quarantine is completely bypassed.
    gateway_ch = discord.utils.get(guild.channels, name="gateway")
    if gateway_ch and gateway_ch.overwrites_for(guild.default_role).view_channel is True:
        await gateway_ch.set_permissions(guild.default_role, view_channel=False, read_messages=False)
        dangers.append("**#gateway** was set visible to @everyone — the onboarding quarantine was wide open. I've hidden it again.")

    # 3. Same idea for the whole Admin-Only category (#gateway + #logs).
    admin_cat = discord.utils.get(guild.categories, name="Admin-Only")
    if admin_cat and admin_cat.overwrites_for(guild.default_role).view_channel is True:
        await admin_cat.set_permissions(guild.default_role, view_channel=False, read_messages=False)
        dangers.append("The **Admin-Only** category was visible to @everyone, exposing #gateway and #logs. I've hidden it again.")

    # 4. Solitary confinement must actually isolate prisoners.
    solitary_ch = discord.utils.get(guild.channels, name="⛓️-solitary-confinement")
    prison_role = discord.utils.get(guild.roles, name=ROLE_PRISONER)
    if solitary_ch and prison_role:
        default_ow = solitary_ch.overwrites_for(guild.default_role)
        prison_ow = solitary_ch.overwrites_for(prison_role)
        if default_ow.view_channel is True:
            await solitary_ch.set_permissions(guild.default_role, view_channel=False)
            dangers.append("**#⛓️-solitary-confinement** was visible to @everyone. I've hidden it again.")
        if not prison_ow.view_channel:
            await solitary_ch.set_permissions(prison_role, view_channel=True, send_messages=True)
            repairs.append("Prisoners couldn't actually see **#⛓️-solitary-confinement** — reapplied their access so the punishment is usable.")

    # 🗄️ Duplicate per-alliance categories (e.g. two "[TAG] CHATS") are never
    # auto-merged or deleted — that's destructive. Just flagged for a human
    # to clean up manually.
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT tag FROM alliances")
        all_tags = [row[0] for row in await cur.fetchall()]

    for tag in all_tags:
        chat_dupes = [c for c in guild.categories if c.name == f"{tag} CHATS"]
        voice_dupes = [c for c in guild.categories if c.name == f"{tag} Voice Channels"]
        if len(chat_dupes) > 1:
            repairs.append(f"⚠️ Found {len(chat_dupes)} duplicate **{tag} CHATS** categories — not touched automatically, please merge/delete the extras by hand.")
        if len(voice_dupes) > 1:
            repairs.append(f"⚠️ Found {len(voice_dupes)} duplicate **{tag} Voice Channels** categories — not touched automatically, please merge/delete the extras by hand.")

    # 👋 The server's actual #general (Discord's own default landing
    # channel — not something we created). If it exists, lock down chatting
    # but leave reactions on so people can still wave hello. We never
    # create this channel ourselves, only lock it down if it's there.
    general_ch = discord.utils.get(guild.channels, name="general")
    if general_ch:
        overwrite = general_ch.overwrites_for(guild.default_role)
        if overwrite.send_messages is not False:
            overwrite.send_messages = False
            overwrite.add_reactions = True
            await general_ch.set_permissions(guild.default_role, overwrite=overwrite)
            repairs.append("👋 Locked down **#general** — everyone can still see it and wave hello with reactions, but not chat there.")
        for staff_role_name in (ROLE_JUDGE, ROLE_STITCH, ROLE_MILLIE, ROLE_SENATOR, ROLE_DICTATOR):
            staff_role = discord.utils.get(guild.roles, name=staff_role_name)
            if staff_role:
                staff_ow = general_ch.overwrites_for(staff_role)
                if staff_ow.send_messages is not True:
                    await general_ch.set_permissions(staff_role, send_messages=True)

    return repairs, dangers


async def check_translation_service():
    """A single real test translation, run once per process — confirms the
    Google Cloud Translation API is actually reachable and correctly
    configured, rather than silently falling back to English forever
    without anyone noticing. Deliberately no retries here: this is a
    configuration check, not a resilience test (translate_text() already
    handles retries for real usage) — one clean attempt tells us whether
    the key/API/billing setup is actually correct.

    Returns (success: bool, detail: str). On failure, `detail` is Google's
    own error message where available, since it's already specific and
    actionable — better than us guessing at the cause."""
    if not GOOGLE_API_KEY:
        return False, "no_key"

    url = f"https://translation.googleapis.com/language/translate/v2?key={GOOGLE_API_KEY}"
    session = await get_http_session()
    try:
        async with session.post(url, data={"q": "test", "target": "es", "format": "text"}, timeout=aiohttp.ClientTimeout(total=10)) as resp:
            if resp.status == 200:
                data = await resp.json()
                translated = data.get("data", {}).get("translations", [{}])[0].get("translatedText")
                if translated:
                    return True, translated
                return False, "The test call succeeded but returned no translated text — unexpected response shape."

            try:
                error_data = await resp.json()
                api_message = error_data.get("error", {}).get("message", "No further detail given.")
            except Exception:
                api_message = await resp.text()
            return False, f"HTTP {resp.status}: {api_message}"
    except asyncio.TimeoutError:
        return False, "Connection error: the request to Google's servers timed out after 10 seconds with no response at all."
    except aiohttp.ClientError as e:
        return False, f"Connection error: {e}"


async def report_translation_failure(guild, detail: str):
    if detail == "no_key":
        await notify_owner(
            guild, "🌐 Translation isn't configured",
            "No `GOOGLE_API_KEY` is set, so I can't translate anything — the 🌐 reaction, `/language`, and all "
            "non-English onboarding will silently show English instead.\n\n"
            "**To fix:** get a Google Cloud Translation API key and add `GOOGLE_API_KEY=...` to your `.env` file.",
            color=discord.Color.orange()
        )
        return

    if detail.startswith("Connection error:"):
        # Never even got a response back from Google — this is a network
        # reachability problem, not an API-key/billing/permissions problem.
        # Those two failure modes need completely different fixes, so
        # they get completely different messages.
        explanation = (
            "This means the request never got a response from Google's servers at all — different from a "
            "rejected key or disabled API, which would show up as an HTTP error instead. This usually points to: "
            "no internet access on the machine running the bot right now, a firewall or antivirus blocking "
            "outbound HTTPS to `translation.googleapis.com`, a proxy that needs configuring, or a temporary "
            "network blip. Worth trying: open a browser on that same machine and confirm you can reach any "
            "external site at all, then restart the bot once connectivity's confirmed."
        )
    else:
        explanation = (
            "This is almost always one of: the Cloud Translation API isn't enabled on your Google Cloud project, "
            "billing isn't enabled on that project, or the API key itself is invalid or restricted."
        )

    await notify_owner(
        guild, "🌐 Translation isn't working",
        f"I ran a test translation at startup and it failed.\n\n"
        f"**Details:** {detail}\n\n"
        f"{explanation} Until this is fixed, translation will silently fall back to English everywhere — "
        f"nobody sees an error, they just never get translated.",
        color=discord.Color.red()
    )


async def notify_owner(guild, title: str, description: str, color=discord.Color.red()):
    """DMs the actual server owner directly — not just staff via #logs —
    reserved for things that are genuinely 'going wrong', not routine
    moderation noise."""
    if not guild.owner:
        return
    embed = discord.Embed(title=title, description=description, color=color, timestamp=datetime.now())
    embed.set_footer(text=f"📡 {guild.name} — Direct from Robocop")
    try:
        await guild.owner.send(embed=embed)
    except discord.Forbidden:
        pass


class ConfigFixView(discord.ui.View):
    """Posted to #logs alongside a detected config problem — one click
    resets that specific setting back to its safe default. Not registered
    as a persistent view (a restart loses it), but that's an acceptable
    trade-off here: check_config_health() re-runs and re-posts a fresh
    working button on every startup regardless, so nothing stays silently
    broken for long even if this exact button goes stale."""
    def __init__(self, key: str, safe_default):
        super().__init__(timeout=None)
        self.key = key
        self.safe_default = safe_default

    @discord.ui.button(label="Reset to Default", style=discord.ButtonStyle.danger, emoji="🔧")
    async def fix(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not is_staff_member(interaction.user):
            await interaction.response.send_message("🚫 Staff only.", ephemeral=True)
            return
        await set_guild_setting(interaction.guild.id, f"config:{self.key}", str(self.safe_default))
        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(content=f"✅ Fixed by {interaction.user.mention} — reset to `{self.safe_default}`.", embed=None, view=self)


async def check_config_health(guild):
    """Validates every live-configurable setting someone's actually
    touched (untouched ones are just using their default, nothing to
    check) against its real constraints — type, numeric range, and for
    timezone specifically, whether it's an IANA name ZoneInfo can
    actually resolve. Posts a #logs entry with a one-click fix for
    anything wrong, rather than letting a bad stored value silently
    degrade behavior until someone notices the hard way."""
    problems = []
    for key, meta in CONFIGURABLE_SETTINGS.items():
        raw = await get_guild_setting(guild.id, f"config:{key}")
        if raw is None:
            continue

        try:
            value = raw if meta["type"] is str else meta["type"](raw)
        except (ValueError, TypeError):
            problems.append((key, f"Stored value `{raw}` isn't a valid {meta['type'].__name__}.", meta["default"]))
            continue

        if meta["type"] is not str:
            lo, hi = meta.get("min"), meta.get("max")
            if (lo is not None and value < lo) or (hi is not None and value > hi):
                problems.append((key, f"Stored value `{value}` is outside the valid range ({lo}-{hi}).", meta["default"]))
        elif key == "timezone":
            try:
                ZoneInfo(value)
            except Exception:
                problems.append((key, f"`{value}` isn't a timezone name I can resolve (expects an IANA name like `America/Los_Angeles`).", meta["default"]))

    if not problems:
        return

    log_channel = discord.utils.get(guild.channels, name="logs")
    if not log_channel:
        return
    for key, issue, safe_default in problems:
        embed = discord.Embed(
            title=f"⚠️ CONFIG ISSUE: {CONFIGURABLE_SETTINGS[key]['label']}",
            description=f"{issue}\n\nI'm using the default (`{safe_default}`) until this is fixed — nothing's broken right now, but the stored value should be corrected.",
            color=discord.Color.orange()
        )
        try:
            await log_channel.send(embed=embed, view=ConfigFixView(key, safe_default))
        except discord.HTTPException:
            pass


class SupersededRoleFixView(discord.ui.View):
    """Posted to #logs once a legacy role flagged during an adoption/
    migration has zero remaining holders — everyone who had it either got
    mapped to its replacement or left. Not auto-deleted; this is
    deliberately a suggestion with a button, not an automatic cleanup, so
    nothing disappears without a human confirming it."""
    def __init__(self, role_name: str):
        super().__init__(timeout=None)
        self.role_name = role_name

    @discord.ui.button(label="Delete This Role", style=discord.ButtonStyle.danger, emoji="🗑️")
    async def delete(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not is_senior_staff_member(interaction.user):
            await interaction.response.send_message("🚫 Senator+ only — this is a real deletion.", ephemeral=True)
            return
        await interaction.response.defer()
        role = discord.utils.get(interaction.guild.roles, name=self.role_name)
        if role:
            try:
                await role.delete(reason=f"Superseded legacy role, deleted by {interaction.user}.")
            except discord.Forbidden:
                await interaction.followup.send("❌ I don't have permission to delete that role.", ephemeral=True)
                return
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("UPDATE legacy_roles_tracked SET resolved = 1 WHERE guild_id = ? AND role_name = ?", (interaction.guild.id, self.role_name))
            await conn.commit()
        for item in self.children:
            item.disabled = True
        await interaction.edit_original_response(content=f"✅ Deleted by {interaction.user.mention}.", embed=None, view=self)

    @discord.ui.button(label="Keep It (Stop Asking)", style=discord.ButtonStyle.secondary)
    async def dismiss(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not is_senior_staff_member(interaction.user):
            await interaction.response.send_message("🚫 Senator+ only.", ephemeral=True)
            return
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("UPDATE legacy_roles_tracked SET resolved = 1 WHERE guild_id = ? AND role_name = ?", (interaction.guild.id, self.role_name))
            await conn.commit()
        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(content=f"✅ Got it — {interaction.user.mention} chose to keep this role. Won't ask again.", embed=None, view=self)


async def check_superseded_roles(guild):
    """For every legacy role flagged during an adoption/migration and not
    yet resolved, checks whether it's now down to zero holders — meaning
    everyone who had it got mapped to its replacement, or left. If so,
    posts a friendly #logs reminder with a one-click delete, rather than
    it just sitting there indefinitely as clutter nobody remembers the
    reason for."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT role_name, mapped_to FROM legacy_roles_tracked WHERE guild_id = ? AND resolved = 0", (guild.id,))
        tracked = await cur.fetchall()
    if not tracked:
        return

    log_channel = discord.utils.get(guild.channels, name="logs")
    if not log_channel:
        return

    for role_name, mapped_to in tracked:
        role = discord.utils.get(guild.roles, name=role_name)
        if not role:
            # The role's already gone — someone deleted it manually. Mark it resolved so we stop checking.
            async with db_connect() as conn:
                cur = await conn.cursor()
                await cur.execute("UPDATE legacy_roles_tracked SET resolved = 1 WHERE guild_id = ? AND role_name = ?", (guild.id, role_name))
                await conn.commit()
            continue

        if len(role.members) == 0:
            embed = discord.Embed(
                title=f"🧹 LEGACY ROLE READY FOR CLEANUP: {role_name}",
                description=(
                    f"This role was flagged during a migration (mapped to **{mapped_to}**) and now has **zero** "
                    f"remaining holders — everyone's been moved over or has left. It's safe to delete if you're "
                    f"ready, or keep it around if you'd rather."
                ),
                color=discord.Color.blue()
            )
            try:
                await log_channel.send(embed=embed, view=SupersededRoleFixView(role_name))
            except discord.HTTPException:
                pass


async def check_audit_log_permission(guild):
    """Without 'View Audit Log', #visitors can't tell the difference
    between someone being kicked/banned and just leaving on their own —
    everything would show as 'left voluntarily' even when it wasn't.
    Checked every startup; DMs the owner directly since it's a one-click
    fix they need to actually know about."""
    if guild.me.guild_permissions.view_audit_log:
        return
    await notify_owner(
        guild, "🔍 I need one more permission",
        "I don't currently have **View Audit Log** permission in this server. Without it, #visitors can't tell "
        "whether someone was kicked, banned, or just left on their own — everything will show as 'left "
        "voluntarily' even when it wasn't.\n\n"
        "**To fix:** Server Settings → Roles → find my role → enable **View Audit Log**.",
        color=discord.Color.orange()
    )


async def send_siren_alert(guild, dangers: list):
    """🚨🚨🚨 The big, hard-to-miss alert. Pings the top brass and flashes an animated siren."""
    dictator_role = discord.utils.get(guild.roles, name=ROLE_DICTATOR)
    senator_role = discord.utils.get(guild.roles, name=ROLE_SENATOR)
    ping_targets = " ".join(r.mention for r in (dictator_role, senator_role) if r)

    embed = discord.Embed(
        title="🚨🚨🚨 SECURITY ALERT — ACTION MAY BE REQUIRED 🚨🚨🚨",
        description="\n\n".join(f"⚠️ {d}" for d in dangers),
        color=discord.Color.red(),
        timestamp=datetime.now()
    )
    embed.set_image(url=SIREN_GIF_URL)
    embed.set_footer(text="RoboCop Security Diagnostic — wee-oo, wee-oo, wee-oo")

    log_channel = discord.utils.get(guild.channels, name="logs")
    if log_channel:
        try:
            await log_channel.send(content=ping_targets or None, embed=embed)
        except discord.HTTPException as e:
            print(f"[ERROR] Failed to post siren alert: {e}")

    await notify_owner(
        guild, "🚨 Something needs your attention",
        "A security check just flagged something serious in your server:\n\n" + "\n\n".join(f"⚠️ {d}" for d in dangers)
    )


async def post_latest_version_report(guild, repairs: list):
    """#latest-version is specifically for reviewing what changed/broke
    after a new version gets uploaded — only posts when there's actually
    something to review, so it stays a signal, not routine noise."""
    if not repairs:
        return
    version_channel = discord.utils.get(guild.channels, name="latest-version")
    if not version_channel:
        return
    embed = discord.Embed(
        title="🆕 INCONSISTENCIES FOUND THIS STARTUP",
        description="\n".join(f"• {r}" for r in repairs),
        color=discord.Color.orange(),
        timestamp=datetime.now()
    )
    embed.set_footer(text=f"Instance {INSTANCE_ID}")
    try:
        await version_channel.send(embed=embed)
    except discord.HTTPException:
        pass


async def post_startup_report(guild, repairs: list, trigger_reason: str, ungoverned_members: list = None):
    """Golden-rule logging: every single startup or re-join gets a report,
    even a completely uneventful one."""
    ungoverned_members = ungoverned_members or []
    log_channel = discord.utils.get(guild.channels, name="logs")
    if not log_channel:
        return

    if repairs:
        body = "\n".join(f"• {r}" for r in repairs)
        color = discord.Color.orange()
    else:
        body = "✅ Everything checked out. All tracked roles, categories, and channels are present, and I didn't touch a single one of your customizations."
        color = discord.Color.green()

    embed = discord.Embed(
        title=f"🩺 STARTUP DIAGNOSTIC — {trigger_reason}",
        description=body,
        color=color,
        timestamp=datetime.now()
    )

    view = None
    if ungoverned_members:
        shown = ungoverned_members[:15]
        listing = "\n".join(f"• {m.mention} ({m.display_name})" for m in shown)
        if len(ungoverned_members) > 15:
            listing += f"\n...and {len(ungoverned_members) - 15} more."
        embed.add_field(
            name=f"👥 {len(ungoverned_members)} Unregistered Member(s)",
            value=(
                f"{listing}\n\n"
                f"Nothing was changed automatically; each was sent a one-time DM pointing them at `/register`. "
                f"Anyone whose nickname already matched our format also got their roles granted early — click "
                f"below to finish the rest for everyone eligible."
            ),
            inline=False
        )
        view = BulkAutoRegisterView()

    embed.set_footer(text="Golden rule: I never touch what you've customized unless it's required to fix something broken.")
    try:
        await log_channel.send(embed=embed, view=view)
    except discord.HTTPException as e:
        print(f"[ERROR] Failed to post startup diagnostic: {e}")


async def post_auto_registration_flag(guild, member, name: str, tag: str, servers: list):
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("INSERT OR REPLACE INTO auto_registration_flags (user_id, resolved) VALUES (?, 0)", (member.id,))
        await conn.commit()

    embed = discord.Embed(
        title="🪪 EXISTING MEMBER, MATCHING NICKNAME DETECTED",
        description=(
            f"{member.mention}'s current nickname already matches our format, so I've auto-granted the "
            f"matching roles. They've been asked to run `/register` themselves — if they never do, "
            f"use the button below to finish their registration for them."
        ),
        color=discord.Color.blurple(),
        timestamp=datetime.now()
    )
    embed.add_field(name="Parsed Name", value=name, inline=True)
    embed.add_field(name="Parsed Tag", value=f"[{tag}]", inline=True)
    embed.add_field(name="Parsed Server(s)", value="/".join(servers), inline=True)

    log_channel = discord.utils.get(guild.channels, name="logs")
    if log_channel:
        try:
            await log_channel.send(embed=embed, view=AutoRegisterView(member.id))
        except discord.HTTPException:
            pass


async def finalize_registration_from_nickname(guild, member, name: str, tag: str, servers: list):
    """Shared by the single-member AutoRegisterView button and the bulk
    auto-register button: grants roles, completes the DB record, marks any
    outstanding auto_registration_flags row resolved, and DMs the member."""
    await grant_roles_from_nickname(guild, member, tag, servers)

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute(
            "UPDATE users SET in_game_name = ?, alliance_tag = ?, rank_designation = COALESCE(rank_designation, 'Member'), server_number = ? WHERE user_id = ?",
            (name, tag, ",".join(servers), member.id)
        )
        if cur.rowcount == 0:
            await cur.execute(
                "INSERT INTO users (user_id, original_username, in_game_name, alliance_tag, rank_designation, server_number) VALUES (?, ?, ?, ?, 'Member', ?)",
                (member.id, member.name, name, tag, ",".join(servers))
            )
        await cur.execute("UPDATE auto_registration_flags SET resolved = 1 WHERE user_id = ?", (member.id,))
        await conn.commit()

    try:
        await member.send(
            f"✅ Your registration in **{guild.name}** was completed by staff based on your existing nickname. Welcome aboard, officially!\n\n"
            + await tf(NAME_CHANGE_REMINDER, member.id, abilities=abilities_mention(guild))
        )
    except discord.Forbidden:
        pass


async def find_ungoverned_members(guild) -> list:
    """Every non-bot member who isn't fully registered and doesn't already
    hold Member. Shared by the startup audit and the bulk auto-register
    button, so both always agree on exactly who's affected."""
    member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT user_id, in_game_name, alliance_tag, rank_designation, server_number FROM users")
        rows = {row[0]: row[1:] for row in await cur.fetchall()}

    ungoverned = []
    for m in guild.members:
        if m.bot:
            continue
        row = rows.get(m.id)
        fully_registered = row and row[0] and row[1] and row[2] and row[3]
        has_member_role = member_role in m.roles if member_role else False
        if not fully_registered and not has_member_role:
            ungoverned.append(m)
    return ungoverned


# ------------------------------------------------------------
#  MISSED-JOINER CATCH-UP (8.7) — Discord only announces a join live. If
#  someone joins while RoboCop is offline (a restart, an update, a move to
#  another machine), on_member_join never fires for them, and they'd sit
#  in limbo with no #gateway welcome. Every startup, anyone who joined
#  recently, isn't registered, and never actually started onboarding gets
#  the normal onboarding run for them — exactly as if they'd just arrived.
#  "Never started" = no language chosen yet: the language step always
#  records a choice (or defaults to English), so anyone who got even one
#  step in is left to the existing paused-registration handling instead,
#  and nobody gets restarted over and over on every reboot.
# ------------------------------------------------------------
MISSED_JOIN_LOOKBACK_HOURS = 72     # older unregistered members just get the gentle /register DM, as before
MISSED_JOIN_MAX_PER_STARTUP = 10    # more than this looks like a raid, not a restart — flag it for a human instead
MISSED_JOIN_STAGGER_SECONDS = 8     # spaced out so a handful of catch-ups never trip the raid alarm
_startup_catchup_ids = set()        # members being onboarded by the catch-up — the audit leaves them alone


async def find_missed_joiners(guild) -> list:
    member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)
    cutoff = datetime.now(timezone.utc) - timedelta(hours=MISSED_JOIN_LOOKBACK_HOURS)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT user_id, in_game_name, alliance_tag, rank_designation, server_number, language_selected FROM users")
        rows = {r[0]: r[1:] for r in await cur.fetchall()}

    missed = []
    for m in guild.members:
        if m.bot or m.id in _onboarding_in_progress or m.id in _resume_tasks:
            continue
        if member_role and member_role in m.roles:
            continue
        if is_staff_member(m):
            continue
        if not m.joined_at or m.joined_at < cutoff:
            continue
        row = rows.get(m.id)
        if row and all(row[:4]):
            continue  # fully registered
        if row and row[4]:
            continue  # already started onboarding — the paused-registration handler covers them
        missed.append(m)
    return sorted(missed, key=lambda m: m.joined_at)


async def _run_missed_joiner(member, delay: float):
    await asyncio.sleep(delay)
    try:
        m = member.guild.get_member(member.id)
        if m is None or m.id in _onboarding_in_progress:
            return
        onboard_console(m, "🕳️ joined while I was offline — starting their onboarding now")
        await log_visitor_entry(m)
        await run_onboarding_safe(m)
    finally:
        _startup_catchup_ids.discard(member.id)


async def catch_up_missed_joiners(guild) -> list:
    """Starts onboarding for everyone who joined while RoboCop was offline.
    Returns the list of members it picked up (for the startup report)."""
    missed = await find_missed_joiners(guild)
    if not missed:
        return []

    if len(missed) > MISSED_JOIN_MAX_PER_STARTUP:
        listing = "\n".join(f"• {m.mention} ({m.display_name})" for m in missed[:15])
        await log_event(
            guild,
            f"🕳️ **{len(missed)} PEOPLE JOINED WHILE I WAS OFFLINE** — that's more than {MISSED_JOIN_MAX_PER_STARTUP}, which looks "
            f"more like a raid than a restart, so I did NOT start onboarding for them automatically. They've each been sent "
            f"the usual `/register` DM instead. Take a look:\n{listing}"
        )
        await notify_owner(guild, "🕳️ Lots of people joined while I was offline",
                           f"{len(missed)} unregistered people joined while RoboCop was offline. Onboarding wasn't started "
                           f"automatically (possible raid) — details in #logs.", color=discord.Color.orange())
        return []

    for i, m in enumerate(missed):
        _startup_catchup_ids.add(m.id)
        bot.loop.create_task(_run_missed_joiner(m, i * MISSED_JOIN_STAGGER_SECONDS))

    listing = "\n".join(f"• {m.mention} ({m.display_name}) — joined <t:{int(m.joined_at.timestamp())}:R>" for m in missed)
    await log_event(
        guild,
        f"🕳️ **CAUGHT {len(missed)} MISSED JOINER(S)** — they arrived while I was offline, so Discord never told me. "
        f"Starting the normal #gateway onboarding for them now, as if they'd just walked in:\n{listing}"
    )
    return missed


async def audit_existing_members(guild) -> list:
    """Finds real members who exist in the server but have no RoboCop
    registration — e.g. because RoboCop was just added to a server that
    already had people in it. Never fully onboards them automatically (that
    still needs their own answers), but if their nickname already matches
    our format, grants the matching roles right away as a convenience and
    flags it in #logs with a one-click finish button. Either way, everyone
    gets a one-time DM pointing at /register, tracked so we never re-nag.
    Returns the full list of ungoverned members (not just a count)."""
    ungoverned = await find_ungoverned_members(guild)

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT tag FROM alliances")
        approved_tags = {row[0] for row in await cur.fetchall()}
        await cur.execute("SELECT user_id, registration_prompted FROM users")
        prompted_map = {row[0]: row[1] for row in await cur.fetchall()}

    for m in ungoverned:
        if m.id in _startup_catchup_ids:
            continue  # being onboarded right now by the missed-joiner catch-up — no /register DM needed
        already_prompted = prompted_map.get(m.id, 0)
        if already_prompted:
            continue

        async with db_connect() as conn:
            cur = await conn.cursor()
            if m.id in prompted_map:
                await cur.execute("UPDATE users SET registration_prompted = 1 WHERE user_id = ?", (m.id,))
            else:
                await cur.execute("INSERT INTO users (user_id, original_username, registration_prompted) VALUES (?, ?, 1)", (m.id, m.name))
            await conn.commit()

        parsed = parse_formatted_nickname(m.display_name)
        parsed_key = resolve_alliance_key(parsed[1], parsed[2], approved_tags) if parsed else None
        if parsed and parsed_key:
            name, _shown_tag, servers = parsed
            tag = parsed_key
            await grant_roles_from_nickname(guild, m, tag, servers)
            await post_auto_registration_flag(guild, m, name, tag, servers)
            dm_text = (
                f"👋 Hey — I'm RoboCop, new to **{guild.name}**. Your nickname already matched **[{tag_display(tag)}]**, "
                f"so I've granted you the matching roles now — you're not stuck in limbo. Please still run "
                f"`/register` in #gateway when you get a chance to finish setting up properly."
            )
        else:
            dm_text = (
                f"👋 Hey — I'm RoboCop, new to **{guild.name}**. Looks like you haven't registered with me yet. "
                f"Head to #gateway and run `/register` whenever you get a chance — takes a couple of minutes."
            )

        try:
            await m.send(dm_text)
        except discord.Forbidden:
            pass

    return [m for m in ungoverned if m.id not in _startup_catchup_ids]


# ------------------------------------------------------------
#  STARTUP RECONCILIATION — the live Discord server is the source of
#  truth; the database is a rebuildable cache of it. If the DB is wiped
#  (or was never populated for a server RoboCop was dropped into), this
#  inventories what's actually there — alliance roles + categories,
#  members' tag/server/rank roles, formatted nicknames, Innovator badges —
#  and rebuilds the records from it, so nothing has to be re-onboarded
#  and every command works against a complete picture from the first
#  boot. Fills gaps only: never overwrites a value the DB already has.
# ------------------------------------------------------------
TAG_ROLE_RE = re.compile(r"^[A-Z]{2,4}(·\d+)?$")  # plain tag, or a server-scoped key like HAL·121


def looks_like_alliance_tag_role(guild, role) -> bool:
    """A 2-4 uppercase-letter role is only treated as an alliance if it has
    corroborating structure (its CHATS category or a rank sibling role) —
    otherwise an unrelated short role name like 'VIP' would be adopted as
    an alliance by mistake."""
    if not TAG_ROLE_RE.match(role.name):
        return False
    tag = role.name
    return bool(
        discord.utils.get(guild.categories, name=f"{tag} CHATS")
        or discord.utils.get(guild.roles, name=f"{tag}-R5")
        or discord.utils.get(guild.roles, name=f"{tag}-R4")
    )


SERVER_PATROL_ROLE_RE = re.compile(r"^🗺️ Server (\d+) Patrol$")


async def recover_managed_servers_setting(guild) -> bool:
    """If the guild's managed-servers setting is gone (fresh/wiped DB), read
    it back off the '🗺️ Server N Patrol' roles that are still on the server.
    Must run BEFORE build_global_infrastructure and the inventory, or a
    wiped DB would silently fall back to the 21,121 default and every
    member of any other server would come back with a half record."""
    if await get_guild_setting(guild.id, "managed_servers") is not None:
        return False
    found = sorted({m.group(1) for r in guild.roles if (m := SERVER_PATROL_ROLE_RE.match(r.name))}, key=int)
    if not found:
        return False
    await set_guild_setting(guild.id, "managed_servers", ",".join(found))
    await log_event(guild, f"🗂️ **STARTUP INVENTORY** — managed-servers setting was missing; recovered **{', '.join(found)}** from the live server roles.")
    return True


async def reconcile_database_from_server(guild) -> list:
    repairs = []
    await recover_managed_servers_setting(guild)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT tag FROM alliances")
        known_tags = {r[0] for r in await cur.fetchall()}
        await cur.execute("SELECT user_id FROM innovators")
        known_innovators = {r[0] for r in await cur.fetchall()}
        await cur.execute("SELECT user_id, in_game_name, alliance_tag, rank_designation, server_number FROM users")
        user_rows = {r[0]: r[1:] for r in await cur.fetchall()}
        await cur.execute("SELECT DISTINCT user_id FROM user_nicknames")
        users_with_nick_rows = {r[0] for r in await cur.fetchall()}
        await cur.execute("SELECT user_id FROM users WHERE prison_until IS NOT NULL")
        sentenced = {r[0] for r in await cur.fetchall()}

    # 1. Alliances that exist on the server but not in the DB. A recovered
    #    alliance is marked approved — and since 'approved' means 'not in
    #    the Drunk Tank', any of its members still wearing that role get
    #    released now, instead of sitting there with no timer to free them.
    live_tags = {r.name for r in guild.roles if looks_like_alliance_tag_role(guild, r)}
    drunk_tank_role = discord.utils.get(guild.roles, name=ROLE_DRUNK_TANK)
    for tag in sorted(live_tags - known_tags):
        role = discord.utils.get(guild.roles, name=tag)
        color_hex = str(role.color.value) if role and role.color.value else None
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute(
                "INSERT OR IGNORE INTO alliances (tag, creator_id, status, color_hex, created_at) VALUES (?, NULL, 'approved', ?, ?)",
                (tag, color_hex, datetime.now().isoformat())
            )
            await conn.commit()
        released = 0
        if role and drunk_tank_role:
            for m in list(role.members):
                if drunk_tank_role in m.roles:
                    try:
                        await m.remove_roles(drunk_tank_role, reason="Startup inventory — alliance recovered as approved")
                        released += 1
                    except discord.HTTPException:
                        pass
        repairs.append(f"🏢 Recovered alliance **[{tag}]** from its live role/channels (marked approved" + (f", released {released} from Drunk Tank" if released else "") + ")")
    all_tags = known_tags | live_tags

    # 1b. Prisoners with no sentence on record would never be released — flag them.
    prison_role = discord.utils.get(guild.roles, name=ROLE_PRISONER)
    if prison_role:
        for m in prison_role.members:
            if not m.bot and m.id not in sentenced:
                repairs.append(f"🔒 {m.mention} holds the Prisoner role but has **no sentence on record** — nothing will auto-release them. Run `/pardon {m.id}` if that's not intended.")

    # 2. Innovator badge holders missing from the table.
    innovator_role = discord.utils.get(guild.roles, name=ROLE_INNOVATOR)
    if innovator_role:
        for m in innovator_role.members:
            if m.bot or m.id in known_innovators:
                continue
            async with db_connect() as conn:
                cur = await conn.cursor()
                await cur.execute("INSERT OR IGNORE INTO innovators (user_id, username) VALUES (?, ?)", (m.id, str(m)))
                await conn.commit()
            repairs.append(f"🌟 Recovered Innovator record for {m.mention}")

    # 3. Member records, from roles first (authoritative) and nickname second.
    #    Work out every change in memory first, then write them ALL in one
    #    transaction — one commit instead of one per member. Fewer commits
    #    means far fewer journal/WAL write cycles, and if the write fails,
    #    it fails once, cleanly, with nothing half-applied.
    managed = await get_managed_servers(guild.id)
    member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)
    pending = []  # (member, existing_row_or_None, name, tag, rank, servers)
    for m in guild.members:
        if m.bot:
            continue
        role_names = {r.name for r in m.roles}
        held_tags = [t for t in all_tags if t in role_names]
        parsed = parse_formatted_nickname(m.display_name)
        tag = held_tags[0] if held_tags else (resolve_alliance_key(parsed[1], parsed[2], all_tags) if parsed else None)
        if not tag:
            continue  # nothing to recover from — the ungoverned-member audit handles these
        held_servers = [n for n in managed if role_name_for_server(n) in role_names]
        servers = held_servers or ([s for s in parsed[2] if s in managed] if parsed else [])
        name = (parsed[0] if parsed else strip_nickname_decorations(m.display_name)) or m.name
        rank = "R5" if f"{tag}-R5" in role_names else ("R4" if f"{tag}-R4" in role_names else "Member")
        existing = user_rows.get(m.id)
        if existing and all(existing):
            continue  # fully registered already — leave it alone
        pending.append((m, existing, name, tag, rank, servers))

    if pending:
        async with db_connect() as conn:
            cur = await conn.cursor()
            for m, existing, name, tag, rank, servers in pending:
                server_field = ",".join(servers) or None
                if existing is None:
                    await cur.execute(
                        "INSERT INTO users (user_id, original_username, in_game_name, alliance_tag, rank_designation, server_number, "
                        "language_selected, invite_check_passed, test_disclaimer_ack, registration_prompted, invite_strikes, lifetime_invite_fails) "
                        "VALUES (?, ?, ?, ?, ?, ?, 1, 1, 1, 1, 0, 0)",
                        (m.id, m.name, name, tag, rank, server_field)
                    )
                else:
                    await cur.execute(
                        "UPDATE users SET in_game_name = COALESCE(in_game_name, ?), alliance_tag = COALESCE(alliance_tag, ?), "
                        "rank_designation = COALESCE(rank_designation, ?), server_number = COALESCE(server_number, ?), "
                        "language_selected = 1, invite_check_passed = 1, test_disclaimer_ack = 1, registration_prompted = 1 WHERE user_id = ?",
                        (name, tag, rank, server_field, m.id)
                    )
                # Same rows upsert_user_nickname() would write — inlined here so it's
                # the same transaction (calling it would open a second connection
                # that blocks on this one's uncommitted write lock).
                if servers and m.id not in users_with_nick_rows:
                    for i, num in enumerate(servers):
                        await cur.execute(
                            "INSERT INTO user_nicknames (user_id, server_number, nickname, is_active) VALUES (?, ?, ?, ?) "
                            "ON CONFLICT(user_id, server_number) DO NOTHING",
                            (m.id, num, name, 1 if i == 0 else 0)
                        )
            await conn.commit()

    for m, existing, name, tag, rank, servers in pending:
        if member_role and member_role not in m.roles:
            try:
                await m.add_roles(member_role, reason="Startup reconciliation — holds an alliance tag")
            except discord.HTTPException:
                pass
        what = "Rebuilt" if existing is None else "Completed"
        repairs.append(f"👤 {what} record for {m.mention}: **{name} [{tag}] {format_server_display(servers) or '(no server)'}** — {rank}")

    if repairs:
        await log_event(guild, f"🗂️ **STARTUP INVENTORY — {len(repairs)} record(s) rebuilt from the live server**\n" + "\n".join(f"• {r}" for r in repairs))
    else:
        await log_event(guild, "🗂️ **STARTUP INVENTORY** — database already matches the live server. Nothing to rebuild.")
    return repairs


async def startup_nickname_enforcement(guild) -> list:
    """Every startup: compute what each alliance member's nickname SHOULD be
    from their live roles + DB name, and fix any that don't match — no
    command needed. Every change (and every one I couldn't make, e.g. a
    member ranked above me) is logged to #logs."""
    async with server_busy("booting up and checking nicknames", quiet=True):
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT tag FROM alliances")
            approved_tags = {row[0] for row in await cur.fetchall()}
            await cur.execute("SELECT user_id, in_game_name FROM users")
            in_game_names = {row[0]: row[1] for row in await cur.fetchall()}

        fixed, blocked, incomplete = [], [], 0
        for m in guild.members:
            if m.bot or not any(r.name in approved_tags for r in m.roles):
                continue
            expected = await compute_expected_nickname(m, approved_tags, in_game_names)
            if expected is None:
                incomplete += 1
                continue
            before = m.display_name
            if before.strip() == expected:
                continue
            try:
                await m.edit(nick=expected[:32], reason="Startup nickname enforcement")
                fixed.append(f"✏️ {m.mention}: `{before}` → `{expected}`")
            except discord.Forbidden:
                blocked.append(f"🚫 {m.mention}: should be `{expected}` — I can't edit them (ranked above me); needs a manual fix")
            except discord.HTTPException as e:
                blocked.append(f"⚠️ {m.mention}: should be `{expected}` — Discord refused (`{e}`)")

        if not fixed and not blocked:
            await log_event(guild, f"✅ **STARTUP NICKNAME CHECK** — every alliance member's nickname already matches their roles." + (f" ({incomplete} hold a tag but no server role — nothing to compute.)" if incomplete else ""))
        else:
            header = f"✏️ **STARTUP NICKNAME CHECK — {len(fixed)} fixed, {len(blocked)} need a human**"
            if incomplete:
                header += f" ({incomplete} hold a tag but no server role — skipped)"
            await log_event(guild, header + "\n" + "\n".join(fixed + blocked))
        return fixed


# ------------------------------------------------------------
#  ABILITIES / CLEARANCE SYSTEM
# ------------------------------------------------------------
ORDERED_ABILITY_KEYS = ["MEMBER", "R4", "R5", "JUDGE", "SENATOR", "DICTATOR"]

ABILITY_BLOCKS = {
    "MEMBER": {
        "header": "🧑‍✈️ **Chief Privileges**",
        "lines": [
            "🎮 `/rps [opponent]` — Rock, Paper, Scissors vs another Chief or me.",
            "🏆 `/alliance-leaderboard` — see alliance member-count rankings.",
            "📨 `/request-rank` (in #⚙️-role-requests) — petition for R4/R5 rank in your alliance, or ask your R5 to trust you with `/grant-leadership` directly.",
            "🌐 React with 🌐 on any message for a private DM translation.",
            "🗣️ `/language` — change which language I use when talking to you, any time.",
            "🕐 `/timezone` — set your approximate time zone so I can tell you how the server's schedule lines up with yours.",
            "📇 `/nickname` — if your in-game name is different on each server you play, manage them here.",
            "✏️ `/change-nick` — quick one-step update if your in-game name changed (or you just typo'd it) — keeps your `[TAG] (servers)` tag intact.",
            "🛠️ `/fix-me` — registered with the wrong name, tag, or server? Buttons to fix any of them yourself — or one to summon a human.",
            "🕵️ `/chase-status`, `/leave-chase`, `/join-chase` — Cops & Robbers runs daily at noon, check #💬-general-chat.",
            "🤖 `/catch <name>` — if a Rogue RoboCop is ever hiding among you, this is how you catch it.",
            "📊 `/game-stats` — running server-wide totals for RPS, Cops & Robbers, and Rogue RoboCop (also auto-posted daily).",
            "📅 `/monthly-standings` — see this month's gold/silver/bronze race so far (auto-announced and reset on the 1st).",
            "📢 `/announce <message>` — post to the current channel, once per hour.",
        ],
    },
    "R4": {
        "header": "🎖️ **R4 Command Privileges**",
        "lines": ["🔑 Access to your alliance's 🎖️-leadership-chat."],
    },
    "R5": {
        "header": "👑 **R5 Command Privileges**",
        "lines": [
            "🔑 Full command of your alliance's leadership chat and roster.",
            "⚖️ You can approve or deny R4 requests within your own alliance directly from #logs — no staff needed.",
            "📢 `/announce <message>` — reaches every channel in your alliance at once, once per 30 minutes.",
            "🏷️ `/rename-tag <old> <new>` — rename your own alliance's tag; updates its roles, channels, and every member's record at once.",
        ],
    },
    "JUDGE": {
        "header": "🔨 **JUDGE Privileges** — you're a moderator now, don't let it go to your head",
        "lines": [
            "🔨 `/imprison <nickname> <minutes>` — lock someone in solitary.",
            "🚪 `/unban <user_id>` and `/pardon <user_id>`.",
            "⚠️ `/warn <member> <reason>` and `/warnings <member>`.",
            "🔓 `/approve-tag <tag>` — release a new alliance from the Drunk Tank.",
            "🚨 `/killswitch [minutes] [off]` — emergency chat lockdown.",
            "📋 `/show-banned`, `/show-role`, `/show-db-fields`, `/show-field`, `/re-check-nicknames`.",
            "📢 `/announce <message>` — as staff, this reaches the entire server, no cooldown.",
            "📊 `/server-stats` — translations, referrals, RPS records, and more.",
            "🕵️ `/start-chase` / `/end-chase` — manually trigger or cut short a Cops & Robbers round.",
            "🕹️ `/game-start`, `/game-end`, `/game-restart` — unified control for Cops & Robbers AND Rogue RoboCop: start now or in N minutes, end now or pause-and-auto-resume in N minutes, or restart on the spot.",
            "📅 `/monthly-champions-now` — manually trigger the Monthly Champion announcement and reset standings, without waiting for the 1st.",
            "🏷️ `/rename-tag <old> <new>` — rename ANY alliance's tag (not just your own), same as staff.",
            "📝 `/enforce-registration <member>` — flag an existing member for mandatory registration.",
            "↩️ Undo / Release Now buttons on every #logs entry.",
        ],
    },
    "SENATOR": {
        "header": "🟠 **SENATOR Privileges** — everything a Judge has, plus the keys to the walls",
        "lines": [
            "🏗️ Create and delete channels directly in Discord.",
            "🔒 `/stop-alliance <lock>` — freeze new alliance creation server-wide.",
            "⏱️ `/release-timekeeper` — open a 10-minute alliance-creation burst window.",
            "🛠️ `/add-request-role <role> <description>`.",
            "🌟 `/toggle-innovator-program` — turn future automatic Innovator badge grants on or off.",
            "🏆 `/set-monthly-prize <prize>` — set what next month's Monthly Champion (Gold) actually wins. Defaults to bragging rights.",
            "🧹 `/dissolve-alliance <tag>` — delete a typo-alliance completely (roles, channels, records). Confirms first.",
        ],
    },
    "DICTATOR": {
        "header": "👑 **DICTATOR Privileges** — everything, always, no exceptions",
        "lines": ["🌐 Full Administrator. Every command, every switch, every door."],
    },
}


def compute_capabilities(member) -> list:
    """Returns this member's unlocked capability tiers, in ascending order.
    A true Discord Administrator always gets DICTATOR-level display, even
    without literally holding the DICTATOR role — matching how
    is_staff_member()/is_dictator_member() already treat raw Administrator
    permission as equivalent, so /abilities can't disagree with what the
    permission checks actually allow."""
    names = {r.name for r in member.roles}
    caps = []
    if ROLE_MEMBER in names:
        caps.append("MEMBER")
    if any(n.endswith("-R4") for n in names):
        caps.append("R4")
    if any(n.endswith("-R5") for n in names):
        caps.append("R5")
    if ROLE_JUDGE in names or ROLE_STITCH in names or ROLE_MILLIE in names or ROLE_CHROME in names or ROLE_SILENT in names:
        caps.append("JUDGE")
    if ROLE_SENATOR in names:
        caps.append("SENATOR")
    if ROLE_DICTATOR in names or member.guild_permissions.administrator:
        caps.append("DICTATOR")
    return caps


def build_abilities_text(capabilities) -> str:
    blocks = []
    for key in ORDERED_ABILITY_KEYS:
        if key in capabilities:
            block = ABILITY_BLOCKS[key]
            blocks.append(block["header"] + "\n" + "\n".join(f"  {l}" for l in block["lines"]))
    return "\n\n".join(blocks)


async def mark_capabilities_notified(user_id: int, capabilities):
    if not capabilities:
        return
    async with db_connect() as conn:
        cur = await conn.cursor()
        for cap in capabilities:
            await cur.execute("INSERT OR IGNORE INTO capability_notifications (user_id, capability) VALUES (?, ?)", (user_id, cap))
        await conn.commit()


def rank_color(capabilities) -> discord.Color:
    """Picks a flavorful embed color matching the member's highest rank."""
    if "DICTATOR" in capabilities:
        return DICTATOR_COLOR
    if "SENATOR" in capabilities:
        return SENATOR_COLOR
    if "JUDGE" in capabilities:
        return JUDGE_COLOR
    if "R5" in capabilities:
        return discord.Color.gold()
    if "R4" in capabilities:
        return discord.Color.purple()
    if "MEMBER" in capabilities:
        return discord.Color.teal()
    return discord.Color.greyple()


def build_abilities_embed(member: discord.Member, capabilities, title: str, description: str = "") -> discord.Embed:
    """Shared pretty embed used by the onboarding welcome DM, clearance-upgrade
    DM, and /abilities — one badge/thumbnail/color-coded 'personnel file' look
    across all three."""
    embed = discord.Embed(title=title, description=description, color=rank_color(capabilities), timestamp=datetime.now())
    embed.set_thumbnail(url=member.display_avatar.url)

    if not capabilities:
        embed.add_field(name="📁 On File", value="🤷 Nothing yet — finish up in #gateway first, Chief.", inline=False)
    else:
        for key in ORDERED_ABILITY_KEYS:
            if key in capabilities:
                block = ABILITY_BLOCKS[key]
                # Discord caps each field value at 1024 chars — several tiers
                # (MEMBER, JUDGE) are longer than that, so split on line
                # boundaries into continuation fields instead of crashing.
                for i, chunk in enumerate(_chunk_lines_for_field(block["lines"])):
                    name = block["header"] if i == 0 else f"{block['header']} (cont.)"
                    embed.add_field(name=name[:256], value=chunk, inline=False)

    embed.set_footer(text="🤖 RoboCop Personnel File")
    return embed


EMBED_FIELD_VALUE_LIMIT = 1024


def _chunk_lines_for_field(lines, limit: int = EMBED_FIELD_VALUE_LIMIT) -> list:
    """Packs lines into newline-joined chunks that each fit in one embed
    field value. A single line longer than the limit is hard-truncated
    (none currently are — this is just a guard)."""
    chunks, current = [], ""
    for line in lines:
        if len(line) > limit:
            line = line[:limit - 3] + "..."
        candidate = f"{current}\n{line}" if current else line
        if len(candidate) > limit:
            chunks.append(current)
            current = line
        else:
            current = candidate
    if current:
        chunks.append(current)
    return chunks or ["—"]


# ------------------------------------------------------------
#  FULL PUBLIC COMMAND REFERENCE — every command, everyone can see it,
#  in both a simple (name + one-liner) and verbose (+ every parameter)
#  form. Names/descriptions/parameters are pulled live from the actual
#  registered commands (bot.tree.get_commands()) so this can never drift
#  out of sync with reality the way a hand-typed copy could. The one thing
#  that can't be introspected generically is which rank tier gates a
#  command — that's this dict, extracted from the source's own @is_staff()/
#  @is_senior_staff()/@is_dictator() decorators at the time this was built.
#  If a command's gating decorator ever changes, update its entry here too.
# ------------------------------------------------------------
COMMAND_TIER = {
    "unban": "Judge+", "pardon": "Judge+", "re-check-nicknames": "Judge+", "imprison": "Judge+",
    "approve-tag": "Judge+", "killswitch": "Judge+", "warn": "Judge+", "warnings": "Judge+",
    "server-stats": "Judge+", "show-banned": "Judge+", "show-role": "Judge+", "show-db-fields": "Judge+",
    "show-field": "Judge+", "start-chase": "Judge+", "end-chase": "Judge+", "game-start": "Judge+",
    "game-end": "Judge+", "game-restart": "Judge+", "enforce-registration": "Judge+", "robocop": "Judge+",
    "add-request-role": "Senator+", "configure-setting": "Senator+", "toggle-innovator-program": "Senator+",
    "toggle-rogue-bot-program": "Senator+", "stop-alliance": "Senator+", "release-timekeeper": "Senator+",
    "configure-servers": "Senator+", "grant-rank": "Senator+", "grant-rank-picker": "Senator+",
    "set-monthly-prize": "Senator+", "dissolve-alliance": "Senator+",
    "announce-update": "Dictator", "bulk-onboard-existing": "Dictator", "ptd-reset": "Dictator",
    "ptd-upgrade-now": "Dictator", "adopt-alliance": "Dictator", "migrate-legacy-roles": "Dictator",
    "grant-innovator-all": "Dictator", "restore-innovators": "Dictator", "database-tools": "Dictator",
    "rename-tag": "R5 of that tag, or Judge+",
    "game-stats": "Everyone", "monthly-standings": "Everyone",
    "monthly-champions-now": "Judge+",
}
# Commands that LOOK open to everyone by decorator, but actually carry an
# internal-only restriction the decorator can't express — flagged so the
# public reference doesn't accidentally undersell what they require.
COMMAND_SPECIAL_NOTES = {
    "approve-tag": "For a second alliance with the same tag from another server, type the tag and server, e.g. `HAL-121`.",
    "dissolve-alliance": "For a second alliance with the same tag from another server, type the tag and server, e.g. `HAL-121`.",
    "grant-rank": "For a second alliance with the same tag from another server, type the tag and server, e.g. `HAL-121`.",
    "rename-tag": "Renaming ONTO an existing tag merges the two alliances — admin only (Dictator or Discord Administrator).",
    "announce": "Scope depends on rank: Member reaches the current channel (1/hr), an alliance R5 reaches all of that alliance's channels (1/30min), staff reach the whole server (no limit).",
    "grant-leadership": "R5-only — enforced internally, not by a Discord permission.",
    "revoke-leadership": "R5-only — enforced internally, not by a Discord permission.",
}
COMMAND_TIER_ORDER = ["Everyone", "R5 of that tag, or Judge+", "Judge+", "Senator+", "Dictator"]
COMMAND_TIER_HEADERS = {
    "Everyone": "🧑‍✈️ Open to Everyone",
    "R5 of that tag, or Judge+": "👑 Alliance R5 (own tag) or Staff",
    "Judge+": "🔨 Judge and Above",
    "Senator+": "🟠 Senator and Above",
    "Dictator": "👑 Dictator Only",
}


def build_public_command_reference(verbose: bool) -> list:
    """Returns a list of message-sized text chunks (each safely under
    Discord's 2000-char limit) listing every registered command, grouped by
    tier. verbose=False is a name + one-liner per command; verbose=True adds
    every parameter's own name/description/required-ness."""
    by_tier = {tier: [] for tier in COMMAND_TIER_ORDER}
    for cmd in sorted(bot.tree.get_commands(), key=lambda c: c.name):
        tier = COMMAND_TIER.get(cmd.name, "Everyone")
        if tier not in by_tier:
            tier = "Everyone"  # guard: an unknown tier label must never crash the whole reference
        line = f"`/{cmd.name}` — {cmd.description}"
        note = COMMAND_SPECIAL_NOTES.get(cmd.name)
        if note:
            line += f"\n     ⚠️ {note}"
        if verbose and getattr(cmd, "parameters", None):
            for p in cmd.parameters:
                req = "required" if p.required else "optional"
                pdesc = p.description or "no description given"
                line += f"\n     • **{p.name}** ({req}) — {pdesc}"
        by_tier[tier].append(line)

    chunks = []
    current = "📖 **FULL COMMAND REFERENCE" + (" — VERBOSE" if verbose else " — SIMPLE") + "**\n"
    for tier in COMMAND_TIER_ORDER:
        lines = by_tier[tier]
        if not lines:
            continue
        section = f"\n**{COMMAND_TIER_HEADERS[tier]}**\n" + "\n".join(lines) + "\n"
        if len(current) + len(section) > 1900:
            chunks.append(current)
            current = section
        else:
            current += section
    if current.strip():
        chunks.append(current)
    return chunks


async def sync_abilities_channel_reference(guild, abilities_ch):
    """Keeps a pinned, always-current SIMPLE command list at the top of
    #❓-abilities — this is deliberately what greets anyone opening the
    channel, per design: the simple list up front, with a button to pull
    the full verbose version (every parameter, every tier) on demand rather
    than dumping all of that by default. Edits existing pinned messages in
    place across restarts instead of reposting/re-pinning every time; only
    falls back to a fresh post if a stored message was deleted or the
    chunk count changed since last time."""
    settings_key = f"abilities_simple_msg_ids_{guild.id}"
    chunks = build_public_command_reference(verbose=False)
    intro = "🤖 **Type `/abilities` any time for YOUR personal rundown.** Below is the full server-wide command list.\n"
    chunks = [intro + chunks[0]] + chunks[1:]

    stored_raw = await get_setting(settings_key)
    stored_ids = json.loads(stored_raw) if stored_raw else []

    old_messages = []
    for mid in stored_ids:
        try:
            old_messages.append(await abilities_ch.fetch_message(mid))
        except (discord.NotFound, discord.HTTPException):
            old_messages.append(None)

    new_ids = []
    for idx, content in enumerate(chunks):
        view = AbilitiesReferenceView() if idx == 0 else None
        existing = old_messages[idx] if idx < len(old_messages) else None
        if existing:
            try:
                await existing.edit(content=content, view=view)
                new_ids.append(existing.id)
                continue
            except discord.HTTPException:
                pass  # fall through to posting fresh below
        try:
            msg = await abilities_ch.send(content=content, view=view)
            await msg.pin()
            new_ids.append(msg.id)
        except discord.HTTPException:
            pass

    # Clean up any leftover messages from a previous, longer version of the list.
    for extra in old_messages[len(chunks):]:
        if extra:
            try:
                await extra.delete()
            except discord.HTTPException:
                pass

    await set_setting(settings_key, json.dumps(new_ids))


class AbilitiesReferenceView(discord.ui.View):
    """Lives on the pinned simple-list message in #❓-abilities. Static
    custom_id so bot.add_view() at startup keeps this button alive across
    restarts, same pattern as every other persistent panel in this file."""

    def __init__(self):
        super().__init__(timeout=None)

    @discord.ui.button(label="📖 Show Full Verbose List", style=discord.ButtonStyle.primary, custom_id="rc_abilities_verbose")
    async def show_verbose(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.defer(ephemeral=True)
        chunks = build_public_command_reference(verbose=True)
        await interaction.followup.send(chunks[0], ephemeral=True)
        for chunk in chunks[1:]:
            await interaction.followup.send(chunk, ephemeral=True)


WELCOME_FLAVOR = [
    "Badge issued, paperwork filed, coffee's already going cold in the break room.",
    "Fingerprints on file. Donut privileges: unlocked.",
    "You're officially on the payroll. Try not to embarrass the department.",
    "Sworn in, suited up, and dangerously caffeinated.",
    "Welcome aboard. The vending machine on 3 eats coins and dreams — you've been warned.",
]

UPGRADE_FLAVOR = [
    "Somebody upstairs likes you.",
    "Ink's still wet on the promotion papers.",
    "New badge, who dis.",
    "The paperwork went through. Try to act surprised.",
]

# These names always pass the invite check, regardless of whether anyone in
# the server currently holds Member — solves the bootstrapping problem where
# a brand-new (or freshly reset) server has nobody a first-time onboarder
# could correctly name.
ALWAYS_VALID_INVITER_NAMES = {"mesk", "mesky"}

INVITE_TAUNTS = [
    "Nice try. Stop making things up.",
    "Does your nose grow when you type? Try again.",
    "I've heard better lies from a parrot. Try again.",
    "That name isn't ringing any bells around here. Try again.",
    "Bold guess. Wrong, but bold. Try again.",
]

# Tracks the last line picked per key (a pool name, or a per-user key like
# f"taunt_{member.id}") so a cheeky line never repeats back-to-back.
_last_flavor_choice = {}


def pick_flavor(pool: list, key: str) -> str:
    if not pool:
        return ""
    if len(pool) == 1:
        return pool[0]
    last = _last_flavor_choice.get(key)
    candidates = [line for line in pool if line != last] or pool
    choice = random.choice(candidates)
    _last_flavor_choice[key] = choice
    return choice


async def check_raid(guild):
    """Simple join-rate raid alert: N joins within M seconds pings #logs (throttled to once per window)."""
    global _last_raid_alert
    now = datetime.now()
    _recent_joins.append(now)
    while _recent_joins and (now - _recent_joins[0]).total_seconds() > RAID_JOIN_WINDOW_SECONDS:
        _recent_joins.popleft()

    if len(_recent_joins) >= RAID_JOIN_THRESHOLD:
        if not _last_raid_alert or (now - _last_raid_alert).total_seconds() > RAID_JOIN_WINDOW_SECONDS:
            _last_raid_alert = now
            await log_event(
                guild,
                f"🚨🚨 **POSSIBLE RAID DETECTED** 🚨🚨\n"
                f"{len(_recent_joins)} members joined within {RAID_JOIN_WINDOW_SECONDS} seconds. "
                f"Consider raising the server's verification level or watching #gateway closely."
            )


async def log_mod_action(guild, action_type, target_id, target_name, moderator_label, reason, extra_data=None):
    """Records a ban/kick/imprison action and posts an undoable embed to #logs. Returns the log_id."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute(
            "INSERT INTO mod_log (action_type, target_id, target_name, moderator_label, reason, extra_data) VALUES (?, ?, ?, ?, ?, ?)",
            (action_type, target_id, target_name, moderator_label, reason, extra_data)
        )
        log_id = cur.lastrowid
        await conn.commit()

    meta = ACTION_META.get(action_type, {"title": "🚨 MODERATION ACTION", "color": discord.Color.orange()})
    embed = discord.Embed(title=meta["title"], color=meta["color"], timestamp=datetime.now())
    embed.add_field(name="Target", value=f"{target_name} (`{target_id}`)", inline=False)
    embed.add_field(name="Moderator", value=str(moderator_label), inline=True)
    embed.add_field(name="Reason", value=reason or "No reason given", inline=True)
    embed.set_footer(text=f"Log ID: {log_id}")

    view = UndoActionView(log_id, action_type) if action_type in ACTION_META else None
    log_channel = discord.utils.get(guild.channels, name="logs")
    if log_channel:
        try:
            await log_channel.send(embed=embed, view=view)
        except discord.HTTPException as e:
            print(f"[ERROR] Failed to post mod-log entry: {e}")

    if action_type == "ban":
        await notify_staff_dm(
            guild, meta["title"],
            f"Target: {target_name} (`{target_id}`)\nModerator: {moderator_label}\nReason: {reason or 'No reason given'}",
            color=meta["color"]
        )

    return log_id


async def restore_persistent_views():
    """Re-attaches Undo/Release buttons to recent mod-log entries so they still work after a restart."""
    bot.add_view(RoleOrderFixView())  # static custom_id — one registration covers every alert ever posted
    bot.add_view(DatabaseToolsView())  # same idea — persists the release/reset panel across restarts
    bot.add_view(BulkAutoRegisterView())  # same idea — persists the startup-diagnostic bulk button
    bot.add_view(AbilitiesReferenceView())  # persists the #❓-abilities "Show Full Verbose List" button

    cutoff = (datetime.now() - timedelta(days=14)).isoformat()
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT log_id, action_type FROM mod_log WHERE undone = 0 AND timestamp >= ?", (cutoff,))
        rows = await cur.fetchall()

    for log_id, action_type in rows:
        if action_type in ACTION_META:
            bot.add_view(UndoActionView(log_id, action_type))

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT request_id, rank FROM rank_requests WHERE status = 'pending'")
        pending_requests = await cur.fetchall()

    for request_id, rank in pending_requests:
        bot.add_view(RankRequestView(request_id, rank))

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT tag FROM alliances WHERE status = 'pending'")
        pending_alliances = await cur.fetchall()

    for (tag,) in pending_alliances:
        bot.add_view(AllianceApprovalView(tag))

    # Empty-alliance cleanup offers still sitting in #logs, unanswered.
    for guild in bot.guilds:
        for tag in await _get_orphan_pending(guild):
            bot.add_view(OrphanAllianceCleanupView(tag))

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT user_id FROM auto_registration_flags WHERE resolved = 0")
        pending_autoreg = await cur.fetchall()

    for (user_id,) in pending_autoreg:
        bot.add_view(AutoRegisterView(user_id))

    if rows or pending_requests or pending_alliances or pending_autoreg:
        print(
            f"[SYSTEM] Restored {len(rows)} moderation-log button(s), {len(pending_requests)} R5-request button(s), "
            f"{len(pending_alliances)} alliance-approval button(s), and {len(pending_autoreg)} auto-registration button(s)."
        )


async def handle_undo_action(interaction: discord.Interaction, log_id: int, action_type: str):
    # Acknowledge FIRST, before any DB or Discord API work — release actions
    # can involve several sequential calls (role removal, role restoration,
    # a #logs post, multiple DB writes) that can cumulatively exceed
    # Discord's 3-second response window under real-world conditions,
    # causing "Unknown interaction" if we wait until the end to respond.
    await interaction.response.defer()

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT target_id, target_name, undone FROM mod_log WHERE log_id = ?", (log_id,))
        row = await cur.fetchone()

    if not row:
        await interaction.followup.send("⚠️ Could not find this log entry anymore.", ephemeral=True)
        return

    target_id, target_name, undone = row
    if undone:
        await interaction.followup.send("ℹ️ This action was already reversed.", ephemeral=True)
        return

    guild = interaction.guild
    result_msg = "⚠️ Unknown action type."

    if action_type == "ban":
        try:
            await guild.unban(discord.Object(id=target_id), reason=f"Undone via #logs by {interaction.user}")
        except discord.NotFound:
            pass  # Already unbanned, or was never actually applied on Discord's side
        except discord.Forbidden:
            await interaction.followup.send("❌ I lack permission to unban members.", ephemeral=True)
            return
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("UPDATE users SET timeout_until = NULL, lifetime_invite_fails = 0, invite_strikes = 0 WHERE user_id = ?", (target_id,))
            await cur.execute("DELETE FROM bans WHERE user_id = ?", (target_id,))
            await conn.commit()
        result_msg = f"✅ Ban on **{target_name}** reversed by {interaction.user.mention}. They may rejoin."

    elif action_type == "kick":
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("UPDATE users SET timeout_until = NULL, lifetime_invite_fails = 0, invite_strikes = 0 WHERE user_id = ?", (target_id,))
            await conn.commit()
        result_msg = f"✅ **{target_name}**'s record was cleared by {interaction.user.mention}. They'll get a clean slate if they rejoin."

    elif action_type == "imprison":
        member = guild.get_member(target_id)
        prison_role = discord.utils.get(guild.roles, name=ROLE_PRISONER)
        if member and prison_role:
            await execute_release(member, prison_role)
            result_msg = f"✅ {member.mention} released early by {interaction.user.mention}."
        else:
            result_msg = f"⚠️ Could not find {target_name} in the server to release (they may have left)."

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("UPDATE mod_log SET undone = 1 WHERE log_id = ?", (log_id,))
        await conn.commit()

    original_embed = interaction.message.embeds[0] if interaction.message.embeds else None
    if original_embed:
        original_embed.add_field(name="Status", value=f"✅ Reversed by {interaction.user.mention}", inline=False)
        original_embed.color = discord.Color.green()
        await interaction.edit_original_response(embed=original_embed, view=None)
    else:
        await interaction.edit_original_response(view=None)

    await interaction.followup.send(result_msg, ephemeral=True)
    await log_event(guild, f"↩️ **ACTION REVERSED**\n{result_msg}")


async def clear_gateway_override(guild, member):
    """Cleans up the per-member permission grant on #gateway once someone has left the onboarding flow."""
    gateway_channel = discord.utils.get(guild.channels, name="gateway")
    if gateway_channel:
        try:
            await gateway_channel.set_permissions(member, overwrite=None)
        except (discord.Forbidden, discord.HTTPException):
            pass


HELP_TRIGGER_WORDS = {"help", "?", "??", "staff", "human", "admin", "stuck", "confused", "i don't understand", "i dont understand", "idk"}
_help_escalated = set()  # member IDs who've already had staff pinged this process lifetime — one ping, not a flood


def is_help_request(content: str) -> bool:
    return content.strip().lower().rstrip("!.") in HELP_TRIGGER_WORDS


async def escalate_onboarding_help(member, channel):
    """Someone typed 'help' (or similar) at any onboarding prompt. Ping staff
    ONCE, reassure the person in-channel, and let the flow keep waiting for
    a real answer — nothing gets counted as a strike, nothing gets kicked.
    The whole point: a confused newcomer should never have to guess the
    magic word, and typing the most obvious thing ('help') should do the
    obviously-right thing."""
    guild = member.guild
    try:
        await channel.send(await tf(
            "🆘 {mention}, no problem — I've pinged a human to come help you. Keep going if you can "
            "(just answer as best you're able); **nothing here is permanent**, and staff can fix any "
            "answer afterwards with a click. If you'd rather wait for them, that's fine too.",
            member.id, mention=member.mention
        ))
    except discord.HTTPException:
        pass
    if member.id in _help_escalated:
        return
    _help_escalated.add(member.id)
    await log_event(guild, f"🆘 **NEWCOMER NEEDS A HAND**\n{member.mention} typed for help in #gateway mid-registration. Someone pop in and walk them through it.")
    await notify_staff_dm(
        guild, "🆘 Someone's stuck in #gateway",
        f"{member.mention} asked for help partway through registration. A quick word in #gateway will sort it.",
        color=discord.Color.orange()
    )


# ------------------------------------------------------------
#  ONBOARDING CONSOLE FEED + 2-MINUTE CHECK-IN
#  Every join, every onboarding step, every answer and the final outcome
#  is printed to the console window the bot runs in, so the owner can
#  watch newcomers come through live. And if someone goes quiet for
#  ONBOARDING_CHECKIN_SECONDS at any step, RoboCop pops into #gateway to
#  ask if they're still there and whether they'd like a walkthrough.
# ------------------------------------------------------------
ONBOARDING_CHECKIN_SECONDS = 120

# The old "who invited you?" gate scared newcomers off. Off by default now;
# flip to True to bring it back (strikes, lockouts and referral counting
# all come back with it).
ASK_WHO_INVITED = False

PRIVACY_NOTE = (
    "🔒 **Privacy, straight talk.** Here's *everything* I keep about you:\n"
    "• **What you tell me:** your in-game name (one per game server, if they differ), alliance tag, "
    "game server number(s), language, and a rough time zone — only if you choose to share it.\n"
    "• **Your Discord ID and username** — so I recognise you if you leave and come back.\n"
    "• **Your place in the server:** your rank (R4/R5), rank requests you file, badges like Innovator, "
    "and which registration steps you've finished.\n"
    "• **Game scores:** Rock-Paper-Scissors, Cops & Robbers, Rogue RoboCop and monthly standings.\n"
    "• **Moderation history, if any:** warnings, time-outs, kicks or bans and the reason given — and, if you "
    "ever land in jail, the roles you had so I can hand them back when you're released.\n\n"
    "Also good to know: posts in #🐛-bugs and #💡-suggestions are copied to the staff log, and when you ask "
    "me to translate a message (🌐), its text is sent to Google Translate to do it — nothing is saved. I notice "
    "when you come online so I can send the odd stats reminder, but I don't record it.\n\n"
    "**What I never collect:** no real name, address, phone number, email, location or payment details, "
    "and I don't save your chat messages. Just a robot with a very short notepad. 🤖📝"
)


def onboard_console(member, text: str):
    stamp = datetime.now().strftime("%H:%M:%S")
    name = getattr(member, "display_name", None) or str(member)
    print(f"[ONBOARDING {stamp}] {name} ({member.id}) — {text}", flush=True)


ONBOARDING_STEPS_GUIDE = (
    "🗺️ **No problem, Chief — here's the whole route into the server:**\n\n"
    "**1. 🌍 Language** — pick your language from the menu, or skip it and I'll use English (change it any time with `/language`).\n"
    "**2. 🕐 Time zone** — optional. Pick your rough time zone, or skip it.\n"
    "**3. ⚠️ Test-server notice** — click the green button to say you understand this is a test server.\n"
    "**4. 🪪 Your in-game name** — type your exact username from the game.\n"
    "**5. 🏷️ Alliance tag** — type your alliance's 2–4 letter tag (letters only, e.g. `PTD`), then confirm it.\n"
    "**6. 🗺️ Server number** — type which game server(s) you play on (e.g. `21`).\n\n"
    "That's it — you're in! Just answer the most recent question from me in this channel. "
    "🔒 I don't collect anything beyond those answers — no address, phone number or location. "
    "Still stuck? Type `help` here and a real human will come find you. 🚔"
)


class OnboardingCheckInView(discord.ui.View):
    """Posted in #gateway after ONBOARDING_CHECKIN_SECONDS of silence.
    Answering it never counts as an answer to the actual onboarding
    question — the step keeps waiting either way."""
    def __init__(self, member):
        super().__init__(timeout=300.0)
        self.member = member

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.member.id:
            await interaction.response.send_message("🚔 This check-in isn't for you, Chief.", ephemeral=True)
            return False
        return True

    async def _close(self, interaction: discord.Interaction, content: str):
        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(content=content, view=self)
        self.stop()

    @discord.ui.button(label="Yes, I need help", style=discord.ButtonStyle.primary, emoji="🙋")
    async def need_help(self, interaction: discord.Interaction, button: discord.ui.Button):
        onboard_console(self.member, "🙋 check-in: said YES, needs help — sent the steps guide")
        await self._close(interaction, await t("🙋 Help is on the way — steps below!", self.member.id))
        await interaction.followup.send(await t(ONBOARDING_STEPS_GUIDE, self.member.id), ephemeral=True)

    @discord.ui.button(label="I'm here, all good", style=discord.ButtonStyle.secondary, emoji="👍")
    async def all_good(self, interaction: discord.Interaction, button: discord.ui.Button):
        onboard_console(self.member, "👍 check-in: still here, no help needed")
        await self._close(interaction, await t("👍 Roger that — carry on whenever you're ready.", self.member.id))


async def send_onboarding_checkin(member):
    onboard_console(member, f"⏸️ quiet for {ONBOARDING_CHECKIN_SECONDS // 60} min — asking if they're still there")
    gateway = discord.utils.get(member.guild.text_channels, name="gateway")
    if not gateway:
        return
    try:
        await gateway.send(
            await tf("👀 {mention}, you still there? Would you like some help getting through registration?",
                     member.id, mention=member.mention),
            view=OnboardingCheckInView(member)
        )
    except discord.HTTPException as e:
        await report_error(member.guild, "onboarding 2-minute check-in", member, e)


async def send_onboarding_countdown_dm(member, warning_text: str, seconds_left: int, add_help_hint: bool):
    onboard_console(member, f"⏰ DM warning sent — about {seconds_left}s left before removal")
    hint = " Confused? Just type `help` in #gateway." if add_help_hint else ""
    try:
        await member.send(await t(
            f"⏰ {warning_text} You have about {seconds_left} seconds left to respond in #gateway, or you'll be "
            f"removed from the server. No worries if that happens — you can rejoin any time and pick up right "
            f"where you left off.{hint}",
            member.id
        ))
    except discord.Forbidden:
        pass


class AllianceChoiceView(discord.ui.View):
    """'Which [TAG] is yours?' — one button per existing alliance with that
    tag, plus 'mine's a different one'."""
    def __init__(self, member, options):
        super().__init__(timeout=240.0)
        self.member = member
        self.result = None
        for key, label in options[:4]:
            btn = discord.ui.Button(label=label[:80], style=discord.ButtonStyle.success, emoji="✅")
            btn.callback = self._pick(key)
            self.add_item(btn)
        btn = discord.ui.Button(label="Mine's a different alliance", style=discord.ButtonStyle.secondary, emoji="🔀")
        btn.callback = self._pick("__different__")
        self.add_item(btn)

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.member.id:
            await interaction.response.send_message("🚔 This question isn't for you, Chief.", ephemeral=True)
            return False
        return True

    def _pick(self, key):
        async def callback(interaction: discord.Interaction):
            self.result = key
            await interaction.response.edit_message(view=None)
            self.stop()
        return callback


async def choose_alliance_key(guild, member, gateway_channel, tag: str):
    """The same tag can exist on different game servers. If [tag] is
    already registered here, ask which alliance is theirs; if it's a
    different one, ask which game server it's on and register it as its own
    alliance (key TAG·server). Returns the alliance key to use, or None if
    they stopped answering."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT tag FROM alliances")
        keys = [r[0] for r in await cur.fetchall()]
        await cur.execute("SELECT alliance_tag, server_number FROM users WHERE alliance_tag IS NOT NULL AND server_number IS NOT NULL")
        member_rows = await cur.fetchall()
    cands = [k for k in keys if tag_display(k) == tag]
    if not cands:
        return tag  # brand-new tag

    options = []
    for k in sorted(cands, key=lambda x: (tag_home_server(x) is not None, x)):
        servers = set()
        for a_tag, srv in member_rows:
            if a_tag == k:
                servers.update(await parse_stored_server_field(srv, guild.id))
        if tag_home_server(k):
            servers = {tag_home_server(k)}
        role = discord.utils.get(guild.roles, name=k)
        count = len([m for m in role.members if not m.bot]) if role else 0
        where = ("server " + "/".join(sorted(servers, key=lambda x: int(x) if x.isdigit() else 0))) if servers else "server unknown"
        options.append((k, f"[{tag}] on {where} · {count} member(s)"))

    view = AllianceChoiceView(member, options)
    await gateway_channel.send(await tf(
        "🏢 {mention}, **[{tag}]** is already registered here. Is one of these your alliance? "
        "(The same tag can belong to different alliances on different game servers — that's fine.)",
        member.id, mention=member.mention, tag=tag), view=view)
    if not await view_wait_with_warning(member, view, 240.0, "Still there? Which alliance is yours?"):
        return None
    if view.result != "__different__":
        onboard_console(member, f"   joined existing alliance {view.result}")
        return view.result

    managed = await get_managed_servers(guild.id)
    server_list_display = ", ".join(f"`{n}`" for n in managed)

    def check(m):
        return m.author == member and m.channel == gateway_channel

    await gateway_channel.send(await tf(
        "🔀 No problem, {mention} — two alliances, one tag! Which game server is **your** [{tag}] on? "
        "Just the number — one of: {servers}.",
        member.id, mention=member.mention, tag=tag, servers=server_list_display))
    srv = None
    for attempt in range(3):
        try:
            msg = await wait_with_warning(member, check, 240.0, "Still there? Which server is your alliance on?")
        except asyncio.TimeoutError:
            return None
        nums = normalize_server_input(msg.content, managed)
        if nums:
            srv = nums[0]
            break
        if attempt < 2:
            await gateway_channel.send(await tf(
                "⚠️ That's not one of our servers — just the number, one of: {servers}.",
                member.id, servers=server_list_display))
    if not srv:
        await log_event(guild, f"🆘 **REGISTRATION STALLED — ALLIANCE SERVER**\n{member.mention} has a different **[{tag}]** alliance but couldn't tell me which game server it's on.")
        await notify_staff_dm(guild, "🆘 Someone's stuck choosing their alliance's server", f"{member.mention} has a second **[{tag}]** alliance and got stuck on which server it's from. A quick word in #gateway will sort it.", color=discord.Color.orange())
        return None

    key = make_alliance_key(tag, srv)
    if key in keys:
        onboard_console(member, f"   joined existing alliance {key}")
        return key
    onboard_console(member, f"🔀 second [{tag}] alliance — registering it separately for server {srv} as {key}")
    await log_event(guild, f"🔀 **SAME TAG, DIFFERENT SERVER**\n{member.mention} is registering a separate **[{tag}]** alliance for server {srv}. "
                           f"It's stored as `{key}` (roles/channels use that name); members still show **[{tag}]** in their nickname.")
    await gateway_channel.send(await tf(
        "👍 Got it — your alliance is set up as its own **[{tag}]** for server {srv}. Your name will still "
        "show **[{tag}]**; behind the scenes I label it **{key}** so the two never get mixed up.",
        member.id, tag=tag, srv=srv, key=key))
    return key


class OnboardingMemberLeft(Exception):
    """Raised inside an onboarding wait once the member is no longer in the
    server, so the flow stops instead of DM-ing and 'timing out' a ghost."""


def _member_gone(member) -> bool:
    return member.guild.get_member(member.id) is None


ALLIANCE_CREATION_COOLDOWN_MINUTES = 30
LANGUAGE_DEFAULT_SECONDS = 90  # no language picked by then -> English, instead of removing them
_resume_tasks = {}  # member_id -> pending auto-resume task


async def resume_onboarding_later(guild, member_id: int, delay_seconds: float, tag: str):
    await asyncio.sleep(max(0, delay_seconds) + 5)
    _resume_tasks.pop(member_id, None)
    m = guild.get_member(member_id)
    member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)
    if not m or m.id in _onboarding_in_progress or (member_role and member_role in m.roles):
        return
    gateway = discord.utils.get(guild.text_channels, name="gateway")
    if gateway:
        try:
            await gateway.send(await tf(
                "🚦 {mention}, green light! The alliance line is open again — let's finish setting up **[{tag}]**. "
                "I'll ask for your tag once more.", m.id, mention=m.mention, tag=tag))
        except discord.HTTPException:
            pass
    onboard_console(m, f"🚦 cooldown over — resuming registration for [{tag}]")
    await run_onboarding_safe(m)


async def park_for_alliance_cooldown(guild, member, gateway_channel, tag: str, cooldown_ends: datetime):
    """New alliances are rate-limited server-wide. Instead of a dead end,
    tell the person exactly when, alert staff, and pick them back up
    automatically when the window opens."""
    delay = (cooldown_ends - datetime.now()).total_seconds()
    mins = max(1, int(delay // 60) + 1)
    ts = int(cooldown_ends.timestamp())
    onboard_console(member, f"⏳ new alliance [{tag}] must wait {mins} min (cooldown) — auto-resume at {cooldown_ends:%H:%M}")
    await log_event(guild, f"⏳ **ALLIANCE CREATION WAITING**\nUser: {member.mention} | Tag: [{tag}]\n"
                           f"Cooldown ends <t:{ts}:t> — I'll resume them automatically. `/release-timekeeper` lets them in sooner.")
    await gateway_channel.send(await tf(
        "⏳ {mention}, new alliances roll off the line one at a time, and one was just registered — so **[{tag}]** "
        "can be created at <t:{ts}:t> (<t:{ts}:R>). You don't need to do anything: stay here and I'll ping you "
        "right in this channel when it's time. ☕",
        member.id, mention=member.mention, tag=tag, ts=str(ts)))
    await notify_staff_dm(guild, "⏳ New alliance waiting on the cooldown",
                          f"{member.mention} wants to create **[{tag}]**. The {ALLIANCE_CREATION_COOLDOWN_MINUTES}-minute "
                          f"cooldown ends <t:{ts}:t>; they'll be picked up automatically. Run `/release-timekeeper` "
                          f"if you'd like to let them in now (then they can use `/register`).",
                          color=discord.Color.orange())
    old = _resume_tasks.pop(member.id, None)
    if old:
        old.cancel()
    _resume_tasks[member.id] = bot.loop.create_task(resume_onboarding_later(guild, member.id, delay, tag))


async def announce_onboarding_pause(member, channel):
    """A question went unanswered. Don't just go silent — say we've paused
    and how to carry on (any message in #gateway resumes them)."""
    if _member_gone(member):
        return
    onboard_console(member, "⏸️ paused — no answer in time; any message in #gateway resumes them")
    try:
        await channel.send(await tf(
            "⏸️ {mention}, I'll pause here — no rush. Whenever you're back, just type anything in this "
            "channel and we'll pick up right where you left off.",
            member.id, mention=member.mention))
    except discord.HTTPException:
        pass


_parked_resume_at = {}   # member_id -> monotonic time of the last auto-resume
_parked_staff_pinged = set()


async def handle_parked_gateway_message(message) -> bool:
    """Someone typed in #gateway while no onboarding flow is listening to
    them (it paused, stalled, or hit a cooldown). Previously these messages
    went nowhere. Now: resume their registration automatically, and ping
    staff once. Returns True if handled."""
    m = message.author
    if not isinstance(m, discord.Member) or m.id in _onboarding_in_progress or is_staff_member(m):
        return False
    member_role = discord.utils.get(m.guild.roles, name=ROLE_MEMBER)
    if member_role and member_role in m.roles:
        return False
    onboard_console(m, f"💬 typed in #gateway while paused: '{message.content.strip()[:60]}'")
    if m.id not in _parked_staff_pinged:
        _parked_staff_pinged.add(m.id)
        await log_event(m.guild, f"💬 **PAUSED REGISTRATION — MEMBER IS BACK**\n{m.mention} typed in #gateway: `{message.content.strip()[:200]}`\nI'm picking their registration back up; a friendly word from staff wouldn't hurt.")
        await notify_staff_dm(m.guild, "💬 Someone in #gateway needs a hand",
                              f"{m.mention} was stuck partway through registration and just typed in #gateway. I've restarted their registration — a quick hello there would help.",
                              color=discord.Color.orange())
    now_m = time.monotonic()
    if now_m - _parked_resume_at.get(m.id, 0) < 60:
        return True  # just resumed them a moment ago
    _parked_resume_at[m.id] = now_m
    if m.id in _resume_tasks:
        # They're waiting on the alliance cooldown — resuming now would just hit it again.
        try:
            await message.channel.send(await tf(
                "☕ {mention}, still waiting on the alliance line — I'll ping you here the moment it opens. "
                "A human has been told you're here too.", m.id, mention=m.mention))
        except discord.HTTPException:
            pass
        return True
    try:
        await message.channel.send(await tf(
            "🚔 {mention}, sorry — I'd paused your registration and wasn't listening. Picking it back up now!",
            m.id, mention=m.mention))
    except discord.HTTPException:
        pass
    bot.loop.create_task(run_onboarding_safe(m))
    return True


def _onboarding_milestones(total_timeout: float) -> list:
    """(seconds_from_start, kind) checkpoints for one onboarding wait:
    the #gateway check-in at 2 minutes (if the step is long enough for it
    to be useful), and the countdown DM at the halfway mark — nudged to
    30s after the check-in when the two would otherwise land together."""
    marks = []
    if total_timeout > ONBOARDING_CHECKIN_SECONDS + 30:
        marks.append((ONBOARDING_CHECKIN_SECONDS, "checkin"))
    half = total_timeout / 2
    if marks and abs(half - ONBOARDING_CHECKIN_SECONDS) < 30:
        half = ONBOARDING_CHECKIN_SECONDS + 30
    marks.append((half, "dm"))
    return sorted(marks)


async def wait_with_warning(member, check, total_timeout: float, warning_text: str):
    """Waits up to total_timeout seconds for a matching message in #gateway.
    After 2 minutes of silence, posts a 'still there? need help?' check-in in
    #gateway; around the halfway point, DMs a countdown warning. Raises
    asyncio.TimeoutError if they never respond — getting kicked for timeout
    is fine, they can rejoin any time and pick up exactly where they left off.

    A message that's just a cry for help ('help', '?', 'stuck'...) at ANY
    prompt is intercepted here, centrally — staff get pinged, the person
    gets reassured, and the wait simply continues for their real answer.
    It never counts as a wrong answer, because it isn't one."""
    start = time.monotonic()
    deadline = start + total_timeout
    milestones = _onboarding_milestones(total_timeout)
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0:
            if _member_gone(member):
                raise OnboardingMemberLeft()
            onboard_console(member, "⌛ timed out with no answer")
            raise asyncio.TimeoutError
        next_at = start + milestones[0][0] if milestones else deadline
        this_wait = max(0.05, min(remaining, next_at - now))
        try:
            msg = await bot.wait_for('message', check=check, timeout=this_wait)
        except asyncio.TimeoutError:
            if _member_gone(member):
                raise OnboardingMemberLeft()
            if milestones and time.monotonic() >= start + milestones[0][0] - 0.05:
                _, kind = milestones.pop(0)
                if kind == "checkin":
                    await send_onboarding_checkin(member)
                else:
                    await send_onboarding_countdown_dm(member, warning_text, int(deadline - time.monotonic()), True)
            continue
        if is_help_request(msg.content):
            onboard_console(member, f"🆘 typed '{msg.content.strip()[:40]}' — staff pinged")
            await escalate_onboarding_help(member, msg.channel)
            continue
        return msg


async def view_wait_with_warning(member, view, total_timeout: float, warning_text: str) -> bool:
    """Same check-in + countdown-DM treatment as wait_with_warning, but for a
    button-based View instead of a typed message. The view must already be
    constructed with timeout=total_timeout. Returns True if the view
    resolved (a button was actually clicked), False if it genuinely timed
    out with zero interaction — callers should kick on False, matching how
    every other onboarding step behaves on total silence."""
    start = time.monotonic()
    wait_task = asyncio.ensure_future(view.wait())
    for offset, kind in _onboarding_milestones(total_timeout):
        done, _pending = await asyncio.wait([wait_task], timeout=max(0.0, start + offset - time.monotonic()))
        if wait_task in done:
            timed_out = wait_task.result()
            return not timed_out
        if _member_gone(member):
            view.stop()
            raise OnboardingMemberLeft()
        if kind == "checkin":
            await send_onboarding_checkin(member)
        else:
            await send_onboarding_countdown_dm(member, warning_text, int(start + total_timeout - time.monotonic()), False)

    timed_out = await wait_task
    if timed_out and _member_gone(member):
        raise OnboardingMemberLeft()
    if timed_out:
        onboard_console(member, "⌛ timed out without clicking")
    return not timed_out


async def build_global_infrastructure(guild):
    print(f"\n[SYSTEM] 🕵️ Running infrastructure diagnostics for server: {guild.name}...")
    repairs = []

    restricted_perms = discord.Permissions(send_messages=False, view_channel=True)
    drunk_perms = discord.Permissions(send_messages=False, view_channel=False)

    # Golden rule: ensure_role only ever CREATES a role if it's missing.
    # It never touches color/permissions/hoist on a role that already exists —
    # that's the server admin's to customize, forever.
    member_role = await ensure_role(guild, ROLE_MEMBER, color=MEMBER_COLOR, hoist=True,
                                     why="gates access to the general server", repairs=repairs)

    # 🗺️ One role per configured game-server (default 21,121 — edit any time
    # with /configure-servers). used_server_colors keeps each one visually distinct.
    server_roles = {}
    used_server_colors = set()
    for server_num in await get_managed_servers(guild.id):
        color = get_distinct_alliance_color(used_server_colors)
        used_server_colors.add(color.value)
        server_roles[server_num] = await ensure_role(
            guild, role_name_for_server(server_num), color=color,
            why=f"tracks Chiefs playing on server {server_num}", repairs=repairs
        )

    dt_role = await ensure_role(guild, ROLE_DRUNK_TANK, color=discord.Color.dark_grey(), permissions=drunk_perms,
                                 why="quarantines new alliances pending admin approval", repairs=repairs)
    prison_role = await ensure_role(guild, ROLE_PRISONER, color=discord.Color.dark_red(), permissions=drunk_perms,
                                     why="the /imprison punishment depends on this role", repairs=repairs)
    to_role = await ensure_role(guild, ROLE_TIMEOUT, color=discord.Color.dark_red(), permissions=restricted_perms,
                                 why="fallback restriction when a kick fails", repairs=repairs)

    # NOTE: R4 and R5 are per-alliance roles ("{TAG}-R4" etc.), created on
    # demand the first time someone's actually granted that rank — nobody
    # gets one automatically, not even an alliance's founder. [TAG]-Leadership
    # is a third, quieter per-alliance role: not hoisted, no distinct color,
    # granted automatically alongside R4/R5 or handed out standalone by an
    # R5's discretion. R3 was retired — it never carried real functional
    # meaning in-game, so there was nothing worth replicating here.

    dictator_role = await ensure_role(guild, ROLE_DICTATOR, color=DICTATOR_COLOR, permissions=DICTATOR_PERMISSIONS, hoist=True,
                                       why="the top-level owner rank", repairs=repairs)
    senator_role = await ensure_role(guild, ROLE_SENATOR, color=SENATOR_COLOR, permissions=SENATOR_PERMISSIONS, hoist=True,
                                      why="senior-staff rank with channel management", repairs=repairs)
    judge_role = await ensure_role(guild, ROLE_JUDGE, color=JUDGE_COLOR, permissions=JUDGE_PERMISSIONS, hoist=True,
                                    why="moderator rank", repairs=repairs)

    # ✨ Millie, 🧵 Stitch, 🥈 Chrome — one-of-a-kind honorary badges with
    # real moderator authority. All three also hold the actual JUDGE role
    # directly (enforced in check_critical_security if it's ever missing),
    # and their OWN role is deliberately NOT hoisted — that's what makes
    # them group under the "Judge" heading in the member list instead of
    # each getting their own separate one-person heading. Position above
    # Judge in the hierarchy is what keeps their distinct color winning
    # regardless — hoist and color priority are two different mechanisms,
    # both needed together here. Colors are force-corrected every startup
    # in check_critical_security(), the one deliberate exception to the
    # golden rule.
    millie_role = await ensure_role(guild, ROLE_MILLIE, color=MILLIE_COLOR, permissions=JUDGE_PERMISSIONS, hoist=False,
                                     why="the honorary moderator role", repairs=repairs)
    stitch_role = await ensure_role(guild, ROLE_STITCH, color=STITCH_COLOR, permissions=JUDGE_PERMISSIONS, hoist=False,
                                     why="the honorary moderator role", repairs=repairs)
    chrome_role = await ensure_role(guild, ROLE_CHROME, color=CHROME_COLOR, permissions=JUDGE_PERMISSIONS, hoist=False,
                                     why="the honorary moderator role", repairs=repairs)
    silent_role = await ensure_role(guild, ROLE_SILENT, color=SILENT_COLOR, permissions=JUDGE_PERMISSIONS, hoist=False,
                                     why="the honorary moderator role", repairs=repairs)

    # 🌟 Innovator — purely cosmetic badge for early testers, no permissions
    # attached at all.
    innovator_role = await ensure_role(guild, ROLE_INNOVATOR, color=INNOVATOR_COLOR, hoist=True,
                                        why="the early-tester badge", repairs=repairs)

    # The owner is "the Dictator" by definition — hand them the crown automatically.
    if guild.owner and dictator_role not in guild.owner.roles:
        try:
            await guild.owner.add_roles(dictator_role, reason="Auto-assigning DICTATOR to server owner.")
            repairs.append(f"👑 Handed the DICTATOR crown to {guild.owner.mention} (the server owner) — welcome to absolute power.")
        except discord.Forbidden:
            pass

    admin_cat = discord.utils.get(guild.categories, name="Admin-Only")
    if not admin_cat:
        admin_cat = await guild.create_category("Admin-Only")
        repairs.append("🗄️ Category **Admin-Only** didn't exist — recreated to house #gateway and #logs.")
    await admin_cat.set_permissions(guild.default_role, read_messages=False, view_channel=False)
    for staff_role in (judge_role, stitch_role, millie_role, chrome_role, silent_role, senator_role, dictator_role):
        await admin_cat.set_permissions(staff_role, view_channel=True, read_messages=True, send_messages=True)

    gateway_ch = discord.utils.get(guild.channels, name="gateway")
    if not gateway_ch:
        await guild.create_text_channel("gateway", category=admin_cat, overwrites={guild.default_role: discord.PermissionOverwrite(read_messages=False, view_channel=False)})
        repairs.append("🚪 Channel **#gateway** didn't exist — recreated it, since onboarding runs there.")
    else:
        await gateway_ch.set_permissions(guild.default_role, read_messages=False, view_channel=False)

    if not discord.utils.get(guild.channels, name="logs"):
        await guild.create_text_channel("logs", category=admin_cat)
        repairs.append("📝 Channel **#logs** didn't exist — recreated it (you're reading this in it now).")

    if not discord.utils.get(guild.channels, name="visitors"):
        await guild.create_text_channel("visitors", category=admin_cat)
        repairs.append("🚪 Channel **#visitors** didn't exist — recreated it (tracks who comes and goes, and why).")

    if not discord.utils.get(guild.channels, name="latest-version"):
        await guild.create_text_channel("latest-version", category=admin_cat)
        repairs.append("🆕 Channel **#latest-version** didn't exist — recreated it (inconsistencies found after an update get logged here).")

    # ------------------------------------------------------------
    #  📌 POLICE CHIEF INFO — announcements, rules, bugs, suggestions.
    #  Matched fuzzily (substring, not exact name) since this category and
    #  its announcements/rules channels commonly already exist on an
    #  adopted server under slightly different naming than our canonical
    #  one — the goal here is finding and fixing what's there, not
    #  duplicating it. #bugs and #suggestions are new additions that go in
    #  the same category. The "read only" marker moves from the category
    #  name onto just the two channels that are actually read-only —
    #  #bugs and #suggestions are meant to be posted in, so a blanket
    #  read-only label on the whole category would be misleading.
    # ------------------------------------------------------------
    info_cat = discord.utils.find(lambda c: "POLICE CHIEF INFO" in c.name.upper(), guild.categories)
    if not info_cat:
        info_cat = await guild.create_category("📌 POLICE CHIEF INFO")
        repairs.append("🗄️ Category **📌 POLICE CHIEF INFO** didn't exist — created it.")
    elif "READ" in info_cat.name.upper() and "ONLY" in info_cat.name.upper():
        old_cat_name = info_cat.name
        try:
            await info_cat.edit(name="📌 POLICE CHIEF INFO")
            repairs.append(
                f"✏️ Renamed category **{old_cat_name}** → **📌 POLICE CHIEF INFO** — the read-only marker now lives "
                "on #🔒-announcements and #🔒-rules specifically, not the whole category, since #bugs and #suggestions live here too."
            )
        except discord.Forbidden:
            pass

    info_ro_overwrites = {
        guild.default_role: discord.PermissionOverwrite(view_channel=True, send_messages=False),
        judge_role: discord.PermissionOverwrite(send_messages=True),
        senator_role: discord.PermissionOverwrite(send_messages=True),
        dictator_role: discord.PermissionOverwrite(send_messages=True),
    }
    announcements_ch = discord.utils.find(
        lambda c: isinstance(c, discord.TextChannel) and "announce" in c.name.lower(), guild.channels
    )
    if not announcements_ch:
        await guild.create_text_channel("🔒-announcements", category=info_cat, overwrites=info_ro_overwrites)
        repairs.append("📢 Channel **#🔒-announcements** didn't exist — created it (everyone can read, only staff can post).")
    else:
        if announcements_ch.category_id != info_cat.id:
            try:
                await announcements_ch.edit(category=info_cat)
            except discord.Forbidden:
                pass
        await announcements_ch.set_permissions(guild.default_role, view_channel=True, send_messages=False)
        for staff_role in (judge_role, senator_role, dictator_role):
            await announcements_ch.set_permissions(staff_role, send_messages=True)

    rules_ch = discord.utils.find(
        lambda c: isinstance(c, discord.TextChannel) and "rule" in c.name.lower(), guild.channels
    )
    if not rules_ch:
        await guild.create_text_channel("🔒-rules", category=info_cat, overwrites=info_ro_overwrites)
        repairs.append("📜 Channel **#🔒-rules** didn't exist — created it (everyone can read, only staff can post).")
    else:
        if rules_ch.category_id != info_cat.id:
            try:
                await rules_ch.edit(category=info_cat)
            except discord.Forbidden:
                pass
        await rules_ch.set_permissions(guild.default_role, view_channel=True, send_messages=False)
        for staff_role in (judge_role, senator_role, dictator_role):
            await rules_ch.set_permissions(staff_role, send_messages=True)

    # 🐛 #bugs and 💡 #suggestions — the opposite of read-only: any
    # registered Member can post here. Anything posted gets mirrored to
    # #logs (see on_message) so staff can act on it without needing to
    # also watch these channels directly.
    feedback_overwrites = {
        guild.default_role: discord.PermissionOverwrite(view_channel=False),
        member_role: discord.PermissionOverwrite(view_channel=True, send_messages=True),
    }
    if not discord.utils.get(guild.channels, name="🐛-bugs"):
        await guild.create_text_channel("🐛-bugs", category=info_cat, overwrites=feedback_overwrites)
        repairs.append("🐛 Channel **#🐛-bugs** didn't exist — created it (posts here mirror to #logs automatically).")
    if not discord.utils.get(guild.channels, name="💡-suggestions"):
        await guild.create_text_channel("💡-suggestions", category=info_cat, overwrites=feedback_overwrites)
        repairs.append("💡 Channel **#💡-suggestions** didn't exist — created it (posts here mirror to #logs automatically).")

    roles_cat = discord.utils.get(guild.categories, name="📌 ROLES & REQUESTS")
    if not roles_cat:
        roles_cat = await guild.create_category("📌 ROLES & REQUESTS")
        repairs.append("🗄️ Category **📌 ROLES & REQUESTS** didn't exist — recreated it.")

    role_req_ch = discord.utils.get(guild.channels, name="⚙️-role-requests")
    if not role_req_ch:
        r_overwrites = {
            guild.default_role: discord.PermissionOverwrite(view_channel=True, send_messages=False),
            member_role: discord.PermissionOverwrite(view_channel=True, send_messages=True)
        }
        await guild.create_text_channel("⚙️-role-requests", category=roles_cat, overwrites=r_overwrites)
        repairs.append("⚙️ Channel **#⚙️-role-requests** didn't exist — recreated it (this is where R5 petitions get filed).")

    # 🎓 The abilities channel — a member's personal cheat-sheet on demand.
    abilities_ch = discord.utils.get(guild.channels, name="❓-abilities")
    abilities_just_created = False
    if not abilities_ch:
        ab_overwrites = {
            guild.default_role: discord.PermissionOverwrite(view_channel=True, send_messages=False),
            guild.me: discord.PermissionOverwrite(view_channel=True, send_messages=True),
        }
        abilities_ch = await guild.create_text_channel("❓-abilities", category=roles_cat, overwrites=ab_overwrites)
        abilities_just_created = True
        repairs.append("❓ Channel **#❓-abilities** didn't exist — recreated it and pinned the instructions.")
    try:
        await sync_abilities_channel_reference(guild, abilities_ch)
    except Exception as e:
        print(f"[ERROR] Failed to sync #❓-abilities command reference: {e}")

    main_text_cat = discord.utils.get(guild.categories, name="🏢 MAIN PRECINCT")
    if not main_text_cat:
        main_text_cat = await guild.create_category("🏢 MAIN PRECINCT")
        repairs.append("🗄️ Category **🏢 MAIN PRECINCT** didn't exist — recreated it.")

    # ↩️ Reverting the earlier landing-zone experiment: if a previous run
    # already renamed #💬-general-chat to #🛬-landing-zone, rename it back
    # and restore its original unlocked permissions.
    renamed_back = discord.utils.get(guild.channels, name="🛬-landing-zone")
    if renamed_back and not discord.utils.get(guild.channels, name="💬-general-chat"):
        try:
            await renamed_back.edit(name="💬-general-chat")
            repairs.append("↩️ Reverted **#🛬-landing-zone** back to **#💬-general-chat**, unlocked, as originally intended.")
        except discord.Forbidden:
            pass

    gen_overwrites = {
        guild.default_role: discord.PermissionOverwrite(view_channel=False),
        member_role: discord.PermissionOverwrite(view_channel=True),
        dt_role: discord.PermissionOverwrite(view_channel=False),
        prison_role: discord.PermissionOverwrite(view_channel=False),
        to_role: discord.PermissionOverwrite(view_channel=False)
    }
    general_chat_ch = discord.utils.get(guild.channels, name="💬-general-chat")
    if not general_chat_ch:
        general_chat_ch = await guild.create_text_channel("💬-general-chat", category=main_text_cat, overwrites=gen_overwrites)
        repairs.append("💬 Channel **#💬-general-chat** didn't exist — recreated it.")
    else:
        # In case it got locked by the reverted feature, restore the simple
        # original overwrite (view-only was never the intent here).
        member_ow = general_chat_ch.overwrites_for(member_role)
        if member_ow.send_messages is False:
            await general_chat_ch.set_permissions(member_role, overwrite=discord.PermissionOverwrite(view_channel=True))
            repairs.append("↩️ **#💬-general-chat** was locked down by the reverted feature — restored normal chat access.")

    # 🌟 Innovator-only lounge — visible to badge holders plus staff, a
    # dedicated space for suggestions and issues away from general chat.
    innovator_lounge_overwrites = {
        guild.default_role: discord.PermissionOverwrite(view_channel=False),
        innovator_role: discord.PermissionOverwrite(view_channel=True),
        judge_role: discord.PermissionOverwrite(view_channel=True),
        senator_role: discord.PermissionOverwrite(view_channel=True),
        dictator_role: discord.PermissionOverwrite(view_channel=True),
        stitch_role: discord.PermissionOverwrite(view_channel=True),
        millie_role: discord.PermissionOverwrite(view_channel=True),
        chrome_role: discord.PermissionOverwrite(view_channel=True),
        silent_role: discord.PermissionOverwrite(view_channel=True),
    }
    if not discord.utils.get(guild.channels, name="🌟-innovator-lounge"):
        await guild.create_text_channel("🌟-innovator-lounge", category=main_text_cat, overwrites=innovator_lounge_overwrites)
        repairs.append("🌟 Channel **#🌟-innovator-lounge** didn't exist — created it (Innovator badge holders + staff only).")

    if not await get_guild_setting(guild.id, "chase_info_posted"):
        try:
            chase_intro = await general_chat_ch.send(embed=discord.Embed(
                title="🕵️ ABOUT COPS & ROBBERS",
                description=(
                    "Every day at noon, this server runs a secret game: some of you become **cops**, some "
                    "become **robbers** — nobody knows who's who, not even each other's side. Cops get "
                    "poetic clues every hour; robbers just have to survive six hours, or strike first.\n\n"
                    "You'll get a DM if you're picked. Not interested? `/leave-chase` opts you out any time. "
                    "Curious how you're doing? `/chase-status`.\n\n"
                    "That's it — no spoilers here. Just keep an eye on this channel."
                ),
                color=discord.Color.dark_purple()
            ))
            await chase_intro.pin()
            await set_guild_setting(guild.id, "chase_info_posted", "1")
        except discord.HTTPException:
            pass

    for server_num, srv_role in server_roles.items():
        p_overwrites = {
            guild.default_role: discord.PermissionOverwrite(view_channel=False),
            srv_role: discord.PermissionOverwrite(view_channel=True),
            dt_role: discord.PermissionOverwrite(view_channel=False),
            prison_role: discord.PermissionOverwrite(view_channel=False),
            to_role: discord.PermissionOverwrite(view_channel=False)
        }
        precinct_name = f"🏙️-precinct-{server_num}"
        if not discord.utils.get(guild.channels, name=precinct_name):
            await guild.create_text_channel(precinct_name, category=main_text_cat, overwrites=p_overwrites)
            repairs.append(f"🏙️ Channel **#{precinct_name}** didn't exist — recreated it.")

    main_comms_cat = discord.utils.get(guild.categories, name="🔊 MAIN PRECINCT COMMS")
    if not main_comms_cat:
        main_comms_cat = await guild.create_category("🔊 MAIN PRECINCT COMMS")
        repairs.append("🗄️ Category **🔊 MAIN PRECINCT COMMS** didn't exist — recreated it.")

    if not discord.utils.get(guild.channels, name="🎙️-watercooler-1"):
        watercooler_overwrites = {
            guild.default_role: discord.PermissionOverwrite(view_channel=False),
            member_role: discord.PermissionOverwrite(view_channel=True),
            dt_role: discord.PermissionOverwrite(view_channel=False),
            prison_role: discord.PermissionOverwrite(view_channel=False),
            to_role: discord.PermissionOverwrite(view_channel=False)
        }
        await guild.create_voice_channel("🎙️-watercooler-1", category=main_comms_cat, overwrites=watercooler_overwrites)
        await guild.create_voice_channel("🎙️-watercooler-2", category=main_comms_cat, overwrites=watercooler_overwrites)
        await guild.create_voice_channel("🎙️-watercooler-3", category=main_comms_cat, overwrites=watercooler_overwrites)
        repairs.append("🎙️ The watercooler voice channels were missing — recreated them.")

    for server_num, srv_role in server_roles.items():
        p_overwrites = {
            guild.default_role: discord.PermissionOverwrite(view_channel=False),
            srv_role: discord.PermissionOverwrite(view_channel=True),
            dt_role: discord.PermissionOverwrite(view_channel=False),
            prison_role: discord.PermissionOverwrite(view_channel=False),
            to_role: discord.PermissionOverwrite(view_channel=False)
        }
        car_a, car_b = f"🍩-patrol-car-{server_num}-a", f"🍩-patrol-car-{server_num}-b"
        if not discord.utils.get(guild.channels, name=car_a):
            await guild.create_voice_channel(car_a, category=main_comms_cat, overwrites=p_overwrites)
            await guild.create_voice_channel(car_b, category=main_comms_cat, overwrites=p_overwrites)
            repairs.append(f"🍩 Patrol-car voice channels for server {server_num} were missing — recreated them.")

    prison_cat = discord.utils.get(guild.categories, name="⛓️ MAX SECURITY")
    if not prison_cat:
        prison_cat = await guild.create_category("⛓️ MAX SECURITY")
        repairs.append("🗄️ Category **⛓️ MAX SECURITY** didn't exist — recreated it.")

    if not discord.utils.get(guild.channels, name="⛓️-solitary-confinement"):
        p_overwrites = {
            guild.default_role: discord.PermissionOverwrite(view_channel=False),
            prison_role: discord.PermissionOverwrite(view_channel=True, send_messages=True)
        }
        await guild.create_text_channel("⛓️-solitary-confinement", category=prison_cat, overwrites=p_overwrites)
        repairs.append("⛓️ Channel **#⛓️-solitary-confinement** didn't exist — recreated it (someone was about to have a very confusing sentence).")

    await enforce_role_hierarchy(guild)
    print("[SYSTEM] ✅ Infrastructure diagnostics complete. 100% Operational.\n")
    return repairs


# ============================================================
#  UI VIEWS
# ============================================================
class LanguageSelect(discord.ui.Select):
    def __init__(self, member):
        self.member = member
        options = [
            discord.SelectOption(label="English", value="en", emoji="🇬🇧"),
            discord.SelectOption(label="Russian", value="ru", emoji="🇷🇺"),
            discord.SelectOption(label="German", value="de", emoji="🇩🇪"),
            discord.SelectOption(label="Spanish", value="es", emoji="🇪🇸"),
            discord.SelectOption(label="French", value="fr", emoji="🇫🇷"),
            discord.SelectOption(label="Arabic", value="ar", emoji="🇸🇦"),
            discord.SelectOption(label="Hindi", value="hi", emoji="🇮🇳"),
            discord.SelectOption(label="Portuguese", value="pt", emoji="🇵🇹"),
            discord.SelectOption(label="Mandarin", value="zh-CN", emoji="🇨🇳"),
            discord.SelectOption(label="Japanese", value="ja", emoji="🇯🇵"),
            discord.SelectOption(label="Korean", value="ko", emoji="🇰🇷"),
        ]
        super().__init__(placeholder="Choose your preferred language...", min_values=1, max_values=1, options=options)

    async def callback(self, interaction: discord.Interaction):
        if interaction.user != self.member:
            await interaction.response.send_message("This menu is not for you!", ephemeral=True)
            return

        selected_lang = self.values[0]
        async with db_connect() as conn:
            cursor = await conn.cursor()
            await cursor.execute("UPDATE users SET pref_lang = ? WHERE user_id = ?", (selected_lang, self.member.id))
            await conn.commit()

        confirmation = await translate_text(
            "✅ Language saved! From here on, I'll do my best to talk to you in this language.\n\n"
            "🌍 **TUTORIAL:** If you ever need to read a message in this server, simply react to it with a 🌐 "
            "and I will privately DM you the translation.\n\n"
            "Let's keep going with the rest of your registration below.",
            selected_lang
        )
        await interaction.response.edit_message(
            content=confirmation or "✅ Language saved! Let's keep going with the rest of your registration below.",
            view=None
        )
        self.view.stop()


class LanguageView(discord.ui.View):
    def __init__(self, member, timeout: float = 600.0):
        super().__init__(timeout=timeout)
        self.add_item(LanguageSelect(member))
        self.member = member


# A curated set of common UTC offsets rather than a full IANA city list —
# "pretty simple" per the request. Stored as a signed float (hours), which
# makes computing "how far is this from server time" trivial arithmetic
# without needing a timezone database lookup for the USER's side at all —
# only the server's own configured timezone needs real ZoneInfo handling.
TIMEZONE_OFFSET_CHOICES = [
    ("UTC-10 (Hawaii)", -10.0), ("UTC-9 (Alaska)", -9.0), ("UTC-8 (Pacific)", -8.0),
    ("UTC-7 (Mountain)", -7.0), ("UTC-6 (Central)", -6.0), ("UTC-5 (Eastern)", -5.0),
    ("UTC-4 (Atlantic)", -4.0), ("UTC-3 (Brazil/Argentina)", -3.0), ("UTC+0 (UK/Ireland)", 0.0),
    ("UTC+1 (Central Europe)", 1.0), ("UTC+2 (Eastern Europe)", 2.0), ("UTC+3 (Moscow/East Africa)", 3.0),
    ("UTC+3:30 (Iran)", 3.5), ("UTC+4 (Gulf)", 4.0), ("UTC+5 (Pakistan)", 5.0),
    ("UTC+5:30 (India)", 5.5), ("UTC+6 (Bangladesh)", 6.0), ("UTC+7 (Thailand/Vietnam)", 7.0),
    ("UTC+8 (China/Singapore)", 8.0), ("UTC+9 (Japan/Korea)", 9.0), ("UTC+9:30 (Central Australia)", 9.5),
    ("UTC+10 (Eastern Australia)", 10.0), ("UTC+12 (New Zealand)", 12.0),
]


class TimezoneSelect(discord.ui.Select):
    def __init__(self, member):
        self.member = member
        options = [discord.SelectOption(label=label, value=str(offset)) for label, offset in TIMEZONE_OFFSET_CHOICES]
        super().__init__(placeholder="Choose your approximate time zone...", min_values=1, max_values=1, options=options)

    async def callback(self, interaction: discord.Interaction):
        if interaction.user != self.member:
            await interaction.response.send_message("This isn't your choice to make.", ephemeral=True)
            return

        offset = float(self.values[0])
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("UPDATE users SET pref_timezone = ? WHERE user_id = ?", (str(offset), self.member.id))
            await conn.commit()

        server_tz = await get_guild_timezone(interaction.guild.id)
        server_now = datetime.now(server_tz)
        diff = offset - (server_now.utcoffset().total_seconds() / 3600)
        if abs(diff) < 0.01:
            diff_text = "the same as the server's."
        else:
            direction = "ahead of" if diff > 0 else "behind"
            diff_text = f"**{abs(diff):g} hour(s) {direction}** the server."

        confirmation = await tf(
            "✅ Got it — this server currently runs on **{tzname}** (right now it's **{time}** there), which is {diff} "
            "I'll keep this in mind for anything time-related.",
            self.member.id,
            tzname=server_tz.tzname(server_now) or "server time",
            time=server_now.strftime("%I:%M %p").lstrip("0"),
            diff=diff_text
        )
        await interaction.response.edit_message(content=confirmation, view=None)
        self.view.stop()


class TimezoneView(discord.ui.View):
    """Optional and informational, not a mandatory gate — if someone
    doesn't respond, pref_timezone just stays unset and nothing blocks or
    kicks them over it. It's a nice-to-know, not a checkpoint."""
    def __init__(self, member):
        super().__init__(timeout=180.0)
        self.add_item(TimezoneSelect(member))


class NicknameOnboardSelect(discord.ui.Select):
    def __init__(self, member, existing_nicks, current_name):
        self.member = member
        self._existing_map = dict(existing_nicks)
        options = [discord.SelectOption(label=f"Server {s}: {n}"[:100], value=s) for s, n in existing_nicks[:24]]
        options.append(discord.SelectOption(label=f"Keep what I just typed: {current_name}"[:100], value="__keep__"))
        super().__init__(placeholder="Choose your display name...", min_values=1, max_values=1, options=options)

    async def callback(self, interaction: discord.Interaction):
        if interaction.user != self.member:
            await interaction.response.send_message("This isn't your choice to make.", ephemeral=True)
            return
        value = self.values[0]
        if value != "__keep__":
            self.view.chosen_server = value
            self.view.chosen_name = self._existing_map[value]
        await interaction.response.edit_message(content="✅ Got it.", view=None)
        self.view.stop()


class NicknameOnboardChoiceView(discord.ui.View):
    """Non-blocking and entirely optional — offered the moment someone
    selects 2+ servers during onboarding if we already have stored
    nicknames for any of them. No penalty for ignoring it; whatever they
    just typed stays the default if they never respond."""
    def __init__(self, member, existing_nicks, current_name):
        super().__init__(timeout=120.0)
        self.chosen_name = None
        self.chosen_server = None
        self.add_item(NicknameOnboardSelect(member, existing_nicks, current_name))


class TestServerDisclaimerView(discord.ui.View):
    """A single mandatory acknowledgment — this is a test server and
    everything could be wiped within 7 days. Same 'timeout means kick,
    but with a halfway warning first' treatment as every other onboarding
    step, via view_wait_with_warning."""
    def __init__(self, member):
        super().__init__(timeout=240.0)
        self.member = member
        self.acknowledged = False

    @discord.ui.button(label="I Understand — Let's Go", style=discord.ButtonStyle.success, emoji="✅")
    async def acknowledge(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user != self.member:
            await interaction.response.send_message("This isn't your confirmation to click.", ephemeral=True)
            return
        self.acknowledged = True
        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(content="✅ Got it — thank you for testing with us!", view=self)
        self.stop()


class TagConfirmView(discord.ui.View):
    def __init__(self, member, tag):
        super().__init__(timeout=240.0)
        self.member = member
        self.tag = tag
        self.result = None

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        return interaction.user == self.member

    @discord.ui.button(label="Yes, it's correct! I checked.", style=discord.ButtonStyle.success)
    async def confirm(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.result = "confirm"
        await interaction.response.edit_message(content=f"Tag **[{self.tag}]** confirmed. Checking the roster...", view=None)
        self.stop()

    @discord.ui.button(label="Oops, no that's wrong, I need to enter it again.", style=discord.ButtonStyle.secondary)
    async def retry(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.result = "retry"
        await interaction.response.edit_message(content="No problem. Let's try that again.", view=None)
        self.stop()

    @discord.ui.button(label="Whoops? I don't even know how I got here?", style=discord.ButtonStyle.danger)
    async def trap(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.result = "trap"
        await interaction.response.edit_message(content="Initiating 60-second emergency cool-off...", view=None)
        self.stop()


class UndoActionView(discord.ui.View):
    """Persistent view (timeout=None) attached to ban/kick/imprison log embeds.
    Survives bot restarts because we re-register one of these per outstanding
    log entry in restore_persistent_views()."""

    def __init__(self, log_id: int, action_type: str):
        super().__init__(timeout=None)
        self.log_id = log_id
        self.action_type = action_type
        meta = ACTION_META.get(action_type, {})
        button = discord.ui.Button(
            label=meta.get("button_label", "Undo"),
            style=meta.get("button_style", discord.ButtonStyle.secondary),
            custom_id=f"rc_undo_{action_type}_{log_id}"
        )
        button.callback = self.on_click
        self.add_item(button)

    async def on_click(self, interaction: discord.Interaction):
        if not is_staff_member(interaction.user):
            await interaction.response.send_message("❌ You need Judge rank or higher to do that.", ephemeral=True)
            return
        await handle_undo_action(interaction, self.log_id, self.action_type)


class ConfirmWipeView(discord.ui.View):
    """Short-lived (60s) second step before an irreversible users-table wipe.
    Not persistent on purpose — if the bot restarts mid-confirmation, the
    button just goes stale rather than risking a wipe firing unattended."""

    def __init__(self):
        super().__init__(timeout=60)
        confirm_btn = discord.ui.Button(label="💀 Confirm — Wipe Everything", style=discord.ButtonStyle.danger)
        cancel_btn = discord.ui.Button(label="Cancel", style=discord.ButtonStyle.secondary)
        confirm_btn.callback = self.on_confirm
        cancel_btn.callback = self.on_cancel
        self.add_item(confirm_btn)
        self.add_item(cancel_btn)

    async def on_confirm(self, interaction: discord.Interaction):
        if not is_dictator_member(interaction.user):
            await interaction.response.send_message("❌ DICTATOR rank only.", ephemeral=True)
            return

        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT COUNT(*) FROM users")
            count = (await cur.fetchone())[0]
            await cur.execute("DELETE FROM users")
            await cur.execute("DELETE FROM capability_notifications")
            await conn.commit()

        embed = discord.Embed(
            title="🗑️ USERS DATABASE WIPED",
            description=f"{count} registration record(s) permanently erased by {interaction.user.mention}.\n\n"
                        f"Alliances, mod-log, warnings, and bans were **not** touched.",
            color=discord.Color.dark_red(),
            timestamp=datetime.now()
        )
        await interaction.response.edit_message(embed=embed, view=None)
        await log_event(interaction.guild, f"🗑️ **USERS DATABASE WIPED**\nBy: {interaction.user.mention}\nRecords erased: {count}")

    async def on_cancel(self, interaction: discord.Interaction):
        panel_embed = discord.Embed(
            title="🛠️ DATABASE TOOLS",
            description=(
                "🔓 **Release Current Prisoner(s)** — immediately frees anyone currently serving time.\n\n"
                "🗑️ **Reset Users Database** — permanently wipes every member's registration record "
                "(name, tag, rank, server, strikes). Alliances, mod-log, warnings, and bans are **not** touched."
            ),
            color=discord.Color.dark_gold()
        )
        await interaction.response.edit_message(embed=panel_embed, view=DatabaseToolsView())


class DatabaseToolsView(discord.ui.View):
    """Dictator-only utility panel posted to #logs via /database-tools.
    Persistent — one posting stays usable indefinitely."""

    def __init__(self):
        super().__init__(timeout=None)
        release_btn = discord.ui.Button(
            label="🔓 Release Current Prisoner(s)", style=discord.ButtonStyle.success,
            custom_id="rc_dbtools_release"
        )
        reset_btn = discord.ui.Button(
            label="🗑️ Reset Users Database", style=discord.ButtonStyle.danger,
            custom_id="rc_dbtools_reset"
        )
        release_btn.callback = self.on_release
        reset_btn.callback = self.on_reset
        self.add_item(release_btn)
        self.add_item(reset_btn)

    async def on_release(self, interaction: discord.Interaction):
        if not is_dictator_member(interaction.user):
            await interaction.response.send_message("❌ DICTATOR rank only.", ephemeral=True)
            return

        prison_role = discord.utils.get(interaction.guild.roles, name=ROLE_PRISONER)
        if not prison_role or not prison_role.members:
            await interaction.response.send_message("ℹ️ Nobody is currently imprisoned.", ephemeral=True)
            return

        released = 0
        for member in list(prison_role.members):
            await execute_release(member, prison_role)
            released += 1

        await interaction.response.send_message(f"🔓 Released {released} prisoner(s).", ephemeral=True)

    async def on_reset(self, interaction: discord.Interaction):
        if not is_dictator_member(interaction.user):
            await interaction.response.send_message("❌ DICTATOR rank only.", ephemeral=True)
            return

        confirm_embed = discord.Embed(
            title="⚠️ FINAL WARNING",
            description=(
                "This permanently erases **every** member's registration record — in-game name, alliance tag, "
                "rank, server, strikes. This does **not** touch alliances, mod-log, warnings, or bans.\n\n"
                "**This cannot be undone.**"
            ),
            color=discord.Color.red()
        )
        await interaction.response.edit_message(embed=confirm_embed, view=ConfirmWipeView())


class RoleOrderFixView(discord.ui.View):
    """Persistent button offered when the role hierarchy is out of order or a
    default role has been deleted. Re-runs the full non-destructive
    infrastructure pass — creates anything missing, re-sorts the hierarchy —
    but only when a Senator+ actually clicks it, never on its own."""

    def __init__(self):
        super().__init__(timeout=None)
        btn = discord.ui.Button(
            label="🔧 Fix Order & Recreate Missing",
            style=discord.ButtonStyle.primary,
            custom_id="rc_fix_role_hierarchy"
        )
        btn.callback = self.on_fix
        self.add_item(btn)

    async def on_fix(self, interaction: discord.Interaction):
        if not is_senior_staff_member(interaction.user):
            await interaction.response.send_message("❌ You need Senator rank or higher to do that.", ephemeral=True)
            return

        await interaction.response.send_message("🔧 Running a full infrastructure pass now...", ephemeral=True)
        await build_global_infrastructure(interaction.guild)
        await interaction.followup.send("✅ Done — missing roles/channels recreated, hierarchy re-sorted.", ephemeral=True)

        original_embed = interaction.message.embeds[0] if interaction.message.embeds else None
        if original_embed:
            original_embed.add_field(name="Status", value=f"✅ Fixed by {interaction.user.mention}", inline=False)
            original_embed.color = discord.Color.green()
            try:
                await interaction.message.edit(embed=original_embed, view=None)
            except discord.HTTPException:
                pass


class NicknameFixView(discord.ui.View):
    """One button per flagged member in a nickname-compliance batch (up to
    10 per view/message). Clicking a button renames just that member to
    their computed correct nickname and disables that button."""

    def __init__(self, fixes: list):
        # fixes: list of (user_id, expected_nickname, display_index) tuples
        super().__init__(timeout=1800)
        for user_id, expected, index in fixes:
            btn = discord.ui.Button(label=f"Fix #{index}", style=discord.ButtonStyle.success, custom_id=f"rc_nickfix_{user_id}_{index}")
            btn.callback = self._make_callback(user_id, expected, index, btn)
            self.add_item(btn)

    def _make_callback(self, user_id: int, expected: str, index: int, button: discord.ui.Button):
        async def callback(interaction: discord.Interaction):
            if not is_staff_member(interaction.user):
                await interaction.response.send_message("❌ You need Judge rank or higher to do that.", ephemeral=True)
                return

            member = interaction.guild.get_member(user_id)
            if not member:
                await interaction.response.send_message(f"⚠️ The member for Fix #{index} is no longer in the server.", ephemeral=True)
                return

            try:
                await member.edit(nick=expected[:32])
            except discord.Forbidden:
                await interaction.response.send_message(f"❌ I lack permission to rename {member.mention} (role hierarchy).", ephemeral=True)
                return

            button.disabled = True
            button.label = f"✅ Fixed #{index}"
            await interaction.response.edit_message(view=self)
            await log_event(interaction.guild, f"✏️ **NICKNAME FIXED**\nStaff: {interaction.user.mention}\nMember: {member.mention}\nNew nickname: {expected[:32]}")
        return callback


class BulkAutoRegisterView(discord.ui.View):
    """Static persistent button on the startup diagnostic — attempts to
    auto-register every currently-unregistered member whose nickname
    matches our format, all in one click. Re-scans fresh at click time
    rather than trusting the list shown when the embed was first posted.
    Also carries a second button, specific to this server's PTD adoption:
    a genuinely one-click way to register EVERYONE as [PTD] (21) and fix
    their nicknames, for exactly the situations where typing a slash
    command correctly has been the actual point of failure."""

    def __init__(self):
        super().__init__(timeout=None)
        btn = discord.ui.Button(
            label="🪪 Auto-Register Everyone I Can",
            style=discord.ButtonStyle.primary,
            custom_id="rc_bulk_autoregister"
        )
        btn.callback = self.on_click
        self.add_item(btn)

        ptd_btn = discord.ui.Button(
            label="🚔 Convert Everyone + Migrate Ranks (PTD/21)",
            style=discord.ButtonStyle.danger,
            custom_id="rc_ptd_instant_convert"
        )
        ptd_btn.callback = self.on_ptd_click
        self.add_item(ptd_btn)

        legacy_btn = discord.ui.Button(
            label="🎖️ Migrate Legacy Ranks Now",
            style=discord.ButtonStyle.secondary,
            custom_id="rc_ptd_legacy_migrate"
        )
        legacy_btn.callback = self.on_legacy_click
        self.add_item(legacy_btn)

    async def on_legacy_click(self, interaction: discord.Interaction):
        if not is_dictator_member(interaction.user):
            await interaction.response.send_message("❌ Dictator only for this one.", ephemeral=True)
            return

        await interaction.response.send_message("🎖️ Migrating legacy ranks now — R4/R5 → PTD-R4/PTD-R5, R2/R3 → plain PTD membership, Admin → Dictator.", ephemeral=True)
        guild = interaction.guild
        tag = "PTD"
        admin_candidates, rank_candidates = await scan_legacy_roles(guild)
        dictator_role = discord.utils.get(guild.roles, name=ROLE_DICTATOR)
        member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)
        tag_role = discord.utils.get(guild.roles, name=tag)
        lines = []

        for role in admin_candidates:
            count = 0
            for m in [mm for mm in role.members if not mm.bot]:
                if dictator_role:
                    try:
                        await m.add_roles(dictator_role, reason="PTD legacy migration: Admin -> Dictator.")
                        count += 1
                    except discord.HTTPException:
                        pass
            async with db_connect() as conn:
                cur = await conn.cursor()
                await cur.execute("INSERT OR IGNORE INTO legacy_roles_tracked (guild_id, role_name, mapped_to) VALUES (?, ?, ?)", (guild.id, role.name, "DICTATOR"))
                await conn.commit()
            lines.append(f"👑 **{role.name}** ({count} holder(s)) → DICTATOR")

        for role, tier in rank_candidates:
            human_members = [m for m in role.members if not m.bot]
            count = 0
            if tier >= 4:
                rank_name = f"R{tier}"
                for m in human_members:
                    try:
                        await grant_alliance_rank(guild, m, tag, rank_name)
                        count += 1
                    except Exception:
                        pass
                mapped_to = f"{tag}-{rank_name}"
            else:
                for m in human_members:
                    roles_to_add = [r for r in (tag_role, member_role) if r and r not in m.roles]
                    if roles_to_add:
                        try:
                            await m.add_roles(*roles_to_add, reason="PTD legacy migration.")
                            count += 1
                        except discord.HTTPException:
                            pass
                    else:
                        count += 1
                mapped_to = f"{tag} (member)"
            async with db_connect() as conn:
                cur = await conn.cursor()
                await cur.execute("INSERT OR IGNORE INTO legacy_roles_tracked (guild_id, role_name, mapped_to) VALUES (?, ?, ?)", (guild.id, role.name, mapped_to))
                await conn.commit()
            lines.append(f"🎖️ **{role.name}** ({count} holder(s)) → {mapped_to}")

        if not lines:
            summary = "Nothing found to migrate — every legacy role is already empty or already handled."
        else:
            summary = "\n".join(lines) + "\n\nOnce you've confirmed this looks right, the old roles are now safe to delete."
        await send_long(interaction.followup, f"🎖️ **Legacy rank migration complete.**\n\n{summary}", ephemeral=True)
        await log_event(guild, f"🎖️ **PTD LEGACY RANK MIGRATION** by {interaction.user.mention}\n{summary}")

    async def on_ptd_click(self, interaction: discord.Interaction):
        if not is_dictator_member(interaction.user):
            await interaction.response.send_message("❌ Dictator only for this one.", ephemeral=True)
            return

        await interaction.response.send_message("🚔 Converting everyone to [PTD] (21) now — this will take a moment.", ephemeral=True)
        guild = interaction.guild
        tag = "PTD"
        servers = ["21"]

        tag_role = discord.utils.get(guild.roles, name=tag)
        if not tag_role:
            async with db_connect() as conn:
                cur = await conn.cursor()
                await cur.execute("SELECT color_hex FROM alliances")
                existing_colors = {int(r[0]) for r in await cur.fetchall() if r[0]}
            tag_color = get_distinct_alliance_color(existing_colors)
            tag_role = await ensure_role(guild, tag, color=tag_color, hoist=True)

        member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)
        srv_display = format_server_display(servers)
        server_field = ",".join(servers)
        onboarded, skipped = 0, 0
        nickname_failures, role_grant_failures = [], []
        role_req_ch = discord.utils.get(guild.channels, name="⚙️-role-requests")
        abilities_ch = discord.utils.get(guild.channels, name="❓-abilities")

        for member in guild.members:
            if member.bot:
                continue
            async with db_connect() as conn:
                cur = await conn.cursor()
                await cur.execute("SELECT in_game_name, alliance_tag, rank_designation, server_number FROM users WHERE user_id = ?", (member.id,))
                row = await cur.fetchone()
            if row and row[0] and row[1] and row[2] and row[3]:
                skipped += 1
                continue

            rank = "Member"
            for candidate_rank in ("R5", "R4"):
                candidate_role = discord.utils.get(guild.roles, name=f"{tag}-{candidate_rank}")
                if candidate_role and candidate_role in member.roles:
                    rank = candidate_rank
                    break

            in_game_name = strip_nickname_decorations(member.display_name) or member.name

            async with db_connect() as conn:
                cur = await conn.cursor()
                await cur.execute(
                    "INSERT INTO users (user_id, original_username, in_game_name, alliance_tag, rank_designation, server_number, "
                    "language_selected, invite_check_passed, test_disclaimer_ack) "
                    "VALUES (?, ?, ?, ?, ?, ?, 1, 1, 1) "
                    "ON CONFLICT(user_id) DO UPDATE SET in_game_name=excluded.in_game_name, alliance_tag=excluded.alliance_tag, "
                    "rank_designation=excluded.rank_designation, server_number=excluded.server_number",
                    (member.id, str(member), in_game_name, tag, rank, server_field)
                )
                await conn.commit()

            roles_to_add = [r for r in (member_role, tag_role) if r]
            for num in servers:
                srv_role = discord.utils.get(guild.roles, name=role_name_for_server(num))
                if srv_role:
                    roles_to_add.append(srv_role)
            try:
                await member.add_roles(*roles_to_add)
            except discord.HTTPException as e:
                role_grant_failures.append(f"{member.mention} ({e})")

            name_budget = 32 - len(f" [{tag_display(tag)}] {srv_display}")
            new_nick = f"{in_game_name[:max(1, name_budget)]} [{tag_display(tag)}] {srv_display}"
            try:
                await member.edit(nick=new_nick[:32])
            except discord.Forbidden:
                if member.id == guild.owner_id:
                    nickname_failures.append(f"{member.mention} (server owner — Discord never allows a bot to rename the owner; set yours manually)")
                else:
                    nickname_failures.append(f"{member.mention} (likely holds a role positioned above mine)")
            except discord.HTTPException as e:
                nickname_failures.append(f"{member.mention} ({e})")

            try:
                await member.send(embed=discord.Embed(
                    title="🚔 You're officially registered",
                    description=(
                        f"This server just got upgraded, and you've been carried over as **[{tag}]**, server "
                        f"**{srv_display}**. Run `/abilities` any time for a full rundown, and if you actually play "
                        f"on more than just server {srv_display}, head to "
                        f"{role_req_ch.mention if role_req_ch else '#⚙️-role-requests'} to add any others. "
                        f"If your name isn't quite right, `/nickname` fixes that any time."
                    ),
                    color=discord.Color.blue()
                ))
            except discord.Forbidden:
                pass

            onboarded += 1

        lines = [f"👥 Registered **{onboarded}**, skipped **{skipped}** already-registered."]
        if role_grant_failures:
            lines.append(f"⚠️ **{len(role_grant_failures)}** couldn't be granted roles:")
            lines.extend(f"   • {f}" for f in role_grant_failures)
        if nickname_failures:
            lines.append(f"⚠️ **{len(nickname_failures)}** nicknames couldn't be changed:")
            lines.extend(f"   • {f}" for f in nickname_failures)

        # Registration alone never creates PTD-R4/PTD-R5 — those only get
        # created the moment someone's actually granted that rank. Folding
        # legacy migration into this same click (rather than leaving it as
        # a separate button someone has to remember) closes exactly the
        # gap that let this go unnoticed before.
        admin_candidates, rank_candidates = await scan_legacy_roles(guild)
        dictator_role = discord.utils.get(guild.roles, name=ROLE_DICTATOR)
        if admin_candidates or rank_candidates:
            lines.append("\n🎖️ **Legacy ranks found — migrating those too:**")
        for role in admin_candidates:
            count = 0
            for m in [mm for mm in role.members if not mm.bot]:
                if dictator_role:
                    try:
                        await m.add_roles(dictator_role, reason="PTD legacy migration: Admin -> Dictator.")
                        count += 1
                    except discord.HTTPException:
                        pass
            async with db_connect() as conn:
                cur = await conn.cursor()
                await cur.execute("INSERT OR IGNORE INTO legacy_roles_tracked (guild_id, role_name, mapped_to) VALUES (?, ?, ?)", (guild.id, role.name, "DICTATOR"))
                await conn.commit()
            lines.append(f"   👑 **{role.name}** ({count} holder(s)) → DICTATOR")
        for role, tier in rank_candidates:
            human_members = [m for m in role.members if not m.bot]
            count = 0
            if tier >= 4:
                rank_name = f"R{tier}"
                for m in human_members:
                    try:
                        await grant_alliance_rank(guild, m, tag, rank_name)
                        count += 1
                    except Exception:
                        pass
                mapped_to = f"{tag}-{rank_name}"
            else:
                for m in human_members:
                    roles_to_add = [r for r in (tag_role, member_role) if r and r not in m.roles]
                    if roles_to_add:
                        try:
                            await m.add_roles(*roles_to_add, reason="PTD legacy migration.")
                            count += 1
                        except discord.HTTPException:
                            pass
                    else:
                        count += 1
                mapped_to = f"{tag} (member)"
            async with db_connect() as conn:
                cur = await conn.cursor()
                await cur.execute("INSERT OR IGNORE INTO legacy_roles_tracked (guild_id, role_name, mapped_to) VALUES (?, ?, ?)", (guild.id, role.name, mapped_to))
                await conn.commit()
            lines.append(f"   🎖️ **{role.name}** ({count} holder(s)) → {mapped_to}")

        summary = "\n".join(lines)

        await send_long(interaction.followup, f"🎖️ **[PTD] (21) conversion complete.**\n\n{summary}", ephemeral=True)
        await log_event(guild, f"🚔 **PTD INSTANT CONVERT** by {interaction.user.mention}\n{summary}")

        await interaction.followup.send(
            "Anyone else need a rank? Pick them below and assign R4/R5 directly, or just ignore this if not.",
            view=GrantRankPickerView(tag),
            ephemeral=True
        )

    async def on_click(self, interaction: discord.Interaction):
        if not is_staff_member(interaction.user):
            await interaction.response.send_message("❌ You need Judge rank or higher to do that.", ephemeral=True)
            return

        await interaction.response.send_message("🪪 Scanning and auto-registering eligible members now...", ephemeral=True)

        guild = interaction.guild
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT tag FROM alliances")
            approved_tags = {row[0] for row in await cur.fetchall()}

        completed = []
        skipped = 0

        for m in await find_ungoverned_members(guild):
            parsed = parse_formatted_nickname(m.display_name)
            parsed_key = resolve_alliance_key(parsed[1], parsed[2], approved_tags) if parsed else None
            if not parsed_key:
                skipped += 1
                continue
            name, _shown_tag, servers = parsed
            tag = parsed_key
            await finalize_registration_from_nickname(guild, m, name, tag, servers)
            completed.append(m)

        summary = f"✅ Auto-registered {len(completed)} member(s)."
        if skipped:
            summary += f" {skipped} member(s) couldn't be auto-registered (nickname doesn't match our format) — they'll need to run `/register` themselves."

        await interaction.followup.send(summary, ephemeral=True)
        await log_event(
            guild,
            f"🪪 **BULK AUTO-REGISTRATION**\nBy: {interaction.user.mention}\nCompleted: {len(completed)}\nSkipped (no matching nickname): {skipped}"
        )


class AutoRegisterView(discord.ui.View):
    """Persistent button offered when an existing member's nickname already
    matches our format but they haven't run /register themselves. Lets
    staff finish their registration for them, re-parsing their CURRENT
    nickname fresh at click time rather than trusting stale stored data."""

    def __init__(self, user_id: int):
        super().__init__(timeout=None)
        self.user_id = user_id
        btn = discord.ui.Button(
            label="✅ Auto-Complete Registration", style=discord.ButtonStyle.success,
            custom_id=f"rc_autoreg_{user_id}"
        )
        btn.callback = self.on_click
        self.add_item(btn)

    async def on_click(self, interaction: discord.Interaction):
        if not is_staff_member(interaction.user):
            await interaction.response.send_message("❌ You need Judge rank or higher to do that.", ephemeral=True)
            return

        guild = interaction.guild
        member = guild.get_member(self.user_id)
        if not member:
            await interaction.response.send_message("⚠️ That member is no longer in the server.", ephemeral=True)
            return

        parsed = parse_formatted_nickname(member.display_name)
        if not parsed:
            await interaction.response.send_message("⚠️ Their nickname no longer matches our format — can't auto-complete. They'll need to run /register.", ephemeral=True)
            return

        name, tag, servers = parsed
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT tag FROM alliances")
            tag = resolve_alliance_key(tag, servers, [r[0] for r in await cur.fetchall()]) or tag
            await cur.execute("SELECT status FROM alliances WHERE tag = ?", (tag,))
            alliance_row = await cur.fetchone()
        if not alliance_row:
            await interaction.response.send_message(f"⚠️ [{tag}] isn't a known alliance — can't auto-complete.", ephemeral=True)
            return

        await finalize_registration_from_nickname(guild, member, name, tag, servers)

        original_embed = interaction.message.embeds[0] if interaction.message.embeds else None
        if original_embed:
            original_embed.add_field(name="Status", value=f"✅ Auto-completed by {interaction.user.mention}", inline=False)
            original_embed.color = discord.Color.green()
            await interaction.response.edit_message(embed=original_embed, view=None)
        else:
            await interaction.response.edit_message(view=None)

        await log_event(guild, f"✅ **AUTO-REGISTRATION COMPLETED**\nStaff: {interaction.user.mention}\nMember: {member.mention}\nTag: [{tag}]")


class AllianceApprovalView(discord.ui.View):
    """The 'approve from the log instead of typing a command' button. Persistent
    (timeout=None), restored on startup for any alliance still pending."""

    def __init__(self, tag: str):
        super().__init__(timeout=None)
        self.tag = tag
        btn = discord.ui.Button(
            label=f"✅ Approve [{tag}] Now",
            style=discord.ButtonStyle.success,
            custom_id=f"rc_approve_alliance_{tag}"
        )
        btn.callback = self.on_approve
        self.add_item(btn)

    async def on_approve(self, interaction: discord.Interaction):
        if not is_staff_member(interaction.user):
            await interaction.response.send_message("❌ You need Judge rank or higher to do that.", ephemeral=True)
            return

        did_something = await approve_alliance(interaction.guild, self.tag, approver_label=interaction.user.mention)
        if not did_something:
            await interaction.response.send_message(f"ℹ️ [{self.tag}] was already approved (or no longer exists).", ephemeral=True)
            return

        original_embed = interaction.message.embeds[0] if interaction.message.embeds else None
        if original_embed:
            original_embed.add_field(name="Status", value=f"✅ Approved by {interaction.user.mention}", inline=False)
            original_embed.color = discord.Color.green()
            await interaction.response.edit_message(embed=original_embed, view=None)
        else:
            await interaction.response.edit_message(view=None)


class GrantRankChoiceView(discord.ui.View):
    """Shown after picking a member — R4, R5, or Skip, nothing auto-assumed."""

    def __init__(self, tag: str, member: discord.Member):
        super().__init__(timeout=120.0)
        self.tag = tag
        self.member = member

    @discord.ui.button(label="R5", style=discord.ButtonStyle.danger)
    async def r5(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.defer()
        await grant_alliance_rank(interaction.guild, self.member, self.tag, "R5")
        await interaction.edit_original_response(content=f"✅ {self.member.mention} is now **[{self.tag}]-R5**.", view=None)

    @discord.ui.button(label="R4", style=discord.ButtonStyle.primary)
    async def r4(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.defer()
        await grant_alliance_rank(interaction.guild, self.member, self.tag, "R4")
        await interaction.edit_original_response(content=f"✅ {self.member.mention} is now **[{self.tag}]-R4**.", view=None)

    @discord.ui.button(label="Skip", style=discord.ButtonStyle.secondary)
    async def skip(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.edit_message(content=f"Skipped — {self.member.mention} keeps whatever rank they already have.", view=None)


class GrantRankUserSelect(discord.ui.UserSelect):
    """Discord's own native member picker — search or scroll through the
    ENTIRE server, not limited to a pre-loaded list of 25. This is the
    actual 'click a username' experience, not a dropdown standing in for one."""

    def __init__(self, tag: str):
        self.tag = tag
        super().__init__(placeholder="Pick a member to assign a rank to...", min_values=1, max_values=1)

    async def callback(self, interaction: discord.Interaction):
        member = self.values[0]
        if not isinstance(member, discord.Member):
            await interaction.response.send_message("❌ That doesn't look like a member of this server.", ephemeral=True)
            return
        view = GrantRankChoiceView(self.tag, member)
        await interaction.response.send_message(f"Assign a rank to {member.mention}, or skip:", view=view, ephemeral=True)


class GrantRankPickerView(discord.ui.View):
    def __init__(self, tag: str, timeout: float = 600.0):
        super().__init__(timeout=timeout)
        self.add_item(GrantRankUserSelect(tag))


class RankRequestView(discord.ui.View):
    """Persistent Approve/Deny view attached to R4/R5 rank-request embeds in
    #logs. (R3 never reaches this — it's auto-granted, no approval needed.)"""

    def __init__(self, request_id: int, rank: str):
        super().__init__(timeout=None)
        self.request_id = request_id
        self.rank = rank
        approve_btn = discord.ui.Button(label="✅ Approve", style=discord.ButtonStyle.success, custom_id=f"rc_rank_approve_{request_id}")
        deny_btn = discord.ui.Button(label="❌ Deny", style=discord.ButtonStyle.danger, custom_id=f"rc_rank_deny_{request_id}")
        approve_btn.callback = self.on_approve
        deny_btn.callback = self.on_deny
        self.add_item(approve_btn)
        self.add_item(deny_btn)

    async def _resolve(self, interaction: discord.Interaction, approved: bool):
        await interaction.response.defer()
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT user_id, tag, rank, status FROM rank_requests WHERE request_id = ?", (self.request_id,))
            row = await cur.fetchone()

        if not row:
            await interaction.followup.send("⚠️ Could not find this request anymore.", ephemeral=True)
            return

        user_id, tag, rank, status = row

        if not can_approve_rank_request(interaction.user, tag, rank):
            if rank == "R4":
                await interaction.followup.send(f"❌ You need Judge rank or higher, or **[{tag}]-R5** command, to rule on this.", ephemeral=True)
            else:
                await interaction.followup.send("❌ You need Judge rank or higher to rule on this.", ephemeral=True)
            return

        if status != "pending":
            await interaction.followup.send(f"ℹ️ This request was already {status}.", ephemeral=True)
            return

        guild = interaction.guild
        member = guild.get_member(user_id)
        new_status = "approved" if approved else "denied"

        if approved and member:
            await grant_alliance_rank(guild, member, tag, rank)

        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("UPDATE rank_requests SET status = ? WHERE request_id = ?", (new_status, self.request_id))
            await conn.commit()

        original_embed = interaction.message.embeds[0] if interaction.message.embeds else None
        verdict_text = f"✅ Approved by {interaction.user.mention}" if approved else f"❌ Denied by {interaction.user.mention}"
        if original_embed:
            original_embed.add_field(name="Ruling", value=verdict_text, inline=False)
            original_embed.color = discord.Color.green() if approved else discord.Color.red()
            await interaction.edit_original_response(embed=original_embed, view=None)
        else:
            await interaction.edit_original_response(view=None)

        if member:
            try:
                if approved:
                    await member.send(f"⚖️ Your request for **[{tag}]-{rank}** command was **approved** in **{guild.name}**. Congratulations, Chief.")
                else:
                    await member.send(f"⚖️ Your request for **[{tag}]-{rank}** command was **denied** in **{guild.name}**.")
            except discord.Forbidden:
                pass

        await log_event(guild, f"⚖️ **{rank} REQUEST {new_status.upper()}**\nRuling by: {interaction.user.mention}\nTarget: <@{user_id}> — [{tag}]")

    async def on_approve(self, interaction: discord.Interaction):
        await self._resolve(interaction, True)

    async def on_deny(self, interaction: discord.Interaction):
        await self._resolve(interaction, False)


def rps_winner(a, b):
    if a == b:
        return "tie"
    beats = {"Rock": "Scissors", "Paper": "Rock", "Scissors": "Paper"}
    return "p1" if beats[a] == b else "p2"


# Flavor for a no-show who was demonstrably online (status != offline) the
# whole time and simply never clicked — this is the "callout with personality"
# case, distinct from someone who was legitimately AFK.
RPS_NOSHOW_ONLINE_FLAVOR = [
    "{ghost} was right there, green dot and all, and just... didn't. Bold strategy.",
    "{ghost} saw the buttons. {ghost} chose violence: the violence of ignoring them.",
    "Witnesses confirm {ghost} was online this whole time. No weapon was drawn. Cowardice? Confidence? We may never know.",
    "{ghost} left {opponent} standing there like a fool. Rude, honestly.",
    "The status said 'online.' The buttons said 'unclicked.' {ghost}, we need to talk.",
    "{ghost} apparently had better things to do than Rock, Paper, Scissors. Unbelievable.",
    "Technically {ghost} didn't lose — they just refused to participate in society.",
    "{ghost} is online, has thumbs, and chose neither Rock, Paper, nor Scissors. A mystery for the ages.",
]

# Flavor for a no-show who genuinely appears offline/idle — softer, since this
# one's more plausibly "wasn't actually there."
RPS_NOSHOW_AWAY_FLAVOR = [
    "{ghost} appears to have wandered off mid-showdown. The precinct forgives you, probably.",
    "{ghost} went dark before drawing a weapon. Search party not currently required.",
    "Looks like {ghost} stepped away. Even outlaws need a coffee break.",
    "{ghost} vanished before the draw. Very cinematic, very unhelpful.",
    "No word from {ghost}. Presumed AFK, not presumed guilty.",
    "{ghost} left the showdown early. We'll allow it — this time.",
]


class RPSView(discord.ui.View):
    """Rock/Paper/Scissors: vs another member, or solo vs Robocop if no opponent given."""

    def __init__(self, player1: discord.Member, player2: Optional[discord.Member]):
        super().__init__(timeout=60.0)
        self.player1 = player1
        self.player2 = player2
        self.choices = {}
        self.message = None  # set by the /rps command right after sending, so on_timeout can edit it

    async def on_error(self, interaction: discord.Interaction, error: Exception, item) -> None:
        """discord.py's default behavior for an unhandled exception in a
        button callback is to print to console and do nothing else — which
        looks EXACTLY like 'nothing happens' from the players' side. This
        guarantees it's never silent again, whatever the actual cause is."""
        print(f"[RPS ERROR] {type(error).__name__}: {error}")
        vs = self.player2.mention if self.player2 else "RoboCop"
        ask = await report_error(interaction.guild, f"RPS match ({self.player1.mention} vs {vs})", interaction.user, error)
        msg = f"⚠️ Something broke mid-match — not your fault. Try `/rps` again.\n\n{ask}"
        try:
            if interaction.response.is_done():
                await interaction.followup.send(msg, ephemeral=True)
            else:
                await interaction.response.send_message(msg, ephemeral=True)
        except discord.HTTPException:
            pass

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if await busy_reject_component(interaction):
            return False
        allowed_ids = {self.player1.id}
        if self.player2:
            allowed_ids.add(self.player2.id)
        if interaction.user.id not in allowed_ids:
            await interaction.response.send_message("This isn't your match, Chief!", ephemeral=True)
            return False
        return True

    async def handle_choice(self, interaction: discord.Interaction, choice: str):
        key = self.player1.id if interaction.user.id == self.player1.id else self.player2.id if self.player2 else None
        if key is None:
            key = interaction.user.id
        self.choices[key] = choice
        await interaction.response.send_message(f"You chose **{choice}**! Locking it in...", ephemeral=True)

        if self.player2 is None:
            self.choices["bot"] = random.choice(["Rock", "Paper", "Scissors"])
            await self.resolve(interaction)
        elif self.player1.id in self.choices and self.player2.id in self.choices:
            await self.resolve(interaction)
        else:
            # Only one side has picked so far — a public update in-channel
            # ("X has chosen their weapon") without revealing what, so the
            # match feels alive to spectators while picks stay hidden.
            chooser = self.player1 if key == self.player1.id else self.player2
            waiting_on = self.player2 if key == self.player1.id else self.player1
            try:
                await interaction.message.edit(embed=discord.Embed(
                    title="🎮 STREET JUSTICE SHOWDOWN",
                    description=(
                        f"{self.player1.mention} vs {self.player2.mention}\n\n"
                        f"✅ {chooser.mention} has chosen their weapon!\n"
                        f"⏳ Waiting on {waiting_on.mention}..."
                    ),
                    color=discord.Color.blurple()
                ), view=self)
            except discord.HTTPException:
                pass

    async def resolve(self, interaction: discord.Interaction):
        if getattr(self, "_resolved", False):
            return  # both players' clicks can race here — only process the result once
        self._resolved = True

        for item in self.children:
            item.disabled = True

        p1_choice = self.choices[self.player1.id]
        p2_key = self.player2.id if self.player2 else "bot"
        p2_choice = self.choices[p2_key]
        p2_label = self.player2.mention if self.player2 else "**Robocop**"

        outcome = rps_winner(p1_choice, p2_choice)
        if outcome == "tie":
            result_desc = "a tie — great minds think alike!"
            winner_line = "🤝 Nobody wins this one."
            color = discord.Color.greyple()
            await increment_user_stat(self.player1.id, "rps_ties")
            if self.player2:
                await increment_user_stat(self.player2.id, "rps_ties")
        elif outcome == "p1":
            result_desc = f"**{p1_choice}** beats **{p2_choice}**!"
            winner_line = f"🏆 **{self.player1.mention} IS THE WINNER!**"
            color = discord.Color.green()
            await increment_user_stat(self.player1.id, "rps_wins")
            if self.player2:
                await increment_user_stat(self.player2.id, "rps_losses")
        else:
            result_desc = f"**{p2_choice}** beats **{p1_choice}**!"
            winner_line = f"🏆 **{p2_label} IS THE WINNER!**"
            color = discord.Color.red()
            await increment_user_stat(self.player1.id, "rps_losses")
            if self.player2:
                await increment_user_stat(self.player2.id, "rps_wins")

        embed = discord.Embed(
            title="🎮 STREET JUSTICE SHOWDOWN — RESULTS",
            description=(
                f"🎯 {self.player1.mention} has answered with **{p1_choice}**!\n"
                f"🎯 {p2_label} has answered with **{p2_choice}**!\n\n"
                f"**THE RESULT IS:** {result_desc}\n\n"
                f"{winner_line}"
            ),
            color=color
        )
        try:
            await interaction.message.edit(embed=embed, view=self)
        except discord.HTTPException:
            pass
        self.stop()

    async def on_timeout(self) -> None:
        """discord.py's default timeout behavior is to silently disable the
        buttons and do nothing else — the match just stops, with no message
        change and nobody told anything happened. This makes sure a no-show
        always gets a conclusive, in-character resolution instead of silence.

        No-shows are treated as a no-contest: nobody's stats move. There's no
        established precedent for penalizing a timeout as a loss, and solo
        matches vs. Robocop can't even reach this path (the bot always picks
        instantly), so this only ever fires on a real human opponent."""
        if getattr(self, "_resolved", False):
            return  # already resolved via a race with a real click
        self._resolved = True

        for item in self.children:
            item.disabled = True

        missing_ids = {self.player1.id, self.player2.id} - set(self.choices.keys()) if self.player2 else set()
        if not missing_ids or not self.player2:
            # Nobody's actually missing (shouldn't happen if timeout fired) —
            # bail out quietly rather than risk a confusing message.
            try:
                if self.message:
                    await self.message.edit(view=self)
            except discord.HTTPException:
                pass
            self.stop()
            return

        ghost_id = next(iter(missing_ids))
        ghost = self.player1 if ghost_id == self.player1.id else self.player2
        opponent = self.player2 if ghost_id == self.player1.id else self.player1

        guild = self.message.guild if self.message else None
        member = guild.get_member(ghost_id) if guild else None
        was_online = bool(member and member.status != discord.Status.offline)

        pool = RPS_NOSHOW_ONLINE_FLAVOR if was_online else RPS_NOSHOW_AWAY_FLAVOR
        flavor = random.choice(pool).format(ghost=ghost.mention, opponent=opponent.mention)

        embed = discord.Embed(
            title="🎮 STREET JUSTICE SHOWDOWN — CALLED ON A TECHNICALITY",
            description=(
                f"{self.player1.mention} vs {self.player2.mention}\n\n"
                f"⏱️ {flavor}\n\n"
                f"No weapon, no winner — this one's a no-contest. Nobody's record changes."
            ),
            color=discord.Color.dark_grey()
        )
        try:
            if self.message:
                await self.message.edit(embed=embed, view=self)
        except discord.HTTPException:
            pass
        self.stop()

    @discord.ui.button(label="🪨 Rock", style=discord.ButtonStyle.secondary)
    async def rock(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.handle_choice(interaction, "Rock")

    @discord.ui.button(label="📄 Paper", style=discord.ButtonStyle.secondary)
    async def paper(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.handle_choice(interaction, "Paper")

    @discord.ui.button(label="✂️ Scissors", style=discord.ButtonStyle.secondary)
    async def scissors(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.handle_choice(interaction, "Scissors")


# ============================================================
#  EVENTS
# ============================================================
@bot.event
async def on_ready():
    print(f"\n==============================================")
    print(f" 🤖 [ROBOCOP UPLINK ESTABLISHED] 🤖 ")
    print(f" Target User: {bot.user} (ID: {bot.user.id})")
    print(f" Instance ID: {INSTANCE_ID}")
    print(f"==============================================\n")

    is_takeover = False
    if not getattr(bot, "_leadership_claimed", False):
        bot._leadership_claimed = True
        previous_leader = await get_setting("active_instance_id")
        previous_heartbeat = await get_setting("active_instance_heartbeat")
        await claim_leadership()

        if previous_leader and previous_leader != INSTANCE_ID and previous_heartbeat:
            try:
                last_seen = datetime.fromisoformat(previous_heartbeat)
                is_takeover = (datetime.now() - last_seen).total_seconds() < LEADERSHIP_STALE_THRESHOLD_SECONDS
            except ValueError:
                is_takeover = False

        if is_takeover:
            print(f"[SYSTEM] 👑 Instance {INSTANCE_ID} took over live from {previous_leader}.")
        elif previous_leader and previous_leader != INSTANCE_ID:
            print(f"[SYSTEM] 👑 Instance {INSTANCE_ID} claimed leadership (previous instance {previous_leader} was already gone — routine restart, no announcement needed).")
        else:
            print(f"[SYSTEM] 👑 Instance {INSTANCE_ID} claimed leadership.")
        bot.loop.create_task(leadership_watchdog())
        bot.loop.create_task(busy_watchdog())

    if not getattr(bot, "_translation_checked", False):
        bot._translation_checked = True
        translation_ok, translation_detail = await check_translation_service()
        if translation_ok:
            print(f"[SYSTEM] 🌐 Translation self-check passed (test: 'test' -> '{translation_detail}').")
        else:
            for guild in bot.guilds:
                await report_translation_failure(guild, translation_detail)

    if is_takeover:
        for guild in bot.guilds:
            await announce_version_handoff(guild)

    for guild in bot.guilds:
        log_channel = discord.utils.get(guild.channels, name="logs")
        if log_channel:
            startup_kind = "took over live from a previous instance" if is_takeover else "came online (routine start)"
            try:
                await log_channel.send(
                    f"🤖 **ROBOCOP IS ONLINE** — instance `{INSTANCE_ID[:8]}` {startup_kind}, connected to "
                    f"**{guild.name}** at {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}. If you don't see this "
                    f"message after starting the bot, it isn't actually connected to this server yet — check the "
                    f"console window for errors before trying any commands."
                )
            except discord.HTTPException:
                pass

        # Every step below is isolated by safe_step(): a failure is logged
        # to #logs and startup carries on, rather than one exception
        # silently skipping everything after it (command sync included).
        await safe_step(guild, "recover server list", recover_managed_servers_setting(guild))  # must precede infrastructure
        if guild.id not in bot.infra_ready_guilds:
            repairs = await safe_step(guild, "build infrastructure", build_global_infrastructure(guild), default=[]) or []
            bot.infra_ready_guilds.add(guild.id)
            await safe_step(guild, "resume Cops & Robbers round", reschedule_active_chase_round(guild))
            await safe_step(guild, "resume chase recruit DMs", reschedule_pending_chase_recruits(guild))
            bot.loop.create_task(daily_chase_scheduler(guild))
            bot.loop.create_task(chase_leaderboard_syndication_loop(guild))
            bot.loop.create_task(daily_nickname_maintenance_scheduler(guild))
            bot.loop.create_task(daily_game_stats_scheduler(guild))
            await safe_step(guild, "seed monthly baseline", ensure_monthly_baseline_seeded(guild))
            bot.loop.create_task(monthly_champion_scheduler(guild))
            await safe_step(guild, "resume Rogue RoboCop round", reschedule_active_rogue_round(guild))
        else:
            repairs = []

        sec_repairs, dangers = await safe_step(guild, "security check", check_critical_security(guild), default=([], [])) or ([], [])
        repairs.extend(sec_repairs)

        # Server is the source of truth: rebuild any missing DB records from
        # live roles/channels/nicknames FIRST, so every check below sees a
        # complete picture; then enforce nicknames against those records.
        await safe_step(guild, "database inventory", reconcile_database_from_server(guild))
        await safe_step(guild, "nickname check", startup_nickname_enforcement(guild))

        await safe_step(guild, "role hierarchy check", check_role_hierarchy_and_alert(guild))
        await safe_step(guild, "audit-log permission check", check_audit_log_permission(guild))
        await safe_step(guild, "config health check", check_config_health(guild))
        await safe_step(guild, "superseded roles check", check_superseded_roles(guild))
        await safe_step(guild, "adoption readiness check", check_adoption_readiness(guild))

        await safe_step(guild, "resume prisoner timers", reschedule_pending_prisoners(guild))
        await safe_step(guild, "resume alliance approval timers", reschedule_pending_alliance_approvals(guild))
        await safe_step(guild, "restore lockdown state", restore_lockdown_state(guild))

        if _is_leader:
            await safe_step(guild, "missed-joiner catch-up", catch_up_missed_joiners(guild), default=[])
        ungoverned_members = await safe_step(guild, "unregistered-member audit", audit_existing_members(guild), default=[]) or []

        await safe_step(guild, "startup report", post_startup_report(guild, repairs, "🔌 Robocop booted up", ungoverned_members=ungoverned_members))
        if is_takeover:
            await safe_step(guild, "latest-version report", post_latest_version_report(guild, repairs))
        if dangers:
            await safe_step(guild, "siren alert", send_siren_alert(guild, dangers))

    try:
        await restore_persistent_views()
    except Exception as e:
        print(f"[ERROR] Restoring persistent #logs buttons failed: {type(e).__name__}: {e}")
        for guild in bot.guilds:
            try:
                await log_event(guild, f"🛑 **STARTUP STEP FAILED — restore #logs buttons**\n`{type(e).__name__}: {e}`\nOlder buttons in #logs may not respond until the next restart.")
            except Exception:
                pass

    if not getattr(bot, "_commands_synced", False):
        bot._commands_synced = True
        try:
            synced = await bot.tree.sync()
            print(f"[COMMAND MODULE] 📡 Synced {len(synced)} commands globally (Discord can take up to an hour to actually show these anywhere — this is normal and NOT a sign anything's broken).")
            for guild in bot.guilds:
                bot.tree.copy_global_to(guild=guild)
                guild_synced = await bot.tree.sync(guild=guild)
                print(f"[COMMAND MODULE] ⚡ Synced {len(guild_synced)} commands INSTANTLY to {guild.name} — these should show up in Discord right away.")
        except Exception as e:
            print(f"[ERROR] Failed to sync slash commands: {e}")


@bot.event
async def on_guild_join(guild):
    """Fires when Robocop is invited to a (new, or freshly re-invited) server."""
    print(f"[SYSTEM] 🚔 Rolled up to a new precinct: {guild.name} ({guild.id})")
    await safe_step(guild, "recover server list", recover_managed_servers_setting(guild))
    repairs = await safe_step(guild, "build infrastructure", build_global_infrastructure(guild), default=[]) or []
    bot.infra_ready_guilds.add(guild.id)

    sec_repairs, dangers = await safe_step(guild, "security check", check_critical_security(guild), default=([], [])) or ([], [])
    repairs.extend(sec_repairs)
    await safe_step(guild, "database inventory", reconcile_database_from_server(guild))
    await safe_step(guild, "nickname check", startup_nickname_enforcement(guild))
    await safe_step(guild, "role hierarchy check", check_role_hierarchy_and_alert(guild))
    await safe_step(guild, "audit-log permission check", check_audit_log_permission(guild))
    await safe_step(guild, "config health check", check_config_health(guild))
    await safe_step(guild, "superseded roles check", check_superseded_roles(guild))
    await safe_step(guild, "adoption readiness check", check_adoption_readiness(guild))

    await safe_step(guild, "resume prisoner timers", reschedule_pending_prisoners(guild))
    await safe_step(guild, "resume alliance approval timers", reschedule_pending_alliance_approvals(guild))
    await safe_step(guild, "restore lockdown state", restore_lockdown_state(guild))
    await safe_step(guild, "resume Cops & Robbers round", reschedule_active_chase_round(guild))
    await safe_step(guild, "resume chase recruit DMs", reschedule_pending_chase_recruits(guild))
    bot.loop.create_task(daily_chase_scheduler(guild))
    bot.loop.create_task(chase_leaderboard_syndication_loop(guild))
    bot.loop.create_task(daily_nickname_maintenance_scheduler(guild))
    bot.loop.create_task(daily_game_stats_scheduler(guild))
    await safe_step(guild, "seed monthly baseline", ensure_monthly_baseline_seeded(guild))
    bot.loop.create_task(monthly_champion_scheduler(guild))
    await safe_step(guild, "resume Rogue RoboCop round", reschedule_active_rogue_round(guild))

    await safe_step(guild, "missed-joiner catch-up", catch_up_missed_joiners(guild), default=[])
    ungoverned_members = await safe_step(guild, "unregistered-member audit", audit_existing_members(guild), default=[]) or []

    await safe_step(guild, "startup report", post_startup_report(guild, repairs, "🚔 Robocop just joined/rejoined this server", ungoverned_members=ungoverned_members))
    if dangers:
        await safe_step(guild, "siren alert", send_siren_alert(guild, dangers))


@bot.event
async def on_raw_reaction_add(payload):
    if not _is_leader:
        return
    if str(payload.emoji) != '🌐':
        return
    if server_is_busy():
        return  # translation is an external API call per reaction — not while we're straining

    now_ts = time.monotonic()
    if now_ts - _translate_cooldowns.get(payload.user_id, 0) < TRANSLATE_COOLDOWN_SECONDS:
        return
    _translate_cooldowns[payload.user_id] = now_ts

    channel = bot.get_channel(payload.channel_id)
    if not channel:
        return

    user = bot.get_user(payload.user_id)
    if user is None:
        try:
            user = await bot.fetch_user(payload.user_id)
        except discord.NotFound:
            return
    if user.bot:
        return

    try:
        message = await channel.fetch_message(payload.message_id)
    except (discord.NotFound, discord.Forbidden):
        return

    if not message.content:
        try:
            await user.send("⚠️ That message doesn't have any text for me to translate (it might be an image or embed).")
        except discord.Forbidden:
            pass
        return

    try:
        dest_lang = await get_user_lang(user.id)
        translated_text = await translate_text(message.content, dest_lang)

        if translated_text is None:
            await user.send("⚠️ Translation service is temporarily unavailable. Please try again in a moment.")
            return

        await user.send(f"🌍 **Translated Message**: {translated_text}\n\n*(Original: {message.content})*")

        await increment_stat("translate_reactions_total")
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("INSERT OR IGNORE INTO translated_messages (message_id) VALUES (?)", (message.id,))
            await conn.commit()
    except Exception as e:
        print(f"[TRANSLATOR ERROR] {e}")
        try:
            await user.send("⚠️ Translation service is currently overloaded or unavailable. Please try again later.")
        except discord.Forbidden:
            pass


async def assign_existing_alliance_roles(guild, member, tag_input):
    tag_role = discord.utils.get(guild.roles, name=tag_input)
    if tag_role:
        await member.add_roles(tag_role)

    async with db_connect() as conn:
        cursor = await conn.cursor()
        await cursor.execute("SELECT status FROM alliances WHERE tag = ?", (tag_input,))
        row = await cursor.fetchone()
    alliance_status = row[0] if row else "pending"

    if alliance_status != "approved":
        drunk_tank_role = discord.utils.get(guild.roles, name=ROLE_DRUNK_TANK)
        if drunk_tank_role:
            await member.add_roles(drunk_tank_role)

    async with db_connect() as conn:
        cursor = await conn.cursor()
        await cursor.execute("UPDATE users SET alliance_tag = ?, rank_designation = ? WHERE user_id = ?", (tag_input, "Member", member.id))
        await conn.commit()


# ------------------------------------------------------------
#  SELF-SERVICE CORRECTIONS — the machinery behind /fix-me. A newcomer
#  who registered with the wrong name, tag, or server shouldn't need a
#  staff member (or a database edit) to sort it out. Each of these does
#  the full job: Discord roles, nickname, AND every DB field, together,
#  so nothing drifts.
# ------------------------------------------------------------
async def rebuild_member_nickname(guild, member) -> str:
    """Rebuilds '{name} [{TAG}] (servers)' purely from the DB record and
    applies it. Returns what was applied (or attempted)."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT in_game_name, alliance_tag, server_number FROM users WHERE user_id = ?", (member.id,))
        row = await cur.fetchone()
    if not row or not row[0]:
        return member.display_name
    name, tag, srv_field = row
    server_nums = await parse_stored_server_field(srv_field, guild.id)
    srv_display = format_server_display(server_nums)
    suffix = (f" [{tag_display(tag)}]" if tag else "") + (f" {srv_display}" if srv_display else "")
    trimmed = name[:max(1, 32 - len(suffix))]
    nick = f"{trimmed}{suffix}"[:32]
    try:
        await member.edit(nick=nick)
    except discord.HTTPException:
        pass
    return nick


async def switch_member_alliance(guild, member, new_tag: str) -> dict:
    """Moves ONE member from their current alliance to an existing one:
    strips every old-tag role (base, -R4, -R5, -Leadership), adds the new
    tag's base role (plus Drunk Tank if that alliance is still pending),
    resets rank to Member, updates the DB, rebuilds the nickname, and then
    checks whether the alliance they just left is now an empty typo-shell
    worth flagging. Returns a summary dict for the caller's message."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT alliance_tag, rank_designation FROM users WHERE user_id = ?", (member.id,))
        row = await cur.fetchone()
    old_tag = row[0] if row else None
    old_rank = row[1] if row else None

    removed = []
    if old_tag:
        for suffix in ("", "-R4", "-R5", "-Leadership"):
            r = discord.utils.get(guild.roles, name=f"{old_tag}{suffix}")
            if r and r in member.roles:
                try:
                    await member.remove_roles(r, reason=f"Switched alliance {old_tag} -> {new_tag}")
                    removed.append(r.name)
                except discord.HTTPException:
                    pass
    drunk_tank_role = discord.utils.get(guild.roles, name=ROLE_DRUNK_TANK)
    if drunk_tank_role and drunk_tank_role in member.roles:
        try:
            await member.remove_roles(drunk_tank_role)
        except discord.HTTPException:
            pass

    await assign_existing_alliance_roles(guild, member, new_tag)  # adds tag role, re-adds Drunk Tank if pending, sets DB tag+rank
    nick = await rebuild_member_nickname(guild, member)

    if old_tag:
        await refresh_leadership_status(guild, old_tag)
        await flag_orphaned_alliance_if_empty(guild, old_tag, member)

    await log_event(
        guild,
        f"🔁 **ALLIANCE SWITCHED**\n{member.mention}: [{old_tag or '—'}] → [{new_tag}]"
        + (f" (was {old_rank}, now Member)" if old_rank and old_rank != "Member" else "")
        + f"\nRoles removed: {', '.join(removed) if removed else 'none'}\nNickname: **{nick}**"
    )
    return {"old_tag": old_tag, "old_rank": old_rank, "nick": nick}


async def change_member_servers(guild, member, server_nums: list) -> str:
    """Replaces a member's server list: swaps the '🗺️ Server N Patrol' roles,
    updates users.server_number, keeps user_nicknames rows in step (seeds
    any new server with the current in-game name, drops rows for servers
    they no longer play), and rebuilds the nickname."""
    managed = await get_managed_servers(guild.id)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT in_game_name, server_number FROM users WHERE user_id = ?", (member.id,))
        row = await cur.fetchone()
    in_game_name = row[0] if row and row[0] else strip_nickname_decorations(member.display_name) or member.name
    old_nums = await parse_stored_server_field(row[1], guild.id) if row and row[1] else []

    for num in managed:
        role = discord.utils.get(guild.roles, name=role_name_for_server(num))
        if not role:
            continue
        try:
            if num in server_nums and role not in member.roles:
                await member.add_roles(role, reason="Server list corrected via /fix-me")
            elif num not in server_nums and role in member.roles:
                await member.remove_roles(role, reason="Server list corrected via /fix-me")
        except discord.HTTPException:
            pass

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("UPDATE users SET server_number = ? WHERE user_id = ?", (",".join(server_nums), member.id))
        for num in old_nums:
            if num not in server_nums:
                await cur.execute("DELETE FROM user_nicknames WHERE user_id = ? AND server_number = ?", (member.id, num))
        await cur.execute("SELECT COUNT(*) FROM user_nicknames WHERE user_id = ? AND is_active = 1", (member.id,))
        (has_active,) = await cur.fetchone()
        await conn.commit()
    for i, num in enumerate(server_nums):
        if num not in old_nums:
            await upsert_user_nickname(member.id, num, in_game_name, make_active=(not has_active and i == 0))
            has_active = True

    nick = await rebuild_member_nickname(guild, member)
    await log_event(guild, f"🗺️ **SERVERS CORRECTED**\n{member.mention}: {'/'.join(old_nums) or '—'} → {'/'.join(server_nums)}\nNickname: **{nick}**")
    return nick


async def dissolve_alliance(guild, tag: str, actor_label: str) -> list:
    """Removes an alliance completely: its roles, its two categories and
    every channel inside them, and its DB rows (alliances, plus clearing
    the tag off any user still pointing at it). Deliberately NOT called
    automatically anywhere — always behind a human's explicit click or
    command, because it's the one truly destructive operation here."""
    done = []
    for suffix in (" CHATS", " Voice Channels"):
        cat = discord.utils.get(guild.categories, name=f"{tag}{suffix}")
        if cat:
            for ch in list(cat.channels):
                try:
                    await ch.delete(reason=f"Alliance [{tag}] dissolved by {actor_label}")
                except discord.HTTPException:
                    pass
            try:
                await cat.delete(reason=f"Alliance [{tag}] dissolved by {actor_label}")
                done.append(f"category '{cat.name}'")
            except discord.HTTPException:
                pass
    for suffix in ("-Leadership", "-R5", "-R4", ""):
        role = discord.utils.get(guild.roles, name=f"{tag}{suffix}")
        if role:
            try:
                await role.delete(reason=f"Alliance [{tag}] dissolved by {actor_label}")
                done.append(f"role '{role.name}'")
            except discord.HTTPException:
                pass
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("DELETE FROM alliances WHERE tag = ?", (tag,))
        await cur.execute("UPDATE users SET alliance_tag = NULL, rank_designation = NULL WHERE alliance_tag = ?", (tag,))
        cleared = cur.rowcount
        await cur.execute("DELETE FROM rank_requests WHERE tag = ?", (tag,))
        await conn.commit()
    done.append(f"DB rows (alliance + {cleared} member record(s) cleared)")
    await _set_orphan_pending(guild, tag, False)
    await log_event(guild, f"🧹 **ALLIANCE DISSOLVED — [{tag}]**\nBy: {actor_label}\nRemoved: {', '.join(done)}")
    return done


async def _get_orphan_pending(guild) -> list:
    raw = await get_guild_setting(guild.id, "orphan_alliances_pending")
    return json.loads(raw) if raw else []


async def _set_orphan_pending(guild, tag: str, pending: bool):
    tags = await _get_orphan_pending(guild)
    if pending and tag not in tags:
        tags.append(tag)
    elif not pending and tag in tags:
        tags.remove(tag)
    await set_guild_setting(guild.id, "orphan_alliances_pending", json.dumps(tags))


async def flag_orphaned_alliance_if_empty(guild, tag: str, leaver):
    """After someone leaves an alliance: if nobody at all holds its tag role
    any more, it's almost certainly a typo-alliance (someone entered 'PDT'
    for 'PTD', which spun up a whole category + roles, then corrected
    themselves). Post a one-click cleanup offer to #logs for staff — never
    auto-delete, because 'empty right now' and 'safe to delete' aren't the
    same thing and a human should make that call."""
    tag_role = discord.utils.get(guild.roles, name=tag)
    if tag_role and tag_role.members:
        return
    if tag in await _get_orphan_pending(guild):
        return  # already flagged, don't spam
    log_channel = discord.utils.get(guild.channels, name="logs")
    if not log_channel:
        return
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT creator_id, created_at FROM alliances WHERE tag = ?", (tag,))
        row = await cur.fetchone()
    creator_note = ""
    if row:
        creator_note = f"\nFounded by <@{row[0]}> at `{(row[1] or '?')[:16]}`"
        if row[0] == leaver.id:
            creator_note += " — **the founder is the one who just left**, which is the classic typo-alliance signature."
    embed = discord.Embed(
        title=f"🧹 EMPTY ALLIANCE — [{tag}]",
        description=(
            f"{leaver.mention} just left **[{tag}]** and nobody holds its tag any more.{creator_note}\n\n"
            f"If this was a typo that spun up infrastructure by accident, one click below removes its roles, "
            f"channels, and database rows. If it's a real alliance that's just empty for now, leave it."
        ),
        color=discord.Color.orange(),
        timestamp=datetime.now()
    )
    await _set_orphan_pending(guild, tag, True)
    try:
        await log_channel.send(embed=embed, view=OrphanAllianceCleanupView(tag))
    except discord.HTTPException:
        pass


class OrphanAllianceCleanupView(discord.ui.View):
    """Persistent (restored on startup from the 'orphan_alliances_pending'
    guild setting) — same tag-in-custom_id pattern as AllianceApprovalView."""

    def __init__(self, tag: str):
        super().__init__(timeout=None)
        self.tag = tag
        btn = discord.ui.Button(label=f"🧹 Dissolve [{tag}]", style=discord.ButtonStyle.danger, custom_id=f"rc_dissolve_alliance_{tag}")
        btn.callback = self.on_dissolve
        self.add_item(btn)
        keep = discord.ui.Button(label="Keep it", style=discord.ButtonStyle.secondary, custom_id=f"rc_keep_alliance_{tag}")
        keep.callback = self.on_keep
        self.add_item(keep)

    async def on_dissolve(self, interaction: discord.Interaction):
        if not is_senior_staff_member(interaction.user):
            await interaction.response.send_message("❌ Senator or higher only — this deletes channels.", ephemeral=True)
            return
        tag_role = discord.utils.get(interaction.guild.roles, name=self.tag)
        if tag_role and tag_role.members:
            await interaction.response.send_message(f"⚠️ [{self.tag}] isn't empty any more ({len(tag_role.members)} member(s)) — not dissolving.", ephemeral=True)
            await _set_orphan_pending(interaction.guild, self.tag, False)
            return
        await interaction.response.defer()
        done = await dissolve_alliance(interaction.guild, self.tag, interaction.user.mention)
        embed = interaction.message.embeds[0] if interaction.message.embeds else discord.Embed(title=f"🧹 [{self.tag}]")
        embed.add_field(name="Status", value=f"🧹 Dissolved by {interaction.user.mention} — {len(done)} thing(s) removed", inline=False)
        embed.color = discord.Color.dark_grey()
        try:
            await interaction.message.edit(embed=embed, view=None)
        except discord.HTTPException:
            pass

    async def on_keep(self, interaction: discord.Interaction):
        if not is_staff_member(interaction.user):
            await interaction.response.send_message("❌ Staff only.", ephemeral=True)
            return
        await _set_orphan_pending(interaction.guild, self.tag, False)
        embed = interaction.message.embeds[0] if interaction.message.embeds else discord.Embed(title=f"🧹 [{self.tag}]")
        embed.add_field(name="Status", value=f"✅ Kept by {interaction.user.mention}", inline=False)
        embed.color = discord.Color.green()
        await interaction.response.edit_message(embed=embed, view=None)


async def run_onboarding_safe(member):
    """Shared error-handled wrapper around handle_member_join — used both for
    a brand-new join and for an existing member manually running /register."""
    _onboarding_in_progress.add(member.id)
    try:
        await handle_member_join(member)
        still_here = member.guild.get_member(member.id)
        member_role = discord.utils.get(member.guild.roles, name=ROLE_MEMBER)
        if still_here is None:
            onboard_console(member, "🚪 onboarding ended — they're no longer in the server (left or removed)")
        elif member_role and member_role in still_here.roles:
            onboard_console(still_here, f"✅ ONBOARDING COMPLETE — now {still_here.display_name}")
        else:
            onboard_console(still_here, "⏸️ onboarding stopped before the end — parked in #gateway (check #logs)")
    except OnboardingMemberLeft:
        onboard_console(member, "🚪 they left the server — onboarding stopped")
    except Exception as e:
        onboard_console(member, f"💥 onboarding crashed: {type(e).__name__}: {e}")
        guild = member.guild
        print(f"[CRITICAL] onboarding crashed for {member} ({member.id}): {e}")
        await log_event(
            guild,
            f"🛑 **ONBOARDING ERROR**\nUser: {member.mention}\nError: `{e}`\n"
            f"They may be stuck in #gateway — check on them manually."
        )
        await notify_owner(
            guild, "🛑 Onboarding just broke for someone",
            f"{member.mention} hit an error partway through registration and may be stuck in #gateway:\n`{e}`"
        )
        gateway_channel = discord.utils.get(guild.channels, name="gateway")
        if gateway_channel:
            try:
                await gateway_channel.send(f"⚠️ {member.mention}, something went wrong on my end. An admin has been notified — hang tight!")
            except discord.HTTPException:
                pass
    finally:
        _onboarding_in_progress.discard(member.id)


@bot.event
async def on_member_join(member):
    if not _is_leader:
        return  # a newer instance is taking over — let it handle this join
    onboard_console(member, f"👋 joined the server (@{member.name})")
    await log_visitor_entry(member)
    await run_onboarding_safe(member)


@bot.event
async def on_member_remove(member):
    if not _is_leader:
        return
    if member.id in _onboarding_in_progress:
        onboard_console(member, "🚪 no longer in the server partway through onboarding (left, or removed for not answering)")
    task = _resume_tasks.pop(member.id, None)
    if task:
        task.cancel()
    await log_visitor_exit(member)


@bot.event
async def on_member_update(before: discord.Member, after: discord.Member):
    if before.roles == after.roles:
        return
    if after.id in _onboarding_in_progress:
        return  # the final onboarding DM already covers this — no spam mid-flow

    gained_raw = [k for k in ORDERED_ABILITY_KEYS if k in compute_capabilities(after) and k not in compute_capabilities(before)]
    if not gained_raw:
        return

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT capability FROM capability_notifications WHERE user_id = ?", (after.id,))
        already_seen = {row[0] for row in await cur.fetchall()}

    gained = [k for k in gained_raw if k not in already_seen]
    if not gained:
        return  # they've held this rank before (e.g. released from prison) — nothing new to tell them

    try:
        upgrade_embed = build_abilities_embed(
            after, gained,
            title=f"🆙 CLEARANCE UPGRADE, {after.display_name}!",
            description=pick_flavor(UPGRADE_FLAVOR, "upgrade")
        )
        await after.send(embed=upgrade_embed)
    except discord.Forbidden:
        pass  # DMs closed — nothing to do
    except discord.HTTPException as e:
        await report_error(after.guild, "clearance-upgrade DM (on_member_update)", after, e)
    await mark_capabilities_notified(after.id, gained)


_rogue_last_comment_at = 0.0


async def forward_feedback_message(message):
    """#🐛-bugs and #💡-suggestions mirror straight to #logs — so staff
    watching #logs (which is where everything important in this bot already
    lands) sees reports the moment they come in, without also having to
    keep both feedback channels open. A 👀 reaction on the original message
    is the only visible acknowledgment the reporter gets automatically."""
    is_bug = message.channel.name == "🐛-bugs"
    log_channel = discord.utils.get(message.guild.channels, name="logs")
    if log_channel:
        embed = discord.Embed(
            title="🐛 BUG REPORT" if is_bug else "💡 SUGGESTION",
            description=message.content[:1900] if message.content else "*(no text — attachment or embed only)*",
            color=discord.Color.orange() if is_bug else discord.Color.blue(),
            timestamp=datetime.now()
        )
        embed.set_author(name=str(message.author), icon_url=message.author.display_avatar.url)
        embed.add_field(name="Jump to message", value=f"[Click here]({message.jump_url})", inline=False)
        if message.attachments:
            embed.add_field(name="Attachments", value="\n".join(a.url for a in message.attachments)[:1024], inline=False)
        try:
            await log_channel.send(embed=embed)
        except discord.HTTPException:
            pass
    try:
        await message.add_reaction("👀")
    except discord.HTTPException:
        pass


@bot.event
async def on_message(message):
    await bot.process_commands(message)  # no prefix commands currently registered, but keeps the door open safely

    if message.author.bot or not message.guild:
        return

    if message.channel.name == "gateway" and _is_leader:
        try:
            await handle_parked_gateway_message(message)
        except Exception as e:
            await report_error(message.guild, "#gateway paused-registration listener", message.author, e)
        return

    if message.channel.name in ("🐛-bugs", "💡-suggestions"):
        await forward_feedback_message(message)
        return

    if not message.channel.name == "💬-general-chat":
        return
    if not _is_leader:
        return
    if server_is_busy():
        return

    global _rogue_last_comment_at
    now_ts = time.monotonic()
    if now_ts - _rogue_last_comment_at < ROGUE_BOT_MIN_COMMENT_GAP_SECONDS:
        return
    if random.random() > ROGUE_BOT_COMMENT_CHANCE:
        return

    active = await get_active_rogue_round(message.guild)
    if not active:
        return

    _rogue_last_comment_at = now_ts
    _, secret_name, _ = active
    identity = next((i for i in ROGUE_BOT_IDENTITIES if i["name"] == secret_name), None)
    if identity and identity["hints"] and random.random() < 0.5:
        line = random.choice(identity["hints"])
    else:
        line = random.choice(ROGUE_BOT_FILLER_LINES)

    try:
        await message.channel.send(line)
    except discord.HTTPException:
        pass


@bot.event
async def on_presence_update(before: discord.Member, after: discord.Member):
    """Thin wrapper (8.7). Presence nudges are nice-to-haves: an instance
    that's handing over to a newer one sends none, and a dropped connection
    mid-DM (common during a handoff or a network blip) just skips that one
    reminder with a single console line, instead of a scary traceback."""
    if not _is_leader:
        return
    try:
        await _handle_presence_update(before, after)
    except (aiohttp.ClientError, asyncio.TimeoutError, ConnectionError, discord.HTTPException) as e:
        print(f"[PRESENCE] Skipped an online-reminder for {after} — connection hiccup ({type(e).__name__}). Harmless.")


async def _handle_presence_update(before: discord.Member, after: discord.Member):
    """Anyone with #logs access gets a gentle nudge when they come online:
    go check that everything's still running smoothly."""
    await _personal_on_login(before, after)  # optional personal add-on — see the bottom of the file

    if after.bot:
        return
    if before.status != discord.Status.offline or after.status == discord.Status.offline:
        return  # only a genuine offline -> online-ish transition counts

    # Everyone (not just staff) gets a light stats reminder on login,
    # cooldown-gated so it's not obnoxious for people who flicker
    # online/offline a lot.
    now_ts = time.monotonic()
    last_stats = _last_stats_reminder.get(after.id, 0)
    if now_ts - last_stats >= STATS_REMINDER_COOLDOWN_HOURS * 3600:
        _last_stats_reminder[after.id] = now_ts
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT rps_wins, rogue_catches FROM user_stats WHERE user_id = ?", (after.id,))
            us = await cur.fetchone()
        rps_wins, rogue_catches = us if us else (0, 0)
        try:
            await after.send(
                f"📊 Welcome back, {after.display_name}! Quick stats check: **{rps_wins}** RPS win(s), "
                f"**{rogue_catches}** Rogue RoboCop catch(es). Run `/stats` any time for the full picture, "
                f"or `/leaderboard` to see where everyone stands."
            )
        except discord.Forbidden:
            pass

    # If this person happens to be in the top 10 overall, give the server
    # a fun heads-up in #general-chat that they're online — separately and
    # more conservatively cooldown-gated, since this one's public, not a DM.
    last_top10 = _last_top10_celebration.get(after.id, 0)
    if now_ts - last_top10 >= TOP10_CELEBRATION_COOLDOWN_HOURS * 3600:
        leaderboard = await compute_leaderboard(after.guild)
        top_ids = {uid for uid, _, _ in leaderboard[:10]}
        if after.id in top_ids:
            _last_top10_celebration[after.id] = now_ts
            general_ch = discord.utils.get(after.guild.channels, name="💬-general-chat")
            if general_ch:
                opener = random.choice(TOP10_ARRIVAL_OPENERS)
                descriptor = random.choice(TOP10_ARRIVAL_DESCRIPTORS).format(mention=after.mention)
                try:
                    await general_ch.send(f"{opener} {descriptor}")
                except discord.HTTPException:
                    pass

    if not is_staff_member(after):
        return

    now_ts = time.monotonic()
    last = _last_online_reminder.get(after.id, 0)
    if now_ts - last < STAFF_ONLINE_REMINDER_COOLDOWN_MINUTES * 60:
        return
    _last_online_reminder[after.id] = now_ts

    caps = compute_capabilities(after)
    log_channel = discord.utils.get(after.guild.channels, name="logs")

    embed = discord.Embed(
        title="🔑 WELCOME BACK ON DUTY",
        description=(
            f"Good to see you online, {after.display_name}. You've got eyes on **#logs** — "
            f"take a minute to check that everything's running smoothly.\n\n"
            f"With power comes responsibility, Chief."
        ),
        color=rank_color(caps),
        timestamp=datetime.now()
    )
    if log_channel:
        embed.add_field(name="Quick Link", value=log_channel.mention, inline=False)

    try:
        await after.send(embed=embed)
    except discord.Forbidden:
        pass


async def handle_member_join(member):
    guild = member.guild
    now = datetime.now()
    gateway_channel = discord.utils.get(guild.channels, name="gateway")

    await check_raid(guild)

    async with db_connect() as conn:
        cursor = await conn.cursor()

        await cursor.execute(
            "SELECT in_game_name, alliance_tag, rank_designation, server_number, language_selected, invite_check_passed, test_disclaimer_ack "
            "FROM users WHERE user_id = ?", (member.id,)
        )
        reg_row = await cursor.fetchone()

        if reg_row and reg_row[0] and reg_row[1] and reg_row[2] and reg_row[3]:
            tag, rank, srv = reg_row[1], reg_row[2], reg_row[3]
            roles_to_add = [
                discord.utils.get(guild.roles, name=ROLE_MEMBER),
                discord.utils.get(guild.roles, name=tag)
            ]
            if rank in ("R3", "R4", "R5"):
                roles_to_add.append(discord.utils.get(guild.roles, name=f"{tag}-{rank}"))
            for num in await parse_stored_server_field(srv, guild.id):
                srv_role = discord.utils.get(guild.roles, name=role_name_for_server(num))
                if srv_role:
                    roles_to_add.append(srv_role)

            for r in roles_to_add:
                if r:
                    try:
                        await member.add_roles(r)
                    except discord.HTTPException:
                        pass

            srv_display = format_server_display(await parse_stored_server_field(srv, guild.id))
            new_nick = f"{reg_row[0]} [{tag_display(tag)}] {srv_display}"
            try:
                await member.edit(nick=new_nick[:32])
            except discord.HTTPException:
                pass

            await log_event(guild, f"🔄 **RETURNING CHIEF**\nUser {member.mention} rejoined. Restored roles and bypassed gateway.")
            onboard_console(member, f"🔄 RETURNING registered Chief — roles restored as {new_nick[:32]}, skipped #gateway")
            return

        await cursor.execute("SELECT lifetime_invite_fails, timeout_until FROM users WHERE user_id = ?", (member.id,))
        row = await cursor.fetchone()

        if row:
            lifetime_fails = row[0]
            timeout_until_str = row[1]
            if lifetime_fails >= 6:
                onboard_console(member, "🔨 banned on arrival — 6 lifetime invite-check failures")
                try:
                    await member.ban(reason="Max lifetime invite failures (6).")
                    await log_mod_action(guild, "ban", member.id, member.display_name, "Robocop (Automated)", "Max lifetime invite failures (6).")
                except discord.HTTPException:
                    pass
                return
            if timeout_until_str and ASK_WHO_INVITED:  # this lockout only ever comes from failing the invite question
                timeout_until = datetime.fromisoformat(timeout_until_str)
                if now < timeout_until:
                    remaining_mins = max(1, int((timeout_until - now).total_seconds() / 60))
                    onboard_console(member, f"🛑 still locked out ({remaining_mins} min left) — removing them again")

                    if gateway_channel:
                        await gateway_channel.set_permissions(member, read_messages=True, send_messages=True)
                        await gateway_channel.send(f"🛑 {member.mention}, you are currently locked out. You still have **{remaining_mins} minute(s)** left. See you then!")

                    await asyncio.sleep(5)
                    try:
                        await member.kick(reason=f"Tried to bypass timeout ({remaining_mins}m left).")
                        await log_mod_action(guild, "kick", member.id, member.display_name, "Robocop (Automated)", f"Tried to bypass an active timeout ({remaining_mins}m left).")
                    except discord.Forbidden:
                        timeout_role = discord.utils.get(guild.roles, name=ROLE_TIMEOUT)
                        member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)
                        if timeout_role:
                            await member.add_roles(timeout_role)
                        if member_role and member_role in member.roles:
                            await member.remove_roles(member_role)
                        await clear_gateway_override(guild, member)
                    return
        else:
            await cursor.execute("INSERT INTO users (user_id, original_username, invite_strikes, lifetime_invite_fails) VALUES (?, ?, 0, 0)", (member.id, member.name))
            await conn.commit()
            onboard_console(member, f"🆕 FIRST VISIT — @{member.name}, account created {member.created_at:%Y-%m-%d}. Starting onboarding in #gateway")

    if gateway_channel:
        await gateway_channel.set_permissions(member, read_messages=True, send_messages=True)
    else:
        # Nowhere to run the flow — bail out loudly instead of failing silently later.
        await log_event(guild, f"🛑 **ONBOARDING ERROR**\n#gateway channel not found for {member.mention}. Run infrastructure setup.")
        return

    def check(m):
        return m.author == member and m.channel == gateway_channel

    is_resuming = bool(reg_row and (any(reg_row[:4]) or reg_row[4] or reg_row[5] or reg_row[6]))
    if is_resuming:
        onboard_console(member, "↩️ back again — resuming registration where they left off")
        await gateway_channel.send(
            f"🔄 **Welcome back, {member.mention}!** Let's pick up right where we left off — "
            f"I'll skip anything you already answered."
        )

    # --- PHASE 0: LANGUAGE SELECTION (always first, skipped if already chosen) ---
    language_already_selected = bool(reg_row and reg_row[4])
    if not language_already_selected:
        onboard_console(member, "step 1/6: choosing a language")
        lang_view = LanguageView(member, timeout=LANGUAGE_DEFAULT_SECONDS)
        lang_msg = await gateway_channel.send(
            f"{member.mention} 🌍 **Please select your language** / Por favor selecciona tu idioma / Veuillez choisir votre langue / "
            "Bitte wählen Sie Ihre Sprache / Пожалуйста, выберите язык / الرجاء اختيار لغتك / कृपया अपनी भाषा चुनें\n"
            "*(English, Russian, German, Spanish, French, Arabic, Hindi — plus a few more in the list below.)*\n"
            f"*No choice in {LANGUAGE_DEFAULT_SECONDS} seconds? No problem — I'll carry on in English.*",
            view=lang_view
        )
        timed_out = await lang_view.wait()
        if timed_out:
            if _member_gone(member):
                raise OnboardingMemberLeft()
            onboard_console(member, "🌍 no language picked — defaulting to English")
            async with db_connect() as conn:
                cursor = await conn.cursor()
                await cursor.execute("UPDATE users SET pref_lang = 'en' WHERE user_id = ?", (member.id,))
                await conn.commit()
            try:
                await lang_msg.edit(view=None)
            except discord.HTTPException:
                pass
            await gateway_channel.send(
                f"🇬🇧 {member.mention}, no language picked, so we'll carry on in **English**. "
                "You can switch any time with `/language`."
            )
        async with db_connect() as conn:
            cursor = await conn.cursor()
            await cursor.execute("UPDATE users SET language_selected = 1 WHERE user_id = ?", (member.id,))
            await conn.commit()

    # --- PRIVACY NOTE — right after language, so it arrives in their language ---
    try:
        await send_long(gateway_channel, f"{member.mention} " + await t(PRIVACY_NOTE, member.id))  # translations can run long — split safely
    except discord.HTTPException:
        pass

    # --- PHASE 0.25: TIME ZONE PREFERENCE (optional, informational — never blocks or kicks) ---
    async with db_connect() as conn:
        cursor = await conn.cursor()
        await cursor.execute("SELECT pref_timezone FROM users WHERE user_id = ?", (member.id,))
        tz_row = await cursor.fetchone()
    if not (tz_row and tz_row[0]):
        onboard_console(member, "step 2/6: time zone (optional)")
        tz_view = TimezoneView(member)
        await gateway_channel.send(
            member.mention + " " + await tf(
                "🕐 One more optional thing — what time zone are you roughly in? This server runs on a fixed "
                "schedule (things like the daily Cops & Robbers round), so this just helps me tell you how that "
                "lines up with your own time. Totally skippable if you'd rather not say.",
                member.id
            ),
            view=tz_view
        )
        await tz_view.wait()  # no kick on timeout — this is a nice-to-know, not a checkpoint

    # --- PHASE 0.5: TEST SERVER DISCLAIMER (mandatory, once) ---
    disclaimer_ack = bool(reg_row and reg_row[6])
    if not disclaimer_ack:
        onboard_console(member, "step 3/6: test-server notice")
        disclaimer_view = TestServerDisclaimerView(member)
        await gateway_channel.send(
            content=await tf(
                "⚠️ **BEFORE WE GO ANY FURTHER, {mention}** — this is a **test server**. We're actively "
                "building and breaking things here, which means **everything could be wiped at any point "
                "between now and 7 days from today** — your registration, your alliance, your messages, all "
                "of it. That's not a threat, just the honest deal.\n\n"
                "🙏 Thank you for being one of our testers — genuinely, it helps a lot. Click below to "
                "confirm you understand, and let's get you set up.",
                member.id, mention=member.mention
            ),
            view=disclaimer_view
        )
        resolved = await view_wait_with_warning(member, disclaimer_view, 240.0, "Still there to confirm you understand?")
        if not resolved:
            try:
                await member.kick(reason="Never acknowledged the test-server disclaimer during onboarding.")
                await log_mod_action(guild, "kick", member.id, member.display_name, "Robocop (Automated)", "Never responded to the test-server disclaimer.")
            except discord.HTTPException:
                pass
            return

        async with db_connect() as conn:
            cursor = await conn.cursor()
            await cursor.execute("UPDATE users SET test_disclaimer_ack = 1 WHERE user_id = ?", (member.id,))
            await conn.commit()

    # --- PHASE 1: PRE-ONBOARDING INVITE CHECK ---
    invite_check_passed = bool(reg_row and reg_row[5]) or not ASK_WHO_INVITED
    if not invite_check_passed:
        onboard_console(member, "optional step: who invited them? (ASK_WHO_INVITED is on)")
        await gateway_channel.send(await t(
            f"Welcome to the gateway, {member.mention}.\n"
            "**Who from the game invited you to this server?**\n"
            "*(Warning: Do not lie. I will know, and I have a low tolerance for bad manners.)*\n"
            "*Confused at any point? Just type `help` and a real person will come find you.*",
            member.id
        ))

        strikes = 0
        match_found = False
        member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)

        while strikes < 3:
            try:
                msg = await wait_with_warning(member, check, 360.0, "Still there?")
                guessed_name = msg.content.strip().lower()
                referrer = None

                if guessed_name in ALWAYS_VALID_INVITER_NAMES:
                    match_found = True
                else:
                    for current_member in guild.members:
                        if member_role in current_member.roles:
                            if clean_display_name(current_member.display_name) == guessed_name:
                                match_found = True
                                referrer = current_member
                                break

                onboard_console(member, f"   answered inviter: '{msg.content.strip()[:40]}' → {'✅ accepted' if match_found else '❌ not recognized'}")
                if match_found:
                    await gateway_channel.send(await tf("✅ Identity confirmed. Thank you, {mention}.", member.id, mention=member.mention))
                    async with db_connect() as conn:
                        cursor = await conn.cursor()
                        await cursor.execute("UPDATE users SET invite_check_passed = 1 WHERE user_id = ?", (member.id,))
                        await conn.commit()
                    if referrer:
                        await increment_user_stat(referrer.id, "referrals")
                    break
                else:
                    strikes += 1
                    async with db_connect() as conn:
                        cursor = await conn.cursor()
                        await cursor.execute("UPDATE users SET lifetime_invite_fails = lifetime_invite_fails + 1 WHERE user_id = ?", (member.id,))
                        await conn.commit()

                    if strikes < 3:
                        taunt_text = await t(pick_flavor(INVITE_TAUNTS, f'taunt_{member.id}'), member.id)
                        await gateway_channel.send(f"{member.mention} {taunt_text}")
                    else:
                        timeout_time = now + timedelta(minutes=30)
                        async with db_connect() as conn:
                            cursor = await conn.cursor()
                            await cursor.execute("UPDATE users SET timeout_until = ? WHERE user_id = ?", (timeout_time.isoformat(), member.id))
                            await conn.commit()

                        await gateway_channel.send(await tf("That's 3 strikes, {mention}. You are being booted for 30 minutes.", member.id, mention=member.mention))

                        await asyncio.sleep(3)
                        try:
                            await member.kick(reason="Failed invite check 3 times.")
                            await log_mod_action(guild, "kick", member.id, member.display_name, "Robocop (Automated)", "Failed invite verification 3 times.")
                        except discord.Forbidden:
                            timeout_role = discord.utils.get(guild.roles, name=ROLE_TIMEOUT)
                            if timeout_role:
                                await member.add_roles(timeout_role)
                            if member_role and member_role in member.roles:
                                await member.remove_roles(member_role)
                            await clear_gateway_override(guild, member)
                        return
            except asyncio.TimeoutError:
                try:
                    await member.kick(reason="Invite check timeout.")
                    await log_mod_action(guild, "kick", member.id, member.display_name, "Robocop (Automated)", "Never responded to the invite-check prompt.")
                except discord.HTTPException:
                    pass
                return

    # --- PHASE 2: IDENTITY ---
    in_game_name = reg_row[0] if reg_row and reg_row[0] else None
    if not in_game_name:
        onboard_console(member, "step 4/6: in-game name")
        await gateway_channel.send(await tf("{mention}, what is your exact in-game username?", member.id, mention=member.mention))
        try:
            name_msg = await wait_with_warning(member, check, 240.0, "Still working on your username?")
            in_game_name = name_msg.content.strip()
            onboard_console(member, f"   in-game name: {in_game_name[:40]}")
            async with db_connect() as conn:
                cursor = await conn.cursor()
                await cursor.execute("UPDATE users SET in_game_name = ? WHERE user_id = ?", (in_game_name, member.id))
                await conn.commit()
            try:
                await gateway_channel.send(await tf(NAME_CHANGE_REMINDER, member.id, abilities=abilities_mention(member.guild)))
            except discord.HTTPException:
                pass
        except asyncio.TimeoutError:
            await announce_onboarding_pause(member, gateway_channel)
            return

    # --- PHASE 3: ALLIANCE TAG & ASSIGNMENT ---
    tag_input = reg_row[1] if reg_row and reg_row[1] else None
    if not tag_input:
        onboard_console(member, "step 5/6: alliance tag")
        tag_strikes = 0
        while True:
            await gateway_channel.send(await tf("{mention} Understood, {name}. Now, enter your **Alliance Tag** (2 to 4 letters strictly).", member.id, mention=member.mention, name=in_game_name))
            try:
                tag_msg = await wait_with_warning(member, check, 240.0, "Still working on your alliance tag?")
                tag_input = tag_msg.content.strip().upper()
                onboard_console(member, f"   tag entered: {tag_input[:20]}")

                if 2 <= len(tag_input) <= 4 and tag_input.isalpha():
                    view = TagConfirmView(member, tag_input)
                    await gateway_channel.send(await tf("⚠️ {mention}, you entered **[{tag}]**. Please double-check this.", member.id, mention=member.mention, tag=tag_input), view=view)
                    resolved = await view_wait_with_warning(member, view, 240.0, "Still there to confirm your tag?")
                    if not resolved:
                        try:
                            await member.kick(reason="Never confirmed alliance tag during onboarding.")
                            await log_mod_action(guild, "kick", member.id, member.display_name, "Robocop (Automated)", "Never responded to the tag-confirmation prompt.")
                        except discord.HTTPException:
                            pass
                        return

                    if view.result == "retry":
                        continue
                    elif view.result == "trap":
                        try:
                            await member.timeout(timedelta(seconds=60), reason="Trap door button.")
                        except discord.HTTPException:
                            pass
                        return
                    elif view.result == "confirm":
                        chosen = await choose_alliance_key(guild, member, gateway_channel, tag_input)
                        if chosen is None:
                            await announce_onboarding_pause(member, gateway_channel)
                            return
                        tag_input = chosen  # plain tag, or a server-scoped key like HAL·121
                        break
                    else:
                        return
                else:
                    tag_strikes += 1
                    if tag_strikes < 3:
                        await gateway_channel.send(await tf(
                            "⚠️ {mention} That doesn't look like an alliance tag — it's the **2 to 4 letters** shown next "
                            "to your alliance's name in the game (letters only, e.g. `PTD`). Try again, or type `help`.",
                            member.id, mention=member.mention
                        ))
                    else:
                        # Three garbage tags in a row. Used to be a permanent ban after
                        # two — but a genuinely confused newcomer ('P T D', 'PTD1', 'my
                        # alliance is PTD') looks identical to a troll from here, and a
                        # permanent ban for confusion is the wrong default. Stop the
                        # flow, leave them parked in #gateway, and hand it to a human.
                        await gateway_channel.send(await tf(
                            "🛑 {mention}, I still can't make sense of that tag, so I've stopped here and pinged "
                            "staff to help you finish up. Hang tight — you're not in trouble.",
                            member.id, mention=member.mention
                        ))
                        await log_event(guild, f"🆘 **REGISTRATION STALLED — TAG**\n{member.mention} gave 3 invalid alliance tags in a row (last: `{tag_input}`). They're parked in #gateway waiting for a human.")
                        await notify_staff_dm(guild, "🆘 Someone's stuck on their alliance tag", f"{member.mention} couldn't get past the tag prompt in #gateway. A quick word there will sort it.", color=discord.Color.orange())
                        return
            except asyncio.TimeoutError:
                await announce_onboarding_pause(member, gateway_channel)
                return

        async with db_connect() as conn:
            cursor = await conn.cursor()
            await cursor.execute("SELECT creator_id FROM alliances WHERE tag = ?", (tag_input,))
            existing_alliance = await cursor.fetchone()

        if existing_alliance:
            await gateway_channel.send(await tf("🏢 Tag **[{tag}]** recognized. Assigning you to the existing roster...", member.id, tag=tag_input))
            await assign_existing_alliance_roles(guild, member, tag_input)

        else:
            async with db_connect() as conn:
                cursor = await conn.cursor()
                await cursor.execute("SELECT value FROM settings WHERE key = 'alliance_lock'")
                lock_status = await cursor.fetchone()
                if lock_status and lock_status[0] == 'locked':
                    onboard_console(member, f"🔒 new alliance [{tag_input}] refused — alliance creation is locked (parked in #gateway)")
                    await gateway_channel.send(await tf(
                        "🔒 {mention}, new alliances are paused by staff right now, so I can't create **[{tag}]** yet. "
                        "I've let them know you're waiting — hang tight, you're not in trouble.",
                        member.id, mention=member.mention, tag=tag_input))
                    await notify_staff_dm(guild, "🔒 Someone's waiting to create an alliance", f"{member.mention} wants to create **[{tag_input}]** but alliance creation is locked (`/stop-alliance`). They're parked in #gateway.", color=discord.Color.orange())
                    return

                await cursor.execute("SELECT tag FROM alliances WHERE creator_id = ?", (member.id,))
                if await cursor.fetchone():
                    await log_event(guild, f"⏳ **ALLIANCE CREATION BLOCKED**\nUser: {member.mention} | Attempted Tag: [{tag_input}]\nReason: User lifetime limit reached.")
                    onboard_console(member, f"🚫 new alliance [{tag_input}] refused — they already founded one (parked in #gateway)")
                    await gateway_channel.send(await tf(
                        "🚫 {mention}, each Chief can only found one alliance here, and you've already started one. "
                        "Double-check your tag — or type anything here and a human will help you sort it out.",
                        member.id, mention=member.mention))
                    return

                await cursor.execute("SELECT value FROM settings WHERE key = 'timekeeper_burst'")
                burst = await cursor.fetchone()
                cooldown_ends = None
                now_c = datetime.now()  # fresh — `now` was captured when they joined, possibly many minutes ago
                if not (burst and datetime.fromisoformat(burst[0]) > now_c):
                    await cursor.execute("SELECT created_at FROM alliances")
                    # Newest REAL creation time. Anything claiming to be in the future is a
                    # bad timestamp, never a reason to make someone wait.
                    times = [ct for ct in (parse_db_local_time(r[0]) for r in await cursor.fetchall()) if ct and ct <= now_c + timedelta(minutes=1)]
                    if times and now_c < max(times) + timedelta(minutes=ALLIANCE_CREATION_COOLDOWN_MINUTES):
                        cooldown_ends = max(times) + timedelta(minutes=ALLIANCE_CREATION_COOLDOWN_MINUTES)

                await cursor.execute("SELECT color_hex FROM alliances")
                existing_colors = {int(r[0]) for r in await cursor.fetchall() if r[0]}

            if cooldown_ends:
                await park_for_alliance_cooldown(guild, member, gateway_channel, tag_input, cooldown_ends)
                return

            tag_color = get_distinct_alliance_color(existing_colors)

            created_new = False
            async with db_connect() as conn:
                cursor = await conn.cursor()
                try:
                    await cursor.execute(
                        "INSERT INTO alliances (tag, creator_id, status, color_hex, created_at) VALUES (?, ?, 'pending', ?, ?)",
                        (tag_input, member.id, str(tag_color.value), datetime.now().isoformat())
                    )
                    await cursor.execute("UPDATE users SET alliance_tag = ?, rank_designation = ? WHERE user_id = ?", (tag_input, "Member", member.id))
                    await conn.commit()
                    created_new = True
                except sqlite3.IntegrityError:
                    await conn.rollback()

            if not created_new:
                # Someone else claimed this exact tag in the split second between our
                # availability check and the insert. Fold gracefully into their roster
                # instead of crashing the whole onboarding flow.
                await gateway_channel.send(await tf("⚠️ Someone just claimed **[{tag}]** a moment before you. Joining the existing roster instead...", member.id, tag=tag_input))
                await assign_existing_alliance_roles(guild, member, tag_input)
            else:
                # 🎉 FOUNDER'S PASS: while the server has fewer than this many
                # alliances total, the first N of them get waved straight
                # through — no Drunk Tank, no waiting, no vetting, and no
                # rank either (founders don't get automatic R5 anymore — see
                # /request-rank). Both numbers are live-configurable via
                # /configure-setting, not hardcoded.
                founders_pass_threshold = await get_config_value(guild.id, "founders_pass_threshold")
                founders_pass_max_server_size = await get_config_value(guild.id, "founders_pass_max_server_size")
                alliance_approval_minutes = await get_config_value(guild.id, "alliance_approval_minutes")

                async with db_connect() as conn:
                    cursor = await conn.cursor()
                    await cursor.execute("SELECT COUNT(*) FROM alliances")
                    alliance_count = (await cursor.fetchone())[0]
                is_founders_pass = alliance_count < founders_pass_max_server_size and alliance_count <= founders_pass_threshold

                drunk_tank_role = discord.utils.get(guild.roles, name=ROLE_DRUNK_TANK)
                if is_founders_pass:
                    async with db_connect() as conn:
                        cursor = await conn.cursor()
                        await cursor.execute("UPDATE alliances SET status = 'approved' WHERE tag = ?", (tag_input,))
                        await conn.commit()
                    await gateway_channel.send(await tf(
                        "🎉 **FOUNDER'S PASS!** [{tag}] is alliance #{count} on this server — "
                        "one of the first {threshold}, ever. Full access, right now, no waiting.",
                        member.id, tag=tag_input, count=alliance_count, threshold=founders_pass_threshold
                    ))
                elif drunk_tank_role:
                    await member.add_roles(drunk_tank_role)

                tag_role = await ensure_role(guild, tag_input, color=tag_color, hoist=True)
                await member.add_roles(tag_role)

                await enforce_role_hierarchy(guild)

                print(f"[INFRASTRUCTURE] Generating dynamic category and channels for [{tag_input}]...")
                await gateway_channel.send(await tf("🏗️ Constructing infrastructure for **[{tag}]**...", member.id, tag=tag_input))

                cat_overwrites = {
                    guild.default_role: discord.PermissionOverwrite(view_channel=False),
                    tag_role: discord.PermissionOverwrite(view_channel=True),
                    guild.me: discord.PermissionOverwrite(view_channel=True, manage_channels=True)
                }

                try:
                    chat_category = discord.utils.get(guild.categories, name=f"{tag_input} CHATS")
                    if not chat_category:
                        chat_category = await guild.create_category(f"{tag_input} CHATS", overwrites=cat_overwrites)

                    voice_category = discord.utils.get(guild.categories, name=f"{tag_input} Voice Channels")
                    if not voice_category:
                        voice_category = await guild.create_category(f"{tag_input} Voice Channels", overwrites=cat_overwrites)

                    if not discord.utils.get(chat_category.text_channels, name="💬-lobby"):
                        await guild.create_text_channel("💬-lobby", category=chat_category)
                    if not discord.utils.get(chat_category.text_channels, name="♟️-strategy"):
                        await guild.create_text_channel("♟️-strategy", category=chat_category)
                    if not discord.utils.get(chat_category.text_channels, name="📸-screenshots"):
                        await guild.create_text_channel("📸-screenshots", category=chat_category)
                    if not discord.utils.get(chat_category.text_channels, name="🚨-currently-active-events"):
                        await guild.create_text_channel("🚨-currently-active-events", category=chat_category)
                    if not discord.utils.get(voice_category.voice_channels, name="🔊-Lobby-VC"):
                        await guild.create_voice_channel("🔊-Lobby-VC", category=voice_category)
                    if not discord.utils.get(voice_category.voice_channels, name="🚨🎙️-Event-VC"):
                        await guild.create_voice_channel("🚨🎙️-Event-VC", category=voice_category)

                    # Visible to the whole alliance so they know it exists, but
                    # nobody can post until someone actually holds R4/R5 — those
                    # roles get their own explicit send_messages grant the first
                    # time they're handed out (see grant_alliance_rank).
                    leader_overwrites = {
                        guild.default_role: discord.PermissionOverwrite(view_channel=False),
                        guild.me: discord.PermissionOverwrite(view_channel=True),
                        tag_role: discord.PermissionOverwrite(view_channel=True, send_messages=False),
                    }
                    leadership_chat = discord.utils.get(chat_category.text_channels, name="🎖️-leadership-chat")
                    if not leadership_chat:
                        leadership_chat = await guild.create_text_channel("🎖️-leadership-chat", category=chat_category, overwrites=leader_overwrites)
                    print(f"[INFRASTRUCTURE] [{tag_input}] generation complete.")
                    await refresh_leadership_status(guild, tag_input)

                    if is_founders_pass:
                        new_alliance_embed = discord.Embed(
                            title=f"🎉 NEW ALLIANCE FORMED — [{tag_input}] (Founder's Pass)",
                            description=f"Founder: {member.mention}\nStatus: ✅ Auto-approved (one of the first {founders_pass_threshold} alliances on this server). No automatic rank — founder can claim one via /request-rank like anyone else.",
                            color=discord.Color.green(),
                            timestamp=datetime.now()
                        )
                        log_channel = discord.utils.get(guild.channels, name="logs")
                        if log_channel:
                            await log_channel.send(embed=new_alliance_embed)
                    else:
                        # Give the founder a heads-up + start the safety-net clock.
                        approve_at = now + timedelta(minutes=alliance_approval_minutes)
                        async with db_connect() as conn:
                            cursor = await conn.cursor()
                            await cursor.execute("UPDATE alliances SET auto_approve_at = ? WHERE tag = ?", (approve_at.isoformat(), tag_input))
                            await conn.commit()

                        await gateway_channel.send(await tf(
                            "⏳ **PENDING MODERATOR APPROVAL** — [{tag}] needs a staff sign-off before you get full "
                            "access to the live channels. Nobody around? No problem: you'll be **automatically approved in "
                            "{minutes} minutes** and moved out of the Drunk Tank either way.",
                            member.id, tag=tag_input, minutes=alliance_approval_minutes
                        ))

                        new_alliance_embed = discord.Embed(
                            title=f"🏗️ NEW ALLIANCE FORMED — [{tag_input}]",
                            description=(
                                f"Founder: {member.mention}\n"
                                f"Status: 🍺 Pending approval — auto-approves in {alliance_approval_minutes} minutes if untouched"
                            ),
                            color=discord.Color.gold(),
                            timestamp=datetime.now()
                        )
                        log_channel = discord.utils.get(guild.channels, name="logs")
                        if log_channel:
                            await log_channel.send(embed=new_alliance_embed, view=AllianceApprovalView(tag_input))

                        await notify_staff_dm(
                            guild, f"🏗️ NEW ALLIANCE — [{tag_input}]",
                            f"{member.mention} just founded **[{tag_input}]**. Auto-approves in "
                            f"{alliance_approval_minutes} minutes if nobody reviews it — approve early from #logs.",
                            color=discord.Color.gold()
                        )
                        bot.loop.create_task(schedule_alliance_auto_approval(guild, tag_input, alliance_approval_minutes * 60))
                except Exception as e:
                    print(f"[ERROR] Failed to generate alliance channels: {e}")
                    await log_event(guild, f"⚠️ **CHANNEL GENERATION FAILED** for [{tag_input}]: `{e}`")

    # --- PHASE 4: SERVER AUTH & FINALIZATION ---
    onboard_console(member, "step 6/6: server number")
    async with db_connect() as conn:
        cursor = await conn.cursor()
        await cursor.execute("SELECT server_number FROM users WHERE user_id = ?", (member.id,))
        srv_row = await cursor.fetchone()
    server_nums = await parse_stored_server_field(srv_row[0], guild.id) if srv_row and srv_row[0] else []

    if not server_nums:
        managed_servers = await get_managed_servers(guild.id)
        server_list_display = ", ".join(f"`{n}`" for n in managed_servers)
        server_strikes = 0
        while server_strikes < 3:
            await gateway_channel.send(await t(
                f"{member.mention}, what server are you from? Enter one or more of: {server_list_display} "
                f"(comma-separated if more than one), or `all`.",
                member.id
            ))
            try:
                srv_msg = await wait_with_warning(member, check, 240.0, "Still deciding on your server?")
                onboard_console(member, f"   server answer: {srv_msg.content.strip()[:30]}")
                srv_input = srv_msg.content.strip().lower()

                if srv_input == "all":
                    server_nums = managed_servers
                else:
                    server_nums = normalize_server_input(srv_input, managed_servers)

                if server_nums:
                    async with db_connect() as conn:
                        cursor = await conn.cursor()
                        await cursor.execute("UPDATE users SET server_number = ? WHERE user_id = ?", (",".join(server_nums), member.id))
                        await conn.commit()

                    if len(server_nums) > 1:
                        async with db_connect() as conn:
                            cursor = await conn.cursor()
                            placeholders = ",".join("?" * len(server_nums))
                            await cursor.execute(
                                f"SELECT server_number, nickname FROM user_nicknames WHERE user_id = ? AND server_number IN ({placeholders})",
                                (member.id, *server_nums)
                            )
                            existing_nicks = await cursor.fetchall()

                        if existing_nicks:
                            options_text = "\n".join(f"• Server `{s}`: **{n}**" for s, n in existing_nicks)
                            nick_view = NicknameOnboardChoiceView(member, existing_nicks, in_game_name)
                            await gateway_channel.send(await tf(
                                "📇 You've told me different nicknames before for some of these servers:\n{options}\n\n"
                                "Pick one below to use as your display name, or keep what you just entered (**{current}**). "
                                "No rush — if you don't answer, I'll just use what you typed.",
                                member.id, options=options_text, current=in_game_name
                            ), view=nick_view)
                            await nick_view.wait()  # optional — no kick on timeout, current name is a perfectly fine default
                            if nick_view.chosen_name:
                                in_game_name = nick_view.chosen_name
                            active_server = nick_view.chosen_server or server_nums[0]
                            for num in server_nums:
                                await upsert_user_nickname(member.id, num, in_game_name, make_active=(num == active_server))
                        else:
                            for num in server_nums:
                                await upsert_user_nickname(member.id, num, in_game_name, make_active=(num == server_nums[0]))
                            await gateway_channel.send(await tf(
                                "📇 Quick heads up: since you're playing on multiple servers, your in-game name might "
                                "not be the same on all of them. I've saved **{name}** for now — if it's different on "
                                "one of your other servers, you can manage separate nicknames any time with `/nickname`.",
                                member.id, name=in_game_name
                            ))
                    else:
                        await upsert_user_nickname(member.id, server_nums[0], in_game_name, make_active=True)
                    break
                else:
                    server_strikes += 1
                    if server_strikes == 3:
                        # Used to be a permanent ban. Three misses here is far more
                        # likely "doesn't know what a server number is" than malice —
                        # park them and get a human, same as the tag prompt.
                        await gateway_channel.send(await tf(
                            "🛑 {mention}, I still can't match that to one of our servers, so I've stopped here and "
                            "pinged staff to help you finish up. Hang tight — you're not in trouble.",
                            member.id, mention=member.mention
                        ))
                        await log_event(guild, f"🆘 **REGISTRATION STALLED — SERVER**\n{member.mention} gave 3 unrecognized server answers (last: `{srv_input}`). Valid: {server_list_display}. They're parked in #gateway waiting for a human.")
                        await notify_staff_dm(guild, "🆘 Someone's stuck on their server number", f"{member.mention} couldn't get past the server prompt in #gateway. A quick word there will sort it.", color=discord.Color.orange())
                        return
                    else:
                        await gateway_channel.send(await tf(
                            "⚠️ That doesn't match any of our servers. It's the **number** shown in the game — one of: "
                            "{options}. Just the number is fine (e.g. `21`), or `all`. Type `help` if you're unsure.",
                            member.id, options=server_list_display
                        ))
            except asyncio.TimeoutError:
                await announce_onboarding_pause(member, gateway_channel)
                return

    await maybe_grant_innovator(guild, member, server_nums)

    srv_display = format_server_display(server_nums)
    name_budget = 32 - len(f" [{tag_display(tag_input)}] {srv_display}")
    trimmed_name = in_game_name[:max(1, name_budget)]
    new_nickname = f"{trimmed_name} [{tag_display(tag_input)}] {srv_display}"

    try:
        await member.edit(nick=new_nickname[:32])
    except discord.Forbidden:
        await gateway_channel.send(await tf("⚠️ {mention}, I lack the authority to change your nickname due to server hierarchy. Please manually change it to: **{nickname}**", member.id, mention=member.mention, nickname=new_nickname[:32]))
    except discord.HTTPException:
        pass

    member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)
    if member_role:
        await member.add_roles(member_role)
    for num in server_nums:
        srv_role = discord.utils.get(guild.roles, name=role_name_for_server(num))
        if srv_role:
            await member.add_roles(srv_role)

    onboard_embed = discord.Embed(
        title="✅ NEW CHIEF ONBOARDED",
        color=discord.Color.green(),
        timestamp=datetime.now()
    )
    onboard_embed.set_thumbnail(url=member.display_avatar.url)
    onboard_embed.add_field(name="Discord User", value=member.mention, inline=False)
    onboard_embed.add_field(name="Assigned Name", value=new_nickname, inline=False)
    onboard_embed.add_field(name="Roles Granted", value=f"Member, [{tag_input}], Server {'/'.join(server_nums)}", inline=False)
    log_channel = discord.utils.get(guild.channels, name="logs")
    if log_channel:
        try:
            await log_channel.send(embed=onboard_embed)
        except discord.HTTPException:
            pass

    try:
        await gateway_channel.set_permissions(member, read_messages=False, send_messages=False)
    except discord.HTTPException as e:
        print(f"[ERROR] Failed to revoke gateway access: {e}")

    # 🎓 Send them their personal field manual — private, just for them, in
    # their own language — plus a note on where to find help later.
    caps = compute_capabilities(member)
    abilities_ch = discord.utils.get(guild.channels, name="❓-abilities")
    try:
        welcome_embed = build_abilities_embed(
            member, caps,
            title=f"🚔 WELCOME TO THE FORCE, {member.display_name}!",
            description=pick_flavor(WELCOME_FLAVOR, "welcome")
        )
        where_to_find_info = await t(
            f"👉 **Head to {abilities_ch.mention if abilities_ch else '#❓-abilities'} to see exactly what you're "
            f"cleared to do here.** It's got the full list, pinned right at the top.\n\n"
            f"A few other things worth knowing:\n"
            f"• Something wrong with your name, tag, or server? `/fix-me` — buttons for each, no staff needed.\n"
            f"• `/stats` any time — your record and rank across RPS, Rogue RoboCop, and Cops & Robbers.\n"
            f"• React 🌐 on any message for a private translation into your language.\n"
            f"• Keep an eye on #💬-general-chat around noon — something interesting happens there daily.",
            member.id
        )
        welcome_embed.add_field(name="📍 Where To Find Things", value=where_to_find_info, inline=False)
        await member.send(embed=welcome_embed)
        await mark_capabilities_notified(member.id, caps)
    except discord.Forbidden:
        pass

    recruit_at = datetime.now() + timedelta(seconds=CHASE_RECRUIT_DELAY_SECONDS)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("UPDATE users SET chase_recruit_at = ? WHERE user_id = ?", (recruit_at.isoformat(), member.id))
        await conn.commit()
    bot.loop.create_task(schedule_chase_recruit_dm(member, CHASE_RECRUIT_DELAY_SECONDS))


# ============================================================
#  COPS & ROBBERS — game engine
# ============================================================
async def get_eligible_chase_pool(guild) -> list:
    """Everyone currently holding Member, minus anyone who's opted out."""
    member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)
    if not member_role:
        return []
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT user_id FROM chase_opt_outs")
        opted_out = {row[0] for row in await cur.fetchall()}
    return [m for m in member_role.members if not m.bot and m.id not in opted_out]


async def get_active_chase_round(guild):
    """Returns (round_id, ends_at, last_hint_tier) for the current active
    round, or None if there isn't one."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT round_id, ends_at, last_hint_tier FROM chase_rounds WHERE status = 'active' ORDER BY round_id DESC LIMIT 1")
        row = await cur.fetchone()
    return row


def get_chase_target_identity(member, db_row):
    """Pulls the server(s)/tag/base-name a chase target is scored/hinted
    against, straight from their current roles and stored name — same
    source of truth the nickname-compliance system already uses."""
    tag = db_row[1] if db_row else None
    servers = db_row[3].split(",") if db_row and db_row[3] else []
    base_name = (db_row[0] if db_row and db_row[0] else strip_nickname_decorations(member.display_name)) or member.name
    return tag, servers, base_name


def build_hint_text(tier: int, tag: str, servers: list, base_name: str) -> str:
    pool = CHASE_HINT_POOL.get(tier, CHASE_HINT_POOL[6])
    template = random.choice(pool)
    partial = base_name[:max(1, len(base_name) // 2)] + "_" * (len(base_name) - len(base_name) // 2)
    return template.format(
        server=servers[0] if servers else "??",
        tag_letter=tag[0] if tag else "?",
        name_length=len(base_name),
        name_letter=base_name[0].upper() if base_name else "?",
        tag=tag_display(tag) if tag else "???",
        partial_name=partial,
    )


def compute_guess_score(guess_text: str, tag: str, servers: list, base_name: str) -> float:
    """0.0-1.0 — how close a /arrest or /ambush guess is to a target's real
    identity. Weighted: name similarity matters most, tag and server are
    smaller confirming signals — matches the fuzzy 'close counts' design."""
    guess_lower = guess_text.lower().strip()
    score = 0.0
    if servers and any(num in guess_lower for num in servers):
        score += 0.25
    if tag and tag.lower() in guess_lower:
        score += 0.35
    name_sim = SequenceMatcher(None, guess_lower, base_name.lower()).ratio()
    score += name_sim * 0.40
    return min(score, 1.0)


async def start_chase_round(guild, started_by: str) -> tuple:
    """Returns (success: bool, message: str)."""
    if await get_active_chase_round(guild):
        return False, "A chase is already underway — end it first with `/end-chase`."
    if server_is_busy():
        return False, f"🔧 RoboCop is busy ({_busy['reason']}) — no new chases until the garage door's back up. Try again in a few minutes."

    general_ch = discord.utils.get(guild.channels, name="💬-general-chat")
    if not general_ch:
        return False, "Couldn't find #💬-general-chat — run infrastructure setup first."

    pool = await get_eligible_chase_pool(guild)
    if len(pool) < CHASE_MIN_PARTICIPANTS:
        return False, f"Only {len(pool)} eligible member(s) — need at least {CHASE_MIN_PARTICIPANTS} for a chase to make sense."

    cop_ratio = await get_config_value(guild.id, "chase_cop_ratio")
    round_hours = await get_config_value(guild.id, "chase_round_hours")

    random.shuffle(pool)
    cop_count = max(1, round(len(pool) * cop_ratio))
    cop_count = min(cop_count, len(pool) - 2)  # always leave at least 2 robbers
    cops, robbers = pool[:cop_count], pool[cop_count:]

    now = datetime.now()
    ends_at = now + timedelta(hours=round_hours)
    next_hint_at = now + timedelta(seconds=CHASE_HINT_INTERVAL_SECONDS)

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute(
            "INSERT INTO chase_rounds (ends_at, status, started_by, last_hint_tier, next_hint_at, last_activity_at) VALUES (?, 'active', ?, 0, ?, ?)",
            (ends_at.isoformat(), started_by, next_hint_at.isoformat(), now.isoformat())
        )
        round_id = cur.lastrowid
        for m in cops:
            await cur.execute("INSERT INTO chase_participants (round_id, user_id, role) VALUES (?, ?, 'cop')", (round_id, m.id))
        for m in robbers:
            await cur.execute("INSERT INTO chase_participants (round_id, user_id, role) VALUES (?, ?, 'robber')", (round_id, m.id))
        await conn.commit()

    for m in cops:
        try:
            await m.send(embed=discord.Embed(
                title="🚔 YOU'VE BEEN DEPUTIZED",
                description=(
                    "You're a **cop** in this round's Cops & Robbers. Somewhere in this server, robbers are "
                    "hiding in plain sight. Every hour, I'll DM you a poetic clue narrowing down who's still "
                    "at large — use `/arrest <name>` to make your move. Guess close and I'll tell you you're "
                    "warm, even if you miss.\n\nTell no one. Good luck, Chief."
                ),
                color=discord.Color.blue()
            ))
        except discord.Forbidden:
            pass
    for m in robbers:
        try:
            await m.send(embed=discord.Embed(
                title="🕶️ YOU'RE ON THE RUN",
                description=(
                    "You're a **robber** in this round's Cops & Robbers. Cops are getting clues about you "
                    "every hour — the trail gets warmer as the round goes on. Survive the full "
                    f"{round_hours} hours and you win. Or go on the offensive: `/ambush <name>` to try "
                    "and take out a cop yourself.\n\nTell no one. Stay sharp."
                ),
                color=discord.Color.dark_grey()
            ))
        except discord.Forbidden:
            pass

    announcement_msg = await general_ch.send(embed=discord.Embed(
        title="🚨 THE CHASE IS ON 🚨",
        description=(
            f"Somewhere among you, {len(cops)} cop(s) and {len(robbers)} robber(s) walk unseen. Nobody "
            "knows who's who — not even each other's side.\n\n"
            f"The round runs for **{round_hours} hours**. Clues drop hourly, in secret, to the cops "
            "alone. When it ends, everything gets revealed.\n\n"
            "You won't know if you're playing until you get a DM. Good luck out there."
        ),
        color=discord.Color.red(),
        timestamp=datetime.now()
    ))
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("UPDATE chase_rounds SET announcement_msg_id = ? WHERE round_id = ?", (announcement_msg.id, round_id))
        await conn.commit()

    await log_event(guild, f"🚨 **CHASE STARTED**\nBy: {started_by}\nCops: {len(cops)} | Robbers: {len(robbers)}\nEnds: {ends_at.strftime('%Y-%m-%d %H:%M')}")
    bot.loop.create_task(run_chase_round_timers(guild, round_id))
    return True, f"🚨 Chase started — {len(cops)} cop(s), {len(robbers)} robber(s). Ends in {round_hours} hours."


async def send_chase_hints(guild, round_id: int, tier: int):
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT user_id FROM chase_participants WHERE round_id = ? AND role = 'cop' AND eliminated = 0", (round_id,))
        cops = [row[0] for row in await cur.fetchall()]
        await cur.execute("SELECT user_id FROM chase_participants WHERE round_id = ? AND role = 'robber' AND eliminated = 0", (round_id,))
        robber_ids = [row[0] for row in await cur.fetchall()]

    if not cops or not robber_ids:
        return

    lines = []
    for i, uid in enumerate(robber_ids, start=1):
        member = guild.get_member(uid)
        if not member:
            continue
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT in_game_name, alliance_tag, rank_designation, server_number FROM users WHERE user_id = ?", (uid,))
            db_row = await cur.fetchone()
        tag, servers, base_name = get_chase_target_identity(member, db_row)
        lines.append(f"**Suspect #{i}:** {build_hint_text(tier, tag, servers, base_name)}")

    embed = discord.Embed(
        title=f"🔎 CASE FILES — HOUR {tier}",
        description="\n\n".join(lines) if lines else "All suspects currently accounted for.",
        color=discord.Color.gold(),
        timestamp=datetime.now()
    )
    embed.set_footer(text="Use /arrest <name> to make your move.")

    for cop_id in cops:
        cop = guild.get_member(cop_id)
        if cop:
            try:
                await cop.send(embed=embed)
            except discord.Forbidden:
                pass


async def post_chase_leaderboard(guild):
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT user_id, arrests_made FROM chase_stats WHERE arrests_made > 0 ORDER BY arrests_made DESC LIMIT 5")
        top_cops = await cur.fetchall()
        await cur.execute("SELECT user_id, robber_wins FROM chase_stats WHERE robber_wins > 0 ORDER BY robber_wins DESC LIMIT 5")
        top_robbers = await cur.fetchall()
        await cur.execute("SELECT user_id, ambushes_made FROM chase_stats WHERE ambushes_made > 0 ORDER BY ambushes_made DESC LIMIT 5")
        top_ambushers = await cur.fetchall()

    if not (top_cops or top_robbers or top_ambushers):
        return

    general_ch = discord.utils.get(guild.channels, name="💬-general-chat")
    if not general_ch:
        return

    embed = discord.Embed(title="🏆 COPS & ROBBERS — STANDINGS 🏆", color=discord.Color.gold(), timestamp=datetime.now())
    if top_cops:
        embed.add_field(name="👮 Most Arrests", value="\n".join(f"<@{u}> — {c}" for u, c in top_cops), inline=True)
    if top_ambushers:
        embed.add_field(name="🗡️ Most Ambushes", value="\n".join(f"<@{u}> — {c}" for u, c in top_ambushers), inline=True)
    if top_robbers:
        embed.add_field(name="🕶️ Most Evasions", value="\n".join(f"<@{u}> — {c}" for u, c in top_robbers), inline=True)
    embed.set_footer(text="Updated every 12 hours")

    try:
        await general_ch.send(embed=embed)
    except discord.HTTPException:
        pass


async def end_chase_round(guild, round_id: int, reason: str):
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT user_id, role, eliminated, participated FROM chase_participants WHERE round_id = ?", (round_id,))
        participants = await cur.fetchall()

    cop_lines, robber_lines = [], []

    async with db_connect() as conn:
        cur = await conn.cursor()
        for user_id, role, eliminated, participated in participants:
            await cur.execute(
                "INSERT INTO chase_stats (user_id, rounds_played) VALUES (?, 1) "
                "ON CONFLICT(user_id) DO UPDATE SET rounds_played = rounds_played + 1",
                (user_id,)
            )
            if not participated:
                await cur.execute(
                    "UPDATE chase_stats SET non_participation = non_participation + 1 WHERE user_id = ?", (user_id,)
                )
            elif role == "cop":
                if not eliminated:
                    # a cop "wins" by landing at least one arrest during the round
                    await cur.execute("SELECT arrests_made FROM chase_stats WHERE user_id = ?", (user_id,))
                    arrests_row = await cur.fetchone()
                    if arrests_row and arrests_row[0] > 0:
                        await cur.execute("UPDATE chase_stats SET cop_wins = cop_wins + 1 WHERE user_id = ?", (user_id,))
            elif role == "robber":
                if not eliminated:
                    await cur.execute("UPDATE chase_stats SET robber_wins = robber_wins + 1 WHERE user_id = ?", (user_id,))

            member = guild.get_member(user_id)
            label = member.mention if member else f"<@{user_id}>"
            if role == "cop":
                cop_lines.append(f"👮 {label}")
            elif role == "robber":
                robber_lines.append(f"{'✅ Survived' if not eliminated else '🚨 Caught'} — {label}")
        await cur.execute("UPDATE chase_rounds SET status = 'ended' WHERE round_id = ?", (round_id,))
        await conn.commit()

    general_ch = discord.utils.get(guild.channels, name="💬-general-chat")
    if general_ch:
        survivors = sum(1 for _, role, elim, part in participants if role == "robber" and part and not elim)
        embed = discord.Embed(
            title="🎬 UNMASKED — THE CHASE IS OVER",
            description=(
                f"*{reason}*\n\n"
                f"The badges come off, the disguises drop — here's who was playing who this round. "
                + (f"**{survivors}** robber(s) made it to the end without getting caught." if robber_lines else "")
            ),
            color=discord.Color.purple(),
            timestamp=datetime.now()
        )
        if cop_lines:
            embed.add_field(name="👮 The Cops", value="\n".join(cop_lines)[:1024], inline=False)
        if robber_lines:
            embed.add_field(name="🕶️ The Robbers", value="\n".join(robber_lines)[:1024], inline=False)
        try:
            await general_ch.send(embed=embed)
        except discord.HTTPException:
            pass

    await log_event(guild, f"🎬 **CHASE ENDED** (round #{round_id})\nReason: {reason}")


async def void_chase_round(guild, round_id: int):
    """For the specific case of a round nobody ever engaged with: unlike
    end_chase_round, this doesn't touch anyone's stats (nobody's
    rounds_played/non_participation counts change — there's nothing to
    hold against people for a match that never really happened), doesn't
    post an 'it's over' recap, and deletes the original public 'CHASE IS
    ON' announcement plus the round's own DB rows — so a dead round leaves
    no trace in the channel or the stats instead of cluttering both."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT announcement_msg_id FROM chase_rounds WHERE round_id = ?", (round_id,))
        row = await cur.fetchone()
        await cur.execute("DELETE FROM chase_participants WHERE round_id = ?", (round_id,))
        await cur.execute("DELETE FROM chase_rounds WHERE round_id = ?", (round_id,))
        await conn.commit()

    msg_id = row[0] if row else None
    if msg_id:
        general_ch = discord.utils.get(guild.channels, name="💬-general-chat")
        if general_ch:
            try:
                old_msg = await general_ch.fetch_message(msg_id)
                await old_msg.delete()
            except discord.HTTPException:
                pass

    await log_event(guild, f"🗑️ **CHASE VOIDED** (round #{round_id}) — nobody made a move in 30 minutes. No stats recorded, announcement removed.")


async def run_chase_round_timers(guild, round_id: int):
    """Drives one round's hourly hints through to its configured end,
    entirely from persisted DB state so a restart mid-round just picks
    back up."""
    round_hours = await get_config_value(guild.id, "chase_round_hours")
    while True:
        try:
            async with db_connect() as conn:
                cur = await conn.cursor()
                await cur.execute("SELECT status, ends_at, last_hint_tier, next_hint_at, last_activity_at FROM chase_rounds WHERE round_id = ?", (round_id,))
                row = await cur.fetchone()
            if not row or row[0] != "active":
                return

            _, ends_at_str, last_tier, next_hint_at_str, last_activity_str = row
            ends_at = datetime.fromisoformat(ends_at_str)
            next_hint_at = datetime.fromisoformat(next_hint_at_str) if next_hint_at_str else datetime.now()
            last_activity = datetime.fromisoformat(last_activity_str) if last_activity_str else None
            now = datetime.now()

            if now >= ends_at:
                await end_chase_round(guild, round_id, "⏰ Time's up — the clock ran out.")
                return

            if last_activity and (now - last_activity).total_seconds() >= GAME_INACTIVITY_TIMEOUT_SECONDS:
                await void_chase_round(guild, round_id)
                return

            if now >= next_hint_at and last_tier < round_hours:
                new_tier = last_tier + 1
                await send_chase_hints(guild, round_id, new_tier)
                new_next = now + timedelta(seconds=CHASE_HINT_INTERVAL_SECONDS)
                async with db_connect() as conn:
                    cur = await conn.cursor()
                    await cur.execute("UPDATE chase_rounds SET last_hint_tier = ?, next_hint_at = ? WHERE round_id = ?", (new_tier, new_next.isoformat(), round_id))
                    await conn.commit()
        except Exception as e:
            print(f"[ERROR] Chase round #{round_id} timer hit an error, will retry: {e}")

        await asyncio.sleep(30)


async def reschedule_active_chase_round(guild):
    """Startup recovery: resumes an in-progress round's timers after a restart."""
    active = await get_active_chase_round(guild)
    if active:
        round_id = active[0]
        print(f"[SYSTEM] 🚨 Resuming Cops & Robbers round #{round_id} after restart.")
        bot.loop.create_task(run_chase_round_timers(guild, round_id))


async def get_active_rogue_round(guild):
    """Returns (round_id, secret_name, ends_at) for the current hiding
    Rogue RoboCop, or None if nobody's currently hiding."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT round_id, secret_name, ends_at FROM rogue_bot_rounds WHERE status = 'active' ORDER BY round_id DESC LIMIT 1")
        return await cur.fetchone()


async def start_rogue_bot_round(guild) -> bool:
    """Kicks off a new round if nothing's already hiding. Returns False if
    one's already active — only one Rogue RoboCop at a time."""
    if await get_active_rogue_round(guild):
        return False
    if server_is_busy():
        return False  # no new Rogue RoboCop rounds while the real one is busy

    identity = random.choice(ROGUE_BOT_IDENTITIES)
    round_hours = await get_config_value(guild.id, "rogue_round_hours")
    now = datetime.now()
    ends_at = now + timedelta(hours=round_hours)

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute(
            "INSERT INTO rogue_bot_rounds (secret_name, ends_at, status, last_activity_at) VALUES (?, ?, 'active', ?)",
            (identity["name"], ends_at.isoformat(), now.isoformat())
        )
        round_id = cur.lastrowid
        await conn.commit()

    bot.loop.create_task(run_rogue_bot_round_timer(guild, round_id))
    return True


async def end_rogue_bot_round(guild, round_id: int, escaped: bool, caught_by: int = None, custom_description: str = None) -> bool:
    """Atomically closes out a round — the WHERE status='active' guard
    means only the first caller to reach this (a guess winning the race,
    or the expiry timer) actually succeeds; everyone else gets False and
    should treat it as 'someone/something else already ended this.'

    custom_description lets a caller (e.g. the inactivity auto-close, or a
    manual /game-end) override the generic "got away" copy with something
    more specific, while still using the same escaped=True bookkeeping."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute(
            "UPDATE rogue_bot_rounds SET status = 'ended', caught_by = ?, caught_at = ? WHERE round_id = ? AND status = 'active'",
            (caught_by, datetime.now().isoformat() if caught_by else None, round_id)
        )
        await conn.commit()
        if cur.rowcount == 0:
            return False
        await cur.execute("SELECT secret_name FROM rogue_bot_rounds WHERE round_id = ?", (round_id,))
        row = await cur.fetchone()
        secret_name = row[0] if row else "???"

    general_ch = discord.utils.get(guild.channels, name="💬-general-chat")
    if general_ch:
        if escaped:
            embed = discord.Embed(
                title="🕵️ THE ROGUE ROBOCOP GOT AWAY",
                description=custom_description or f"Nobody caught it in time — turns out **{secret_name}** was the culprit all along. It'll surface again eventually...",
                color=discord.Color.dark_grey()
            )
        else:
            catcher = guild.get_member(caught_by)
            embed = discord.Embed(
                title="🎉 THE ROGUE ROBOCOP HAS BEEN CAPTURED",
                description=f"{catcher.mention if catcher else 'Someone'} caught it! The culprit was **{secret_name}** all along.",
                color=discord.Color.gold()
            )
        try:
            await general_ch.send(embed=embed)
        except discord.HTTPException:
            pass
    return True


async def void_rogue_round(guild, round_id: int):
    """Same idea as void_chase_round: a round nobody even attempted to catch
    just disappears — no stats touched, no public message (Rogue RoboCop
    never posts one until it's caught or escapes anyway), just the DB row
    gone and a quiet #logs note for staff."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("DELETE FROM rogue_bot_rounds WHERE round_id = ?", (round_id,))
        await conn.commit()
    await log_event(guild, f"🗑️ **ROGUE ROBOCOP VOIDED** (round #{round_id}) — nobody even tried `/catch` in 30 minutes. No stats recorded.")


async def run_rogue_bot_round_timer(guild, round_id: int):
    while True:
        await asyncio.sleep(60)
        try:
            async with db_connect() as conn:
                cur = await conn.cursor()
                await cur.execute("SELECT status, ends_at, last_activity_at FROM rogue_bot_rounds WHERE round_id = ?", (round_id,))
                row = await cur.fetchone()
            if not row or row[0] != "active":
                return
            if datetime.now() >= datetime.fromisoformat(row[1]):
                await end_rogue_bot_round(guild, round_id, escaped=True)
                return
            last_activity_str = row[2]
            if last_activity_str:
                last_activity = datetime.fromisoformat(last_activity_str)
                if (datetime.now() - last_activity).total_seconds() >= GAME_INACTIVITY_TIMEOUT_SECONDS:
                    await void_rogue_round(guild, round_id)
                    return
        except Exception as e:
            print(f"[ERROR] Rogue bot round #{round_id} timer hit an error, will retry: {e}")


async def reschedule_active_rogue_round(guild):
    """Startup recovery: resumes an in-progress round's expiry timer after a restart."""
    active = await get_active_rogue_round(guild)
    if active:
        round_id = active[0]
        print(f"[SYSTEM] 🕵️ Resuming Rogue RoboCop round #{round_id} after restart.")
        bot.loop.create_task(run_rogue_bot_round_timer(guild, round_id))



async def daily_nickname_maintenance(guild):
    """Runs once a day: backfills user_nicknames for anyone who predates
    this system (or who was auto-registered without going through the
    interactive flow), and prunes entries for servers someone's since
    left. Doesn't touch live Discord nicknames — that's what
    /re-check-nicknames is for."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT user_id, in_game_name, server_number FROM users WHERE in_game_name IS NOT NULL AND server_number IS NOT NULL")
        all_users = await cur.fetchall()

    backfilled, pruned = 0, 0
    for user_id, in_game_name, server_field in all_users:
        server_nums = await parse_stored_server_field(server_field, guild.id)
        if not server_nums:
            continue

        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT server_number, is_active FROM user_nicknames WHERE user_id = ?", (user_id,))
            existing = await cur.fetchall()
        existing_servers = {s for s, _ in existing}
        has_active = any(a for _, a in existing)

        for num in server_nums:
            if num not in existing_servers:
                await upsert_user_nickname(user_id, num, in_game_name, make_active=not has_active)
                has_active = True
                backfilled += 1

        stale = [s for s, _ in existing if s not in server_nums]
        if stale:
            async with db_connect() as conn:
                cur = await conn.cursor()
                for s in stale:
                    await cur.execute("DELETE FROM user_nicknames WHERE user_id = ? AND server_number = ?", (user_id, s))
                    pruned += 1
                await conn.commit()

    if backfilled or pruned:
        await log_event(guild, f"📇 **NICKNAME MAINTENANCE**\nBackfilled: {backfilled} | Pruned stale entries: {pruned}")


async def daily_nickname_maintenance_scheduler(guild):
    while True:
        try:
            tz = await get_guild_timezone(guild.id)
            maintenance_hour = await get_config_value(guild.id, "nickname_maintenance_hour")
            now_local = datetime.now(tz)
            next_run = now_local.replace(hour=maintenance_hour, minute=0, second=0, microsecond=0)
            if next_run <= now_local:
                next_run += timedelta(days=1)
            await asyncio.sleep((next_run - now_local).total_seconds())

            if not _is_leader:
                continue
            await daily_nickname_maintenance(guild)
        except Exception as e:
            print(f"[ERROR] Nickname maintenance scheduler hit an error, will retry tomorrow: {e}")
            await asyncio.sleep(3600)


async def build_game_stats_embed(guild) -> discord.Embed:
    """Server-wide running totals across all three games — shared by the
    on-demand /game-stats command and the daily digest post. Voided rounds
    (30-minute-inactivity closures with zero engagement) are excluded by
    construction: they're deleted outright rather than marked 'ended', so
    they never show up in these counts."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT COALESCE(SUM(rps_wins),0), COALESCE(SUM(rps_losses),0), COALESCE(SUM(rps_ties),0) FROM user_stats")
        rps_wins, rps_losses, rps_ties = await cur.fetchone()

        await cur.execute("SELECT COUNT(*) FROM chase_rounds WHERE status = 'ended'")
        (chase_rounds_played,) = await cur.fetchone()
        await cur.execute(
            "SELECT COALESCE(SUM(cop_wins),0), COALESCE(SUM(robber_wins),0), "
            "COALESCE(SUM(arrests_made),0), COALESCE(SUM(ambushes_made),0) FROM chase_stats"
        )
        cop_wins, robber_wins, arrests_made, ambushes_made = await cur.fetchone()

        await cur.execute("SELECT COUNT(*) FROM rogue_bot_rounds WHERE status = 'ended'")
        (rogue_rounds_played,) = await cur.fetchone()
        await cur.execute("SELECT COUNT(*) FROM rogue_bot_rounds WHERE status = 'ended' AND caught_by IS NOT NULL")
        (rogue_caught,) = await cur.fetchone()
    rogue_escaped = rogue_rounds_played - rogue_caught

    embed = discord.Embed(
        title="📊 SERVER GAME STATISTICS",
        description="Running totals across every match ever played on this server.",
        color=discord.Color.blurple(),
        timestamp=datetime.now()
    )
    embed.add_field(
        name="🎮 Rock, Paper, Scissors",
        value=f"**{rps_wins}** win(s) · **{rps_losses}** loss(es) · **{rps_ties}** tie(s)",
        inline=False
    )
    embed.add_field(
        name="🚔 Cops & Robbers",
        value=(
            f"**{chase_rounds_played}** round(s) completed\n"
            f"🏆 Cop win(s): **{cop_wins}** | Robber win(s): **{robber_wins}**\n"
            f"🔫 Arrests made: **{arrests_made}** | Ambushes made: **{ambushes_made}**"
        ),
        inline=False
    )
    embed.add_field(
        name="🕵️ Rogue RoboCop",
        value=f"**{rogue_rounds_played}** round(s) completed — 🎉 Caught: **{rogue_caught}** | 🏃 Got away: **{rogue_escaped}**",
        inline=False
    )
    embed.set_footer(text="Voided rounds (nobody played) aren't counted here. Run /game-stats any time for the latest.")
    return embed


async def daily_game_stats_scheduler(guild):
    """Posts the same embed /game-stats builds to #general-chat once a day,
    at the configured hour (default midnight, local server time) — a
    passive digest on top of the on-demand command, same scheduling
    pattern as daily_chase_scheduler and the nickname maintenance job."""
    while True:
        try:
            tz = await get_guild_timezone(guild.id)
            stats_hour = await get_config_value(guild.id, "game_stats_hour")
            now_local = datetime.now(tz)
            next_run = now_local.replace(hour=stats_hour, minute=0, second=0, microsecond=0)
            if next_run <= now_local:
                next_run += timedelta(days=1)
            await asyncio.sleep((next_run - now_local).total_seconds())

            if not _is_leader:
                continue
            general_ch = discord.utils.get(guild.channels, name="💬-general-chat")
            if not general_ch:
                continue
            embed = await build_game_stats_embed(guild)
            embed.title = "📊 DAILY GAME STATS DIGEST"
            await general_ch.send(embed=embed)
        except Exception as e:
            print(f"[ERROR] Daily game-stats scheduler hit an error, will retry tomorrow: {e}")
            await asyncio.sleep(3600)


async def daily_chase_scheduler(guild):
    """Auto-starts a round every day at the configured hour, if nothing's
    already running and there's a big enough pool. /start-chase can
    trigger one on demand any time regardless of this schedule."""
    while True:
        try:
            tz = await get_guild_timezone(guild.id)
            start_hour = await get_config_value(guild.id, "chase_start_hour")
            now_local = datetime.now(tz)
            next_run = now_local.replace(hour=start_hour, minute=0, second=0, microsecond=0)
            if next_run <= now_local:
                next_run += timedelta(days=1)
            await asyncio.sleep((next_run - now_local).total_seconds())

            if not _is_leader:
                continue
            await wait_until_not_busy()  # the daily chase waits for maintenance rather than being skipped
            if await get_active_chase_round(guild):
                continue
            success, message = await start_chase_round(guild, "🕛 Automatic Daily Chase")
            if not success:
                await log_event(guild, f"ℹ️ **DAILY CHASE SKIPPED**\n{message}")
        except Exception as e:
            print(f"[ERROR] Daily chase scheduler hit an error, will retry tomorrow: {e}")
            await asyncio.sleep(3600)  # back off an hour rather than tight-looping on a persistent error


async def schedule_chase_recruit_dm(member, delay_seconds: float):
    await asyncio.sleep(max(0, delay_seconds))
    guild = member.guild
    if not guild.get_member(member.id):
        return  # they've left since
    try:
        await member.send(embed=discord.Embed(
            title="🕵️ A Word From The Grapevine",
            description=(
                "Word on the street is you've been keeping your nose clean here for a few hours now.\n\n"
                "Every day at noon, this precinct runs something a little different: **Cops & Robbers**. "
                "Roles get handed out in secret — you might already have played without knowing it, or you "
                "might get pulled into the next one. Cops hunt with poetic clues. Robbers hide in plain "
                "sight, and can strike back. Nobody finds out who's who until someone gets caught, or the "
                "six hours run out.\n\n"
                "You're automatically in the mix for future rounds. Not your thing? Run `/leave-chase` any "
                "time to sit it out.\n\nSee you in the shadows, Chief."
            ),
            color=discord.Color.dark_purple()
        ))
    except discord.Forbidden:
        pass
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("UPDATE users SET chase_recruit_sent = 1 WHERE user_id = ?", (member.id,))
        await conn.commit()


async def reschedule_pending_chase_recruits(guild):
    """Startup recovery for the 6-hours-after-joining recruitment DM."""
    now = datetime.now()
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT user_id, chase_recruit_at FROM users WHERE chase_recruit_at IS NOT NULL AND chase_recruit_sent = 0")
        rows = await cur.fetchall()

    restored = 0
    for user_id, recruit_at_str in rows:
        member = guild.get_member(user_id)
        if not member:
            continue
        try:
            recruit_at = datetime.fromisoformat(recruit_at_str)
        except (TypeError, ValueError):
            continue
        remaining = (recruit_at - now).total_seconds()
        if remaining <= 0:
            bot.loop.create_task(schedule_chase_recruit_dm(member, 0))
        else:
            bot.loop.create_task(schedule_chase_recruit_dm(member, remaining))
        restored += 1
    if restored:
        print(f"[SYSTEM] Rescheduled {restored} pending Cops & Robbers recruitment DM(s).")


async def chase_leaderboard_syndication_loop(guild):
    while True:
        await asyncio.sleep(CHASE_LEADERBOARD_INTERVAL_SECONDS)
        try:
            if not _is_leader:
                continue
            await post_chase_leaderboard(guild)
        except Exception as e:
            print(f"[ERROR] Chase leaderboard syndication hit an error, will retry next cycle: {e}")


# ============================================================
#  SLASH COMMANDS (ADMIN ONLY)
# ============================================================
@bot.tree.command(name="unban", description="Unbans a user from Discord and resets their Robocop infractions.")
@app_commands.describe(user_id="Discord User ID (right-click user -> Copy User ID)")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def unban_user(interaction: discord.Interaction, user_id: str):
    try:
        uid = int(user_id.strip())
    except ValueError:
        await interaction.response.send_message("❌ Invalid user ID format.", ephemeral=True)
        return

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("UPDATE users SET timeout_until = NULL, lifetime_invite_fails = 0, invite_strikes = 0 WHERE user_id = ?", (uid,))
        await cur.execute("DELETE FROM bans WHERE user_id = ?", (uid,))
        await cur.execute("UPDATE mod_log SET undone = 1 WHERE target_id = ? AND action_type = 'ban' AND undone = 0", (uid,))
        await conn.commit()

    try:
        user_to_unban = await bot.fetch_user(uid)
        await interaction.guild.unban(user_to_unban, reason=f"Unbanned by admin {interaction.user.name}")
        await interaction.response.send_message(f"✅ Successfully unbanned **{user_to_unban.name}** ({uid}) and cleared all infractions.", ephemeral=True)
        await log_event(interaction.guild, f"🕊️ **LIFETIME BAN LIFTED**\nAdmin: {interaction.user.mention}\nTarget: {user_to_unban.mention} (`{uid}`)\nAction: Discord ban revoked and database reset.")
    except discord.NotFound:
        await interaction.response.send_message(f"⚠️ Cleared database records, but user `{uid}` was not found in Discord's server ban list.", ephemeral=True)
    except discord.Forbidden:
        await interaction.response.send_message("❌ Robocop lacks the 'Ban Members' permission to revoke bans in this server.", ephemeral=True)
    except Exception as e:
        await interaction.response.send_message(f"❌ An error occurred: {e}", ephemeral=True)


@bot.tree.command(name="pardon", description="Clears active timeouts, resets invite fails, and releases prisoners.")
@app_commands.describe(user_id="Discord User ID (right-click user -> Copy User ID)")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def pardon(interaction: discord.Interaction, user_id: str):
    await interaction.response.defer(ephemeral=True)
    try:
        uid = int(user_id.strip())
    except ValueError:
        await interaction.followup.send("❌ Invalid ID format.", ephemeral=True)
        return

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("UPDATE users SET timeout_until = NULL, lifetime_invite_fails = 0, prison_until = NULL WHERE user_id = ?", (uid,))
        await cur.execute("UPDATE mod_log SET undone = 1 WHERE target_id = ? AND action_type = 'imprison' AND undone = 0", (uid,))
        await conn.commit()

    member = interaction.guild.get_member(uid)
    cleared_roles = []
    if member:
        timeout_role = discord.utils.get(interaction.guild.roles, name=ROLE_TIMEOUT)
        prison_role = discord.utils.get(interaction.guild.roles, name=ROLE_PRISONER)

        if timeout_role and timeout_role in member.roles:
            await member.remove_roles(timeout_role)
            cleared_roles.append("Time-Out Corner")

        if prison_role and prison_role in member.roles:
            await member.remove_roles(prison_role)
            await restore_stored_roles(member)
            cleared_roles.append("Prisoner")

    if cleared_roles and member:
        await send_splash_announcement(interaction.guild, uid, PARDON_SPLASH_FLAVOR, member.mention)

    await interaction.followup.send(f"✅ User ID {uid} has been pardoned. ({', '.join(cleared_roles) if cleared_roles else 'No active lockup roles found'})", ephemeral=True)
    await log_event(interaction.guild, f"🕊️ **USER PARDONED**\nAdmin: {interaction.user.mention}\nTarget ID: {uid}\nAction: Infractions cleared. Released from restrictions.")


@bot.tree.command(name="re-check-nicknames", description="Audits nickname compliance against actual current roles, with one-click fixes.")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def re_check_nicknames(interaction: discord.Interaction):
    async with server_busy("re-checking every nickname on the server"):
        await interaction.response.send_message("🔍 Auditing nicknames against current roles...", ephemeral=True)

        guild = interaction.guild
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT tag FROM alliances")
            approved_tags = {row[0] for row in await cur.fetchall()}
            await cur.execute("SELECT user_id, in_game_name FROM users")
            in_game_names = {row[0]: row[1] for row in await cur.fetchall()}

        mismatches = []
        incomplete = 0

        for m in guild.members:
            if m.bot:
                continue
            if not any(r.name in approved_tags for r in m.roles):
                continue  # not an alliance member — nothing to check

            expected = await compute_expected_nickname(m, approved_tags, in_game_names)
            if expected is None:
                incomplete += 1
                continue

            if m.display_name.strip() != expected:
                mismatches.append((m, expected))

        if not mismatches and not incomplete:
            await interaction.edit_original_response(content="✅ Every alliance member's nickname already matches their roles. Nothing to fix.")
            return

        summary_lines = [f"🔍 **Audit complete.** {len(mismatches)} nickname(s) don't match current roles."]
        if incomplete:
            summary_lines.append(f"ℹ️ {incomplete} member(s) hold an alliance tag but no configured server role, so I can't compute an expected nickname for them.")
        if mismatches:
            summary_lines.append("Details and one-click fixes are in #logs.")
        await interaction.edit_original_response(content="\n".join(summary_lines))

        if not mismatches:
            return

        log_channel = discord.utils.get(guild.channels, name="logs")
        if not log_channel:
            return

        BATCH_SIZE = 10
        for batch_start in range(0, len(mismatches), BATCH_SIZE):
            batch = mismatches[batch_start:batch_start + BATCH_SIZE]
            lines = []
            fixes = []
            for i, (m, expected) in enumerate(batch, start=batch_start + 1):
                lines.append(f"**#{i}** {m.mention}\n　Now: `{m.display_name}`\n　Fixed: `{expected}`")
                fixes.append((m.id, expected, i))

            embed = discord.Embed(
                title=f"✏️ NICKNAME COMPLIANCE — {batch_start + 1}–{batch_start + len(batch)} of {len(mismatches)}",
                description="\n\n".join(lines),
                color=discord.Color.orange(),
                timestamp=datetime.now()
            )
            try:
                await log_channel.send(embed=embed, view=NicknameFixView(fixes))
            except discord.HTTPException:
                pass


@bot.tree.command(name="imprison", description="Lock a user in solitary confinement. Strips roles to prevent bypass.")
@app_commands.describe(nickname="Base in-game name (no tags)", minutes="Minutes to lock up")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def imprison(interaction: discord.Interaction, nickname: str, minutes: int):
    if minutes <= 0:
        await interaction.response.send_message("❌ Minutes must be a positive number.", ephemeral=True)
        return

    target = find_member_by_base_name(interaction.guild, nickname)
    if not target:
        await interaction.response.send_message(f"❌ Could not find user matching base name '{nickname}'.", ephemeral=True)
        return

    prison_role = discord.utils.get(interaction.guild.roles, name=ROLE_PRISONER)
    if not prison_role:
        await interaction.response.send_message("❌ Prisoner role not found. Run infrastructure setup first.", ephemeral=True)
        return

    # NOTE: is_premium_subscriber() must be called (it's a method, not a
    # property) — leaving off the parentheses made this condition always
    # False in the original code, meaning NO roles were ever stripped.
    roles_to_remove = [
        r for r in target.roles
        if r != interaction.guild.default_role and not r.is_premium_subscriber() and r.name != "Prisoner"
    ]

    for r in roles_to_remove:
        if r.position >= interaction.guild.me.top_role.position:
            await interaction.response.send_message(f"❌ I cannot imprison `{target.display_name}` because they possess the role `{r.name}`, which is higher than or equal to my rank!", ephemeral=True)
            return

    try:
        await interaction.response.defer()

        release_time = datetime.now() + timedelta(minutes=minutes)
        role_ids = ",".join(str(r.id) for r in roles_to_remove)
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("UPDATE users SET stored_roles = ?, prison_until = ? WHERE user_id = ?", (role_ids, release_time.isoformat(), target.id))
            await conn.commit()

        if roles_to_remove:
            await target.remove_roles(*roles_to_remove)
        await target.add_roles(prison_role)

        await interaction.followup.send(f"🚨 {target.mention} stripped of rank and imprisoned for {minutes} minute(s).")

        await log_mod_action(
            interaction.guild, "imprison", target.id, target.display_name,
            interaction.user.mention, f"{minutes} minute(s) — {len(roles_to_remove)} role(s) stripped"
        )

        prison_channel = discord.utils.get(interaction.guild.channels, name="⛓️-solitary-confinement")
        if prison_channel:
            await prison_channel.send(f"⛓️ Welcome to your cell, {target.mention}. Reflect on your actions.")

        await send_splash_announcement(interaction.guild, target.id, IMPRISON_SPLASH_FLAVOR, target.mention)

        bot.loop.create_task(schedule_release(target, prison_role, minutes * 60))

    except discord.Forbidden:
        await interaction.followup.send(f"❌ Missing permissions to fully imprison `{target.display_name}`.", ephemeral=True)
    except Exception as e:
        await interaction.followup.send(f"❌ An error occurred: {e}", ephemeral=True)


@bot.tree.command(name="approve-tag", description="Unlocks quarantined alliance & removes Drunk Tank.")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def approve_tag(interaction: discord.Interaction, tag: str):
    tag = normalize_alliance_key(tag)
    did_something = await approve_alliance(interaction.guild, tag, approver_label=interaction.user.mention)
    if not did_something:
        await interaction.response.send_message(f"ℹ️ [{tag}] doesn't exist or was already approved.", ephemeral=True)
        return
    await interaction.response.send_message(f"✅ Tag [{tag}] approved and released from the Drunk Tank.")


@bot.tree.command(name="announce", description="Broadcast an announcement — scope and cooldown depend on your rank.")
@app_commands.describe(message="The announcement text")
async def announce(interaction: discord.Interaction, message: str):
    guild = interaction.guild
    user = interaction.user
    now_ts = time.monotonic()

    if is_staff_member(user):
        targets = await gather_all_community_channels(guild)
        scope_label = "the entire server"

    else:
        role_names = {r.name for r in user.roles}
        r5_tags = [name[:-3] for name in role_names if name.endswith("-R5")]

        if r5_tags:
            tag = r5_tags[0]
            last = _announce_cooldowns.get(user.id, 0)
            if now_ts - last < ANNOUNCE_R5_COOLDOWN_SECONDS:
                remaining = int(ANNOUNCE_R5_COOLDOWN_SECONDS - (now_ts - last))
                await interaction.response.send_message(f"⏳ You can announce again in {remaining // 60}m {remaining % 60}s.", ephemeral=True)
                return

            chat_category = discord.utils.get(guild.categories, name=f"{tag} CHATS")
            targets = list(chat_category.text_channels) if chat_category else []
            scope_label = f"**[{tag}]**'s channels"
        else:
            last = _announce_cooldowns.get(user.id, 0)
            if now_ts - last < ANNOUNCE_DEFAULT_COOLDOWN_SECONDS:
                remaining = int(ANNOUNCE_DEFAULT_COOLDOWN_SECONDS - (now_ts - last))
                await interaction.response.send_message(f"⏳ You can announce again in {remaining // 60}m {remaining % 60}s.", ephemeral=True)
                return

            targets = [interaction.channel]
            scope_label = "this channel"

        _announce_cooldowns[user.id] = now_ts

    if not targets:
        await interaction.response.send_message("❌ Couldn't find any chat channels to announce to.", ephemeral=True)
        return

    embed = discord.Embed(
        title="🚨 ANNOUNCEMENT FROM COMMAND 🚨",
        description=message,
        color=discord.Color.blue(),
        timestamp=datetime.now()
    )
    embed.set_footer(text=f"Announced by {user.display_name}")

    await interaction.response.send_message(f"📢 Broadcasting to {scope_label} ({len(targets)} channel(s))...", ephemeral=True)

    sent = 0
    failed = 0
    for ch in targets:
        try:
            await ch.send(embed=embed)
            sent += 1
        except discord.HTTPException:
            failed += 1

    result = f"✅ Sent to {sent} channel(s)."
    if failed:
        result += f" ⚠️ Failed on {failed}."
    await interaction.followup.send(result, ephemeral=True)
    await log_event(guild, f"📢 **ANNOUNCEMENT BROADCAST**\nBy: {user.mention}\nScope: {scope_label}\nChannels reached: {sent}\nMessage: {message[:500]}")


@bot.tree.command(name="killswitch", description="Emergency lockdown pausing chat.")
@app_commands.describe(minutes="Minutes to lockdown (1-30)", off="Turn off lockdown")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def killswitch(interaction: discord.Interaction, minutes: int = 1, off: bool = False):
    await interaction.response.defer()
    guild = interaction.guild

    if off:
        await lift_lockdown(guild)
        off_embed = discord.Embed(title="🟢 LOCKDOWN LIFTED", description="Perimeter secure. Normal chat functions restored.", color=discord.Color.green())
        await interaction.followup.send(embed=off_embed)
        await log_event(guild, f"🟢 **KILLSWITCH LIFTED**\nAdmin: {interaction.user.mention}\nAction: Chat unlocked manually.")
        return

    minutes = max(1, min(minutes, 30))
    member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)

    perms = guild.default_role.permissions
    perms.update(send_messages=False)
    await guild.default_role.edit(permissions=perms)
    if member_role:
        m_perms = member_role.permissions
        m_perms.update(send_messages=False)
        await member_role.edit(permissions=m_perms)

    end_time = datetime.now() + timedelta(minutes=minutes)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("INSERT OR REPLACE INTO settings (key, value) VALUES (?, ?)", (f"lockdown_until_{guild.id}", end_time.isoformat()))
        await conn.commit()

    embed = discord.Embed(
        title="🚨 EMERGENCY PROTOCOL ENGAGED 🚨",
        description=f"**BASE UNDER ATTACK!**\nPublic chat has been locked by {interaction.user.mention}.\n\n⏳ **Status:** *{minutes} minute(s) remaining...*",
        color=discord.Color.red()
    )
    embed.set_image(url="https://media.giphy.com/media/v1.Y2lkPTc5MGI3NjExMjM4NTRjZjM2ZjNmMWU0MWE5MjA2ODQ5MThkM2I3YzdmNDFmNmU5MiZlcD12MV9pbnRlcm5hbF9naWZzX2dpZklkJmN0PWc/11TSYq5z9XUms0/giphy.gif")

    await interaction.followup.send(embed=embed)
    await log_event(guild, f"🔴 **KILLSWITCH ENGAGED**\nAdmin: {interaction.user.mention}\nDuration: {minutes} minute(s)")

    msg = await interaction.original_response()
    try:
        await msg.pin()
    except discord.HTTPException:
        pass

    while datetime.now() < end_time:
        remaining = int((end_time - datetime.now()).total_seconds())
        if remaining <= 0:
            break
        m, s = divmod(remaining, 60)
        await asyncio.sleep(15)
        try:
            embed.description = f"**BASE UNDER ATTACK!**\nPublic chat has been locked by {interaction.user.mention}.\n\n⏳ **Status:** *{m}m {s}s remaining.*"
            await interaction.edit_original_response(embed=embed)
        except discord.HTTPException:
            break

    await lift_lockdown(guild)

    try:
        embed.title = "🟢 LOCKDOWN LIFTED"
        embed.description = "Perimeter secure. Normal chat functions restored."
        embed.color = discord.Color.green()
        embed.set_image(url=None)
        await interaction.edit_original_response(embed=embed)
        await msg.unpin()
    except discord.HTTPException:
        pass


@bot.tree.command(name="warn", description="Issue a formal warning to a member.")
@app_commands.describe(member="The member to warn", reason="Why they're being warned")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def warn(interaction: discord.Interaction, member: discord.Member, reason: str):
    await interaction.response.defer()
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("INSERT INTO warnings (user_id, moderator_id, reason) VALUES (?, ?, ?)", (member.id, interaction.user.id, reason))
        await cur.execute("SELECT COUNT(*) FROM warnings WHERE user_id = ?", (member.id,))
        warn_count = (await cur.fetchone())[0]
        await conn.commit()

    warn_embed = discord.Embed(
        title="⚠️ WARNING ISSUED",
        color=discord.Color.orange(),
        timestamp=datetime.now()
    )
    warn_embed.set_thumbnail(url=member.display_avatar.url)
    warn_embed.add_field(name="Target", value=member.mention, inline=True)
    warn_embed.add_field(name="Total Warnings", value=str(warn_count), inline=True)
    warn_embed.add_field(name="Reason", value=reason, inline=False)
    warn_embed.set_footer(text=f"Issued by {interaction.user.display_name}")

    await interaction.followup.send(embed=warn_embed)
    log_channel = discord.utils.get(interaction.guild.channels, name="logs")
    if log_channel:
        try:
            await log_channel.send(embed=warn_embed)
        except discord.HTTPException:
            pass

    try:
        await member.send(f"⚠️ You have received a formal warning in **{interaction.guild.name}**.\nReason: {reason}\nPlease review the server rules to avoid further action.")
    except discord.Forbidden:
        pass


@bot.tree.command(name="warnings", description="View a member's warning history.")
@app_commands.describe(member="The member to check")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def warnings_cmd(interaction: discord.Interaction, member: discord.Member):
    await interaction.response.defer(ephemeral=True)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT reason, timestamp FROM warnings WHERE user_id = ? ORDER BY timestamp DESC", (member.id,))
        rows = await cur.fetchall()

    if not rows:
        await interaction.followup.send(f"✅ {member.display_name} has no warnings on file.", ephemeral=True)
        return

    out = f"⚠️ **Warning History for {member.display_name}** ({len(rows)} total):\n"
    out += "\n".join([f"• {r[1]} — {r[0]}" for r in rows])
    await interaction.followup.send(out[:2000], ephemeral=True)


@bot.tree.command(name="server-stats", description="View tracked usage statistics — translations, referrals, RPS records, and more.")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def server_stats(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    async with db_connect() as conn:
        cur = await conn.cursor()

        await cur.execute("SELECT key, value FROM stats")
        global_stats = {row[0]: row[1] for row in await cur.fetchall()}

        await cur.execute("SELECT COUNT(*) FROM translated_messages")
        distinct_messages = (await cur.fetchone())[0]

        await cur.execute("SELECT user_id, referrals FROM user_stats WHERE referrals > 0 ORDER BY referrals DESC LIMIT 5")
        top_referrers = await cur.fetchall()

        await cur.execute(
            "SELECT user_id, rps_wins, rps_losses, rps_ties FROM user_stats "
            "WHERE rps_wins + rps_losses + rps_ties > 0 ORDER BY rps_wins DESC LIMIT 5"
        )
        top_rps = await cur.fetchall()

        await cur.execute("SELECT user_id, rogue_catches FROM user_stats WHERE rogue_catches > 0 ORDER BY rogue_catches DESC LIMIT 5")
        top_rogue_catchers = await cur.fetchall()

    embed = discord.Embed(title="📊 SERVER STATISTICS", color=discord.Color.blurple(), timestamp=datetime.now())

    embed.add_field(
        name="🌐 Translation Usage",
        value=(
            f"Translations served: **{global_stats.get('translations_used', 0)}**\n"
            f"🌐-reaction uses: **{global_stats.get('translate_reactions_total', 0)}** "
            f"(on **{distinct_messages}** distinct message(s))"
        ),
        inline=False
    )

    if top_referrers:
        lines = [f"<@{uid}> — {count} referral(s)" for uid, count in top_referrers]
        embed.add_field(name="🎫 Top Referrers", value="\n".join(lines), inline=False)
    else:
        embed.add_field(name="🎫 Top Referrers", value="No referrals tracked yet.", inline=False)

    if top_rps:
        lines = []
        for uid, wins, losses, ties in top_rps:
            total = wins + losses + ties
            ratio = f"{wins}/{losses}/{ties}" + (f" ({wins / total:.0%} win rate)" if total else "")
            lines.append(f"<@{uid}> — {ratio}")
        embed.add_field(name="🎮 Top RPS Records (W/L/T)", value="\n".join(lines), inline=False)
    else:
        embed.add_field(name="🎮 Top RPS Records", value="Nobody's played yet.", inline=False)

    if top_rogue_catchers:
        lines = [f"<@{uid}> — {count} catch(es)" for uid, count in top_rogue_catchers]
        embed.add_field(name="🤖 Rogue RoboCop Catches", value="\n".join(lines), inline=False)

    embed.set_footer(text="More stats may be added over time — this is a living dashboard.")
    await interaction.followup.send(embed=embed, ephemeral=True)


@bot.tree.command(name="show-banned", description="Displays permanently banned users & infraction logs.")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def show_banned(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT username, reason, timestamp FROM bans")
        records = await cur.fetchall()
    if not records:
        await interaction.followup.send("No database bans found.", ephemeral=True)
        return
    out = "**Permanently Banned Users:**\n" + "\n".join([f"• {r[0]} - {r[1]} ({r[2]})" for r in records])
    await interaction.followup.send(out[:2000], ephemeral=True)


@bot.tree.command(name="add-request-role", description="Adds custom role option to database.")
@app_commands.describe(role="Role name", description="Role description")
@app_commands.default_permissions(manage_channels=True)
@is_senior_staff()
async def add_request_role(interaction: discord.Interaction, role: str, description: str):
    await interaction.response.defer(ephemeral=True)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("INSERT OR REPLACE INTO custom_roles (role_name, description) VALUES (?, ?)", (role, description))
        await conn.commit()
    await interaction.followup.send(f"✅ Custom role option **{role}** added to database.", ephemeral=True)


@bot.tree.command(name="configure-setting", description="View or change a live-adjustable setting.")
@app_commands.describe(setting="Which setting to view or change", value="New value (leave blank to just view the current value)")
@app_commands.choices(setting=[
    app_commands.Choice(name=meta["label"][:100], value=key) for key, meta in CONFIGURABLE_SETTINGS.items()
])
@app_commands.default_permissions(manage_channels=True)
@is_senior_staff()
async def configure_setting(interaction: discord.Interaction, setting: str, value: str = None):
    meta = CONFIGURABLE_SETTINGS[setting]
    current = await get_config_value(interaction.guild.id, setting)

    if value is None:
        await interaction.response.send_message(
            f"📋 **{meta['label']}**\nCurrent value: `{current}`\nDefault: `{meta['default']}`",
            ephemeral=True
        )
        return

    if meta["type"] is str:
        if setting == "timezone":
            try:
                ZoneInfo(value)
            except Exception:
                await interaction.response.send_message(
                    f"❌ `{value}` isn't a timezone I can resolve. Use an IANA name like `America/Los_Angeles` or `Europe/London`.",
                    ephemeral=True
                )
                return
        new_value = value
    else:
        try:
            new_value = meta["type"](value)
        except ValueError:
            await interaction.response.send_message(f"❌ `{value}` isn't a valid {meta['type'].__name__}.", ephemeral=True)
            return
        lo, hi = meta.get("min"), meta.get("max")
        if (lo is not None and new_value < lo) or (hi is not None and new_value > hi):
            await interaction.response.send_message(f"❌ Must be between {lo} and {hi}.", ephemeral=True)
            return

    await set_guild_setting(interaction.guild.id, f"config:{setting}", str(new_value))
    await interaction.response.send_message(f"✅ **{meta['label']}** is now `{new_value}` (was `{current}`).", ephemeral=True)
    await log_event(interaction.guild, f"🔧 **SETTING CHANGED**\nBy: {interaction.user.mention}\n{meta['label']}: `{current}` → `{new_value}`")


@bot.tree.command(name="toggle-innovator-program", description="Turn future automatic Innovator badge grants on or off.")
@app_commands.describe(active="True to keep granting the badge to new registrants, False to stop")
@app_commands.default_permissions(manage_channels=True)
@is_senior_staff()
async def toggle_innovator_program(interaction: discord.Interaction, active: bool):
    await set_guild_setting(interaction.guild.id, "innovator_program_active", "1" if active else "0")
    status = "ON — new registrants will keep getting the badge" if active else "OFF — no new Innovator badges will be granted"
    await interaction.response.send_message(f"🌟 Innovator program is now **{status}**. Existing badge holders are unaffected either way.", ephemeral=True)


@bot.tree.command(name="toggle-rogue-bot-program", description="Turn the automatic Rogue RoboCop round (triggered by version handoffs) on or off.")
@app_commands.describe(active="True for normal operation, False to suppress it — handy during a deliberate migration/adoption event")
@app_commands.default_permissions(manage_channels=True)
@is_senior_staff()
async def toggle_rogue_bot_program(interaction: discord.Interaction, active: bool):
    await set_guild_setting(interaction.guild.id, "rogue_bot_program_active", "1" if active else "0")
    status = "ON — a real version handoff will kick off a round as usual" if active else "OFF — version handoffs won't start a round until this is turned back on"
    await interaction.response.send_message(f"🕵️ Rogue RoboCop program is now **{status}**. Any round already in progress is unaffected either way.", ephemeral=True)


@bot.tree.command(name="announce-update", description="Manually fire the system-update announcement and brief lockdown, without waiting for a live handoff.")
@app_commands.default_permissions(administrator=True)
@is_dictator()
async def announce_update(interaction: discord.Interaction):
    await interaction.response.send_message("📢 Sending it now...", ephemeral=True)
    await announce_version_handoff(interaction.guild)


@bot.tree.command(name="bulk-onboard-existing", description="Bulk-register everyone already in the server — for adopting an existing single-alliance server.")
@app_commands.describe(tag="The alliance tag to assume for everyone", servers="Server number(s) to assume for everyone, comma-separated (e.g. 21,121)")
@app_commands.default_permissions(administrator=True)
@is_dictator()
async def bulk_onboard_existing(interaction: discord.Interaction, tag: str, servers: str):
    async with server_busy("onboarding a whole alliance at once"):
        guild = interaction.guild
        tag = tag.strip().upper()
        server_list = [s.strip() for s in servers.split(",") if s.strip()]
        managed = await get_managed_servers(guild.id)
        invalid = [s for s in server_list if s not in managed]
        if invalid:
            await interaction.response.send_message(f"❌ Not configured servers: {', '.join(invalid)}. Configured: {', '.join(managed)}", ephemeral=True)
            return
        if not server_list:
            await interaction.response.send_message("❌ Give at least one server number.", ephemeral=True)
            return

        tag_role = discord.utils.get(guild.roles, name=tag)
        if not tag_role:
            await interaction.response.send_message(f"❌ No **{tag}** role exists yet — run `/adopt-alliance {tag}` first.", ephemeral=True)
            return

        await interaction.response.defer(ephemeral=True)

        member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)
        srv_display = format_server_display(server_list)
        server_field = ",".join(server_list)

        onboarded, skipped = 0, 0
        for member in guild.members:
            if member.bot:
                continue

            async with db_connect() as conn:
                cur = await conn.cursor()
                await cur.execute(
                    "SELECT in_game_name, alliance_tag, rank_designation, server_number FROM users WHERE user_id = ?",
                    (member.id,)
                )
                row = await cur.fetchone()

            if row and row[0] and row[1] and row[2] and row[3]:
                skipped += 1
                continue

            # Guess rank from whatever tag-rank role they might already hold —
            # e.g. from /migrate-legacy-roles having already run first.
            rank = "Member"
            for candidate_rank in ("R5", "R4"):
                candidate_role = discord.utils.get(guild.roles, name=f"{tag}-{candidate_rank}")
                if candidate_role and candidate_role in member.roles:
                    rank = candidate_rank
                    break

            in_game_name = strip_nickname_decorations(member.display_name) or member.name

            async with db_connect() as conn:
                cur = await conn.cursor()
                await cur.execute(
                    "INSERT INTO users (user_id, original_username, in_game_name, alliance_tag, rank_designation, server_number, "
                    "language_selected, invite_check_passed, test_disclaimer_ack) "
                    "VALUES (?, ?, ?, ?, ?, ?, 1, 1, 1) "
                    "ON CONFLICT(user_id) DO UPDATE SET in_game_name=excluded.in_game_name, alliance_tag=excluded.alliance_tag, "
                    "rank_designation=excluded.rank_designation, server_number=excluded.server_number",
                    (member.id, str(member), in_game_name, tag, rank, server_field)
                )
                await conn.commit()

            roles_to_add = [r for r in (member_role, tag_role) if r]
            for num in server_list:
                srv_role = discord.utils.get(guild.roles, name=role_name_for_server(num))
                if srv_role:
                    roles_to_add.append(srv_role)
            try:
                await member.add_roles(*roles_to_add)
            except discord.HTTPException:
                pass

            name_budget = 32 - len(f" [{tag_display(tag)}] {srv_display}")
            new_nick = f"{in_game_name[:max(1, name_budget)]} [{tag_display(tag)}] {srv_display}"
            try:
                await member.edit(nick=new_nick[:32])
            except discord.HTTPException:
                pass

            role_req_ch = discord.utils.get(guild.channels, name="⚙️-role-requests")
            abilities_ch = discord.utils.get(guild.channels, name="❓-abilities")
            try:
                await member.send(embed=discord.Embed(
                    title="🚔 You're officially registered",
                    description=(
                        f"This server just got upgraded, and you've been carried over as **[{tag}]**, server "
                        f"**{srv_display}** — no action needed on your part, that's already done.\n\n"
                        f"A couple of things worth knowing: run `/abilities` any time (also works great in "
                        f"{abilities_ch.mention if abilities_ch else '#❓-abilities'}) for a full rundown of what you "
                        f"can do. And if you actually play on more than just server {srv_display}, head to "
                        f"{role_req_ch.mention if role_req_ch else '#⚙️-role-requests'} to add any other servers you're "
                        f"on — I only assumed the one for now.\n\n"
                        f"If your in-game name isn't quite right, `/nickname` lets you fix that any time too."
                    ),
                    color=discord.Color.blue()
                ))
            except discord.Forbidden:
                pass

            onboarded += 1

        await interaction.followup.send(
            f"✅ **Bulk onboarding complete.**\nRegistered: **{onboarded}**\nAlready registered (skipped): **{skipped}**\n\n"
            f"Everyone registered got: name = their current display name, alliance = [{tag}], servers = {srv_display}, "
            f"rank = whatever [{tag}]-R4/R5 role they already held (else plain Member) — plus a DM pointing them at "
            f"`/abilities` and #⚙️-role-requests for any other servers they actually play on beyond {srv_display}. "
            f"Anyone can correct their own name any time with `/nickname`.",
            ephemeral=True
        )
        await log_event(guild, f"📇 **BULK ONBOARDING**\nBy: {interaction.user.mention}\nTag: [{tag}]\nServers: {srv_display}\nRegistered: {onboarded} | Skipped: {skipped}")


# ------------------------------------------------------------
#  ALLIANCE ADOPTION WIZARD — for bringing an existing, already-populated
#  server (built before this bot, or before it managed multiple alliances)
#  into our structure without losing anything. Every mapping is a human
#  choice from a live-fetched list of what's actually there — nothing is
#  guessed or auto-matched by name.
# ------------------------------------------------------------
@bot.tree.command(name="ptd-reset", description="Clears PTD's alliance registration for a clean /ptd-upgrade-now retry. Channels/roles untouched.")
@app_commands.default_permissions(administrator=True)
@is_dictator()
async def ptd_reset(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("DELETE FROM alliances WHERE tag = 'PTD'")
        deleted = cur.rowcount
        await conn.commit()

    if deleted:
        await interaction.followup.send(
            "✅ Cleared PTD's alliance registration. `/ptd-upgrade-now` will run as a full fresh attempt now — "
            "anything already correct (channels, roles, individual registrations) will still just be recognized "
            "and skipped, not redone or broken.",
            ephemeral=True
        )
        await log_event(interaction.guild, f"🔄 **PTD REGISTRATION RESET** by {interaction.user.mention} — ready for a clean /ptd-upgrade-now run.")
    else:
        await interaction.followup.send("ℹ️ PTD wasn't registered as an alliance yet — nothing to clear. `/ptd-upgrade-now` should already run fresh.", ephemeral=True)


@bot.tree.command(name="ptd-upgrade-now", description="One-shot: adopt PTD's channels, migrate legacy roles, and register everyone. No wizard needed.")
@app_commands.default_permissions(administrator=True)
@is_dictator()
async def ptd_upgrade_now(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    guild = interaction.guild
    tag = "PTD"
    servers = ["21"]

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT status FROM alliances WHERE tag = ?", (tag,))
        existing = await cur.fetchone()
    if existing:
        await interaction.followup.send(
            f"ℹ️ **[{tag}]** is already registered (status: `{existing[0]}`). This command is for the first run only — "
            f"if something needs redoing, that's a different, more targeted fix.",
            ephemeral=True
        )
        return

    await interaction.followup.send("🚨 **INITIATING FULL PRECINCT UPGRADE — PTD DIVISION.** Standing by while every unit gets processed. Full report incoming the moment it's done.", ephemeral=True)
    log_lines = []

    # Guaranteed feedback, no matter what happens: if ANYTHING unexpected
    # throws partway through, this catches it, reports exactly how far it
    # got using whatever's already in log_lines, and posts the real error
    # to both the admin and #logs — never just silence.
    try:
        async with server_busy("upgrading the whole PTD precinct"):
            await _execute_ptd_upgrade(interaction, guild, tag, servers, log_lines)
    except Exception as e:
        print(f"[PTD UPGRADE ERROR] {type(e).__name__}: {e}")
        partial_summary = "\n".join(f"• {line}" for line in log_lines) if log_lines else "(nothing completed yet — it broke on the very first step)"
        error_msg = (
            f"🚨 **PTD upgrade hit an unexpected error and stopped partway through.**\n\n"
            f"**What completed before it broke:**\n{partial_summary}\n\n"
            f"**Error:** `{type(e).__name__}: {e}`\n\n"
            f"Nothing after this point ran. Safe to fix the underlying issue and run `/ptd-upgrade-now` again — "
            f"anything already done will just be recognized as already-complete and skipped."
        )
        await send_long(interaction.followup, error_msg, ephemeral=True)
        log_channel = discord.utils.get(guild.channels, name="logs")
        if log_channel:
            await send_long(log_channel, error_msg)


async def _execute_ptd_upgrade(interaction: discord.Interaction, guild, tag: str, servers: list, log_lines: list):
    """The actual PTD one-shot upgrade work, split out so the command
    wrapper above can guarantee error reporting around it without needing
    to touch a single line of the logic itself."""
    # --- Alliance role, bulk-granted to everyone immediately (the exact
    # gap that caused real problems earlier tonight if skipped) ---
    tag_role = discord.utils.get(guild.roles, name=tag)
    if not tag_role:
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT color_hex FROM alliances")
            existing_colors = {int(r[0]) for r in await cur.fetchall() if r[0]}
        tag_color = get_distinct_alliance_color(existing_colors)
        tag_role = await ensure_role(guild, tag, color=tag_color, hoist=True)
        log_lines.append(f"🏷️ Created the **{tag}** role.")

    granted = 0
    for member in guild.members:
        if not member.bot and tag_role not in member.roles:
            try:
                await member.add_roles(tag_role, reason="PTD one-shot upgrade.")
                granted += 1
            except discord.HTTPException:
                pass
    if granted:
        log_lines.append(f"🏷️ Granted **{tag}** to **{granted}** existing member(s).")

    # --- Category and known channels, using this server's exact names ---
    category = discord.utils.get(guild.categories, name="[PTD] CHATS") or discord.utils.get(guild.categories, name="PTD CHATS")
    if category:
        try:
            await category.edit(name=f"{tag} CHATS")
            log_lines.append(f"📁 Renamed category to **{tag} CHATS**.")
        except discord.HTTPException as e:
            log_lines.append(f"⚠️ Couldn't rename category: {e}")
    else:
        cat_overwrites = {
            guild.default_role: discord.PermissionOverwrite(view_channel=False),
            tag_role: discord.PermissionOverwrite(view_channel=True),
            guild.me: discord.PermissionOverwrite(view_channel=True, manage_channels=True)
        }
        category = await guild.create_category(f"{tag} CHATS", overwrites=cat_overwrites)
        log_lines.append(f"📁 Created fresh category **{tag} CHATS**.")

    for old_name, new_name in {"strategy": "♟️-strategy", "screenshots": "📸-screenshots", "currently-active-events": "🚨-currently-active-events"}.items():
        ch = discord.utils.get(category.text_channels, name=old_name) or discord.utils.get(guild.channels, name=new_name)
        if ch and ch.name != new_name:
            try:
                await ch.edit(name=new_name, category=category)
                log_lines.append(f"✏️ Renamed **#{old_name}** → **{new_name}**.")
            except discord.HTTPException as e:
                log_lines.append(f"⚠️ Couldn't rename {old_name}: {e}")
        elif not ch:
            await guild.create_text_channel(new_name, category=category)
            log_lines.append(f"➕ Created **{new_name}**.")

    existing_general = discord.utils.get(guild.channels, name="💬-general-chat")
    old_lobby = discord.utils.get(category.text_channels, name="lobby")
    if not existing_general and old_lobby:
        main_text_cat = discord.utils.get(guild.categories, name="🏢 MAIN PRECINCT")
        try:
            await old_lobby.edit(name="💬-general-chat", category=main_text_cat)
            log_lines.append("💬 Moved **#lobby** to the shared community area as **#💬-general-chat**.")
        except discord.HTTPException as e:
            log_lines.append(f"⚠️ Couldn't repurpose #lobby: {e}")
        await guild.create_text_channel("💬-lobby", category=category)
        log_lines.append("💬 Created a fresh **#💬-lobby** for PTD.")
    elif existing_general and not discord.utils.get(category.text_channels, name="💬-lobby"):
        await guild.create_text_channel("💬-lobby", category=category)
        log_lines.append("💬 **#💬-general-chat** already existed — created **#💬-lobby** for PTD alongside it.")

    welcome_ch = discord.utils.get(category.text_channels, name="welcome")
    if welcome_ch:
        admin_cat = discord.utils.get(guild.categories, name="Admin-Only")
        try:
            await welcome_ch.edit(category=admin_cat, sync_permissions=False)
            await welcome_ch.set_permissions(guild.default_role, view_channel=False)
            log_lines.append("🗄️ Archived **#welcome** — moved to Admin-Only, hidden, history kept.")
        except discord.HTTPException as e:
            log_lines.append(f"⚠️ Couldn't archive #welcome: {e}")

    if not discord.utils.get(category.text_channels, name="🎖️-leadership-chat"):
        leader_overwrites = {
            guild.default_role: discord.PermissionOverwrite(view_channel=False),
            guild.me: discord.PermissionOverwrite(view_channel=True),
            tag_role: discord.PermissionOverwrite(view_channel=True, send_messages=False),
        }
        await guild.create_text_channel("🎖️-leadership-chat", category=category, overwrites=leader_overwrites)
        log_lines.append("🎖️ Created **#🎖️-leadership-chat**.")

    voice_cat = discord.utils.get(guild.categories, name="[PTD] Voice Channels") or discord.utils.get(guild.categories, name="PTD Voice Channels")
    if voice_cat:
        try:
            await voice_cat.edit(name=f"{tag} Voice Channels")
            log_lines.append(f"📁 Renamed voice category to **{tag} Voice Channels**.")
        except discord.HTTPException:
            pass
        for old_name, new_name in {"Lobby VC": "🔊-Lobby-VC", "Event VC": "🚨🎙️-Event-VC"}.items():
            vc = discord.utils.get(voice_cat.voice_channels, name=old_name)
            if vc:
                try:
                    await vc.edit(name=new_name)
                    log_lines.append(f"✏️ Renamed voice **{old_name}** → **{new_name}**.")
                except discord.HTTPException:
                    pass

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute(
            "INSERT INTO alliances (tag, creator_id, status, color_hex, created_at) VALUES (?, ?, 'approved', ?, ?) "
            "ON CONFLICT(tag) DO UPDATE SET status='approved'",
            (tag, interaction.user.id, str(tag_role.color.value), datetime.now().isoformat())
        )
        await conn.commit()
    log_lines.append(f"✅ Registered **[{tag}]** as an approved alliance.")

    await enforce_role_hierarchy(guild)
    await refresh_leadership_status(guild, tag)

    # --- Legacy role migration, using the exact defaults already agreed on ---
    admin_candidates, rank_candidates = await scan_legacy_roles(guild)
    dictator_role = discord.utils.get(guild.roles, name=ROLE_DICTATOR)
    member_role = discord.utils.get(guild.roles, name=ROLE_MEMBER)

    for role in admin_candidates:
        count = 0
        for m in [mm for mm in role.members if not mm.bot]:
            if dictator_role:
                try:
                    await m.add_roles(dictator_role, reason="PTD one-shot: legacy Admin -> Dictator.")
                    count += 1
                except discord.HTTPException:
                    pass
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("INSERT OR IGNORE INTO legacy_roles_tracked (guild_id, role_name, mapped_to) VALUES (?, ?, ?)", (guild.id, role.name, "DICTATOR"))
            await conn.commit()
        log_lines.append(f"👑 Legacy **{role.name}** ({count} holder(s)) → DICTATOR.")

    for role, tier in rank_candidates:
        human_members = [m for m in role.members if not m.bot]
        count = 0
        if tier >= 4:
            rank_name = f"R{tier}"
            for m in human_members:
                try:
                    await grant_alliance_rank(guild, m, tag, rank_name)
                    count += 1
                except Exception:
                    pass
            mapped_to = f"{tag}-{rank_name}"
        else:
            for m in human_members:
                roles_to_add = [r for r in (tag_role, member_role) if r and r not in m.roles]
                if roles_to_add:
                    try:
                        await m.add_roles(*roles_to_add, reason="PTD one-shot: legacy rank migration.")
                        count += 1
                    except discord.HTTPException:
                        pass
                else:
                    count += 1
            mapped_to = f"{tag} (member)"
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("INSERT OR IGNORE INTO legacy_roles_tracked (guild_id, role_name, mapped_to) VALUES (?, ?, ?)", (guild.id, role.name, mapped_to))
            await conn.commit()
        log_lines.append(f"🎖️ Legacy **{role.name}** ({count} holder(s)) → {mapped_to}.")

    # --- Register and rename everyone ---
    srv_display = format_server_display(servers)
    server_field = ",".join(servers)
    onboarded, skipped = 0, 0
    nickname_failures = []
    role_grant_failures = []
    role_req_ch = discord.utils.get(guild.channels, name="⚙️-role-requests")
    abilities_ch = discord.utils.get(guild.channels, name="❓-abilities")

    for member in guild.members:
        if member.bot:
            continue
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT in_game_name, alliance_tag, rank_designation, server_number FROM users WHERE user_id = ?", (member.id,))
            row = await cur.fetchone()
        if row and row[0] and row[1] and row[2] and row[3]:
            skipped += 1
            continue

        rank = "Member"
        for candidate_rank in ("R5", "R4"):
            candidate_role = discord.utils.get(guild.roles, name=f"{tag}-{candidate_rank}")
            if candidate_role and candidate_role in member.roles:
                rank = candidate_rank
                break

        in_game_name = strip_nickname_decorations(member.display_name) or member.name

        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute(
                "INSERT INTO users (user_id, original_username, in_game_name, alliance_tag, rank_designation, server_number, "
                "language_selected, invite_check_passed, test_disclaimer_ack) "
                "VALUES (?, ?, ?, ?, ?, ?, 1, 1, 1) "
                "ON CONFLICT(user_id) DO UPDATE SET in_game_name=excluded.in_game_name, alliance_tag=excluded.alliance_tag, "
                "rank_designation=excluded.rank_designation, server_number=excluded.server_number",
                (member.id, str(member), in_game_name, tag, rank, server_field)
            )
            await conn.commit()

        roles_to_add = [r for r in (member_role, tag_role) if r]
        for num in servers:
            srv_role = discord.utils.get(guild.roles, name=role_name_for_server(num))
            if srv_role:
                roles_to_add.append(srv_role)
        try:
            await member.add_roles(*roles_to_add)
        except discord.HTTPException as e:
            role_grant_failures.append(f"{member.mention} ({e})")

        name_budget = 32 - len(f" [{tag_display(tag)}] {srv_display}")
        new_nick = f"{in_game_name[:max(1, name_budget)]} [{tag_display(tag)}] {srv_display}"
        try:
            await member.edit(nick=new_nick[:32])
        except discord.Forbidden:
            if member.id == guild.owner_id:
                nickname_failures.append(f"{member.mention} (server owner — Discord never allows a bot to rename the owner, no matter its permissions; you'll need to set this one yourself)")
            else:
                nickname_failures.append(f"{member.mention} (likely holds a role positioned above mine)")
        except discord.HTTPException as e:
            nickname_failures.append(f"{member.mention} ({e})")

        try:
            await member.send(embed=discord.Embed(
                title="🚔 You're officially registered",
                description=(
                    f"This server just got upgraded, and you've been carried over as **[{tag}]**, server "
                    f"**{srv_display}** — no action needed on your part, that's already done.\n\n"
                    f"Run `/abilities` any time (also works great in {abilities_ch.mention if abilities_ch else '#❓-abilities'}) "
                    f"for a full rundown of what you can do. And if you actually play on more than just server "
                    f"{srv_display}, head to {role_req_ch.mention if role_req_ch else '#⚙️-role-requests'} to add any "
                    f"other servers you're on.\n\nIf your in-game name isn't quite right, `/nickname` fixes that any time."
                ),
                color=discord.Color.blue()
            ))
        except discord.Forbidden:
            pass

        onboarded += 1

    log_lines.append(f"👥 Registered **{onboarded}** member(s), skipped **{skipped}** already-registered.")
    if role_grant_failures:
        log_lines.append(f"⚠️ **{len(role_grant_failures)}** member(s) couldn't be granted their roles — this means they may still be missing general-chat access:")
        for failure in role_grant_failures:
            log_lines.append(f"   • {failure}")
    if nickname_failures:
        log_lines.append(f"⚠️ **{len(nickname_failures)}** nickname(s) couldn't be changed (registration itself still succeeded for these people):")
        for failure in nickname_failures:
            log_lines.append(f"   • {failure}")

    summary = "\n".join(f"• {line}" for line in log_lines)
    await send_long(interaction.followup, f"🎖️ **PRECINCT UPGRADE COMPLETE — PTD DIVISION FULLY OPERATIONAL.**\n\n{summary}\n\nAll units accounted for. Good work, Chief.", ephemeral=True)
    await log_event(guild, f"📇 **PTD ONE-SHOT UPGRADE COMPLETE**\nBy: {interaction.user.mention}\n{summary}")

    await interaction.followup.send(
        "Anyone else need a rank? Pick them below and assign R4/R5 directly, or just ignore this if not.",
        view=GrantRankPickerView(tag),
        ephemeral=True
    )


@bot.tree.command(name="adopt-alliance", description="Adopt an existing alliance's channels/roles into our structure, one confirmed step at a time.")
@app_commands.describe(tag="The alliance's tag (2-4 letters)")
@app_commands.default_permissions(administrator=True)
@is_dictator()
async def adopt_alliance(interaction: discord.Interaction, tag: str):
    tag = tag.strip().upper()
    if not (2 <= len(tag) <= 4 and tag.isalpha()):
        await interaction.response.send_message("❌ Tag must be 2-4 letters.", ephemeral=True)
        return

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT status FROM alliances WHERE tag = ?", (tag,))
        existing = await cur.fetchone()
    if existing:
        await interaction.response.send_message(f"❌ **[{tag}]** is already registered (status: `{existing[0]}`). This is for adopting something new.", ephemeral=True)
        return

    state = AllianceAdoptionState(tag, interaction.user)
    view = AdoptionCategoryView(interaction.guild, state)
    await interaction.response.send_message(
        f"📇 **Step 1 of 4 — [{tag}] category**\n\nWhich existing category holds this alliance's channels? "
        "Pick \"None\" if you want everything created fresh instead.",
        view=view,
        ephemeral=True
    )


class AllianceAdoptionState:
    """Carries the whole /adopt-alliance wizard's progress across several
    chained interactions — one instance per admin's in-progress adoption."""
    def __init__(self, tag: str, admin):
        self.tag = tag
        self.admin = admin
        self.category = None  # discord.CategoryChannel or None ("create fresh")
        self.mapping = {"lobby": None, "strategy": None, "screenshots": None, "events": None}
        self.general_chat_source = None  # discord.TextChannel or None
        self.retire_channels = []  # list of discord.TextChannel to archive
        self.voice_category = None
        self.voice_mapping = {"lobby_vc": None, "event_vc": None}


class AdoptionCategorySelect(discord.ui.Select):
    def __init__(self, guild, state: AllianceAdoptionState):
        self.state = state
        categories = guild.categories[:24]
        options = [discord.SelectOption(label=cat.name[:100], value=str(cat.id)) for cat in categories]
        options.append(discord.SelectOption(label="— None, create a fresh category —", value="__none__"))
        super().__init__(placeholder="Which category holds this alliance's channels?", min_values=1, max_values=1, options=options)

    async def callback(self, interaction: discord.Interaction):
        if interaction.user != self.state.admin:
            await interaction.response.send_message("This isn't your wizard.", ephemeral=True)
            return
        value = self.values[0]
        self.state.category = None if value == "__none__" else discord.utils.get(interaction.guild.categories, id=int(value))

        channels_in_category = list(self.state.category.text_channels) if self.state.category else []
        view = AdoptionChannelMappingView(self.state, channels_in_category)
        await interaction.response.edit_message(
            content=(
                f"📇 **Step 2 of 4 — [{self.state.tag}] channel mapping**\n"
                f"Category: **{self.state.category.name if self.state.category else '(will create fresh)'}**\n\n"
                "For each slot below, pick the existing channel it should become, or leave it on "
                "\"None, create fresh\" if there isn't one yet. Nothing happens until you hit Confirm."
            ),
            view=view
        )


class AdoptionCategoryView(discord.ui.View):
    def __init__(self, guild, state: AllianceAdoptionState):
        super().__init__(timeout=600.0)
        self.add_item(AdoptionCategorySelect(guild, state))


class AdoptionChannelSlotSelect(discord.ui.Select):
    def __init__(self, slot_key: str, placeholder: str, channels: list, row: int):
        self.slot_key = slot_key
        options = [discord.SelectOption(label=ch.name[:100], value=str(ch.id)) for ch in channels[:24]]
        options.append(discord.SelectOption(label="None, create fresh", value="__none__", default=not channels))
        super().__init__(placeholder=placeholder, min_values=1, max_values=1, options=options, row=row)

    async def callback(self, interaction: discord.Interaction):
        view: AdoptionChannelMappingView = self.view
        if interaction.user != view.state.admin:
            await interaction.response.send_message("This isn't your wizard.", ephemeral=True)
            return
        value = self.values[0]
        view.state.mapping[self.slot_key] = None if value == "__none__" else discord.utils.get(interaction.guild.text_channels, id=int(value))
        await interaction.response.defer()


class AdoptionMappingConfirmButton(discord.ui.Button):
    def __init__(self):
        super().__init__(label="Confirm & Continue", style=discord.ButtonStyle.success, row=4)

    async def callback(self, interaction: discord.Interaction):
        view: AdoptionChannelMappingView = self.view
        if interaction.user != view.state.admin:
            await interaction.response.send_message("This isn't your wizard.", ephemeral=True)
            return

        category_channels = list(view.state.category.text_channels) if view.state.category else []
        next_view = AdoptionGeneralChatRetireView(view.state, interaction.guild, category_channels)
        await interaction.response.edit_message(
            content=(
                f"📇 **Step 3 of 4 — [{view.state.tag}] special cases**\n\n"
                "Should any channel here actually become the server-wide **#💬-general-chat** instead of staying "
                "alliance-specific? (If you pick one, a fresh, empty lobby gets created for this alliance "
                "afterward, since the original is moving to a shared role.)\n\n"
                "Anything not otherwise assigned can be archived (moved to Admin-Only, hidden, history kept) — "
                "pick as many as apply, or none."
            ),
            view=next_view
        )


class AdoptionChannelMappingView(discord.ui.View):
    def __init__(self, state: AllianceAdoptionState, channels_in_category: list):
        super().__init__(timeout=600.0)
        self.state = state
        self.add_item(AdoptionChannelSlotSelect("lobby", "Lobby channel...", channels_in_category, row=0))
        self.add_item(AdoptionChannelSlotSelect("strategy", "Strategy channel...", channels_in_category, row=1))
        self.add_item(AdoptionChannelSlotSelect("screenshots", "Screenshots channel...", channels_in_category, row=2))
        self.add_item(AdoptionChannelSlotSelect("events", "Active-events channel...", channels_in_category, row=3))
        self.add_item(AdoptionMappingConfirmButton())


class AdoptionGeneralChatSelect(discord.ui.Select):
    def __init__(self, channels: list, row: int):
        options = [discord.SelectOption(label=ch.name[:100], value=str(ch.id)) for ch in channels[:24]]
        options.append(discord.SelectOption(label="None — keep everything alliance-specific", value="__none__", default=True))
        super().__init__(placeholder="Repurpose a channel as server-wide #general-chat?", min_values=1, max_values=1, options=options, row=row)

    async def callback(self, interaction: discord.Interaction):
        view: AdoptionGeneralChatRetireView = self.view
        if interaction.user != view.state.admin:
            await interaction.response.send_message("This isn't your wizard.", ephemeral=True)
            return
        value = self.values[0]
        view.state.general_chat_source = None if value == "__none__" else discord.utils.get(interaction.guild.text_channels, id=int(value))
        await interaction.response.defer()


class AdoptionRetireSelect(discord.ui.Select):
    def __init__(self, channels: list, row: int):
        has_options = bool(channels)
        options = [discord.SelectOption(label=ch.name[:100], value=str(ch.id)) for ch in channels[:24]] or \
                  [discord.SelectOption(label="(nothing left to archive)", value="__none__")]
        super().__init__(
            placeholder="Archive any leftover channels? (optional)",
            min_values=0, max_values=len(options) if has_options else 1,
            options=options, row=row, disabled=not has_options
        )

    async def callback(self, interaction: discord.Interaction):
        view: AdoptionGeneralChatRetireView = self.view
        if interaction.user != view.state.admin:
            await interaction.response.send_message("This isn't your wizard.", ephemeral=True)
            return
        view.state.retire_channels = [discord.utils.get(interaction.guild.text_channels, id=int(v)) for v in self.values if v != "__none__"]
        await interaction.response.defer()


class AdoptionVoiceCategorySelect(discord.ui.Select):
    def __init__(self, guild, row: int):
        categories = guild.categories[:24]
        options = [discord.SelectOption(label=cat.name[:100], value=str(cat.id)) for cat in categories]
        options.append(discord.SelectOption(label="— None, create a fresh category —", value="__none__"))
        super().__init__(placeholder="Which category holds voice channels?", min_values=1, max_values=1, options=options, row=row)

    async def callback(self, interaction: discord.Interaction):
        view: AdoptionGeneralChatRetireView = self.view
        if interaction.user != view.state.admin:
            await interaction.response.send_message("This isn't your wizard.", ephemeral=True)
            return
        value = self.values[0]
        view.state.voice_category = None if value == "__none__" else discord.utils.get(interaction.guild.categories, id=int(value))
        await interaction.response.defer()


class AdoptionStep3ContinueButton(discord.ui.Button):
    def __init__(self):
        super().__init__(label="Continue to Voice Mapping", style=discord.ButtonStyle.success, row=3)

    async def callback(self, interaction: discord.Interaction):
        view: AdoptionGeneralChatRetireView = self.view
        if interaction.user != view.state.admin:
            await interaction.response.send_message("This isn't your wizard.", ephemeral=True)
            return
        # If the same channel got picked as both "becomes general-chat" and
        # "archive," general-chat wins — it's the more specific, deliberate choice.
        if view.state.general_chat_source and view.state.general_chat_source in view.state.retire_channels:
            view.state.retire_channels.remove(view.state.general_chat_source)

        voice_channels = list(view.state.voice_category.voice_channels) if view.state.voice_category else []
        next_view = AdoptionVoiceMappingView(view.state, voice_channels)
        await interaction.response.edit_message(
            content=(
                f"🔊 **Step 4 of 4 — [{view.state.tag}] voice channels**\n"
                f"Voice category: **{view.state.voice_category.name if view.state.voice_category else '(will create fresh)'}**\n\n"
                "Pick the existing voice channels for each slot, or leave on \"create fresh.\" This is the last "
                "step — hitting Confirm & Execute actually makes all the changes."
            ),
            view=next_view
        )


class AdoptionGeneralChatRetireView(discord.ui.View):
    def __init__(self, state: AllianceAdoptionState, guild, category_channels: list):
        super().__init__(timeout=600.0)
        self.state = state
        already_mapped_ids = {ch.id for ch in state.mapping.values() if ch}
        leftover = [ch for ch in category_channels if ch.id not in already_mapped_ids]
        self.add_item(AdoptionGeneralChatSelect(category_channels, row=0))
        self.add_item(AdoptionRetireSelect(leftover, row=1))
        self.add_item(AdoptionVoiceCategorySelect(guild, row=2))
        self.add_item(AdoptionStep3ContinueButton())


class AdoptionVoiceSlotSelect(discord.ui.Select):
    def __init__(self, slot_key: str, placeholder: str, channels: list, row: int):
        self.slot_key = slot_key
        options = [discord.SelectOption(label=ch.name[:100], value=str(ch.id)) for ch in channels[:24]]
        options.append(discord.SelectOption(label="None, create fresh", value="__none__", default=not channels))
        super().__init__(placeholder=placeholder, min_values=1, max_values=1, options=options, row=row)

    async def callback(self, interaction: discord.Interaction):
        view: AdoptionVoiceMappingView = self.view
        if interaction.user != view.state.admin:
            await interaction.response.send_message("This isn't your wizard.", ephemeral=True)
            return
        value = self.values[0]
        view.state.voice_mapping[self.slot_key] = None if value == "__none__" else discord.utils.get(interaction.guild.voice_channels, id=int(value))
        await interaction.response.defer()


class AdoptionExecuteButton(discord.ui.Button):
    def __init__(self):
        super().__init__(label="✅ Confirm & Execute", style=discord.ButtonStyle.danger, row=2)

    async def callback(self, interaction: discord.Interaction):
        view: AdoptionVoiceMappingView = self.view
        if interaction.user != view.state.admin:
            await interaction.response.send_message("This isn't your wizard.", ephemeral=True)
            return
        await interaction.response.edit_message(content="⚙️ Working on it — renaming, creating, and registering everything now...", view=None)
        summary = await execute_alliance_adoption(interaction.guild, view.state)
        await interaction.followup.send(summary, ephemeral=True)


class AdoptionVoiceMappingView(discord.ui.View):
    def __init__(self, state: AllianceAdoptionState, voice_channels: list):
        super().__init__(timeout=600.0)
        self.state = state
        self.add_item(AdoptionVoiceSlotSelect("lobby_vc", "Lobby voice channel...", voice_channels, row=0))
        self.add_item(AdoptionVoiceSlotSelect("event_vc", "Event voice channel...", voice_channels, row=1))
        self.add_item(AdoptionExecuteButton())


async def execute_alliance_adoption(guild, state: AllianceAdoptionState) -> str:
    """Performs the actual adoption: renames/creates the category and
    channels per the wizard's choices, moves a repurposed general-chat
    channel out to the shared community area, archives anything flagged
    for retirement (moved to Admin-Only, hidden, history kept — never
    deleted), creates a fresh lobby if the old one got repurposed, wires
    up leadership-chat, and registers the alliance directly as approved —
    bypassing Founder's Pass entirely, since this isn't a new founding."""
    async with server_busy("adopting an existing alliance's channels"):
        tag = state.tag
        log_lines = []

        tag_role = discord.utils.get(guild.roles, name=tag)
        if not tag_role:
            async with db_connect() as conn:
                cur = await conn.cursor()
                await cur.execute("SELECT color_hex FROM alliances")
                existing_colors = {int(r[0]) for r in await cur.fetchall() if r[0]}
            tag_color = get_distinct_alliance_color(existing_colors)
            tag_role = await ensure_role(guild, tag, color=tag_color, hoist=True)
            log_lines.append(f"🏷️ Created the **{tag}** alliance role.")

        # Critical: the whole [TAG] CHATS category's visibility depends on
        # holding this role. /migrate-legacy-roles only reaches people holding
        # a legacy rank role (R2-R5) — everyone else (anyone who was just a
        # plain "Member" with no rank) needs it granted here directly, or
        # they'd silently lose visibility into their own alliance's channels
        # the moment this category gets locked down to tag_role holders.
        granted_count = 0
        for member in guild.members:
            if not member.bot and tag_role not in member.roles:
                try:
                    await member.add_roles(tag_role, reason=f"Bulk grant during [{tag}] adoption — preserving existing access.")
                    granted_count += 1
                except discord.HTTPException:
                    pass
        if granted_count:
            log_lines.append(f"🏷️ Granted **{tag}** to **{granted_count}** existing member(s), so nobody loses visibility into their own channels.")

        if state.category:
            try:
                await state.category.edit(name=f"{tag} CHATS")
                log_lines.append(f"📁 Renamed category to **{tag} CHATS**.")
            except discord.HTTPException as e:
                log_lines.append(f"⚠️ Couldn't rename category: {e}")
            category = state.category
        else:
            cat_overwrites = {
                guild.default_role: discord.PermissionOverwrite(view_channel=False),
                tag_role: discord.PermissionOverwrite(view_channel=True),
                guild.me: discord.PermissionOverwrite(view_channel=True, manage_channels=True)
            }
            category = await guild.create_category(f"{tag} CHATS", overwrites=cat_overwrites)
            log_lines.append(f"📁 Created a fresh category **{tag} CHATS**.")

        slot_names = {"lobby": "💬-lobby", "strategy": "♟️-strategy", "screenshots": "📸-screenshots", "events": "🚨-currently-active-events"}
        repurposing_lobby = bool(
            state.general_chat_source and state.mapping.get("lobby") and state.mapping["lobby"].id == state.general_chat_source.id
        )

        for slot, expected_name in slot_names.items():
            existing = state.mapping.get(slot)
            if slot == "lobby" and repurposing_lobby:
                await guild.create_text_channel(expected_name, category=category)
                log_lines.append(f"💬 Created a fresh **{expected_name}** (the old lobby is becoming general-chat, see below).")
                continue
            if existing:
                try:
                    await existing.edit(name=expected_name, category=category)
                    log_lines.append(f"✏️ Renamed **#{existing.name}** → **{expected_name}**.")
                except discord.HTTPException as e:
                    log_lines.append(f"⚠️ Couldn't rename {slot}: {e}")
            else:
                await guild.create_text_channel(expected_name, category=category)
                log_lines.append(f"➕ Created **{expected_name}** — nothing existing matched this slot.")

        if not discord.utils.get(category.text_channels, name="🎖️-leadership-chat"):
            leader_overwrites = {
                guild.default_role: discord.PermissionOverwrite(view_channel=False),
                guild.me: discord.PermissionOverwrite(view_channel=True),
                tag_role: discord.PermissionOverwrite(view_channel=True, send_messages=False),
            }
            await guild.create_text_channel("🎖️-leadership-chat", category=category, overwrites=leader_overwrites)
            log_lines.append("🎖️ Created **#🎖️-leadership-chat**.")

        if state.general_chat_source:
            existing_general = discord.utils.get(guild.channels, name="💬-general-chat")
            if existing_general:
                log_lines.append(f"ℹ️ **#💬-general-chat** already exists — left **#{state.general_chat_source.name}** where it is rather than creating a duplicate.")
            else:
                main_text_cat = discord.utils.get(guild.categories, name="🏢 MAIN PRECINCT")
                try:
                    await state.general_chat_source.edit(name="💬-general-chat", category=main_text_cat)
                    log_lines.append(f"💬 Moved **#{state.general_chat_source.name}** to the shared community area as **#💬-general-chat**.")
                except discord.HTTPException as e:
                    log_lines.append(f"⚠️ Couldn't repurpose general-chat: {e}")

        if state.retire_channels:
            admin_cat = discord.utils.get(guild.categories, name="Admin-Only")
            for ch in state.retire_channels:
                try:
                    await ch.edit(category=admin_cat, sync_permissions=False)
                    await ch.set_permissions(guild.default_role, view_channel=False)
                    log_lines.append(f"🗄️ Archived **#{ch.name}** — moved to Admin-Only, hidden, history kept.")
                except discord.HTTPException as e:
                    log_lines.append(f"⚠️ Couldn't archive #{ch.name}: {e}")

        voice_slot_names = {"lobby_vc": "🔊-Lobby-VC", "event_vc": "🚨🎙️-Event-VC"}
        if state.voice_category:
            try:
                await state.voice_category.edit(name=f"{tag} Voice Channels")
                log_lines.append(f"📁 Renamed voice category to **{tag} Voice Channels**.")
            except discord.HTTPException as e:
                log_lines.append(f"⚠️ Couldn't rename voice category: {e}")
            voice_category = state.voice_category
        else:
            voice_category = await guild.create_category(f"{tag} Voice Channels")
            log_lines.append(f"📁 Created a fresh voice category **{tag} Voice Channels**.")

        for slot, expected_name in voice_slot_names.items():
            existing = state.voice_mapping.get(slot)
            if existing:
                try:
                    await existing.edit(name=expected_name, category=voice_category)
                    log_lines.append(f"✏️ Renamed voice **{existing.name}** → **{expected_name}**.")
                except discord.HTTPException as e:
                    log_lines.append(f"⚠️ Couldn't rename {slot}: {e}")
            else:
                await guild.create_voice_channel(expected_name, category=voice_category)
                log_lines.append(f"➕ Created voice **{expected_name}**.")

        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute(
                "INSERT INTO alliances (tag, creator_id, status, color_hex, created_at) VALUES (?, ?, 'approved', ?, ?) "
                "ON CONFLICT(tag) DO UPDATE SET status = 'approved'",
                (tag, state.admin.id, str(tag_role.color.value), datetime.now().isoformat())
            )
            await conn.commit()
        log_lines.append(f"✅ Registered **[{tag}]** as an approved alliance.")

        await enforce_role_hierarchy(guild)
        await refresh_leadership_status(guild, tag)

        summary = "\n".join(log_lines)
        await log_event(guild, f"📇 **ALLIANCE ADOPTED: [{tag}]**\nBy: {state.admin.mention}\n{summary}")
        return f"✅ **Adoption complete for [{tag}].**\n\n{summary}"


# ------------------------------------------------------------
#  LEGACY ROLE MIGRATION — scans for rank/admin roles that predate this
#  bot (or predate it managing multiple alliances) and walks the admin
#  through mapping each one, one at a time. Nothing is guessed: bot-only
#  roles and known Discord-native roles (Server Booster, etc.) are simply
#  never presented as candidates at all.
# ------------------------------------------------------------
LEGACY_ROLE_SKIP_NAMES = {"Server Booster"}


async def scan_legacy_roles(guild):
    """Returns (admin_role_candidates, rank_role_candidates) — the second
    a list of (role, tier_number) tuples. Filters out anything already
    ours, anything Discord-native, and anything with zero human holders
    (bot-only roles, or roles nobody currently has)."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT tag FROM alliances")
        known_tags = {row[0] for row in await cur.fetchall()}

    admin_candidates = []
    rank_candidates = []

    for role in guild.roles:
        if role.is_default() or role.name in LEGACY_ROLE_SKIP_NAMES:
            continue
        if role.name in DEFAULT_ROLE_NAMES or role.name in known_tags:
            continue
        if any(role.name.startswith(f"{tag}-") for tag in known_tags):
            continue  # one of our own per-alliance R4/R5/Leadership roles

        human_members = [m for m in role.members if not m.bot]
        if not human_members:
            continue  # bot-only or genuinely empty — nothing to migrate

        stripped = role.name.strip()
        if stripped.lower() in ("admin", "administrator"):
            admin_candidates.append(role)
        else:
            match = re.match(r"^r\s*(\d+)$", stripped, re.IGNORECASE)
            if match:
                rank_candidates.append((role, int(match.group(1))))

    return admin_candidates, rank_candidates


async def check_adoption_readiness(guild):
    """Detects the clearest, most reliable signal of an unmigrated,
    pre-this-bot server — leftover legacy rank/admin roles — and always,
    every single startup, privately walks whoever holds Dictator through
    the full process, step by step, with the reasoning for each one, not
    just a bare command list. A compact version also goes to #logs for
    the record. Self-correcting: once /migrate-legacy-roles clears out
    what scan_legacy_roles finds, this naturally stops firing on its own,
    no separate 'mark as done' needed."""
    admin_candidates, rank_candidates = await scan_legacy_roles(guild)
    if not (admin_candidates or rank_candidates):
        return

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute(
            "SELECT COUNT(*) FROM users WHERE in_game_name IS NOT NULL AND alliance_tag IS NOT NULL "
            "AND rank_designation IS NOT NULL AND server_number IS NOT NULL"
        )
        registered_count = (await cur.fetchone())[0]
    total_humans = len([m for m in guild.members if not m.bot])
    unregistered_count = max(0, total_humans - registered_count)

    # Compact version, for the record, visible to all staff.
    log_channel = discord.utils.get(guild.channels, name="logs")
    if log_channel:
        embed = discord.Embed(
            title="🕵️ THIS LOOKS LIKE AN ADOPTED SERVER",
            description=(
                f"Found **{len(admin_candidates) + len(rank_candidates)}** legacy admin/rank role(s) that predate "
                f"me, and **{unregistered_count}** of **{total_humans}** member(s) aren't fully registered yet.\n\n"
                "A full, private walkthrough has been sent to whoever holds Dictator. Short version — the "
                "**STARTUP DIAGNOSTIC** message also posted in #logs carries a button for exactly this (no "
                "typing, so nothing can silently fail to register as a real click): 🚔 Convert Everyone + "
                "Migrate Ranks → hand-assign any special identities → `/announce-update`. Typed "
                "equivalents exist too (`/adopt-alliance`, `/migrate-legacy-roles`, `/bulk-onboard-existing`) "
                "if you'd rather.\n\n"
                "This keeps showing up at every startup until it's actually resolved."
            ),
            color=discord.Color.blue()
        )
        try:
            await log_channel.send(embed=embed)
        except discord.HTTPException:
            pass

    # The real thing: a private, patient, step-by-step DM, since — fairly —
    # a bare command list isn't actually a walkthrough.
    dictator_role = discord.utils.get(guild.roles, name=ROLE_DICTATOR)
    if not dictator_role:
        return

    walkthrough = discord.Embed(
        title="🕵️ Let's get this server fully set up",
        description=(
            f"I noticed this server has history from before I was here — **{len(admin_candidates) + len(rank_candidates)}** "
            f"old rank/admin role(s), and **{unregistered_count}** of **{total_humans}** member(s) I don't have full "
            f"records for yet. Completely normal for a server that existed before this bot — here's exactly what to "
            f"do about it, one step at a time, and why each one matters."
        ),
        color=discord.Color.blue()
    )
    walkthrough.add_field(
        name="0️⃣ Try the button first, if you can",
        value=(
            "The **STARTUP DIAGNOSTIC** message in #logs carries a button that covers steps 1 and 2 below "
            "together, in one click — no typing required, which matters since a mistyped or not-quite-selected "
            "slash command can silently do nothing at all. If you see it, it's the safer path. The steps below "
            "work identically either way, typed or clicked."
        ),
        inline=False
    )
    walkthrough.add_field(
        name="1️⃣ /adopt-alliance <tag>",
        value=(
            "Brings the alliance's existing channels — lobby, strategy, screenshots, whatever's already there — "
            "into the structure I expect, without losing any of it. You'll confirm each channel mapping yourself; "
            "nothing happens automatically. Skip this if you've already run it."
        ),
        inline=False
    )
    walkthrough.add_field(
        name="2️⃣ /migrate-legacy-roles",
        value=(
            "Finds old rank roles (R2, R3, R4, R5, a plain \"Admin\" role, etc.) and walks you through mapping "
            "each one into the new system, one at a time, with a chance to confirm or skip each."
        ),
        inline=False
    )
    walkthrough.add_field(
        name="3️⃣ /bulk-onboard-existing <tag> <servers>",
        value=(
            "Registers everyone already in the server and formats their name properly. Tell it which server "
            "number(s) actually apply — I won't guess. Everyone gets a DM afterward pointing them at `/abilities` "
            "and #⚙️-role-requests in case they're on more servers than you assumed."
        ),
        inline=False
    )
    walkthrough.add_field(
        name="4️⃣ Hand-assign any special identities",
        value=(
            "If anyone here should become a real moderator, that's deliberately a manual step — right-click their "
            "name → Roles → add the identity directly. I'll never infer on my own that someone should be a mod."
        ),
        inline=False
    )
    walkthrough.add_field(
        name="5️⃣ /announce-update",
        value="Once everything above is actually done, this tells everyone at once, on your own schedule.",
        inline=False
    )
    walkthrough.set_footer(text="I'll send this again at every startup until it's fully resolved — you won't lose track of where you are.")

    for dictator in dictator_role.members:
        if dictator.bot:
            continue
        try:
            await dictator.send(embed=walkthrough)
        except discord.Forbidden:
            pass


class LegacyMigrationState:
    def __init__(self, admin, admin_roles: list, rank_roles: list):
        self.admin = admin
        self.admin_roles = admin_roles  # queue — front item is always "currently shown"
        self.rank_roles = rank_roles    # queue of (role, tier)
        self.log = []


def _peek_legacy_step(state: LegacyMigrationState):
    if state.admin_roles:
        return "admin", state.admin_roles[0]
    if state.rank_roles:
        return "rank", state.rank_roles[0]
    return None, None


async def show_next_legacy_step(interaction: discord.Interaction, state: LegacyMigrationState, use_followup: bool = False):
    kind, item = _peek_legacy_step(state)

    if kind == "admin":
        role = item
        human_count = len([m for m in role.members if not m.bot])
        content = f"👑 Found role **{role.name}** with {human_count} holder(s) — looks like a legacy admin role. Map to DICTATOR?"
        view = LegacyAdminRoleView(state, role)
    elif kind == "rank":
        role, tier = item
        human_count = len([m for m in role.members if not m.bot])
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT tag FROM alliances")
            tags = [row[0] for row in await cur.fetchall()]
        if tier >= 4:
            explainer = f"maps to **[TAG]-R{tier}** for whichever alliance you pick (this also grants Leadership access automatically)."
        else:
            explainer = "has no rank equivalent in-game — holders will just be confirmed as members of whichever alliance you pick."
        content = f"🎖️ Found role **{role.name}** with {human_count} holder(s) — {explainer}"
        view = LegacyRankRoleView(state, role, tier, tags)
    else:
        summary = "\n".join(state.log) if state.log else "Nothing was changed."
        content = f"✅ **Legacy role migration complete.**\n\n{summary}"
        view = None

    if use_followup:
        await interaction.followup.send(content, view=view, ephemeral=True)
    else:
        await interaction.response.edit_message(content=content, view=view)

    if kind is None and not use_followup:
        await log_event(interaction.guild, f"🔧 **LEGACY ROLE MIGRATION COMPLETE**\nBy: {state.admin.mention}\n{summary}")


class LegacyAdminRoleView(discord.ui.View):
    def __init__(self, state: LegacyMigrationState, role):
        super().__init__(timeout=300.0)
        self.state = state
        self.role = role

    @discord.ui.button(label="Map to DICTATOR", style=discord.ButtonStyle.success)
    async def confirm(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user != self.state.admin:
            await interaction.response.send_message("This isn't your wizard.", ephemeral=True)
            return
        self.state.admin_roles.pop(0)
        dictator_role = discord.utils.get(interaction.guild.roles, name=ROLE_DICTATOR)
        count = 0
        for m in [mm for mm in self.role.members if not mm.bot]:
            if dictator_role:
                try:
                    await m.add_roles(dictator_role, reason="Legacy Admin role migration.")
                    count += 1
                except discord.HTTPException:
                    pass
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute(
                "INSERT OR IGNORE INTO legacy_roles_tracked (guild_id, role_name, mapped_to) VALUES (?, ?, ?)",
                (interaction.guild.id, self.role.name, "DICTATOR")
            )
            await conn.commit()
        self.state.log.append(f"✅ **{self.role.name}** ({count} holder(s)) → DICTATOR")
        await show_next_legacy_step(interaction, self.state)

    @discord.ui.button(label="Skip", style=discord.ButtonStyle.secondary)
    async def skip(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user != self.state.admin:
            await interaction.response.send_message("This isn't your wizard.", ephemeral=True)
            return
        self.state.admin_roles.pop(0)
        self.state.log.append(f"⏭️ **{self.role.name}** — skipped")
        await show_next_legacy_step(interaction, self.state)


class LegacyRankTagSelect(discord.ui.Select):
    def __init__(self, tags: list):
        options = [discord.SelectOption(label=t, value=t) for t in tags[:25]]
        super().__init__(placeholder="Which alliance should these holders belong to?", min_values=1, max_values=1, options=options)

    async def callback(self, interaction: discord.Interaction):
        view: LegacyRankRoleView = self.view
        if interaction.user != view.state.admin:
            await interaction.response.send_message("This isn't your wizard.", ephemeral=True)
            return
        await view.apply(interaction, self.values[0])


class LegacyRankConfirmButton(discord.ui.Button):
    """Used when exactly one alliance exists — a plain confirm instead of a dropdown with only one choice."""
    def __init__(self, tag: str):
        self.tag = tag
        super().__init__(label=f"Apply [{tag}] to all holders", style=discord.ButtonStyle.success)

    async def callback(self, interaction: discord.Interaction):
        view: LegacyRankRoleView = self.view
        if interaction.user != view.state.admin:
            await interaction.response.send_message("This isn't your wizard.", ephemeral=True)
            return
        await view.apply(interaction, self.tag)


class LegacyRankSkipButton(discord.ui.Button):
    def __init__(self):
        super().__init__(label="Skip This Role", style=discord.ButtonStyle.secondary)

    async def callback(self, interaction: discord.Interaction):
        view: LegacyRankRoleView = self.view
        if interaction.user != view.state.admin:
            await interaction.response.send_message("This isn't your wizard.", ephemeral=True)
            return
        view.state.rank_roles.pop(0)
        view.state.log.append(f"⏭️ **{view.role.name}** — skipped")
        await show_next_legacy_step(interaction, view.state)


class LegacyRankRoleView(discord.ui.View):
    def __init__(self, state: LegacyMigrationState, role, tier: int, tags: list):
        super().__init__(timeout=300.0)
        self.state = state
        self.role = role
        self.tier = tier
        if len(tags) == 1:
            self.add_item(LegacyRankConfirmButton(tags[0]))
        elif len(tags) > 1:
            self.add_item(LegacyRankTagSelect(tags))
        self.add_item(LegacyRankSkipButton())

    async def apply(self, interaction: discord.Interaction, tag: str):
        self.state.rank_roles.pop(0)
        human_members = [m for m in self.role.members if not m.bot]
        count = 0

        if self.tier >= 4:
            rank_name = f"R{self.tier}"
            for m in human_members:
                try:
                    await grant_alliance_rank(interaction.guild, m, tag, rank_name)
                    count += 1
                except Exception:
                    pass
            mapped_to = f"{tag}-{rank_name}"
        else:
            tag_role = discord.utils.get(interaction.guild.roles, name=tag)
            member_role = discord.utils.get(interaction.guild.roles, name=ROLE_MEMBER)
            for m in human_members:
                roles_to_add = [r for r in (tag_role, member_role) if r and r not in m.roles]
                if roles_to_add:
                    try:
                        await m.add_roles(*roles_to_add, reason="Legacy rank-role migration.")
                        count += 1
                    except discord.HTTPException:
                        pass
                else:
                    count += 1
            mapped_to = f"{tag} (member)"

        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute(
                "INSERT OR IGNORE INTO legacy_roles_tracked (guild_id, role_name, mapped_to) VALUES (?, ?, ?)",
                (interaction.guild.id, self.role.name, mapped_to)
            )
            await conn.commit()

        self.state.log.append(f"✅ **{self.role.name}** ({count} holder(s)) → {mapped_to}")
        await show_next_legacy_step(interaction, self.state)


@bot.tree.command(name="migrate-legacy-roles", description="Scan for old rank/admin roles from before this bot and map them into the new system, one at a time.")
@app_commands.default_permissions(administrator=True)
@is_dictator()
async def migrate_legacy_roles(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    admin_roles, rank_roles = await scan_legacy_roles(interaction.guild)
    if not admin_roles and not rank_roles:
        await interaction.followup.send("✅ Nothing found — no legacy roles need migrating.", ephemeral=True)
        return

    state = LegacyMigrationState(interaction.user, admin_roles, rank_roles)
    await show_next_legacy_step(interaction, state, use_followup=True)


@bot.tree.command(name="grant-innovator-all", description="One-time bulk grant: Innovator badge for everyone currently in the server, bypassing the usual caps.")
@app_commands.default_permissions(administrator=True)
@is_dictator()
async def grant_innovator_to_current_members(interaction: discord.Interaction):
    guild = interaction.guild
    innovator_role = discord.utils.get(guild.roles, name=ROLE_INNOVATOR)
    if not innovator_role:
        await interaction.response.send_message("❌ The Innovator role doesn't exist right now — run infrastructure setup first.", ephemeral=True)
        return

    await interaction.response.defer(ephemeral=True)

    granted_members = []
    for member in guild.members:
        if member.bot:
            continue
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("INSERT OR IGNORE INTO innovators (user_id, username) VALUES (?, ?)", (member.id, str(member)))
            await conn.commit()
            newly_inserted = cur.rowcount > 0
        if innovator_role not in member.roles:
            try:
                await member.add_roles(innovator_role, reason="Bulk-granted — everyone present at this server's transition.")
            except discord.HTTPException:
                pass
        if newly_inserted:
            granted_members.append(member)

    if granted_members:
        general_ch = discord.utils.get(guild.channels, name="💬-general-chat")
        if general_ch:
            try:
                await general_ch.send(embed=discord.Embed(
                    title="🌟 EVERYONE HERE JUST BECAME AN INNOVATOR",
                    description=f"All **{len(granted_members)}** of you currently in this server have been recognized as founding Innovators — thank you for being here from the start.",
                    color=INNOVATOR_COLOR
                ))
            except discord.HTTPException:
                pass

        for member in granted_members:
            try:
                await member.send(embed=discord.Embed(
                    title="🌟 Thank you, genuinely",
                    description=(
                        "Mesk wanted me to pass this along personally: he really appreciates you being here "
                        "this early, testing things, dealing with the rough edges, helping this become what "
                        "it's going to be. That's not a small thing, and it doesn't go unnoticed.\n\n"
                        "This badge is tied to **your Discord ID**, not just this server — so however many "
                        "servers this ends up running in down the line, you'll always carry it. As things "
                        "grow, it's meant to keep meaning something: a little extra access, a little extra "
                        "trust, because you were here first.\n\n"
                        "You've also got access to **#🌟-innovator-lounge** now — a quieter space, just badge "
                        "holders and staff, for suggestions and issues.\n\n"
                        "Thank you for being one of the first."
                    ),
                    color=INNOVATOR_COLOR
                ))
            except discord.Forbidden:
                pass

    await interaction.followup.send(
        f"🌟 Granted the Innovator badge to **{len(granted_members)}** member(s) who didn't already have it "
        f"(anyone else was already recorded). This bypasses the usual first-50/first-25 caps — it's a "
        f"one-time thing for whoever's here right now.",
        ephemeral=True
    )
    await log_event(guild, f"🌟 **INNOVATOR BULK GRANT**\nBy: {interaction.user.mention}\nGranted: {len(granted_members)} member(s)")


@bot.tree.command(name="restore-innovators", description="Re-grant the Innovator badge to everyone recorded in the database, in case roles got reset.")
@app_commands.default_permissions(administrator=True)
@is_dictator()
async def restore_innovators(interaction: discord.Interaction):
    guild = interaction.guild
    innovator_role = discord.utils.get(guild.roles, name=ROLE_INNOVATOR)
    if not innovator_role:
        await interaction.response.send_message("❌ The Innovator role doesn't exist right now — run infrastructure setup first.", ephemeral=True)
        return

    await interaction.response.defer(ephemeral=True)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT user_id FROM innovators")
        recorded_ids = [row[0] for row in await cur.fetchall()]

    restored, missing = 0, 0
    for user_id in recorded_ids:
        member = guild.get_member(user_id)
        if not member:
            missing += 1
            continue
        if innovator_role not in member.roles:
            try:
                await member.add_roles(innovator_role, reason="Restoring Innovator badge from database record.")
                restored += 1
            except discord.HTTPException:
                pass

    await interaction.followup.send(
        f"🌟 Restored the Innovator badge to **{restored}** member(s) from **{len(recorded_ids)}** recorded testers. "
        f"({missing} recorded tester(s) are no longer in the server.)",
        ephemeral=True
    )
    await log_event(guild, f"🌟 **INNOVATOR BADGES RESTORED**\nBy: {interaction.user.mention}\nRestored: {restored} | No longer in server: {missing}")


@bot.tree.command(name="stop-alliance", description="Master kill switch freezing all new alliance creation.")
@app_commands.describe(lock="True to lock, False to unlock")
@app_commands.default_permissions(manage_channels=True)
@is_senior_staff()
async def stop_alliance(interaction: discord.Interaction, lock: bool):
    await interaction.response.defer(ephemeral=True)
    status = 'locked' if lock else 'unlocked'
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("INSERT OR REPLACE INTO settings (key, value) VALUES ('alliance_lock', ?)", (status,))
        await conn.commit()
    await interaction.followup.send(f"🔒 Alliance creation status set to: **{status.upper()}**", ephemeral=True)
    await log_event(interaction.guild, f"🔒 **ALLIANCE LOCK TOGGLED**\nAdmin: {interaction.user.mention}\nStatus: {status.upper()}")


@bot.tree.command(name="release-timekeeper", description="Opens 10-minute burst window (5 tags max).")
@app_commands.default_permissions(manage_channels=True)
@is_senior_staff()
async def release_timekeeper(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    burst_time = (datetime.now() + timedelta(minutes=10)).isoformat()
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("INSERT OR REPLACE INTO settings (key, value) VALUES ('timekeeper_burst', ?)", (burst_time,))
        await conn.commit()
    await interaction.followup.send("⏱️ Timekeeper burst window opened for 10 minutes!", ephemeral=True)
    await log_event(interaction.guild, f"⏱️ **TIMEKEEPER BURST OPENED**\nAdmin: {interaction.user.mention}\nAction: 10-minute rapid creation window activated.")


@bot.tree.command(name="database-tools", description="Posts a #logs panel: release current prisoners, or reset the users database.")
@app_commands.default_permissions(administrator=True)
@is_dictator()
async def database_tools(interaction: discord.Interaction):
    embed = discord.Embed(
        title="🛠️ DATABASE TOOLS",
        description=(
            "🔓 **Release Current Prisoner(s)** — immediately frees anyone currently serving time.\n\n"
            "🗑️ **Reset Users Database** — permanently wipes every member's registration record "
            "(name, tag, rank, server, strikes). Alliances, mod-log, warnings, and bans are **not** touched."
        ),
        color=discord.Color.dark_gold(),
        timestamp=datetime.now()
    )
    log_channel = discord.utils.get(interaction.guild.channels, name="logs")
    if not log_channel:
        await interaction.response.send_message("❌ #logs channel not found.", ephemeral=True)
        return

    await log_channel.send(embed=embed, view=DatabaseToolsView())
    await interaction.response.send_message("🛠️ Posted the database tools panel in #logs.", ephemeral=True)


@bot.tree.command(name="configure-servers", description="Set which Police Chief servers this community supports (e.g. '21,121' or '30,17' or '10-15').")
@app_commands.describe(servers="Comma-separated numbers and/or ranges, e.g. '21,121' or '10-15'")
@app_commands.default_permissions(manage_channels=True)
@is_senior_staff()
async def configure_servers(interaction: discord.Interaction, servers: str):
    new_list = parse_server_spec(servers)
    if not new_list:
        await interaction.response.send_message("❌ Couldn't parse that — try something like `21,121` or `10-15`.", ephemeral=True)
        return
    if len(new_list) > 25:
        await interaction.response.send_message(f"❌ That's {len(new_list)} servers — capping at 25 to avoid creating a wall of channels. Narrow it down.", ephemeral=True)
        return

    old_list = await get_managed_servers(interaction.guild.id)
    await set_guild_setting(interaction.guild.id, "managed_servers", ",".join(new_list))

    await interaction.response.send_message(f"🗺️ Managed servers updated to: {', '.join(new_list)}. Setting up anything new now...", ephemeral=True)

    await build_global_infrastructure(interaction.guild)

    added = [n for n in new_list if n not in old_list]
    removed = [n for n in old_list if n not in new_list]

    summary_lines = []
    if added:
        summary_lines.append(f"➕ Added: {', '.join(added)} — role + precinct channel + patrol cars created.")
    if removed:
        summary_lines.append(
            f"➖ Removed from config: {', '.join(removed)}. Their roles/channels were **left in place** "
            f"(golden rule) — remove them manually if you actually want them gone."
        )
    if not summary_lines:
        summary_lines.append("No actual change in the server list — just re-confirmed the current config.")

    embed = discord.Embed(
        title="🗺️ SERVER CONFIGURATION UPDATED",
        description=f"By: {interaction.user.mention}\nNow managing: {', '.join(new_list)}\n\n" + "\n".join(summary_lines),
        color=discord.Color.blurple(),
        timestamp=datetime.now()
    )
    log_channel = discord.utils.get(interaction.guild.channels, name="logs")
    if log_channel:
        await log_channel.send(embed=embed)


@bot.tree.command(name="show-role", description="Ephemeral admin audit listing members for a target role.")
@app_commands.describe(role="The role to audit")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def show_role(interaction: discord.Interaction, role: discord.Role):
    members = [m.display_name for m in role.members]
    if not members:
        await interaction.response.send_message(f"No members found holding role {role.name}.", ephemeral=True)
        return
    out = f"**Members holding {role.name} ({len(members)}):**\n" + ", ".join(members)
    await interaction.response.send_message(out[:2000], ephemeral=True)


@bot.tree.command(name="show-db-fields", description="Lists all database fields and values for a user.")
@app_commands.describe(member="The server member to inspect")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def show_db_fields(interaction: discord.Interaction, member: discord.Member):
    await interaction.response.defer(ephemeral=True)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT user_id, original_username, in_game_name, alliance_tag, rank_designation, server_number, invite_strikes, lifetime_invite_fails, timeout_until, pref_lang, prison_until FROM users WHERE user_id = ?", (member.id,))
        row = await cur.fetchone()

    if not row:
        await interaction.followup.send(f"❌ No database record found for {member.mention}.", ephemeral=True)
        return

    fields = ["User ID", "Original Username", "In-Game Name", "Alliance Tag", "Rank Designation", "Server Number", "Invite Strikes", "Lifetime Fails", "Timeout Until", "Pref Lang", "Prison Until"]
    out = f"📂 **Database Fields for {member.display_name}:**\n"
    for field, val in zip(fields, row):
        out += f"• **{field}:** {val if val is not None else 'None'}\n"
    await interaction.followup.send(out[:2000], ephemeral=True)


@bot.tree.command(name="show-field", description="Lists everything in the database sorted by a specific field.")
@app_commands.describe(field="Choose field to sort/filter by")
@app_commands.choices(field=[
    app_commands.Choice(name="Alliance Tag", value="alliance_tag"),
    app_commands.Choice(name="Server Number", value="server_number"),
    app_commands.Choice(name="Rank Designation", value="rank_designation"),
    app_commands.Choice(name="In-Game Name", value="in_game_name")
])
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def show_field(interaction: discord.Interaction, field: str):
    allowed_fields = {"alliance_tag", "server_number", "rank_designation", "in_game_name"}
    if field not in allowed_fields:
        await interaction.response.send_message("❌ Invalid field.", ephemeral=True)
        return

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute(f"SELECT in_game_name, original_username, {field} FROM users ORDER BY {field} ASC")
        rows = await cur.fetchall()

    if not rows:
        await interaction.response.send_message("❌ No user records found in the database.", ephemeral=True)
        return

    out = f"📊 **Database Sorted by {field.replace('_', ' ').title()}:**\n"
    for r in rows:
        name = r[0] or r[1] or "Unknown"
        val = r[2] if r[2] is not None else "None"
        out += f"• **{val}** — {name}\n"
    await interaction.response.send_message(out[:2000], ephemeral=True)


@bot.tree.command(name="alliance-leaderboard", description="Shows alliance member counts, ranked.")
async def alliance_leaderboard(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("🚔 This only works inside the server itself, not in a DM.", ephemeral=True)
        return
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT tag FROM alliances")
        tags = [row[0] for row in await cur.fetchall()]

    if not tags:
        await interaction.response.send_message("🏆 No alliances registered yet — someone's gotta be first.", ephemeral=True)
        return

    counts = []
    for tag in tags:
        role = discord.utils.get(interaction.guild.roles, name=tag)
        if role:
            counts.append((tag, len(role.members)))

    counts.sort(key=lambda x: x[1], reverse=True)
    medals = ["🥇", "🥈", "🥉"]

    lines = []
    for i, (tag, count) in enumerate(counts[:15]):
        rank_marker = medals[i] if i < 3 else f"`#{i + 1}`"
        lines.append(f"{rank_marker} **[{tag}]** — {count} member{'s' if count != 1 else ''}")

    embed = discord.Embed(
        title="🏆 ALLIANCE LEADERBOARD 🏆",
        description="\n".join(lines),
        color=discord.Color.gold(),
        timestamp=datetime.now()
    )
    if interaction.guild.icon:
        embed.set_thumbnail(url=interaction.guild.icon.url)
    embed.set_footer(text=f"{len(counts)} alliance(s) on the board")
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="start-chase", description="Manually start a round of Cops & Robbers right now.")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def start_chase(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    success, message = await start_chase_round(interaction.guild, interaction.user.mention)
    await interaction.followup.send(message, ephemeral=True)


@bot.tree.command(name="end-chase", description="End the current Cops & Robbers round early.")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def end_chase(interaction: discord.Interaction):
    active = await get_active_chase_round(interaction.guild)
    if not active:
        await interaction.response.send_message("ℹ️ There's no chase currently running.", ephemeral=True)
        return
    await interaction.response.send_message("🛑 Ending the current chase...", ephemeral=True)
    await end_chase_round(interaction.guild, active[0], f"🛑 Ended early by {interaction.user.mention}.")


# ------------------------------------------------------------
#  GENERAL GAME CONTROL — /game-start, /game-restart, /game-end
#  A unified admin interface covering BOTH round-based games (Cops &
#  Robbers and Rogue RoboCop) so staff aren't hunting for a different
#  command per game. /start-chase and /end-chase above still work as
#  shortcuts specifically for Cops & Robbers.
# ------------------------------------------------------------
GAME_CHOICES = [
    app_commands.Choice(name="Cops & Robbers", value="chase"),
    app_commands.Choice(name="Rogue RoboCop", value="rogue"),
]


async def _game_start_now(guild, game_value: str, started_by: str) -> tuple:
    """Returns (success: bool, message: str). Shared by /game-start and the
    delayed-start / auto-resume background tasks below."""
    if game_value == "chase":
        return await start_chase_round(guild, started_by)
    else:
        if server_is_busy():
            return False, f"🔧 RoboCop is busy ({_busy['reason']}) — the Rogue RoboCop will have to lurk later. Try again in a few minutes."
        ok = await start_rogue_bot_round(guild)
        if ok:
            return True, "🕵️ A new Rogue RoboCop round is now hiding somewhere in the server."
        return False, "ℹ️ A Rogue RoboCop round is already active."


async def _game_end_now(guild, game_value: str, reason: str) -> tuple:
    """Returns (success: bool, message: str). success=False just means
    nothing was running — not an error."""
    if game_value == "chase":
        active = await get_active_chase_round(guild)
        if not active:
            return False, "ℹ️ There's no Cops & Robbers round currently running."
        await end_chase_round(guild, active[0], reason)
        return True, "🛑 Cops & Robbers round ended."
    else:
        active = await get_active_rogue_round(guild)
        if not active:
            return False, "ℹ️ There's no Rogue RoboCop round currently hiding."
        await end_rogue_bot_round(guild, active[0], escaped=True, custom_description=reason)
        return True, "🛑 Rogue RoboCop round ended."


async def _delayed_game_start(guild, game_value: str, label: str, minutes: int, started_by: str):
    """Fire-and-forget background task backing 'start in N minutes' and the
    auto-resume half of /game-end's resume_in_minutes. If someone else
    already started a fresh round of this game before the timer fires,
    _game_start_now just reports 'already active' and this quietly no-ops —
    which is the right behavior, not a bug to guard against further."""
    await asyncio.sleep(max(0, minutes) * 60)
    await wait_until_not_busy()  # a scheduled start/auto-resume waits out any busy period instead of fizzling
    try:
        ok, message = await _game_start_now(guild, game_value, started_by)
        await log_event(guild, f"🕹️ Scheduled start for **{label}**: {message}")
    except Exception as e:
        print(f"[ERROR] Delayed game-start for {game_value} failed: {e}")


@bot.tree.command(name="game-start", description="Start Cops & Robbers or Rogue RoboCop now, or schedule it for N minutes from now.")
@app_commands.describe(game="Which game to start", in_minutes="Optional: wait this many minutes before starting")
@app_commands.choices(game=GAME_CHOICES)
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def game_start(interaction: discord.Interaction, game: app_commands.Choice[str], in_minutes: Optional[int] = None):
    await interaction.response.defer(ephemeral=True)
    guild = interaction.guild
    if in_minutes and in_minutes > 0:
        await interaction.followup.send(f"⏳ **{game.name}** will start in {in_minutes} minute(s).", ephemeral=True)
        await log_event(guild, f"🕹️ {interaction.user.mention} scheduled **{game.name}** to start in {in_minutes} minute(s).")
        bot.loop.create_task(_delayed_game_start(guild, game.value, game.name, in_minutes, interaction.user.mention))
        return
    ok, message = await _game_start_now(guild, game.value, interaction.user.mention)
    await interaction.followup.send(message, ephemeral=True)


@bot.tree.command(name="game-end", description="End Cops & Robbers or Rogue RoboCop now, optionally auto-restarting it after N minutes.")
@app_commands.describe(game="Which game to end", resume_in_minutes="Optional: automatically start a fresh round again after this many minutes")
@app_commands.choices(game=GAME_CHOICES)
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def game_end(interaction: discord.Interaction, game: app_commands.Choice[str], resume_in_minutes: Optional[int] = None):
    await interaction.response.defer(ephemeral=True)
    guild = interaction.guild
    reason = f"🛑 Paused by {interaction.user.mention}." if resume_in_minutes else f"🛑 Ended early by {interaction.user.mention}."
    ok, message = await _game_end_now(guild, game.value, reason)
    if resume_in_minutes and resume_in_minutes > 0:
        message += f"\n⏸️ Will automatically start a fresh round of **{game.name}** in {resume_in_minutes} minute(s)."
        bot.loop.create_task(_delayed_game_start(
            guild, game.value, game.name, resume_in_minutes,
            f"auto-resume after a pause by {interaction.user.mention}"
        ))
    await interaction.followup.send(message, ephemeral=True)


@bot.tree.command(name="game-restart", description="End the current round of a game (if any) and immediately start a fresh one.")
@app_commands.describe(game="Which game to restart")
@app_commands.choices(game=GAME_CHOICES)
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def game_restart(interaction: discord.Interaction, game: app_commands.Choice[str]):
    await interaction.response.defer(ephemeral=True)
    guild = interaction.guild
    await _game_end_now(guild, game.value, f"🔄 Restarted by {interaction.user.mention}.")
    ok, message = await _game_start_now(guild, game.value, interaction.user.mention)
    await interaction.followup.send(f"🔄 Restarted **{game.name}**.\n{message}", ephemeral=True)


@bot.tree.command(name="game-stats", description="See running server-wide totals for RPS, Cops & Robbers, and Rogue RoboCop.")
async def game_stats(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("🚔 This only works inside the server itself, not in a DM.", ephemeral=True)
        return
    await interaction.response.defer()
    embed = await build_game_stats_embed(interaction.guild)
    await interaction.followup.send(embed=embed)


@bot.tree.command(name="arrest", description="[Cops & Robbers] If you're a cop, try to arrest a robber by name.")
@app_commands.describe(name="Your best guess at who's hiding — name, tag, server, whatever you've got")
async def arrest(interaction: discord.Interaction, name: str):
    await _resolve_chase_guess(interaction, name, guesser_role="cop", target_role="robber")


@bot.tree.command(name="ambush", description="[Cops & Robbers] If you're a robber, try to take out a cop by name.")
@app_commands.describe(name="Your best guess at who's hunting you — name, tag, server, whatever you've got")
async def ambush(interaction: discord.Interaction, name: str):
    await _resolve_chase_guess(interaction, name, guesser_role="robber", target_role="cop")


async def _resolve_chase_guess(interaction: discord.Interaction, guess_text: str, guesser_role: str, target_role: str):
    # Defer immediately, before any of this — the loop below queries the
    # DB once per active target, which scales with how many people are
    # still in the round. The more successful and popular this game gets,
    # the more likely a non-deferred response would time out, which is
    # exactly backwards, so this one gets the safety net unconditionally.
    await interaction.response.defer(ephemeral=True)
    guild = interaction.guild
    active = await get_active_chase_round(guild)
    if not active:
        await interaction.followup.send("ℹ️ There's no chase running right now.", ephemeral=True)
        return
    round_id = active[0]

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("UPDATE chase_rounds SET last_activity_at = ? WHERE round_id = ?", (datetime.now().isoformat(), round_id))
        await conn.commit()
        await cur.execute(
            "SELECT role, eliminated FROM chase_participants WHERE round_id = ? AND user_id = ?",
            (round_id, interaction.user.id)
        )
        me = await cur.fetchone()

    if not me:
        await interaction.followup.send("You're not part of this round.", ephemeral=True)
        return
    if me[0] != guesser_role:
        await interaction.followup.send(f"You're not a {guesser_role} this round — that's not your move to make.", ephemeral=True)
        return
    if me[1]:
        await interaction.followup.send("You're already out of this round.", ephemeral=True)
        return

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("UPDATE chase_participants SET participated = 1 WHERE round_id = ? AND user_id = ?", (round_id, interaction.user.id))
        await conn.commit()
        await cur.execute(
            "SELECT user_id FROM chase_participants WHERE round_id = ? AND role = ? AND eliminated = 0",
            (round_id, target_role)
        )
        target_ids = [row[0] for row in await cur.fetchall()]

    best_score, best_id = 0.0, None
    for uid in target_ids:
        member = guild.get_member(uid)
        if not member:
            continue
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT in_game_name, alliance_tag, rank_designation, server_number FROM users WHERE user_id = ?", (uid,))
            db_row = await cur.fetchone()
        tag, servers, base_name = get_chase_target_identity(member, db_row)
        score = compute_guess_score(guess_text, tag, servers, base_name)
        if score > best_score:
            best_score, best_id = score, uid

    if best_score >= CHASE_HIT_THRESHOLD:
        target_member = guild.get_member(best_id)
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute(
                "UPDATE chase_participants SET eliminated = 1, eliminated_by = ?, eliminated_at = ? "
                "WHERE round_id = ? AND user_id = ? AND eliminated = 0",
                (interaction.user.id, datetime.now().isoformat(), round_id, best_id)
            )
            await conn.commit()
            won_race = cur.rowcount > 0

        if not won_race:
            # Someone else caught this exact target a moment earlier — treat it
            # as a near-miss rather than double-crediting two people for one catch.
            await interaction.followup.send(random.choice(CHASE_WARM_FLAVOR), ephemeral=True)
            return

        stat_col = "arrests_made" if guesser_role == "cop" else "ambushes_made"
        await increment_user_stat(interaction.user.id, stat_col)
        await increment_user_stat(best_id, "times_caught")

        await interaction.followup.send(random.choice(CHASE_HIT_FLAVOR), ephemeral=True)

        verb = "ARRESTED" if guesser_role == "cop" else "AMBUSHED"
        general_ch = discord.utils.get(guild.channels, name="💬-general-chat")
        if general_ch:
            target_label = target_member.mention if target_member else f"<@{best_id}>"
            try:
                await general_ch.send(embed=discord.Embed(
                    description=f"🚨 **{verb}!** {interaction.user.mention} just took {target_label} out of the chase.",
                    color=discord.Color.red()
                ))
            except discord.HTTPException:
                pass
        if target_member:
            try:
                await target_member.send(f"🚨 You've been {verb.lower()} by {interaction.user.mention}. You're out of this round — better luck next time, Chief.")
            except discord.Forbidden:
                pass
    elif best_score >= CHASE_WARM_THRESHOLD:
        await interaction.followup.send(random.choice(CHASE_WARM_FLAVOR), ephemeral=True)
        if best_id:
            warned_member = guild.get_member(best_id)
            if warned_member:
                try:
                    await warned_member.send("👀 Someone's getting warm. Might want to lay low.")
                except discord.Forbidden:
                    pass
    else:
        await interaction.followup.send(random.choice(CHASE_COLD_FLAVOR), ephemeral=True)


@bot.tree.command(name="leave-chase", description="Opt out of being auto-included in future Cops & Robbers rounds.")
async def leave_chase(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("INSERT OR IGNORE INTO chase_opt_outs (user_id) VALUES (?)", (interaction.user.id,))
        await conn.commit()
    await interaction.followup.send("🚪 You're opted out of future Cops & Robbers rounds. Run `/join-chase` any time to opt back in.", ephemeral=True)


@bot.tree.command(name="join-chase", description="Opt back in to being included in future Cops & Robbers rounds.")
async def join_chase(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("DELETE FROM chase_opt_outs WHERE user_id = ?", (interaction.user.id,))
        await conn.commit()
    await interaction.followup.send("🕵️ You're back in the mix for future Cops & Robbers rounds. See you out there, Chief.", ephemeral=True)


@bot.tree.command(name="chase-status", description="Check whether you're in the current Cops & Robbers round.")
async def chase_status(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("🚔 This only works inside the server itself, not in a DM.", ephemeral=True)
        return
    await interaction.response.defer(ephemeral=True)
    active = await get_active_chase_round(interaction.guild)
    if not active:
        await interaction.followup.send("ℹ️ No chase is currently running.", ephemeral=True)
        return
    round_id, ends_at_str, last_tier = active
    ends_at = datetime.fromisoformat(ends_at_str)
    remaining = max(0, int((ends_at - datetime.now()).total_seconds() // 60))

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT role, eliminated FROM chase_participants WHERE round_id = ? AND user_id = ?", (round_id, interaction.user.id))
        me = await cur.fetchone()

    if not me:
        await interaction.followup.send(f"You're not part of this round. It ends in about {remaining} minute(s).", ephemeral=True)
        return

    role, eliminated = me
    if eliminated:
        status = "❌ You've been taken out of this round."
    elif role == "cop":
        round_hours = await get_config_value(interaction.guild.id, "chase_round_hours")
        status = f"🚔 You're a **cop**, still active. Hints so far: {last_tier}/{round_hours}."
    else:
        status = "🕶️ You're a **robber**, still at large."
    await interaction.followup.send(f"{status}\nRound ends in about {remaining} minute(s).", ephemeral=True)


@bot.tree.command(name="catch", description="Guess the Rogue RoboCop's secret identity, if one is currently hiding.")
@app_commands.describe(name="Your best guess at the rogue bot's secret name")
async def catch_cmd(interaction: discord.Interaction, name: str):
    await interaction.response.defer(ephemeral=True)
    active = await get_active_rogue_round(interaction.guild)
    if not active:
        await interaction.followup.send("ℹ️ No rogue bot is currently hiding. Nothing to catch right now.", ephemeral=True)
        return

    round_id, secret_name, _ = active
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("UPDATE rogue_bot_rounds SET last_activity_at = ? WHERE round_id = ?", (datetime.now().isoformat(), round_id))
        await conn.commit()
    guess_clean = clean_display_name(name)
    secret_clean = clean_display_name(secret_name)
    score = SequenceMatcher(None, guess_clean, secret_clean).ratio()

    if score >= CHASE_HIT_THRESHOLD:
        won = await end_rogue_bot_round(interaction.guild, round_id, escaped=False, caught_by=interaction.user.id)
        if not won:
            await interaction.followup.send("Argh — someone just beat you to it by a hair!", ephemeral=True)
            return
        await increment_user_stat(interaction.user.id, "rogue_catches")
        await interaction.followup.send(f"🎉 **GOTCHA!** It really was **{secret_name}**. Nice work, Chief.", ephemeral=True)
    elif score >= CHASE_WARM_THRESHOLD:
        await interaction.followup.send(random.choice(CHASE_WARM_FLAVOR), ephemeral=True)
    else:
        await interaction.followup.send(random.choice(CHASE_COLD_FLAVOR), ephemeral=True)


@bot.tree.command(name="stats", description="See your own stats — RPS record, Rogue RoboCop catches, Cops & Robbers, and your overall rank.")
async def stats_cmd(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("🚔 This only works inside the server itself, not in a DM.", ephemeral=True)
        return

    guild = interaction.guild
    user_id = interaction.user.id

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT referrals, rps_wins, rps_losses, rps_ties, rogue_catches FROM user_stats WHERE user_id = ?", (user_id,))
        us = await cur.fetchone()
        await cur.execute("SELECT rounds_played, cop_wins, robber_wins, arrests_made, ambushes_made, times_caught FROM chase_stats WHERE user_id = ?", (user_id,))
        cs = await cur.fetchone()
        await cur.execute("SELECT 1 FROM innovators WHERE user_id = ?", (user_id,))
        is_innovator = bool(await cur.fetchone())

    referrals, rps_wins, rps_losses, rps_ties, rogue_catches = us if us else (0, 0, 0, 0, 0)
    rounds_played, cop_wins, robber_wins, arrests_made, ambushes_made, times_caught = cs if cs else (0, 0, 0, 0, 0, 0)

    leaderboard = await compute_leaderboard(guild, force_refresh=True)
    rank = next((i + 1 for i, (uid, _, _) in enumerate(leaderboard) if uid == user_id), None)
    my_score = next((score for uid, score, _ in leaderboard if uid == user_id), 0)

    embed = discord.Embed(
        title=f"📊 {interaction.user.display_name}'s Stats",
        color=discord.Color.blurple()
    )
    embed.add_field(name="🎮 Rock, Paper, Scissors", value=f"{rps_wins}W / {rps_losses}L / {rps_ties}T", inline=True)
    embed.add_field(name="🕵️ Rogue RoboCop Catches", value=str(rogue_catches), inline=True)
    embed.add_field(name="🎯 Referrals", value=str(referrals), inline=True)
    embed.add_field(
        name="🚔 Cops & Robbers",
        value=(
            f"Rounds played: {rounds_played}\n"
            f"Cop round wins: {cop_wins} | Robber round wins: {robber_wins}\n"
            f"Arrests made: {arrests_made} | Ambushes made: {ambushes_made}\n"
            f"Times caught: {times_caught}"
        ),
        inline=False
    )
    if is_innovator:
        embed.add_field(name="🌟 Innovator", value="Founding badge holder.", inline=True)
    embed.add_field(
        name="🏆 Overall",
        value=f"**{my_score}** points" + (f" — ranked **#{rank}**" if rank else " — not on the board yet, get out there!"),
        inline=False
    )
    embed.set_footer(text="Points: referral=2, RPS win=1, rogue catch=5, chase round win=3, arrest/ambush=2, Innovator=+10")

    await interaction.response.send_message(embed=embed, ephemeral=True)


@bot.tree.command(name="leaderboard", description="See the server's top 10 overall — combining every tracked achievement.")
async def leaderboard_cmd(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("🚔 This only works inside the server itself, not in a DM.", ephemeral=True)
        return

    leaderboard = await compute_leaderboard(interaction.guild, force_refresh=True)
    if not leaderboard:
        await interaction.response.send_message("📊 Nobody's on the board yet — go make some history.", ephemeral=True)
        return

    lines = []
    medals = ["🥇", "🥈", "🥉"]
    for i, (uid, score, _) in enumerate(leaderboard[:10]):
        member = interaction.guild.get_member(uid)
        label = member.mention if member else f"<@{uid}>"
        prefix = medals[i] if i < 3 else f"**#{i + 1}**"
        lines.append(f"{prefix} {label} — {score} points")

    embed = discord.Embed(
        title="🏆 PRECINCT LEADERBOARD",
        description="\n".join(lines),
        color=discord.Color.gold()
    )
    embed.set_footer(text="Run /stats to see your own full breakdown.")
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="monthly-standings", description="See this month's gold/silver/bronze standings so far, without resetting anything.")
async def monthly_standings_cmd(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("🚔 This only works inside the server itself, not in a DM.", ephemeral=True)
        return
    await interaction.response.defer()

    standings = await compute_monthly_champion_standings(interaction.guild)
    if not standings:
        await interaction.followup.send("📅 Nobody's scored anything yet this month — plenty of time left to change that.")
        return

    lines = []
    for i, (uid, month_score, _) in enumerate(standings[:10]):
        member = interaction.guild.get_member(uid)
        label = member.mention if member else f"<@{uid}>"
        prefix = MEDAL_LABEL[i] if i < 3 else f"**#{i + 1}**"
        lines.append(f"{prefix} — {label} ({month_score} points)")

    embed = discord.Embed(
        title="📅 MONTHLY STANDINGS (so far)",
        description="\n".join(lines),
        color=discord.Color.gold()
    )
    embed.set_footer(text="Live standings — resets automatically once the winners are announced next month.")
    await interaction.followup.send(embed=embed)


@bot.tree.command(name="set-monthly-prize", description="Set what this month's #1 Monthly Champion actually wins.")
@app_commands.describe(prize="The prize text to announce for Gold. Leave blank to reset to the default (bragging rights).")
@app_commands.default_permissions(manage_guild=True)
@is_senior_staff()
async def set_monthly_prize(interaction: discord.Interaction, prize: str = None):
    await interaction.response.defer(ephemeral=True)
    prize = (prize or "").strip()
    if not prize:
        await set_guild_setting(interaction.guild.id, "monthly_prize", DEFAULT_MONTHLY_PRIZE)
        await interaction.followup.send(f"✅ Monthly prize reset to the default: **{DEFAULT_MONTHLY_PRIZE}**", ephemeral=True)
    else:
        await set_guild_setting(interaction.guild.id, "monthly_prize", prize)
        await interaction.followup.send(f"✅ Monthly prize set to: **{prize}**\nThis is what next month's Gold winner will see announced.", ephemeral=True)
    await log_event(interaction.guild, f"🏆 **MONTHLY PRIZE UPDATED**\nStaff: {interaction.user.mention}\nNew prize: {prize or DEFAULT_MONTHLY_PRIZE}")


@bot.tree.command(name="monthly-champions-now", description="Manually trigger the Monthly Champion announcement right now (also resets standings for next month).")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def monthly_champions_now(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    await announce_monthly_champions(interaction.guild)
    await interaction.followup.send("✅ Monthly Champion announced (if there were any qualifying scores) and standings have been reset for the new month.", ephemeral=True)


@bot.tree.command(name="rps", description="Challenge another Chief (or Robocop) to Rock, Paper, Scissors.")
@app_commands.describe(opponent="Who to challenge (leave blank to face Robocop)")
async def rps(interaction: discord.Interaction, opponent: discord.Member = None):
    if opponent and opponent.bot:
        await interaction.response.send_message("You can't challenge a bot to a duel of wits... except me, apparently.", ephemeral=True)
        return
    if opponent and opponent.id == interaction.user.id:
        await interaction.response.send_message("You can't challenge yourself, Chief.", ephemeral=True)
        return

    view = RPSView(interaction.user, opponent)
    vs_text = opponent.mention if opponent else "**Robocop**"
    embed = discord.Embed(
        title="🎮 STREET JUSTICE SHOWDOWN",
        description=f"{interaction.user.mention} vs {vs_text}\nChoose your weapon below — picks are hidden until everyone's locked in!",
        color=discord.Color.blurple()
    )
    await interaction.response.send_message(embed=embed, view=view)
    view.message = await interaction.original_response()


@bot.tree.command(name="enforce-registration", description="Flag a specific existing member for mandatory registration right now.")
@app_commands.describe(member="The member who needs to register")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def enforce_registration(interaction: discord.Interaction, member: discord.Member):
    if member.bot:
        await interaction.response.send_message("❌ Can't register a bot.", ephemeral=True)
        return
    if member.id in _onboarding_in_progress:
        await interaction.response.send_message(f"⏳ {member.mention} is already mid-registration — check #gateway.", ephemeral=True)
        return

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT in_game_name, alliance_tag, rank_designation, server_number FROM users WHERE user_id = ?", (member.id,))
        row = await cur.fetchone()
    if row and row[0] and row[1] and row[2] and row[3]:
        await interaction.response.send_message(f"✅ {member.mention} is already fully registered — nothing to enforce.", ephemeral=True)
        return

    gateway_channel = discord.utils.get(interaction.guild.channels, name="gateway")
    if not gateway_channel:
        await interaction.response.send_message("❌ #gateway channel not found. Run infrastructure setup first.", ephemeral=True)
        return

    await interaction.response.send_message(f"🚔 Enforcing registration for {member.mention} — they've been flagged in #gateway.", ephemeral=True)

    try:
        await gateway_channel.set_permissions(member, read_messages=True, send_messages=True)
        await gateway_channel.send(f"🚨 {member.mention}, {interaction.user.mention} has flagged you for **mandatory registration**. Let's get this sorted — answer the questions below.")
    except discord.HTTPException:
        pass

    await log_event(interaction.guild, f"📋 **REGISTRATION ENFORCED**\nStaff: {interaction.user.mention}\nTarget: {member.mention}")

    await run_onboarding_safe(member)


class AddNicknameModal(discord.ui.Modal, title="Add / Update a Nickname"):
    server_number = discord.ui.TextInput(label="Server Number", placeholder="e.g. 21", max_length=10)
    nickname_input = discord.ui.TextInput(label="Your in-game name on this server", max_length=32)

    def __init__(self, member):
        super().__init__()
        self.member = member

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        server = self.server_number.value.strip()
        nickname = self.nickname_input.value.strip()

        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT server_number FROM users WHERE user_id = ?", (self.member.id,))
            row = await cur.fetchone()
        their_servers = await parse_stored_server_field(row[0], self.member.guild.id) if row and row[0] else []

        if server not in their_servers:
            servers_display = ", ".join(their_servers) if their_servers else "none on file"
            await interaction.followup.send(
                f"⚠️ You're not currently registered for server `{server}` (your servers: {servers_display}). "
                f"If that needs updating, talk to staff.",
                ephemeral=True
            )
            return

        await upsert_user_nickname(self.member.id, server, nickname, make_active=False)
        view = ConfirmActivateNicknameView(self.member, server, nickname)
        await interaction.followup.send(
            f"✅ Saved **{nickname}** for server `{server}`. Want to make this your active display name now?\n\n"
            + await tf(NAME_CHANGE_REMINDER, self.member.id, abilities=abilities_mention(self.member.guild)),
            view=view, ephemeral=True
        )


class ConfirmActivateNicknameView(discord.ui.View):
    def __init__(self, member, server, nickname):
        super().__init__(timeout=120.0)
        self.member = member
        self.server = server
        self.nickname = nickname

    @discord.ui.button(label="Yes, use it now", style=discord.ButtonStyle.success, emoji="✅")
    async def yes(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user != self.member:
            await interaction.response.send_message("This isn't your panel.", ephemeral=True)
            return
        await switch_active_nickname(interaction.guild, self.member, self.server)
        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(content=f"✅ Your display name is now **{self.nickname}**.", view=self)

    @discord.ui.button(label="No, just save it", style=discord.ButtonStyle.secondary)
    async def no(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user != self.member:
            await interaction.response.send_message("This isn't your panel.", ephemeral=True)
            return
        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(content=f"✅ Saved **{self.nickname}** for later — your display name is unchanged.", view=self)


class NicknameSwitchSelect(discord.ui.Select):
    def __init__(self, member, entries):
        self.member = member
        options = [
            discord.SelectOption(label=f"Server {s}: {n}"[:100], value=s, default=bool(active))
            for s, n, active in entries[:25]
        ]
        super().__init__(placeholder="Switch your active display name...", min_values=1, max_values=1, options=options)

    async def callback(self, interaction: discord.Interaction):
        if interaction.user != self.member:
            await interaction.response.send_message("This isn't your panel.", ephemeral=True)
            return
        server = self.values[0]
        success = await switch_active_nickname(interaction.guild, self.member, server)
        if success:
            await interaction.response.send_message(f"✅ Switched your active display name for server `{server}`.", ephemeral=True)
        else:
            await interaction.response.send_message("❌ Something went wrong — try again.", ephemeral=True)


class NicknameManageView(discord.ui.View):
    def __init__(self, member, entries):
        super().__init__(timeout=180.0)
        self.member = member
        if len(entries) > 1:
            self.add_item(NicknameSwitchSelect(member, entries))

    @discord.ui.button(label="➕ Add / Update a Nickname", style=discord.ButtonStyle.primary)
    async def add_nickname(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user != self.member:
            await interaction.response.send_message("This isn't your panel.", ephemeral=True)
            return
        await interaction.response.send_modal(AddNicknameModal(self.member))


@bot.tree.command(name="nickname", description="Manage your in-game nicknames across different servers.")
async def nickname_cmd(interaction: discord.Interaction):
    await interaction.response.defer(ephemeral=True)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute(
            "SELECT server_number, nickname, is_active FROM user_nicknames WHERE user_id = ? ORDER BY server_number",
            (interaction.user.id,)
        )
        entries = await cur.fetchall()

    if not entries:
        await interaction.followup.send(
            "You don't have any saved nicknames yet — handy if your in-game name is different across servers. "
            "Add one below.",
            view=NicknameManageView(interaction.user, entries), ephemeral=True
        )
        return

    lines = [f"• Server `{s}`: **{n}**" + (" ✅ *(active)*" if a else "") for s, n, a in entries]
    embed = discord.Embed(title="📇 Your Nicknames", description="\n".join(lines), color=discord.Color.blue())
    await interaction.followup.send(embed=embed, view=NicknameManageView(interaction.user, entries), ephemeral=True)


class ChangeNickModal(discord.ui.Modal, title="What's your new in-game name?"):
    new_name = discord.ui.TextInput(label="Your in-game name", placeholder="Just the name — no tags or server numbers", max_length=32)

    def __init__(self, member, reason_label: str):
        super().__init__()
        self.member = member
        self.reason_label = reason_label

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        new_name = self.new_name.value.strip()
        if not new_name:
            await interaction.followup.send("❌ That can't be blank — run `/change-nick` again.", ephemeral=True)
            return
        cleaned = strip_nickname_decorations(new_name) or new_name

        full_nickname = await apply_ingame_name_change(interaction.guild, self.member, cleaned)
        reminder = await tf(NAME_CHANGE_REMINDER, interaction.user.id, abilities=abilities_mention(interaction.guild))
        await interaction.followup.send(f"✅ Done — your display name is now **{full_nickname}**.\n\n{reminder}", ephemeral=True)
        await log_event(
            interaction.guild,
            f"📇 **NICKNAME CHANGED** ({self.reason_label})\n{self.member.mention} is now **{full_nickname}**"
        )


class ChangeNickReasonView(discord.ui.View):
    """Asks WHY before touching anything — a genuine in-game name change
    and a typo/registration mistake land in the same place either way
    (only the base name changes, tag/server suffix untouched), but the
    reason still gets logged so staff can tell the two apart later if it
    ever matters."""

    def __init__(self, member):
        super().__init__(timeout=120.0)
        self.member = member

    @discord.ui.button(label="I actually changed it in-game", style=discord.ButtonStyle.primary, emoji="🔄")
    async def changed(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user != self.member:
            await interaction.response.send_message("This isn't your panel.", ephemeral=True)
            return
        await interaction.response.send_modal(ChangeNickModal(self.member, "actual in-game name change"))

    @discord.ui.button(label="I made a mistake / typo", style=discord.ButtonStyle.secondary, emoji="✏️")
    async def mistake(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user != self.member:
            await interaction.response.send_message("This isn't your panel.", ephemeral=True)
            return
        await interaction.response.send_modal(ChangeNickModal(self.member, "typo/registration correction"))


@bot.tree.command(name="change-nick", description="Update your in-game name if it changed, or fix a typo — keeps your alliance tag/server tag intact.")
async def change_nick_cmd(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("🚔 This only works inside the server itself, not in a DM.", ephemeral=True)
        return
    await interaction.response.send_message(
        "📇 Quick question first — did you actually change your name **in the game**, or did you just make a "
        "typo/mistake when you registered?",
        view=ChangeNickReasonView(interaction.user),
        ephemeral=True
    )


class FixTagModal(discord.ui.Modal, title="Which alliance are you actually in?"):
    tag_input = discord.ui.TextInput(label="Alliance tag (2-4 letters)", placeholder="e.g. PTD", max_length=4, min_length=2)

    def __init__(self, member):
        super().__init__()
        self.member = member

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        guild = interaction.guild
        new_tag = self.tag_input.value.strip().upper()
        if not (2 <= len(new_tag) <= 4 and new_tag.isalpha()):
            await interaction.followup.send("❌ A tag is 2–4 letters only (e.g. `PTD`). Run `/fix-me` again to retry.", ephemeral=True)
            return

        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT alliance_tag, rank_designation, server_number FROM users WHERE user_id = ?", (self.member.id,))
            row = await cur.fetchone()
            await cur.execute("SELECT tag FROM alliances")
            known_keys = [r[0] for r in await cur.fetchall()]
        my_servers = await parse_stored_server_field(row[2], guild.id) if row and row[2] else []
        new_tag = resolve_alliance_key(new_tag, my_servers, known_keys) or new_tag  # same tag on another server -> the right one
        in_db = new_tag in known_keys
        current_tag = row[0] if row else None
        current_rank = row[1] if row else None

        if new_tag == current_tag:
            await interaction.followup.send(f"ℹ️ You're already in **[{new_tag}]** — nothing to change.", ephemeral=True)
            return

        if not in_db and not tag_exists_live(guild, new_tag):
            await interaction.followup.send(
                f"🤔 There's no alliance **[{new_tag}]** on this server yet. If you're **founding** a new one, that needs a "
                f"human — I've pinged staff. If you just mistyped it, run `/fix-me` again.",
                ephemeral=True
            )
            await log_event(guild, f"🆘 **FIX-ME: UNKNOWN TAG**\n{self.member.mention} tried to switch to **[{new_tag}]**, which doesn't exist. They may be trying to found it — check in with them.")
            await notify_staff_dm(guild, "🆘 /fix-me hit an unknown tag", f"{self.member.mention} wants to be in **[{new_tag}]**, which doesn't exist here. Might be a new alliance — worth a look.", color=discord.Color.orange())
            return

        # R5s of the *current* tag get pointed at the right tool if it's the
        # tag itself that's wrong, rather than quietly demoted to Member.
        if current_tag and current_rank == "R5":
            r5_role = discord.utils.get(guild.roles, name=f"{current_tag}-R5")
            if r5_role and r5_role in self.member.roles:
                await interaction.followup.send(
                    f"👑 You're the **R5 of [{current_tag}]**. Two different things you might mean:\n"
                    f"• The alliance's *tag itself* is wrong → use `/rename-tag {current_tag} {new_tag}` (keeps you R5, moves everyone).\n"
                    f"• You personally are *moving* to [{new_tag}] → confirm below. **You'd become a regular Member there** and [{current_tag}] would lose its R5.",
                    view=ConfirmTagSwitchView(self.member, current_tag, new_tag), ephemeral=True
                )
                return

        await interaction.followup.send(
            f"🏷️ Move you from **[{current_tag or 'no alliance'}]** to **[{new_tag}]**?"
            + (f" You'll lose your **{current_rank}** rank in [{current_tag}]." if current_rank in ("R4", "R5") else ""),
            view=ConfirmTagSwitchView(self.member, current_tag, new_tag), ephemeral=True
        )


class ConfirmTagSwitchView(discord.ui.View):
    def __init__(self, member, old_tag, new_tag):
        super().__init__(timeout=120.0)
        self.member, self.old_tag, self.new_tag = member, old_tag, new_tag

    @discord.ui.button(label="Yes, switch me", style=discord.ButtonStyle.success, emoji="✅")
    async def yes(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user != self.member:
            await interaction.response.send_message("This isn't your panel.", ephemeral=True)
            return
        await interaction.response.defer(ephemeral=True)
        result = await switch_member_alliance(interaction.guild, self.member, self.new_tag)
        for item in self.children:
            item.disabled = True
        await interaction.edit_original_response(content=f"✅ Done — you're now in **[{self.new_tag}]**. Display name: **{result['nick']}**", view=self)

    @discord.ui.button(label="Cancel", style=discord.ButtonStyle.secondary)
    async def no(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user != self.member:
            await interaction.response.send_message("This isn't your panel.", ephemeral=True)
            return
        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(content="👍 No changes made.", view=self)


class FixServerModal(discord.ui.Modal, title="Which server(s) do you play on?"):
    servers_input = discord.ui.TextInput(label="Server number(s)", placeholder="e.g. 21  —  or  21, 121  if you play on both", max_length=60)

    def __init__(self, member):
        super().__init__()
        self.member = member

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        managed = await get_managed_servers(interaction.guild.id)
        raw = self.servers_input.value.strip().lower()
        nums = managed if raw == "all" else normalize_server_input(raw, managed)
        if not nums:
            await interaction.followup.send(
                f"❌ I couldn't match that to any of our servers. Valid: {', '.join(f'`{n}`' for n in managed)} (or `all`). Run `/fix-me` again.",
                ephemeral=True
            )
            return
        nick = await change_member_servers(interaction.guild, self.member, nums)
        await interaction.followup.send(f"✅ Servers set to **{'/'.join(nums)}**. Display name: **{nick}**", ephemeral=True)


class FixMeView(discord.ui.View):
    def __init__(self, member):
        super().__init__(timeout=180.0)
        self.member = member

    async def _mine(self, interaction) -> bool:
        if interaction.user != self.member:
            await interaction.response.send_message("This isn't your panel — run `/fix-me` yourself.", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="My name is wrong", style=discord.ButtonStyle.primary, emoji="✏️", row=0)
    async def fix_name(self, interaction: discord.Interaction, button: discord.ui.Button):
        if await self._mine(interaction):
            await interaction.response.send_modal(ChangeNickModal(self.member, "via /fix-me"))

    @discord.ui.button(label="My alliance tag is wrong", style=discord.ButtonStyle.primary, emoji="🏷️", row=0)
    async def fix_tag(self, interaction: discord.Interaction, button: discord.ui.Button):
        if await self._mine(interaction):
            await interaction.response.send_modal(FixTagModal(self.member))

    @discord.ui.button(label="My server is wrong", style=discord.ButtonStyle.primary, emoji="🗺️", row=1)
    async def fix_server(self, interaction: discord.Interaction, button: discord.ui.Button):
        if await self._mine(interaction):
            await interaction.response.send_modal(FixServerModal(self.member))

    @discord.ui.button(label="I don't understand — get me a human", style=discord.ButtonStyle.secondary, emoji="🆘", row=1)
    async def get_help(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not await self._mine(interaction):
            return
        await interaction.response.defer(ephemeral=True)
        guild = interaction.guild
        await log_event(guild, f"🆘 **MEMBER NEEDS A HAND**\n{self.member.mention} hit 'get me a human' in /fix-me. Reach out to them.")
        await notify_staff_dm(guild, "🆘 Someone needs help", f"{self.member.mention} asked for a human via /fix-me — a quick DM will sort it.", color=discord.Color.orange())
        await interaction.followup.send(
            "🆘 Done — I've pinged staff, and someone will reach out. In the meantime, here's the short version of how names work here:\n\n"
            "• Your Discord name is built as **`YourName [TAG] (server)`** — I do that automatically.\n"
            "• **YourName** = your exact in-game username.\n"
            "• **TAG** = the 2–4 letters next to your alliance's name in the game.\n"
            "• **server** = the number of the game server you play on.\n\n"
            "If any of those three is wrong, `/fix-me` has a button for it — and nothing you pick is permanent.",
            ephemeral=True
        )


@bot.tree.command(name="fix-me", description="Registered with the wrong name, tag, or server? Fix it yourself here — or get a human.")
async def fix_me_cmd(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("🚔 This only works inside the server itself, not in a DM.", ephemeral=True)
        return
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT in_game_name, alliance_tag, server_number FROM users WHERE user_id = ?", (interaction.user.id,))
        row = await cur.fetchone()
    if not row or not (row[0] and row[1] and row[2]):
        gateway = discord.utils.get(interaction.guild.channels, name="gateway")
        await interaction.response.send_message(
            f"📋 You haven't finished registering yet, so there's nothing to fix — head to {gateway.mention if gateway else '#gateway'} "
            f"and run `/register`. (Type `help` there any time and a human will come.)",
            ephemeral=True
        )
        return
    servers = await parse_stored_server_field(row[2], interaction.guild.id)
    await interaction.response.send_message(
        f"🛠️ **Here's what I have on file for you:**\n"
        f"• In-game name: **{row[0]}**\n• Alliance: **[{row[1]}]**\n• Server(s): **{'/'.join(servers) or '—'}**\n\n"
        f"What's wrong?",
        view=FixMeView(interaction.user), ephemeral=True
    )


class ConfirmDissolveView(discord.ui.View):
    def __init__(self, actor, tag):
        super().__init__(timeout=60.0)
        self.actor, self.tag = actor, tag

    @discord.ui.button(label="Yes, dissolve it", style=discord.ButtonStyle.danger, emoji="🧹")
    async def yes(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user != self.actor:
            await interaction.response.send_message("This isn't your panel.", ephemeral=True)
            return
        await interaction.response.defer(ephemeral=True)
        done = await dissolve_alliance(interaction.guild, self.tag, interaction.user.mention)
        for item in self.children:
            item.disabled = True
        await interaction.edit_original_response(content=f"🧹 **[{self.tag}]** dissolved — removed: {', '.join(done)}", view=self)

    @discord.ui.button(label="Cancel", style=discord.ButtonStyle.secondary)
    async def no(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user != self.actor:
            await interaction.response.send_message("This isn't your panel.", ephemeral=True)
            return
        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(content="👍 Nothing touched.", view=self)


@bot.tree.command(name="dissolve-alliance", description="Delete an alliance entirely — roles, channels, and records. Typo cleanup. Asks first.")
@app_commands.describe(tag="The alliance tag to remove")
@app_commands.default_permissions(manage_channels=True)
@is_senior_staff()
async def dissolve_alliance_cmd(interaction: discord.Interaction, tag: str):
    tag = normalize_alliance_key(tag)
    guild = interaction.guild
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT 1 FROM alliances WHERE tag = ?", (tag,))
        in_db = bool(await cur.fetchone())
        await cur.execute("SELECT COUNT(*) FROM users WHERE alliance_tag = ?", (tag,))
        (db_members,) = await cur.fetchone()
    if not in_db and not tag_exists_live(guild, tag):
        await interaction.response.send_message(f"❌ No alliance **[{tag}]** found — not in the database, not on the server.", ephemeral=True)
        return
    tag_role = discord.utils.get(guild.roles, name=tag)
    live_members = len(tag_role.members) if tag_role else 0
    warn = f"\n⚠️ **It is NOT empty** — {live_members} member(s) hold the role, {db_members} record(s) point at it. They'll all be left with no alliance." if (live_members or db_members) else "\n✅ It's empty — nobody holds the role, no records point at it."
    await interaction.response.send_message(
        f"🧹 Dissolve **[{tag}]**? This deletes its roles, both categories with every channel inside, and its database rows. **Cannot be undone.**{warn}",
        view=ConfirmDissolveView(interaction.user, tag), ephemeral=True
    )


@bot.tree.command(name="language", description="Change the language I use when talking to you.")
async def language_cmd(interaction: discord.Interaction):
    view = LanguageView(interaction.user)
    await interaction.response.send_message(
        "🌍 Pick your language below — I'll use it for everything I say to you personally from now on.",
        view=view,
        ephemeral=True
    )


@bot.tree.command(name="timezone", description="Set or change your approximate time zone.")
async def timezone_cmd(interaction: discord.Interaction):
    view = TimezoneView(interaction.user)
    await interaction.response.send_message(
        "🕐 Pick your approximate time zone below — I'll use it to tell you how this server's schedule lines up with your own.",
        view=view,
        ephemeral=True
    )


@bot.tree.command(name="register", description="Manually start (or restart) your RoboCop registration if you were never onboarded.")
async def register(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("🚔 This only works inside the server itself, not in a DM — head back there and try again.", ephemeral=True)
        return

    gateway_channel = discord.utils.get(interaction.guild.channels, name="gateway")
    if gateway_channel and interaction.channel.id != gateway_channel.id:
        await interaction.response.send_message(f"📋 Please run this in {gateway_channel.mention}.", ephemeral=True)
        return

    if interaction.user.id in _onboarding_in_progress:
        await interaction.response.send_message("⏳ You're already mid-registration — check the messages above!", ephemeral=True)
        return

    await interaction.response.send_message("🚔 Starting your registration now — check the messages below!", ephemeral=True)
    await run_onboarding_safe(interaction.user)


ACHIEVEMENT_WEIGHTS = {
    "referral": 2, "rps_win": 1, "rogue_catch": 5,
    "chase_cop_win": 3, "chase_robber_win": 3, "chase_arrest": 2, "chase_ambush": 2,
    "innovator_bonus": 10,
}


_leaderboard_cache = {}  # guild_id -> (monotonic_timestamp, results)
LEADERBOARD_CACHE_SECONDS = 300  # 5 minutes — plenty fresh for a fun leaderboard, cuts redundant recomputation


async def compute_leaderboard(guild, force_refresh: bool = False) -> list:
    """Returns [(user_id, score, breakdown_dict), ...] sorted descending —
    one combined ranking across every tracked achievement: RPS, Rogue
    RoboCop catches, Cops & Robbers, referrals, and Innovator status.
    Only includes members still actually in the guild, and only those
    with a nonzero score. Cached briefly by default — this gets called
    on every single login for the top-10 celebration check, and that
    background check doesn't need millisecond-fresh accuracy. Pass
    force_refresh=True for a deliberate, user-initiated check (/stats,
    /leaderboard) where someone who just won a match reasonably expects
    to see it reflected right away."""
    cached = _leaderboard_cache.get(guild.id)
    if not force_refresh and cached and (time.monotonic() - cached[0]) < LEADERBOARD_CACHE_SECONDS:
        return cached[1]

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT user_id, referrals, rps_wins, rogue_catches FROM user_stats")
        user_stat_rows = {r[0]: r for r in await cur.fetchall()}
        await cur.execute("SELECT user_id, cop_wins, robber_wins, arrests_made, ambushes_made FROM chase_stats")
        chase_rows = {r[0]: r for r in await cur.fetchall()}
        await cur.execute("SELECT user_id FROM innovators")
        innovator_ids = {r[0] for r in await cur.fetchall()}

    all_ids = set(user_stat_rows) | set(chase_rows) | innovator_ids
    results = []
    for uid in all_ids:
        if not guild.get_member(uid):
            continue
        us = user_stat_rows.get(uid, (uid, 0, 0, 0))
        cs = chase_rows.get(uid, (uid, 0, 0, 0, 0))
        is_innovator = uid in innovator_ids
        breakdown = {
            "referrals": us[1], "rps_wins": us[2], "rogue_catches": us[3],
            "chase_cop_wins": cs[1], "chase_robber_wins": cs[2],
            "chase_arrests": cs[3], "chase_ambushes": cs[4],
            "innovator": is_innovator,
        }
        score = (
            us[1] * ACHIEVEMENT_WEIGHTS["referral"] +
            us[2] * ACHIEVEMENT_WEIGHTS["rps_win"] +
            us[3] * ACHIEVEMENT_WEIGHTS["rogue_catch"] +
            cs[1] * ACHIEVEMENT_WEIGHTS["chase_cop_win"] +
            cs[2] * ACHIEVEMENT_WEIGHTS["chase_robber_win"] +
            cs[3] * ACHIEVEMENT_WEIGHTS["chase_arrest"] +
            cs[4] * ACHIEVEMENT_WEIGHTS["chase_ambush"] +
            (ACHIEVEMENT_WEIGHTS["innovator_bonus"] if is_innovator else 0)
        )
        if score > 0:
            results.append((uid, score, breakdown))
    results.sort(key=lambda x: -x[1])
    _leaderboard_cache[guild.id] = (time.monotonic(), results)
    return results


# ------------------------------------------------------------
#  MONTHLY CHAMPION — gold/silver/bronze standings computed as a delta off
#  the same all-time scoring compute_leaderboard() already does, rather
#  than a second parallel point ledger wired into RPS/Chase/Rogue's award
#  code in five separate places. "This month's" score for a member is
#  simply (their current all-time score) - (their score at the start of
#  the month, i.e. the baseline). The baseline resets right after every
#  monthly announcement.
# ------------------------------------------------------------
DEFAULT_MONTHLY_PRIZE = "Bragging rights. Pure, unfiltered bragging rights."
MEDAL_LABEL = {0: "🥇 Gold", 1: "🥈 Silver", 2: "🥉 Bronze"}


async def compute_monthly_champion_standings(guild) -> list:
    """Returns [(user_id, month_score, breakdown), ...] sorted descending,
    keeping only members with a positive gain since the last baseline
    snapshot. Members with no baseline row yet are treated as starting
    from 0 (fine for someone who joined mid-month — their whole all-time
    score is fairly "this month's" for them)."""
    leaderboard = await compute_leaderboard(guild, force_refresh=True)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT user_id, score FROM monthly_score_baseline WHERE guild_id = ?", (guild.id,))
        baselines = {r[0]: r[1] for r in await cur.fetchall()}

    standings = []
    for uid, score, breakdown in leaderboard:
        month_score = score - baselines.get(uid, 0)
        if month_score > 0:
            standings.append((uid, month_score, breakdown))
    standings.sort(key=lambda x: -x[1])
    return standings


async def snapshot_monthly_baseline(guild):
    """Wipes and repopulates this guild's baseline from the current live
    all-time leaderboard totals — called right after every monthly
    announcement (so next month's race starts at zero) and once, on first
    startup for a guild with no baseline yet, so the very first month
    doesn't dump every member's entire lifetime score as "this month"."""
    leaderboard = await compute_leaderboard(guild, force_refresh=True)
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("DELETE FROM monthly_score_baseline WHERE guild_id = ?", (guild.id,))
        await cur.executemany(
            "INSERT INTO monthly_score_baseline (guild_id, user_id, score) VALUES (?, ?, ?)",
            [(guild.id, uid, score) for uid, score, _ in leaderboard]
        )
        await conn.commit()


async def ensure_monthly_baseline_seeded(guild):
    """Startup safety net — if this guild has never had a baseline snapshot
    taken (fresh install, or upgrading from a version before this feature
    existed), seed one silently now rather than letting the first monthly
    announcement award everyone's entire lifetime score as "this month"."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT 1 FROM monthly_score_baseline WHERE guild_id = ? LIMIT 1", (guild.id,))
        has_baseline = await cur.fetchone()
    if not has_baseline:
        await snapshot_monthly_baseline(guild)


async def announce_monthly_champions(guild):
    """Posts the Gold/Silver/Bronze embed to #general-chat, reads the
    configurable prize text (falling back to DEFAULT_MONTHLY_PRIZE), logs
    to #logs, then resets the baseline for next month. Only the #1 Gold
    winner gets the configurable prize — Silver/Bronze get medal
    recognition without a separately configurable prize of their own,
    matching how this was asked for (one prize concept, alongside a tier
    structure)."""
    standings = await compute_monthly_champion_standings(guild)
    general_ch = discord.utils.get(guild.channels, name="💬-general-chat")

    if not standings:
        if general_ch:
            try:
                await general_ch.send(
                    "📅 **MONTHLY CHAMPION** — nobody put any points on the board this month. "
                    "No medals to hand out — get out there and earn some, Chiefs."
                )
            except discord.HTTPException:
                pass
        await log_event(guild, "📅 **MONTHLY CHAMPION**\nNo qualifying scores this month — nothing announced.")
        await snapshot_monthly_baseline(guild)
        return

    prize = await get_guild_setting(guild.id, "monthly_prize") or DEFAULT_MONTHLY_PRIZE

    lines = []
    for i, (uid, month_score, _) in enumerate(standings[:3]):
        member = guild.get_member(uid)
        label = member.mention if member else f"<@{uid}>"
        lines.append(f"{MEDAL_LABEL[i]} — {label} ({month_score} points)")
    embed = discord.Embed(
        title="📅 MONTHLY CHAMPION",
        description="\n".join(lines),
        color=discord.Color.gold(),
        timestamp=datetime.now()
    )
    embed.add_field(name="🏆 This month's prize (Gold only)", value=prize, inline=False)
    embed.set_footer(text="Standings reset now — a fresh race starts today.")

    if general_ch:
        try:
            await general_ch.send(embed=embed)
        except discord.HTTPException:
            pass
    await log_event(guild, f"📅 **MONTHLY CHAMPION ANNOUNCED**\n" + "\n".join(lines) + f"\nPrize: {prize}")

    await snapshot_monthly_baseline(guild)


async def monthly_champion_scheduler(guild):
    """Fires once, on the 1st of each month at the configured hour (local
    server time), same wall-clock-recompute-next_run scheduling pattern as
    daily_chase_scheduler/daily_game_stats_scheduler — recomputing from
    wall-clock time each loop (rather than 'N days after last run') is
    what correctly handles every month's different length and the
    December -> January year rollover without special-casing either."""
    while True:
        try:
            tz = await get_guild_timezone(guild.id)
            champ_hour = await get_config_value(guild.id, "monthly_champion_hour")
            now_local = datetime.now(tz)
            next_run = now_local.replace(day=1, hour=champ_hour, minute=0, second=0, microsecond=0)
            if next_run <= now_local:
                if next_run.month == 12:
                    next_run = next_run.replace(year=next_run.year + 1, month=1)
                else:
                    next_run = next_run.replace(month=next_run.month + 1)
            await asyncio.sleep((next_run - now_local).total_seconds())

            if not _is_leader:
                continue
            await announce_monthly_champions(guild)
        except Exception as e:
            print(f"[ERROR] Monthly champion scheduler hit an error, will retry tomorrow: {e}")
            await asyncio.sleep(3600)


async def build_rap_sheet(user_id: int) -> str:
    """A quick moderation-history summary — warnings, invite-check fails,
    and the last few mod-log entries where this person was the target."""
    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT COUNT(*) FROM warnings WHERE user_id = ?", (user_id,))
        warn_count = (await cur.fetchone())[0]
        await cur.execute(
            "SELECT action_type, reason, undone, timestamp FROM mod_log WHERE target_id = ? ORDER BY timestamp DESC LIMIT 5",
            (user_id,)
        )
        mod_rows = await cur.fetchall()
        await cur.execute("SELECT lifetime_invite_fails FROM users WHERE user_id = ?", (user_id,))
        fails_row = await cur.fetchone()

    lifetime_fails = fails_row[0] if fails_row else 0

    if warn_count == 0 and not mod_rows and lifetime_fails == 0:
        return "✅ Clean record. No warnings, no mod actions on file."

    lines = []
    if warn_count:
        lines.append(f"⚠️ {warn_count} warning(s) on file.")
    if lifetime_fails:
        lines.append(f"🎫 {lifetime_fails} invite-check failure(s) (lifetime).")
    for action_type, reason, undone, ts in mod_rows:
        marker = " ↩️ (reversed)" if undone else ""
        date_str = ts.split(" ")[0] if ts else "?"
        lines.append(f"• `{date_str}` **{action_type.upper()}**{marker} — {reason or 'no reason given'}")

    return "\n".join(lines)[:1024]


@bot.tree.command(name="abilities", description="Get a verbose, cheeky rundown of everything you can do with Robo right now.")
async def abilities(interaction: discord.Interaction):
    if not interaction.guild:
        await interaction.response.send_message("🚔 This only works inside the server itself, not in a DM.", ephemeral=True)
        return

    caps = compute_capabilities(interaction.user)
    role_names = {r.name for r in interaction.user.roles}

    intro_by_rank = {
        ROLE_DICTATOR: "👑 Oh. It's *you*. You already own the building, the block, and probably my source code. But sure, here's the formality:",
        ROLE_SENATOR: "🟠 Well, well. Half the keys to the kingdom and a suspiciously good haircut. Pulling your file now:",
        ROLE_JUDGE: "🔨 Order in the court! Nice robe. Here's what it actually lets you do:",
        ROLE_STITCH: "🧵 Stitched into the department permanently, I see. Here's what that purple actually gets you:",
        ROLE_MILLIE: "✨ Ah, Millie. Pink badge, real authority, don't test her. Here's what that gets you:",
    }
    intro = next((v for k, v in intro_by_rank.items() if k in role_names), None)
    if intro is None:
        intro = "🕵️ Running a background check on you now... relax, it's just for show. Here's your clearance:"
    intro = await t(intro, interaction.user.id)

    embed = build_abilities_embed(interaction.user, caps, title="📁 Personnel File", description=intro)

    rap_sheet = await build_rap_sheet(interaction.user.id)
    embed.add_field(name="📋 Rap Sheet", value=await t(rap_sheet, interaction.user.id), inline=False)

    help_text = (
        "🌐 React with 🌐 on any message and I'll DM you a private translation into your language.\n"
        "📊 Run `/stats` any time to check your own record and rank — RPS, Rogue RoboCop catches, "
        "Cops & Robbers, all in one place.\n"
        "❓ Slash commands (the `/` ones) show their own description and options right in Discord as you type them — "
        "just start typing `/` to browse what's available to you."
    )
    embed.add_field(name="🌐 Translation & Commands", value=await t(help_text, interaction.user.id), inline=False)

    await interaction.response.send_message(embed=embed, ephemeral=True)


@bot.tree.command(name="request-rank", description="Request a rank in your alliance. Both R4 and R5 need staff or your R5's approval.")
@app_commands.describe(rank="Which rank to request")
@app_commands.choices(rank=[
    app_commands.Choice(name="R4 — Officer (needs approval)", value="R4"),
    app_commands.Choice(name="R5 — Command (needs approval)", value="R5"),
])
async def request_rank(interaction: discord.Interaction, rank: str):
    await interaction.response.defer()
    role_req_channel = discord.utils.get(interaction.guild.channels, name="⚙️-role-requests")
    if role_req_channel and interaction.channel.id != role_req_channel.id:
        await interaction.followup.send(f"📋 Please file this request in {role_req_channel.mention}.", ephemeral=True)
        return

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT alliance_tag FROM users WHERE user_id = ?", (interaction.user.id,))
        row = await cur.fetchone()

    tag = row[0] if row else None
    if not tag:
        await interaction.followup.send(
            "❌ You aren't registered with an alliance yet — run `/register` first, then try this again.",
            ephemeral=True
        )
        await log_event(
            interaction.guild,
            f"⚠️ **RANK REQUEST BLOCKED** — {interaction.user.mention} tried to request **{rank}** but isn't "
            f"registered with an alliance yet. They've been told to run `/register`."
        )
        return

    existing_role = discord.utils.get(interaction.guild.roles, name=f"{tag}-{rank}")
    if existing_role and existing_role in interaction.user.roles:
        await interaction.followup.send(f"✅ You already hold **[{tag}]-{rank}**.", ephemeral=True)
        return

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT request_id FROM rank_requests WHERE user_id = ? AND tag = ? AND rank = ? AND status = 'pending'", (interaction.user.id, tag, rank))
        if await cur.fetchone():
            await interaction.followup.send(f"⏳ You already have a pending {rank} request. Sit tight.", ephemeral=True)
            return

        await cur.execute("INSERT INTO rank_requests (user_id, tag, rank) VALUES (?, ?, ?)", (interaction.user.id, tag, rank))
        request_id = cur.lastrowid
        await conn.commit()

    embed = discord.Embed(
        title=f"⚖️ {rank} COMMAND REQUEST",
        description=f"{interaction.user.mention} is requesting **[{tag}]-{rank}** command.",
        color=discord.Color.gold(),
        timestamp=datetime.now()
    )
    embed.add_field(name="Requester", value=f"{interaction.user.mention} (`{interaction.user.id}`)", inline=False)
    embed.add_field(name="Alliance Tag", value=f"[{tag}]", inline=True)
    embed.add_field(name="Rank Requested", value=rank, inline=True)
    if rank == "R4":
        embed.add_field(name="Who Can Rule", value="Judge+ staff, or this alliance's own R5", inline=False)
    embed.set_footer(text=f"Request ID: {request_id}")

    log_channel = discord.utils.get(interaction.guild.channels, name="logs")
    if log_channel:
        await log_channel.send(embed=embed, view=RankRequestView(request_id, rank))

    await notify_staff_dm(
        interaction.guild, f"⚖️ {rank} COMMAND REQUEST",
        f"{interaction.user.mention} wants **[{tag}]-{rank}** command. Rule on it from #logs.",
        color=discord.Color.gold()
    )

    if rank == "R4":
        r5_role = discord.utils.get(interaction.guild.roles, name=f"{tag}-R5")
        if r5_role:
            for leader in r5_role.members:
                if leader.id == interaction.user.id:
                    continue
                try:
                    await leader.send(
                        f"⚖️ {interaction.user.mention} is requesting **[{tag}]-R4** in your alliance. "
                        f"As R5 you can approve or deny it directly from #logs."
                    )
                except discord.Forbidden:
                    pass

    await interaction.followup.send(
        f"📨 **REQUEST FILED.** Your bid for **[{tag}]-{rank}** command has been forwarded to command staff for review."
    )


async def _resolve_r5_grant_target(interaction: discord.Interaction, member: discord.Member):
    """Shared guard for /grant-leadership and /revoke-leadership — staff
    can act on any alliance, but a plain R5 can only act within their own,
    and only on a member of that same alliance."""
    if is_staff_member(interaction.user):
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT alliance_tag FROM users WHERE user_id = ?", (member.id,))
            row = await cur.fetchone()
        return row[0] if row else None

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT alliance_tag FROM users WHERE user_id = ?", (interaction.user.id,))
        my_row = await cur.fetchone()
    my_tag = my_row[0] if my_row else None
    if not my_tag:
        return None

    r5_role = discord.utils.get(interaction.guild.roles, name=f"{my_tag}-R5")
    if not (r5_role and r5_role in interaction.user.roles):
        return None

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT alliance_tag FROM users WHERE user_id = ?", (member.id,))
        target_row = await cur.fetchone()
    target_tag = target_row[0] if target_row else None
    return my_tag if target_tag == my_tag else None


@bot.tree.command(name="grant-rank", description="Directly assign R4 or R5 to a specific member. Dictator/Senator only.")
@app_commands.describe(member="Who to assign a rank to", tag="Alliance tag (leave blank if there's only one)", rank="R4 or R5")
@app_commands.choices(rank=[
    app_commands.Choice(name="R4", value="R4"),
    app_commands.Choice(name="R5", value="R5"),
])
@app_commands.default_permissions(manage_channels=True)
@is_senior_staff()
async def grant_rank_cmd(interaction: discord.Interaction, member: discord.Member, rank: str, tag: str = None):
    await interaction.response.defer(ephemeral=True)
    tag = normalize_alliance_key(tag) if tag else tag
    if not tag:
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT tag FROM alliances")
            tags = [row[0] for row in await cur.fetchall()]
        if len(tags) == 1:
            tag = tags[0]
        else:
            await interaction.followup.send(
                f"❌ {len(tags)} alliance(s) exist — specify which one with the `tag` option: {', '.join(tags) if tags else '(none registered yet)'}",
                ephemeral=True
            )
            return
    else:
        tag = tag.strip().upper()

    await grant_alliance_rank(interaction.guild, member, tag, rank)
    await interaction.followup.send(f"✅ {member.mention} is now **[{tag}]-{rank}**.", ephemeral=True)
    await log_event(interaction.guild, f"⚖️ **RANK GRANTED DIRECTLY**\nBy: {interaction.user.mention}\nTo: {member.mention}\nRank: [{tag}]-{rank}")


def tag_exists_live(guild, tag: str) -> bool:
    """Checks the live Discord server itself for evidence of this tag — any
    of its roles or its category channels — regardless of whether the
    'alliances' DB table has a matching row. Catches a tag that genuinely
    exists on the server but was never (or is no longer) tracked in the
    database, e.g. from an adoption/migration that didn't fully register
    it — the exact gap that made an earlier tag-rename request fail even
    though the tag was plainly sitting right there on the server."""
    for suffix in ("", "-R4", "-R5", "-Leadership"):
        if discord.utils.get(guild.roles, name=f"{tag}{suffix}"):
            return True
    for suffix in (" CHATS", " Voice Channels"):
        if discord.utils.get(guild.categories, name=f"{tag}{suffix}"):
            return True
    return False


TAG_ROLE_SUFFIXES = ("", "-R4", "-R5", "-Leadership")


def merge_preview(guild, old_tag: str, new_tag: str) -> str:
    """Plain-English 'what will happen' lines for the merge confirmation."""
    def count(tag, suffix):
        r = discord.utils.get(guild.roles, name=f"{tag}{suffix}")
        return len(r.members) if r else 0
    lines = [
        f"• **{count(old_tag, '')}** [{old_tag}] member(s) move onto the [{new_tag}] role "
        f"(which already has **{count(new_tag, '')}**).",
        "• Everyone keeps their rank (R4/R5/Leadership move across to the matching "
        f"[{new_tag}] role), nicknames are rewritten to [{new_tag}], and their database records follow.",
    ]
    old_r5, new_r5 = count(old_tag, "-R5"), count(new_tag, "-R5")
    if old_r5 and new_r5:
        lines.append(
            f"• ⚠️ Both alliances have an R5 ({old_r5} + {new_r5}) — [{new_tag}] will end up with "
            f"{old_r5 + new_r5}. Sort that out afterwards with `/grant-rank`."
        )
    return "\n".join(lines)


async def merge_alliance_into(guild, old_tag: str, new_tag: str, actor) -> dict:
    """Admin-only 'rename onto an existing tag': moves every [old_tag]
    member onto the matching [new_tag] roles (keeping their rank), updates
    their DB records and nicknames, retires the old alliance's DB row,
    and then flags the now-empty [old_tag] roles/channels in #logs for a
    human to Dissolve or Keep — never deletes channels by itself."""
    moved_members = set()
    role_notes = []
    failures = []

    for suffix in TAG_ROLE_SUFFIXES:
        old_role = discord.utils.get(guild.roles, name=f"{old_tag}{suffix}")
        if not old_role:
            continue
        new_role = discord.utils.get(guild.roles, name=f"{new_tag}{suffix}")
        if not new_role and suffix:
            # [new_tag] has no role of this kind yet (e.g. no HAL-R5): the
            # cleanest move is to rename the old one — its holders keep it.
            try:
                await old_role.edit(name=f"{new_tag}{suffix}", reason=f"Tag merge {old_tag} -> {new_tag} by {actor}")
                role_notes.append(f"{old_tag}{suffix} renamed → {new_tag}{suffix}")
                moved_members.update(m.id for m in old_role.members)
                if suffix == "-Leadership":
                    # Give the renamed role access to the NEW alliance's leadership chat.
                    cat = discord.utils.get(guild.categories, name=f"{new_tag} CHATS")
                    lc = discord.utils.get(cat.text_channels, name="🎖️-leadership-chat") if cat else None
                    if lc:
                        await lc.set_permissions(old_role, view_channel=True, send_messages=True)
            except discord.HTTPException as e:
                failures.append(f"couldn't rename role {old_role.name}: {e}")
            continue
        if not new_role:
            # Base tag role missing even though the tag "exists" (category
            # only) — create it rather than leave members tagless.
            try:
                new_role = await ensure_role(guild, new_tag, color=old_role.color, hoist=old_role.hoist)
            except discord.HTTPException as e:
                failures.append(f"couldn't create role {new_tag}: {e}")
                continue
        if suffix == "-Leadership":
            new_role = await ensure_leadership_role(guild, new_tag)
        count = 0
        for member in list(old_role.members):
            try:
                if new_role not in member.roles:
                    await member.add_roles(new_role, reason=f"Tag merge {old_tag} -> {new_tag}")
                await member.remove_roles(old_role, reason=f"Tag merge {old_tag} -> {new_tag}")
                moved_members.add(member.id)
                count += 1
            except discord.HTTPException as e:
                failures.append(f"{member.mention} ({old_role.name}): {e}")
        role_notes.append(f"{old_tag}{suffix} → {new_tag}{suffix}: {count} moved")

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT status FROM alliances WHERE tag = ?", (old_tag,))
        old_row = await cur.fetchone()
        await cur.execute("SELECT status FROM alliances WHERE tag = ?", (new_tag,))
        new_row = await cur.fetchone()
        await cur.execute("SELECT user_id FROM users WHERE alliance_tag = ?", (old_tag,))
        db_member_ids = [r[0] for r in await cur.fetchall()]
        await cur.execute("UPDATE users SET alliance_tag = ? WHERE alliance_tag = ?", (new_tag, old_tag))
        db_updated = cur.rowcount
        await cur.execute("UPDATE rank_requests SET tag = ? WHERE tag = ?", (new_tag, old_tag))
        if not new_row:
            # [new_tag] only existed on the server — register it, inheriting
            # the old alliance's approval status so nobody gets demoted to pending.
            await cur.execute(
                "INSERT OR IGNORE INTO alliances (tag, creator_id, status, created_at) VALUES (?, ?, ?, ?)",
                (new_tag, actor.id, old_row[0] if old_row else "approved", datetime.now().isoformat())
            )
        await cur.execute("DELETE FROM alliances WHERE tag = ?", (old_tag,))
        await conn.commit()

    # Rebuild nicknames from the (now updated) DB for everyone touched.
    for uid in moved_members | set(db_member_ids):
        member = guild.get_member(uid)
        if not member:
            continue
        if member.id == guild.owner_id:
            failures.append(f"{member.mention} (server owner — Discord won't let a bot change the owner's nickname; set it to [{new_tag}] yourself)")
            continue
        if uid in db_member_ids:
            await rebuild_member_nickname(guild, member)  # full rebuild from their DB record
        elif f"[{old_tag}]" in (member.display_name or ""):
            # Held the role but has no users row — nothing to rebuild from,
            # so just swap the tag in their current nickname.
            try:
                await member.edit(nick=member.display_name.replace(f"[{tag_display(old_tag)}]", f"[{tag_display(new_tag)}]")[:32],
                                  reason=f"Tag merge {old_tag} -> {new_tag}")
            except discord.HTTPException as e:
                failures.append(f"{member.mention} (nickname): {e}")

    await refresh_leadership_status(guild, new_tag)
    await enforce_role_hierarchy(guild)

    # Offer cleanup of the leftover old-tag roles/channels — human decides.
    log_channel = discord.utils.get(guild.channels, name="logs")
    if log_channel and old_tag not in await _get_orphan_pending(guild):
        await _set_orphan_pending(guild, old_tag, True)
        try:
            await log_channel.send(
                embed=discord.Embed(
                    title=f"🧹 MERGED ALLIANCE LEFTOVERS — [{old_tag}]",
                    description=(
                        f"{actor.mention} merged **[{old_tag}]** into **[{new_tag}]**. Everyone has moved over; "
                        f"the old [{old_tag}] roles and channels are still here. Dissolve them once you've "
                        f"saved anything worth keeping from the old channels."
                    ),
                    color=discord.Color.orange(),
                    timestamp=datetime.now()
                ),
                view=OrphanAllianceCleanupView(old_tag)
            )
        except discord.HTTPException:
            pass

    return {
        "moved": len(moved_members),
        "db_updated": db_updated,
        "role_notes": role_notes,
        "failures": failures,
        "new_status": new_row[0] if new_row else (old_row[0] if old_row else "approved"),
    }


class ConfirmTagMergeView(discord.ui.View):
    """The admin's 'are you sure?' for renaming onto a tag that already exists."""

    def __init__(self, actor, old_tag: str, new_tag: str):
        super().__init__(timeout=120.0)
        self.actor, self.old_tag, self.new_tag = actor, old_tag, new_tag

    @discord.ui.button(label="Yes, merge them", style=discord.ButtonStyle.danger, emoji="🏷️")
    async def yes(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user != self.actor:
            await interaction.response.send_message("This isn't your panel.", ephemeral=True)
            return
        if not is_dictator_member(interaction.user):
            await interaction.response.send_message("❌ Admins only.", ephemeral=True)
            return
        await interaction.response.defer(ephemeral=True)
        for item in self.children:
            item.disabled = True
        await interaction.edit_original_response(content=f"🚚 Moving the whole **[{self.old_tag}]** crew into **[{self.new_tag}]** HQ… hang tight, this can take a minute on a big alliance.", view=self)
        guild = interaction.guild
        try:
            async with server_busy(f"merging [{self.old_tag}] into [{self.new_tag}]"):
                result = await merge_alliance_into(guild, self.old_tag, self.new_tag, interaction.user)
        except Exception as e:
            ask = await report_error(guild, f"alliance merge [{self.old_tag}] → [{self.new_tag}]", interaction.user, e)
            await interaction.edit_original_response(
                content=(f"❌ The merge hit a snag partway: `{type(e).__name__}`. Running `/rename-tag {self.old_tag} {self.new_tag}` "
                         f"again picks up where it left off.\n\n{ask}"),
                view=self
            )
            return

        general_ch = discord.utils.get(guild.channels, name="💬-general-chat")
        if general_ch:
            try:
                await general_ch.send(embed=discord.Embed(
                    title="🏷️ ALLIANCE RENAMED",
                    description=f"**[{self.old_tag}]** has joined forces with **[{self.new_tag}]**! Same crew, bigger precinct. 🚔 Welcome them in, Chiefs.",
                    color=discord.Color.gold()
                ))
            except discord.HTTPException:
                pass

        fail_text = ""
        if result["failures"]:
            shown = result["failures"][:15]
            fail_text = "\n⚠️ Problems:\n" + "\n".join(f"• {f}" for f in shown)
            if len(result["failures"]) > 15:
                fail_text += f"\n• …and {len(result['failures']) - 15} more"
        status_note = f"\nℹ️ [{self.new_tag}] is still **{result['new_status']}**." if result["new_status"] != "approved" else ""
        await log_event(
            guild,
            f"🏷️ **ALLIANCE MERGED (admin override)**\n[{self.old_tag}] → [{self.new_tag}] (tag already existed)\n"
            f"By: {interaction.user.mention}\nMembers moved: {result['moved']}\nDB records updated: {result['db_updated']}\n"
            f"Roles: {'; '.join(result['role_notes']) or 'none found'}{status_note}{fail_text}"
        )
        await interaction.edit_original_response(
            content=(
                f"✅ **[{self.old_tag}]** merged into **[{self.new_tag}]** — {result['moved']} member(s) moved, "
                f"{result['db_updated']} record(s) updated, nicknames rewritten. "
                f"A cleanup offer for the old [{self.old_tag}] channels is waiting in #logs."
                + (f"\n⚠️ {len(result['failures'])} problem(s) — see #logs." if result["failures"] else "")
            ),
            view=self
        )

    @discord.ui.button(label="Cancel", style=discord.ButtonStyle.secondary)
    async def no(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user != self.actor:
            await interaction.response.send_message("This isn't your panel.", ephemeral=True)
            return
        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(content="👍 Stood down. Nothing touched — both alliances live to fight another day.", view=self)


@bot.tree.command(name="rename-tag", description="Rename an alliance's tag — updates its roles, channels, and every member's record.")
@app_commands.describe(old_tag="The alliance's current tag", new_tag="The new tag (2-4 letters)")
async def rename_tag(interaction: discord.Interaction, old_tag: str, new_tag: str):
    """Open to everyone by decorator (no clean way to gate a slash command on
    'R5 of whichever tag you typed in a parameter' ahead of time), but the
    actual rename only proceeds for staff or that specific alliance's own
    R5 — checked below, same self-governance pattern as R4 approval."""
    if not interaction.guild:
        await interaction.response.send_message("🚔 This only works inside the server itself, not in a DM.", ephemeral=True)
        return
    await interaction.response.defer(ephemeral=True)
    guild = interaction.guild
    old_tag = normalize_alliance_key(old_tag)
    new_tag = new_tag.strip().upper()

    if not (2 <= len(new_tag) <= 4 and new_tag.isalpha()):
        await interaction.followup.send("❌ The new tag needs to be 2–4 letters, nothing else.", ephemeral=True)
        return
    if new_tag == old_tag:
        await interaction.followup.send("ℹ️ That's already the current tag — nothing to change.", ephemeral=True)
        return

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("SELECT tag FROM alliances WHERE tag = ?", (old_tag,))
        exists_in_db = bool(await cur.fetchone())
        await cur.execute("SELECT tag FROM alliances WHERE tag = ?", (new_tag,))
        collision_in_db = bool(await cur.fetchone())

    # Check the database AND the live server itself (roles/categories) —
    # a tag can be real (roles, channels, an active R5) without ever having
    # gotten a database row, so a DB-only check would wrongly refuse it.
    exists_live = tag_exists_live(guild, old_tag)
    if not exists_in_db and not exists_live:
        await interaction.followup.send(
            f"❌ No alliance found with tag **[{old_tag}]** — checked both the database and the server's "
            f"actual roles/channels, nothing turned up either way.",
            ephemeral=True
        )
        return

    # Permission check BEFORE the collision check, so someone with no right
    # to rename this alliance at all never gets told about merge options.
    r5_role = discord.utils.get(guild.roles, name=f"{old_tag}-R5")
    is_own_r5 = bool(r5_role and isinstance(interaction.user, discord.Member) and r5_role in interaction.user.roles)
    if not (is_staff_member(interaction.user) or is_own_r5):
        await interaction.followup.send(
            f"❌ Only **[{old_tag}]**'s own R5, or staff, can rename this alliance.", ephemeral=True
        )
        return

    collision_live = tag_exists_live(guild, new_tag)
    if collision_in_db or collision_live:
        # Renaming onto a tag that already exists = merging two alliances.
        # Allowed, but only for an admin (Dictator or true Discord
        # Administrator), and only after an explicit "are you sure?".
        # Everyone else who could normally rename gets pointed to an admin.
        if not is_dictator_member(interaction.user):
            await interaction.followup.send(
                f"🛑 Whoa there, Chief — **[{new_tag}]** already exists, so renaming **[{old_tag}]** to it would *merge* "
                f"two whole alliances. That's above my pay grade *and* yours. 😅\n"
                f"Ask an admin to run `/rename-tag {old_tag} {new_tag}` — they get the big red button.",
                ephemeral=True
            )
            await log_event(
                guild,
                f"🏷️ **RENAME BLOCKED — TAG ALREADY EXISTS**\n{interaction.user.mention} tried [{old_tag}] → [{new_tag}], "
                f"but [{new_tag}] already exists. Told them to ask an admin."
            )
            return
        summary = merge_preview(guild, old_tag, new_tag)
        await interaction.followup.send(
            f"⚠️ **[{new_tag}] already exists.** Are you *sure* sure, Chief?\n\n"
            f"Renaming **[{old_tag}]** → **[{new_tag}]** will **merge** them:\n{summary}\n\n"
            f"The leftover **[{old_tag}]** roles and channels are NOT deleted automatically — a 🧹 Dissolve / Keep "
            f"offer goes to #logs afterwards, same as any empty alliance.",
            view=ConfirmTagMergeView(interaction.user, old_tag, new_tag),
            ephemeral=True
        )
        return

    renamed_roles = []
    for suffix in ("", "-R4", "-R5", "-Leadership"):
        role = discord.utils.get(guild.roles, name=f"{old_tag}{suffix}")
        if role:
            try:
                await role.edit(name=f"{new_tag}{suffix}")
                renamed_roles.append(f"{old_tag}{suffix} → {new_tag}{suffix}")
            except discord.HTTPException:
                pass

    for suffix in (" CHATS", " Voice Channels"):
        cat = discord.utils.get(guild.categories, name=f"{old_tag}{suffix}")
        if cat:
            try:
                await cat.edit(name=f"{new_tag}{suffix}")
            except discord.HTTPException:
                pass

    async with db_connect() as conn:
        cur = await conn.cursor()
        await cur.execute("UPDATE alliances SET tag = ? WHERE tag = ?", (new_tag, old_tag))
        if not exists_in_db:
            # The tag was only ever real on the live server (roles/channels),
            # never registered in the DB — back-fill a row now under its new
            # name so it's properly tracked from here on out, instead of
            # staying invisible to the database forever.
            await cur.execute(
                "INSERT OR IGNORE INTO alliances (tag, creator_id, status, created_at) VALUES (?, ?, 'approved', ?)",
                (new_tag, interaction.user.id, datetime.now().isoformat())
            )
        await cur.execute("UPDATE users SET alliance_tag = ? WHERE alliance_tag = ?", (new_tag, old_tag))
        member_count = cur.rowcount
        await cur.execute("UPDATE rank_requests SET tag = ? WHERE tag = ?", (new_tag, old_tag))
        await conn.commit()

    general_ch = discord.utils.get(guild.channels, name="💬-general-chat")
    if general_ch:
        try:
            await general_ch.send(embed=discord.Embed(
                title="🏷️ ALLIANCE RENAMED",
                description=f"**[{old_tag}]** is now known as **[{new_tag}]**. Same alliance, new banner — {member_count} member record(s) updated.",
                color=discord.Color.gold()
            ))
        except discord.HTTPException:
            pass

    await log_event(
        guild,
        f"🏷️ **ALLIANCE RENAMED**\n[{old_tag}] → [{new_tag}]\nBy: {interaction.user.mention}\n"
        f"Roles renamed: {', '.join(renamed_roles) if renamed_roles else 'none found'}\nMembers updated: {member_count}"
    )
    db_note = "" if exists_in_db else " (this tag wasn't in the database before — it's now registered under its new name.)"
    await interaction.followup.send(
        f"✅ **[{old_tag}]** renamed to **[{new_tag}]** — {len(renamed_roles)} role(s), channels, and "
        f"{member_count} member record(s) updated.{db_note}",
        ephemeral=True
    )


@bot.tree.command(name="grant-rank-picker", description="Click a username from a live server search and assign R4/R5 on the spot.")
@app_commands.describe(tag="Alliance tag (leave blank if there's only one)")
@app_commands.default_permissions(manage_channels=True)
@is_senior_staff()
async def grant_rank_picker_cmd(interaction: discord.Interaction, tag: str = None):
    tag = normalize_alliance_key(tag) if tag else tag
    if not tag:
        async with db_connect() as conn:
            cur = await conn.cursor()
            await cur.execute("SELECT tag FROM alliances")
            tags = [row[0] for row in await cur.fetchall()]
        if len(tags) == 1:
            tag = tags[0]
        else:
            await interaction.response.send_message(
                f"❌ {len(tags)} alliance(s) exist — specify which one with the `tag` option: {', '.join(tags) if tags else '(none registered yet)'}",
                ephemeral=True
            )
            return
    else:
        tag = tag.strip().upper()

    await interaction.response.send_message(
        f"Pick anyone from the server below to assign **[{tag}]-R4** or **[{tag}]-R5** — or just leave it alone.",
        view=GrantRankPickerView(tag),
        ephemeral=True
    )



@bot.tree.command(name="grant-leadership", description="R5-only: quietly trust someone with leadership-chat access, no formal rank needed.")
@app_commands.describe(member="Who to grant leadership-chat access to")
async def grant_leadership_cmd(interaction: discord.Interaction, member: discord.Member):
    if not interaction.guild:
        await interaction.response.send_message("🚔 This only works inside the server itself, not in a DM.", ephemeral=True)
        return
    tag = await _resolve_r5_grant_target(interaction, member)
    if not tag:
        await interaction.response.send_message("❌ You can only grant this within your own alliance, and only to a member of that alliance.", ephemeral=True)
        return

    role = discord.utils.get(interaction.guild.roles, name=f"{tag}-Leadership")
    if role and role in member.roles:
        await interaction.response.send_message(f"✅ {member.mention} already has leadership access in [{tag}].", ephemeral=True)
        return

    await grant_leadership(interaction.guild, member, tag)
    await interaction.response.send_message(f"🔑 Granted {member.mention} leadership-chat access in [{tag}].", ephemeral=True)
    await log_event(interaction.guild, f"🔑 **LEADERSHIP GRANTED**\nBy: {interaction.user.mention}\nTo: {member.mention}\nAlliance: [{tag}]")
    try:
        await member.send(f"🔑 {interaction.user.mention} has given you leadership-chat access in [{tag}]. Welcome in.")
    except discord.Forbidden:
        pass


@bot.tree.command(name="revoke-leadership", description="R5-only: remove someone's standalone leadership-chat access.")
@app_commands.describe(member="Who to remove leadership-chat access from")
async def revoke_leadership_cmd(interaction: discord.Interaction, member: discord.Member):
    if not interaction.guild:
        await interaction.response.send_message("🚔 This only works inside the server itself, not in a DM.", ephemeral=True)
        return
    tag = await _resolve_r5_grant_target(interaction, member)
    if not tag:
        await interaction.response.send_message("❌ You can only revoke this within your own alliance, and only from a member of that alliance.", ephemeral=True)
        return

    r4_role = discord.utils.get(interaction.guild.roles, name=f"{tag}-R4")
    r5_role = discord.utils.get(interaction.guild.roles, name=f"{tag}-R5")
    if (r4_role and r4_role in member.roles) or (r5_role and r5_role in member.roles):
        await interaction.response.send_message(
            f"❌ {member.mention} currently holds R4 or R5, which always carries leadership access. "
            f"Change their rank first if you want to remove access — revoking leadership alone while they're "
            f"still ranked would just leave them stuck unable to see their own alliance's channel.",
            ephemeral=True
        )
        return

    removed = await revoke_leadership(interaction.guild, member, tag)
    if removed:
        await interaction.response.send_message(f"🔒 Removed {member.mention}'s leadership-chat access in [{tag}].", ephemeral=True)
        await log_event(interaction.guild, f"🔒 **LEADERSHIP REVOKED**\nBy: {interaction.user.mention}\nFrom: {member.mention}\nAlliance: [{tag}]")
    else:
        await interaction.response.send_message(f"ℹ️ {member.mention} doesn't currently have leadership access to remove.", ephemeral=True)


@bot.tree.error
async def on_app_command_error(interaction: discord.Interaction, error: app_commands.AppCommandError):
    if isinstance(error, ServerBusy):
        try:
            if interaction.response.is_done():
                await interaction.followup.send(error.message, ephemeral=True)
            else:
                await interaction.response.send_message(error.message, ephemeral=True)
        except discord.HTTPException:
            pass
        return
    if isinstance(error, (app_commands.MissingPermissions, app_commands.CheckFailure)):
        msg = "🚫 You don't hold sufficient rank for that command, Chief."
    else:
        print(f"[COMMAND ERROR] {error}")
        msg = random.choice(CLIENT_ERROR_FLAVOR)

        # #logs + owner DM + the right "who to ask" line for this person.
        cmd_name = interaction.command.qualified_name if interaction.command else "(unknown command)"
        original = getattr(error, "original", error)  # unwrap CommandInvokeError to the real cause
        msg += "\n\n" + await report_error(interaction.guild, f"command `/{cmd_name}`", interaction.user, original)

        # A little something extra, only for the people who've actually
        # earned it — silence for everyone else, no mention either way.
        if interaction.guild and isinstance(interaction.user, discord.Member):
            innovator_role = discord.utils.get(interaction.guild.roles, name=ROLE_INNOVATOR)
            if innovator_role and innovator_role in interaction.user.roles:
                msg += (
                    "\n\n🌟 And hey — this is exactly why you've got that Innovator badge. Catching things like "
                    "this is precisely what it's for. You're appreciated more than just about anyone else in "
                    "this server right now, Chief."
                )


    try:
        if interaction.response.is_done():
            await interaction.followup.send(msg, ephemeral=True)
        else:
            await interaction.response.send_message(msg, ephemeral=True)
    except discord.HTTPException:
        pass


@bot.tree.command(name="robocop", description="Robocop master command directory.")
@app_commands.default_permissions(kick_members=True)
@is_staff()
async def robocop_help(interaction: discord.Interaction, query: str = None):
    help_text = (
        "🤖 **ROBOCOP ADMINISTRATIVE COMMAND DIRECTORY** 🤖\n\n"
        "🚨 **ADOPTING AN EXISTING (NON-FRESH) SERVER? START HERE.** 🚨\n"
        "The startup diagnostic in **#logs** carries buttons for exactly this — no typing required, "
        "which matters since a mistyped slash command silently does nothing. In order:\n"
        "1️⃣ **🚔 Convert Everyone + Migrate Ranks (PTD/21)** — registers everyone, fixes nicknames, AND maps "
        "old R2-R5/Admin roles into the new system, all in one click\n"
        "2️⃣ Hand-assign any special identities (Chrome, Silent, etc.) — deliberately manual, always\n"
        "3️⃣ `/announce-update` — tells everyone, once you're happy with how it looks\n"
        "Don't see those buttons? They repost at every startup until resolved — just restart the bot. "
        "Prefer typed commands instead? `/ptd-upgrade-now` and `/ptd-reset` do the same first two steps — "
        "but a command that silently fails to register as an actual interaction looks identical to nothing "
        "happening at all, so the buttons are the safer bet.\n\n"
        "**Rank Structure**\n"
        "• 👑 **DICTATOR** — the owner. Full Administrator, no restrictions, always.\n"
        "• 🟠 **SENATOR** — everything a Judge can do, plus creating/deleting channels.\n"
        "• 🔨 **JUDGE** — moderator: kick, ban, timeout, imprison, nicknames, voice-move, audit log. No channel/role/server management.\n\n"
        "**Dictator-Only**\n"
        "• `/database-tools` — posts a #logs panel to release current prisoners or permanently reset the users database (with a confirmation step).\n"
        "• `/restore-innovators` — Re-grants the Innovator badge to everyone recorded in the database, in case roles ever got reset.\n"
        "• `/grant-innovator-all` — One-time bulk grant for a server adoption/transition: everyone currently present, bypassing the usual caps.\n"
        "• `/adopt-alliance <tag>` — Adopt an existing, already-populated server's channels/roles into our structure, one confirmed step at a time.\n"
        "• `/migrate-legacy-roles` — Scan for old rank/admin roles from before this bot and map them into the new system, one at a time.\n"
        "• `/bulk-onboard-existing <tag> <servers>` — Register everyone already in the server, assuming one known alliance. For adopting a single-alliance server only.\n"
        "• `/ptd-upgrade-now` — One-shot typed version of the adoption button above, specific to this server (PTD, server 21).\n"
        "• `/ptd-reset` — Clears PTD's alliance registration for a clean retry, without touching channels/roles/people.\n"
        "• `/announce-update` — Manually fire the 'system update in progress' announcement + brief lockdown, without waiting for a detected live handoff.\n\n"
        "**Moderation** *(Judge and above)*\n"
        "• `/approve-tag <tag>` — Unlocks quarantined alliance & removes Drunk Tank.\n"
        "• `/warn <member> <reason>` — Issues a formal warning (DMs the member, logs it).\n"
        "• `/warnings <member>` — Lists a member's warning history.\n"
        "• `/imprison <nickname> <minutes>` — Locks user in solitary (strips overriding roles).\n"
        "• `/unban <user_id>` — Lifts Discord ban and resets database infractions.\n"
        "• `/pardon <user_id>` — Clears active timeouts, resets fails, and releases prisoners.\n"
        "• `/show-banned` — Displays all permanently banned users & infraction logs.\n"
        "• `/re-check-nicknames` — Compares nicknames against actual current roles and offers one-click fixes for each mismatch, in #logs.\n"
        "• `/enforce-registration <member>` — Flags an existing member for mandatory registration right now, instead of waiting for them to run /register.\n"
        "• `/killswitch [minutes] [off]` — Emergency lockdown pausing chat.\n"
        "• Every ban/kick/imprison posted to #logs carries an **Undo** button — no need to remember commands.\n\n"
        "**Alliances & Server Setup** *(Senator and above)*\n"
        "• `/stop-alliance <lock>` — Master kill switch freezing all new alliance creation.\n"
        "• `/release-timekeeper` — Opens 10-minute burst window.\n"
        "• `/add-request-role <role> <description>` — Adds custom role option to database.\n"
        "• `/configure-servers <list>` — Sets which Police Chief servers this community supports (e.g. `21,121` or `10-15`). Live, no restart needed.\n"
        "• `/toggle-innovator-program` — Turns future automatic Innovator badge grants on or off.\n"
        "• `/toggle-rogue-bot-program` — Turns the automatic Rogue RoboCop round on or off, useful to suppress during a migration.\n"
        "• `/set-monthly-prize [prize]` — Sets what next month's #1 Monthly Champion (Gold) wins. Leave blank to reset to the default (bragging rights).\n"
        "• `/dissolve-alliance <tag>` — Removes an alliance entirely: roles, both categories and their channels, DB rows. For typo-alliances. Confirms first; also offered as a one-click button in #logs whenever an alliance empties out.\n\n"
        "**Data / Audit** *(Judge and above)*\n"
        "• `/show-role <role>` — Ephemeral admin audit listing members for a target role.\n"
        "• `/show-db-fields <member>` — Lists all fields and values for a specific user.\n"
        "• `/show-field <field>` — Lists all users sorted by a specific database field.\n"
        "• `/server-stats` — Translations served, referral counts, RPS win/loss records, and more.\n"
        "• `/start-chase` / `/end-chase` — Manually trigger or cut short a Cops & Robbers round (auto-runs daily at noon PST).\n"
        "• `/game-start`, `/game-end`, `/game-restart` — Unified control for BOTH round games (Cops & Robbers, Rogue RoboCop): "
        "start now or in N minutes, end now or pause-and-auto-resume in N minutes, or restart. Either game also auto-ends "
        f"itself if nobody makes a real move for {GAME_INACTIVITY_TIMEOUT_SECONDS // 60} minutes straight.\n"
        "• `/rename-tag <old> <new>` — Rename any alliance's tag; updates its roles, channels, and every member's record. "
        "(An alliance's own R5 can also do this for their own tag, no staff needed. Renaming onto a tag that already exists merges the two — admin only, with an are-you-sure step.)\n"
        "• `/monthly-champions-now` — Manually fire the Monthly Champion announcement (gold/silver/bronze) and reset standings, without waiting for the 1st.\n\n"
        "**Open to everyone**\n"
        "• `/language` — Change which language I use when talking to you, any time after onboarding too.\n"
        "• `/timezone` — Set or change your approximate time zone, so I can tell you how the server's schedule lines up with yours.\n"
        "• `/nickname` — If your in-game name differs across servers you play on, manage per-server nicknames and switch your active display name any time.\n"
        "• `/change-nick` — One-step name update: asks whether it's an actual in-game name change or just a typo, then updates only the base name, leaving `[TAG] (servers)` untouched.\n"
        "• `/fix-me` — Self-service correction panel: wrong name / wrong tag / wrong server, each a button, plus 'get me a human'. Switching tag moves them to an existing alliance (never founds one) and flags the old one in #logs if it's now empty.\n"
        "• `/announce <message>` — Scope depends on rank: members reach the current channel (1/hr), an alliance's R5 reaches all of that alliance's channels (1/30min), staff reach the whole server (no limit).\n"
        "• `/register` (in #gateway) — For members who were already in the server before I was added, or never finished onboarding.\n"
        "• `/abilities` — cheeky, verbose rundown of exactly what YOU can do right now (also in #❓-abilities).\n"
        "• `/request-rank` (used in #⚙️-role-requests) — Requests R4/R5 in your alliance. Staff or your R5 rule on it from #logs.\n"
        "• `/grant-leadership` / `/revoke-leadership` (R5-only) — Directly trust someone with leadership-chat access, no formal rank or approval needed.\n"
        "• `/rps [opponent]` — Rock, Paper, Scissors vs another Chief or Robocop.\n"
        "• `/alliance-leaderboard` — Ranks alliances by member count.\n"
        "• `/arrest <name>` / `/ambush <name>` — Cops & Robbers moves, only usable if you're actually in the current round.\n"
        "• `/chase-status`, `/leave-chase`, `/join-chase` — Check your status, or opt in/out of future rounds.\n"
        "• `/catch <name>` — Guess a hiding Rogue RoboCop's secret identity (triggered by version updates, not scheduled).\n"
        "• `/game-stats` — Running server-wide totals for RPS, Cops & Robbers, and Rogue RoboCop. Also auto-posts to "
        "#general-chat once a day (default midnight local time, adjustable via `/configure-setting game_stats_hour`).\n"
        "• `/monthly-standings` — Live gold/silver/bronze race for the current month, on demand, without resetting anything.\n\n"
        "**Housekeeping**\n"
        "• ✨ There is exactly one **Millie** in this server, always exactly this pink, and she carries full JUDGE-level moderator permissions.\n"
        "• 🧵 There is exactly one **Stitch**, always exactly this purple, and they carry full JUDGE-level moderator permissions.\n"
        "• Every startup and every time I rejoin this server, I post a diagnostic to #logs — and if something's actually wrong "
        "(not just different from default), you'll know because sirens.\n"
        "• I also audit the whole member list on startup — anyone not registered gets a one-time DM pointing them at `/register`. Anyone who *joined while I was offline* (last 3 days, never started registering) gets the full #gateway onboarding started for them automatically instead.\n"
        "• 🚪 **#visitors** logs every join and leave, including why someone left when I can tell (kicked, banned, or just left on their own).\n"
        "• 🆕 **#latest-version** only posts when a startup after an update finds something inconsistent — quiet otherwise.\n"
        f"• 🗑️ A Cops & Robbers or Rogue RoboCop round with zero real engagement for {GAME_INACTIVITY_TIMEOUT_SECONDS // 60} straight "
        "minutes auto-voids: the announcement gets deleted, nobody's stats move, and it won't recount toward `/game-stats`. It also "
        "won't force an early restart — the next automatic round still waits for its normal scheduled time.\n"
        "• 🗂️ **Every startup I inventory the live server** — alliance roles/categories, members' tag/server/rank roles, nicknames, Innovator badges — and rebuild any database record that's missing from it. Wipe the database and it regenerates itself on the next boot; nobody re-registers. Then I check every alliance member's nickname against their roles and fix mismatches on the spot. Both passes log everything to #logs.\n"
        "• 🆘 Anyone who types `help` at any #gateway prompt gets staff pinged (once) and is never penalized for it. Three unusable tag or server answers now **park them and call a human** instead of banning.\n"
        "• 📅 On the 1st of every month, I announce the **Monthly Champion** — gold/silver/bronze, scored the same way "
        "`/leaderboard` already scores everything, just measured from the start of the month instead of all-time. Gold wins "
        "whatever `/set-monthly-prize` is currently set to (default: bragging rights); standings reset right after the announcement.\n"
        "• 🔄 When a new version of me takes over from an old one, I announce it in every community channel and pause chat for "
        f"{VERSION_HANDOFF_LOCKDOWN_SECONDS} seconds during the handoff, then reopen automatically.\n"
        "• 🚨 Genuinely serious findings (security dangers, an onboarding crash) also go straight to the server owner's DMs, not just #logs."
    )
    await interaction.response.send_message(help_text, ephemeral=True)


# ============================================================
#  OPTIONAL PERSONAL EXTRAS — personal_extras.py, if present beside this
#  file, is loaded here. It's the owner's own add-on, deliberately kept out
#  of the published code (.gitignore). Without it, the hook below is a no-op
#  and RoboCop behaves identically.
# ============================================================
async def _personal_on_login(before, after):
    return


_PERSONAL_EXTRAS_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "personal_extras.py")
if os.path.exists(_PERSONAL_EXTRAS_PATH):
    try:
        with open(_PERSONAL_EXTRAS_PATH, encoding="utf-8") as _pf:
            exec(compile(_pf.read(), _PERSONAL_EXTRAS_PATH, "exec"), globals())
        print("[SYSTEM] 🧩 Personal extras loaded.")
    except Exception as _pe:
        print(f"[WARNING] personal_extras.py failed to load ({type(_pe).__name__}: {_pe}) — carrying on without it.")


if __name__ == "__main__":
    if not DISCORD_TOKEN:
        print("[CRITICAL] DISCORD_TOKEN is missing from .env file!")
    else:
        bot.run(DISCORD_TOKEN)
