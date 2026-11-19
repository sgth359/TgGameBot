import asyncio
import functools
import html
import json
import logging
import os
import random
import re
import time
import urllib.parse
from collections import deque
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo

import asyncpg
import httpx
from aiohttp import web
from telegram import ChatPermissions, ForceReply, InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ChatMemberStatus, ChatType, ParseMode
from telegram.error import BadRequest
from telegram.ext import (
    Application,
    ApplicationHandlerStop,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(name)s: %(message)s")
log = logging.getLogger("games-bot")

TOKEN = os.environ["BOT_TOKEN"]
PORT = int(os.environ.get("PORT", "10000"))
SELF_URL = os.environ.get("RENDER_EXTERNAL_URL") or os.environ.get("SELF_URL")
DATABASE_URL = os.environ.get("DATABASE_URL")  # строка подключения Neon
DATA_FILE = os.environ.get("DATA_FILE", "data.json")  # запасной вариант без базы
ADMIN_IDS = {int(x) for x in os.environ.get("ADMIN_IDS", "").split(",") if x.strip().isdigit()}

BINGO_MIN, BINGO_MAX, BINGO_COUNT = 1, 100, 5
MAX_STRIKES = 3
PING_INTERVAL = 600  # секунд
TRIGGER_COOLDOWN = float(os.environ.get("TRIGGER_COOLDOWN", "10"))  # пауза между срабатываниями одного триггера в чате, сек

WARN_LIMIT = int(os.environ.get("WARN_LIMIT", "3"))  # предупреждений до автомута (по умолчанию; меняется в /settings)
WARN_MUTE_HOURS = int(os.environ.get("WARN_MUTE_HOURS", "24"))  # длительность автомута, часы (по умолчанию)
DEFAULT_MUTE_SECONDS = int(os.environ.get("DEFAULT_MUTE_MINUTES", "60")) * 60  # /mute без времени
DEFAULT_TZ = os.environ.get("DEFAULT_TZ", "Europe/Moscow")  # часовой пояс ночного режима по умолчанию
NOTICE_SECONDS = 15  # через сколько секунд удаляются предупреждения бота

# ---------------------------------------------------------------- состояние

# разрешённые чаты: chat_id -> название (кэш, источник правды — база)
allowed_chats: dict[int, str] = {}
# постоянные топы (/top): ключ игрока -> подпись
perm_tops: dict[str, str] = {}
# должники: номер долга -> {"key", "label", "title"}
debts: dict[int, dict] = {}
# чёрный список: ключ игрока -> {"label", "reason"}
blacklist: dict[str, dict] = {}
# триггеры: номер -> {"phrase", "kind", "file_id", "text", "src_chat", "src_msg"}
triggers: dict[int, dict] = {}
trigger_last: dict[tuple[int, int], float] = {}
# триггеры, ожидающие выбора «от лица бота / пересланное»: номер -> данные
pending_triggers: dict[int, dict] = {}
trigger_seq = 0
# --- защитник
# кому разрешены ссылки: chat_id -> {ключ игрока: подпись}
link_allow: dict[int, dict[str, str]] = {}
# стоп-слова: chat_id -> [слова в нижнем регистре]
stopwords: dict[int, list[str]] = {}
# настройки чата (меняются в /settings): chat_id -> {имя: значение}
chat_settings: dict[int, dict] = {}
DEFAULT_SETTINGS = {
    "antilink": True,
    "night": False,
    "night_start": "00:00",
    "night_end": "08:00",
    "tz": DEFAULT_TZ,
    "night_locked": False,  # чат сейчас закрыт ночным режимом
    "night_perms": None,  # права чата до закрытия (чтобы вернуть как было)
    "warn_limit": WARN_LIMIT,
    "warn_mute_h": WARN_MUTE_HOURS,
    "nickwatch": True,  # сообщать в чат о смене ника
}
# предупреждения: (chat_id, user_id) -> количество
warns: dict[tuple[int, int], int] = {}
# username (в нижнем регистре) -> user_id: нужно, чтобы работали /ban @юзер и т. п.
seen_users: dict[str, int] = {}
# как человека зовут сейчас и раньше: user_id -> {"username", "name", "hist": [строки]}
known_names: dict[int, dict] = {}
# смена ника, о которой ещё не сообщили в некоторых чатах: user_id -> {"old", "new", "chats"}
name_pending: dict[int, dict] = {}
admin_cache: dict[tuple[int, int], tuple[float, bool]] = {}
# ждём ответ от админа в личке (своё время ночи, часовой пояс, новое стоп-слово)
dm_input: dict[int, dict] = {}
night_retry_at: dict[int, float] = {}
_bg_tasks: set = set()
# chat_id -> состояние игры
games: dict[int, dict] = {}
# (chat_id, user_id): человек нажал «Записаться» и сейчас должен прислать числа в чат
pending: set[tuple[int, int]] = set()


# ---------------------------------------------------------------- хранилище (Neon / Postgres)

pool = None


def clean_dsn(url: str) -> str:
    """Neon даёт строку с параметрами, которые asyncpg не понимает, — убираем их."""
    parts = urllib.parse.urlsplit(url)
    q = [
        (k, v)
        for k, v in urllib.parse.parse_qsl(parts.query)
        if k not in ("channel_binding", "options")
    ]
    if not any(k == "sslmode" for k, _ in q):
        q.append(("sslmode", "require"))
    return urllib.parse.urlunsplit(parts._replace(query=urllib.parse.urlencode(q)))


def load_file():
    try:
        with open(DATA_FILE, encoding="utf-8") as f:
            d = json.load(f)
        allowed_chats.update({int(k): v for k, v in d.get("chats", {}).items()})
        perm_tops.update(d.get("tops", {}))
        debts.update({int(k): v for k, v in d.get("debts", {}).items()})
        blacklist.update(d.get("black", {}))
        for k, v in d.get("triggers", {}).items():
            triggers[int(k)] = make_trigger(
                v["phrase"], v["kind"], v.get("file_id"), v.get("text"), v.get("src_chat"), v.get("src_msg")
            )
        for c, m in d.get("link_allow", {}).items():
            link_allow[int(c)] = dict(m)
        for c, w in d.get("stopwords", {}).items():
            stopwords[int(c)] = list(w)
        for c, st in d.get("chat_settings", {}).items():
            chat_settings[int(c)] = dict(st)
        for k, n in d.get("warns", {}).items():
            c, u = k.split(":")
            warns[(int(c), int(u))] = n
        for k, v in d.get("names", {}).items():
            known_names[int(k)] = v
    except FileNotFoundError:
        pass
    except Exception as e:
        log.warning("не удалось прочитать %s: %s", DATA_FILE, e)


def save_file():
    try:
        with open(DATA_FILE, "w", encoding="utf-8") as f:
            json.dump(
                {
                    "chats": {str(k): v for k, v in allowed_chats.items()},
                    "tops": perm_tops,
                    "debts": {str(k): v for k, v in debts.items()},
                    "black": blacklist,
                    "triggers": {
                        str(k): dict(t) for k, t in triggers.items()
                    },
                    "link_allow": {str(c): m for c, m in link_allow.items()},
                    "stopwords": {str(c): w for c, w in stopwords.items()},
                    "chat_settings": {str(c): st for c, st in chat_settings.items()},
                    "warns": {f"{c}:{u}": n for (c, u), n in warns.items()},
                    "names": {str(k): v for k, v in known_names.items()},
                },
                f,
                ensure_ascii=False,
            )
    except Exception as e:
        log.warning("не удалось сохранить %s: %s", DATA_FILE, e)


async def init_storage():
    global pool
    if DATABASE_URL:
        pool = await asyncpg.create_pool(
            clean_dsn(DATABASE_URL),
            min_size=1,
            max_size=3,
            statement_cache_size=0,  # нужно для pooled-подключения Neon (pgbouncer)
            max_inactive_connection_lifetime=120,
            command_timeout=30,
        )
        async with pool.acquire() as c:
            await c.execute(
                "CREATE TABLE IF NOT EXISTS chats ("
                " chat_id BIGINT PRIMARY KEY, title TEXT NOT NULL DEFAULT '');"
                "CREATE TABLE IF NOT EXISTS tops ("
                " user_key TEXT PRIMARY KEY, label TEXT NOT NULL DEFAULT '');"
                "CREATE TABLE IF NOT EXISTS debts ("
                " id BIGSERIAL PRIMARY KEY, user_key TEXT NOT NULL, label TEXT NOT NULL DEFAULT '',"
                " title TEXT NOT NULL, created_at TIMESTAMPTZ NOT NULL DEFAULT now());"
                "CREATE TABLE IF NOT EXISTS blacklist ("
                " user_key TEXT PRIMARY KEY, label TEXT NOT NULL DEFAULT '',"
                " reason TEXT NOT NULL DEFAULT '');"
                "CREATE TABLE IF NOT EXISTS triggers ("
                " id BIGSERIAL PRIMARY KEY, phrase TEXT NOT NULL UNIQUE, kind TEXT NOT NULL,"
                " file_id TEXT, content TEXT);"
                "ALTER TABLE triggers ADD COLUMN IF NOT EXISTS src_chat BIGINT;"
                "ALTER TABLE triggers ADD COLUMN IF NOT EXISTS src_msg BIGINT;"
                "ALTER TABLE debts ADD COLUMN IF NOT EXISTS user_id BIGINT;"
                "ALTER TABLE blacklist ADD COLUMN IF NOT EXISTS user_id BIGINT;"
                "CREATE TABLE IF NOT EXISTS link_allow (chat_id BIGINT NOT NULL, user_key TEXT NOT NULL,"
                " label TEXT NOT NULL DEFAULT '', PRIMARY KEY (chat_id, user_key));"
                "CREATE TABLE IF NOT EXISTS stopwords (chat_id BIGINT NOT NULL, word TEXT NOT NULL,"
                " PRIMARY KEY (chat_id, word));"
                "CREATE TABLE IF NOT EXISTS chat_cfg (chat_id BIGINT PRIMARY KEY, data TEXT NOT NULL);"
                "CREATE TABLE IF NOT EXISTS warns (chat_id BIGINT NOT NULL, user_id BIGINT NOT NULL,"
                " cnt INT NOT NULL, PRIMARY KEY (chat_id, user_id));"
                "CREATE TABLE IF NOT EXISTS seen_users (username TEXT PRIMARY KEY, user_id BIGINT NOT NULL);"
                "CREATE TABLE IF NOT EXISTS user_names (user_id BIGINT PRIMARY KEY, username TEXT,"
                " name TEXT NOT NULL DEFAULT '', hist TEXT NOT NULL DEFAULT '[]')"
            )
            for r in await c.fetch("SELECT chat_id, title FROM chats"):
                allowed_chats[r["chat_id"]] = r["title"]
            for r in await c.fetch("SELECT user_key, label FROM tops"):
                perm_tops[r["user_key"]] = r["label"]
            for r in await c.fetch("SELECT id, user_key, label, title, user_id FROM debts ORDER BY id"):
                debts[r["id"]] = {
                    "key": r["user_key"], "label": r["label"], "title": r["title"], "uid": r["user_id"],
                }
            for r in await c.fetch("SELECT user_key, label, reason, user_id FROM blacklist"):
                blacklist[r["user_key"]] = {"label": r["label"], "reason": r["reason"], "uid": r["user_id"]}
            for r in await c.fetch(
                "SELECT id, phrase, kind, file_id, content, src_chat, src_msg FROM triggers ORDER BY id"
            ):
                triggers[r["id"]] = make_trigger(
                    r["phrase"], r["kind"], r["file_id"], r["content"], r["src_chat"], r["src_msg"]
                )
            for r in await c.fetch("SELECT chat_id, user_key, label FROM link_allow"):
                link_allow.setdefault(r["chat_id"], {})[r["user_key"]] = r["label"]
            for r in await c.fetch("SELECT chat_id, word FROM stopwords"):
                stopwords.setdefault(r["chat_id"], []).append(r["word"])
            try:  # настройки из прошлой версии (таблица chat_settings), если она есть
                for r in await c.fetch("SELECT chat_id, antilink FROM chat_settings"):
                    chat_settings.setdefault(r["chat_id"], {})["antilink"] = r["antilink"]
            except Exception:
                pass
            for r in await c.fetch("SELECT chat_id, data FROM chat_cfg"):
                chat_settings.setdefault(r["chat_id"], {}).update(json.loads(r["data"]))
            for r in await c.fetch("SELECT chat_id, user_id, cnt FROM warns"):
                warns[(r["chat_id"], r["user_id"])] = r["cnt"]
            for r in await c.fetch("SELECT username, user_id FROM seen_users"):
                seen_users[r["username"]] = r["user_id"]
            for r in await c.fetch("SELECT user_id, username, name, hist FROM user_names"):
                known_names[r["user_id"]] = {
                    "username": r["username"], "name": r["name"], "hist": json.loads(r["hist"]),
                }
        log.info(
            "База подключена: чатов %d, топов %d, долгов %d, в черном списке %d",
            len(allowed_chats), len(perm_tops), len(debts), len(blacklist),
        )
    else:
        log.warning(
            "DATABASE_URL не задан — данные хранятся в файле %s и пропадут при деплое на бесплатном Render",
            DATA_FILE,
        )
        load_file()
    for x in os.environ.get("ALLOWED_CHATS", "").split(","):
        x = x.strip()
        if re.fullmatch(r"-?\d+", x):
            allowed_chats.setdefault(int(x), "?")


async def db_exec(query: str, *args) -> bool:
    """Выполнить запись в базу (с одним повтором, если Neon «проснулся» не сразу)."""
    if pool is None:
        save_file()
        return True
    for _ in range(2):
        try:
            await pool.execute(query, *args)
            return True
        except (asyncpg.PostgresConnectionError, asyncpg.InterfaceError, OSError) as e:
            log.warning("база недоступна, повтор: %s", e)
            await asyncio.sleep(1.5)
        except Exception as e:
            log.error("ошибка записи в базу: %s", e)
            return False
    return False


async def storage_add_chat(chat_id: int, title: str) -> bool:
    allowed_chats[chat_id] = title
    return await db_exec(
        "INSERT INTO chats (chat_id, title) VALUES ($1, $2) "
        "ON CONFLICT (chat_id) DO UPDATE SET title = EXCLUDED.title",
        chat_id,
        title,
    )


async def storage_del_chat(chat_id: int) -> bool:
    allowed_chats.pop(chat_id, None)
    return await db_exec("DELETE FROM chats WHERE chat_id = $1", chat_id)


async def storage_add_top(key: str, label: str) -> bool:
    perm_tops[key] = label
    return await db_exec(
        "INSERT INTO tops (user_key, label) VALUES ($1, $2) "
        "ON CONFLICT (user_key) DO UPDATE SET label = EXCLUDED.label",
        key,
        label,
    )


async def storage_del_top(key: str) -> bool:
    perm_tops.pop(key, None)
    return await db_exec("DELETE FROM tops WHERE user_key = $1", key)


async def db_fetchrow(query: str, *args):
    """Запись с возвратом строки (INSERT ... RETURNING), с одним повтором. None — не вышло."""
    for _ in range(2):
        try:
            return await pool.fetchrow(query, *args)
        except (asyncpg.PostgresConnectionError, asyncpg.InterfaceError, OSError) as e:
            log.warning("база недоступна, повтор: %s", e)
            await asyncio.sleep(1.5)
        except Exception as e:
            log.error("ошибка записи в базу: %s", e)
            return None
    return None


async def storage_add_debt(key: str, label: str, title: str, uid=None):
    """Возвращает номер долга или None, если сохранить не удалось."""
    if pool is None:
        new_id = max(debts, default=0) + 1
        debts[new_id] = {"key": key, "label": label, "title": title, "uid": uid}
        save_file()
        return new_id
    row = await db_fetchrow(
        "INSERT INTO debts (user_key, label, title, user_id) VALUES ($1, $2, $3, $4) RETURNING id",
        key,
        label,
        title,
        uid,
    )
    if row is None:
        return None
    debts[row["id"]] = {"key": key, "label": label, "title": title, "uid": uid}
    return row["id"]


async def storage_del_debt(debt_id: int) -> bool:
    debts.pop(debt_id, None)
    return await db_exec("DELETE FROM debts WHERE id = $1", debt_id)


async def storage_add_black(key: str, label: str, reason: str, uid=None) -> bool:
    old_uid = blacklist.get(key, {}).get("uid")
    uid = uid or old_uid
    blacklist[key] = {"label": label, "reason": reason, "uid": uid}
    return await db_exec(
        "INSERT INTO blacklist (user_key, label, reason, user_id) VALUES ($1, $2, $3, $4) "
        "ON CONFLICT (user_key) DO UPDATE SET label = EXCLUDED.label, reason = EXCLUDED.reason, "
        "user_id = EXCLUDED.user_id",
        key,
        label,
        reason,
        uid,
    )


async def storage_del_black(key: str) -> bool:
    blacklist.pop(key, None)
    return await db_exec("DELETE FROM blacklist WHERE user_key = $1", key)


def make_trigger(phrase: str, kind: str, file_id, text, src_chat=None, src_msg=None) -> dict:
    return {
        "phrase": phrase,
        "kind": kind,
        "file_id": file_id,
        "text": text,
        "src_chat": src_chat,  # откуда пересылать (режим «пересланное»)
        "src_msg": src_msg,
    }


async def storage_set_trigger(phrase: str, kind: str, file_id, text, src_chat=None, src_msg=None):
    """Создаёт триггер или заменяет существующий с той же фразой. Возвращает номер или None."""
    phrase = phrase.lower()
    existing = next((i for i, t in triggers.items() if t["phrase"] == phrase), None)
    if pool is None:
        tid = existing or max(triggers, default=0) + 1
    elif existing:
        ok = await db_exec(
            "UPDATE triggers SET kind = $2, file_id = $3, content = $4, src_chat = $5, src_msg = $6 "
            "WHERE id = $1",
            existing,
            kind,
            file_id,
            text,
            src_chat,
            src_msg,
        )
        if not ok:
            return None
        tid = existing
    else:
        row = await db_fetchrow(
            "INSERT INTO triggers (phrase, kind, file_id, content, src_chat, src_msg) "
            "VALUES ($1, $2, $3, $4, $5, $6) RETURNING id",
            phrase,
            kind,
            file_id,
            text,
            src_chat,
            src_msg,
        )
        if row is None:
            return None
        tid = row["id"]
    triggers[tid] = make_trigger(phrase, kind, file_id, text, src_chat, src_msg)
    if pool is None:
        save_file()
    return tid


async def storage_del_trigger(trigger_id: int) -> bool:
    triggers.pop(trigger_id, None)
    return await db_exec("DELETE FROM triggers WHERE id = $1", trigger_id)


def spawn(coro):
    """Фоновая задача (чтобы не ждать запись в базу)."""
    task = asyncio.create_task(coro)
    _bg_tasks.add(task)
    task.add_done_callback(_bg_tasks.discard)


def setting(chat_id: int, name: str):
    return chat_settings.get(chat_id, {}).get(name, DEFAULT_SETTINGS[name])


async def storage_allow_link(chat_id: int, keys: list, label: str) -> bool:
    ok = True
    for k in keys:
        link_allow.setdefault(chat_id, {})[k] = label
        ok = await db_exec(
            "INSERT INTO link_allow (chat_id, user_key, label) VALUES ($1, $2, $3) "
            "ON CONFLICT (chat_id, user_key) DO UPDATE SET label = EXCLUDED.label",
            chat_id,
            k,
            label,
        ) and ok
    return ok


async def storage_deny_link(chat_id: int, keys: list) -> bool:
    ok = True
    for k in keys:
        link_allow.get(chat_id, {}).pop(k, None)
        ok = await db_exec(
            "DELETE FROM link_allow WHERE chat_id = $1 AND user_key = $2", chat_id, k
        ) and ok
    return ok


async def storage_add_word(chat_id: int, word: str) -> bool:
    words = stopwords.setdefault(chat_id, [])
    if word not in words:
        words.append(word)
    return await db_exec(
        "INSERT INTO stopwords (chat_id, word) VALUES ($1, $2) ON CONFLICT DO NOTHING", chat_id, word
    )


async def storage_del_word(chat_id: int, word: str) -> bool:
    if word in stopwords.get(chat_id, []):
        stopwords[chat_id].remove(word)
    return await db_exec("DELETE FROM stopwords WHERE chat_id = $1 AND word = $2", chat_id, word)


async def storage_save_cfg(chat_id: int) -> bool:
    """Все настройки чата одной JSON-строкой."""
    data = json.dumps(chat_settings.get(chat_id, {}), ensure_ascii=False)
    return await db_exec(
        "INSERT INTO chat_cfg (chat_id, data) VALUES ($1, $2) "
        "ON CONFLICT (chat_id) DO UPDATE SET data = EXCLUDED.data",
        chat_id,
        data,
    )


async def storage_set_setting(chat_id: int, name: str, value) -> bool:
    chat_settings.setdefault(chat_id, {})[name] = value
    return await storage_save_cfg(chat_id)


async def storage_set_warns(chat_id: int, user_id: int, n: int) -> bool:
    if n <= 0:
        warns.pop((chat_id, user_id), None)
        return await db_exec("DELETE FROM warns WHERE chat_id = $1 AND user_id = $2", chat_id, user_id)
    warns[(chat_id, user_id)] = n
    return await db_exec(
        "INSERT INTO warns (chat_id, user_id, cnt) VALUES ($1, $2, $3) "
        "ON CONFLICT (chat_id, user_id) DO UPDATE SET cnt = EXCLUDED.cnt",
        chat_id,
        user_id,
        n,
    )


async def storage_seen(username: str, user_id: int):
    seen_users[username] = user_id
    if pool is not None:  # в базу пишем в фоне и только при изменении
        spawn(
            db_exec(
                "INSERT INTO seen_users (username, user_id) VALUES ($1, $2) "
                "ON CONFLICT (username) DO UPDATE SET user_id = EXCLUDED.user_id",
                username,
                user_id,
            )
        )


# ---------------------------------------------------------------- helpers

def user_key_label(user):
    """Ключ для сравнения и подпись для списка."""
    if user.username:
        return "@" + user.username.lower(), "@" + user.username
    name = html.escape(user.full_name)
    return f"id:{user.id}", f'<a href="tg://user?id={user.id}">{name}</a>'


def is_num(token: str) -> bool:
    return token.isascii() and token.isdigit()


def is_top(game, key: str) -> bool:
    """Топ: постоянный (/top) или на эту игру (/vtop)."""
    return key in perm_tops or key in game["vtops"]


def fmt_user(username) -> str:
    return f"@{username}" if username else "нет"


async def storage_save_name(uid: int) -> bool:
    rec = known_names[uid]
    return await db_exec(
        "INSERT INTO user_names (user_id, username, name, hist) VALUES ($1, $2, $3, $4) "
        "ON CONFLICT (user_id) DO UPDATE SET username = EXCLUDED.username, name = EXCLUDED.name, "
        "hist = EXCLUDED.hist",
        uid,
        rec["username"],
        rec["name"],
        json.dumps(rec["hist"], ensure_ascii=False),
    )


def name_change_text(uid: int, old: dict, new_u, new_n: str) -> str:
    lines = [
        "🔄 <b>Смена ника</b>",
        f'👤 <a href="tg://user?id={uid}">{html.escape(new_n)}</a> (ID <code>{uid}</code>)',
    ]
    if old["username"] != new_u:
        lines.append(f"Юзернейм: {fmt_user(old['username'])} → {fmt_user(new_u)}")
    if old["name"] != new_n:
        lines.append(f"Имя: {html.escape(old['name'])} → {html.escape(new_n)}")
    return "\n".join(lines)


async def check_name_change(bot, chat_id: int, user, thread=None):
    """Замечает смену юзернейма/имени и сообщает об этом в чат (в каждом чате, где человек пишет)."""
    cur_u, cur_n = user.username, user.full_name
    rec = known_names.get(user.id)
    if rec is None:  # видим человека впервые — просто запоминаем
        known_names[user.id] = {"username": cur_u, "name": cur_n, "hist": []}
        await storage_save_name(user.id)
        return
    if rec["username"] != cur_u or rec["name"] != cur_n:
        old = {"username": rec["username"], "name": rec["name"]}
        today = datetime.now(get_tz(DEFAULT_TZ) or timezone.utc).strftime("%d.%m.%Y")
        rec["hist"] = ([f"{today}: {fmt_user(old['username'])} · {old['name']}"] + rec["hist"])[:10]
        rec["username"], rec["name"] = cur_u, cur_n
        await storage_save_name(user.id)
        # сообщить нужно в каждом чате, где этот человек потом напишет
        name_pending[user.id] = {"old": old, "new": (cur_u, cur_n), "chats": set(allowed_chats)}
    p = name_pending.get(user.id)
    if p and chat_id in p["chats"]:
        p["chats"].discard(chat_id)
        if not p["chats"]:
            name_pending.pop(user.id, None)
        if setting(chat_id, "nickwatch"):
            try:
                await bot.send_message(
                    chat_id,
                    name_change_text(user.id, p["old"], *p["new"]),
                    parse_mode=ParseMode.HTML,
                    message_thread_id=thread,
                )
            except Exception as e:
                log.warning("не удалось сообщить о смене ника: %s", e)


def key_uid(key: str):
    """ID человека по ключу: «id:123» или «@ник» (если бот уже видел этого человека)."""
    if key.startswith("id:"):
        return int(key[3:])
    return seen_users.get(key[1:])


def self_uid(user, key: str):
    """ID пишущего, если ключ — его собственный (а не чужой «@юзер» из команды)."""
    return user.id if key == user_key_label(user)[0] else None


def find_black(key: str, uid=None):
    """Ищет человека в чёрном списке и по @нику, и по ID — так он не уйдёт от списка сменой ника.
    -> (ключ записи, запись) или (None, None)."""
    if key in blacklist:
        return key, blacklist[key]
    uid = uid or key_uid(key)
    if uid:
        if f"id:{uid}" in blacklist:
            return f"id:{uid}", blacklist[f"id:{uid}"]
        for k, e in blacklist.items():
            if e.get("uid") == uid:
                return k, e
    return None, None


def black_entry(key: str, uid=None):
    return find_black(key, uid)[1]


def debt_mark(key: str) -> str:
    """Пометка в конце записи: должник (находим и по @нику, и по ID)."""
    uid = key_uid(key)
    titles = [
        html.escape(d["title"])
        for d in debts.values()
        if d["key"] == key or (uid and d.get("uid") == uid)
    ]
    return f" 💸 должен {', '.join(titles)}" if titles else ""


async def sync_identity(user):
    """Привязывает долги и чёрный список к ID человека и обновляет его текущий ник в подписях."""
    if not debts and not blacklist:
        return
    key, label = user_key_label(user)
    for did, d in debts.items():
        if d.get("uid") == user.id or (d.get("uid") is None and d["key"] == key):
            if d.get("uid") != user.id or d["label"] != label:
                d["uid"], d["label"] = user.id, label
                spawn(db_exec("UPDATE debts SET user_id = $2, label = $3 WHERE id = $1", did, user.id, label))
    for k, e in blacklist.items():
        if e.get("uid") == user.id or (e.get("uid") is None and k == key):
            if e.get("uid") != user.id or e["label"] != label:
                e["uid"], e["label"] = user.id, label
                spawn(db_exec("UPDATE blacklist SET user_id = $2, label = $3 WHERE user_key = $1", k, user.id, label))


async def track_user(user):
    """Запоминаем ник -> ID и привязываем человека к долгам и чёрному списку."""
    if user.username:
        low = user.username.lower()
        if seen_users.get(low) != user.id:
            await storage_seen(low, user.id)
    await sync_identity(user)


def black_message(label: str, own: bool) -> str:
    if own:
        return "Вы находитесь в черном списке, свяжитесь с администратором чата."
    return f"{label} находится в черном списке, свяжитесь с администратором чата."


def parse_numbers(tokens, top=False):
    allowed = (BINGO_COUNT, BINGO_COUNT + 1) if top else (BINGO_COUNT,)
    if len(tokens) not in allowed or not all(is_num(t) for t in tokens):
        return None
    nums = [int(t) for t in tokens]
    if len(set(nums)) != len(nums):
        return None
    if any(not BINGO_MIN <= n <= BINGO_MAX for n in nums):
        return None
    return nums


def numbers_hint(top=False) -> str:
    if top:
        return f"Нужно {BINGO_COUNT} или {BINGO_COUNT + 1} разных чисел от {BINGO_MIN} до {BINGO_MAX}."
    return f"Нужно ровно {BINGO_COUNT} разных чисел от {BINGO_MIN} до {BINGO_MAX}."


def roulette_add(game, owner: str, label: str):
    """Добавляет запись в рулетку. None — успех, иначе число — лимит записей."""
    limit = 2 if is_top(game, owner) else 1
    n = sum(1 for p in game["players"].values() if p.get("owner") == owner)
    if n >= limit:
        return limit
    game["players"][owner if n == 0 else f"{owner}#{n + 1}"] = {"label": label, "owner": owner}
    return None


def render(game) -> str:
    players = game["players"]
    if game["type"] == "roulette":
        title = "🎰 Рулетка"
        how = "Записаться: напишите @ или @юзер, либо нажмите кнопку."
    else:
        title = f"🎯 Бинго ({BINGO_MIN}–{BINGO_MAX})"
        how = (
            "Записаться тремя способами:\n"
            "• @ 1 2 3 4 5\n"
            "• @юзер 1 2 3 4 5\n"
            "• кнопка ниже, затем 5 чисел ответом на сообщение бота\n"
            "Ответом на любое сообщение бота 5 чисел тоже запишут вас."
        )
    status = "🔒 Список закрыт" if game["closed"] else "🟢 Запись открыта"
    lines = [f"<b>{title}</b>", status, "", f"Участники ({len(players)}):"]
    if not players:
        lines.append("пока никого")
    drawn = game["drawn_set"]
    for i, (k, p) in enumerate(players.items(), 1):
        line = f"{i}. {p['label']}"
        if game["type"] == "bingo":
            nums = " ".join(f"{n}✅" if n in drawn else str(n) for n in p["numbers"])
            line += f" — {nums}"
            if p["strikes"]:
                line += f" ⚠️ {p['strikes']}/{MAX_STRIKES}"
        line += debt_mark(p.get("owner", k))
        lines.append(line)
    if not game["closed"]:
        lines += ["", how]
    return "\n".join(lines)


def keyboard(game):
    if game["closed"]:
        return None
    return InlineKeyboardMarkup([[InlineKeyboardButton("✍️ Записаться", callback_data="join")]])


async def refresh(bot, chat_id, game):
    try:
        await bot.edit_message_text(
            render(game),
            chat_id=chat_id,
            message_id=game["msg_id"],
            parse_mode=ParseMode.HTML,
            reply_markup=keyboard(game),
        )
    except BadRequest as e:
        if "not modified" in str(e).lower():
            return
        log.warning("edit failed, sending new list: %s", e)
        m = await bot.send_message(
            chat_id, render(game), parse_mode=ParseMode.HTML, reply_markup=keyboard(game)
        )
        game["msg_id"] = m.message_id


def render_board(game) -> str:
    """Все выпавшие строки одним списком, по порядку выдачи."""
    drawn = game["drawn"]
    rows = ["; ".join(map(str, drawn[k:k + BINGO_COUNT])) for k in range(0, len(drawn), BINGO_COUNT)]
    header = f"🎯 <b>Выпавшие числа</b> (строк: {len(rows)})\n\n"
    if not rows:
        return header + "пока ничего не выпало"
    sep = "\n➖\n"
    cut = False
    # лимит Telegram — 4096 символов: при переполнении убираем самые старые строки
    while len(header) + len(sep.join(rows)) > 3900 and len(rows) > 1:
        rows.pop(0)
        cut = True
    return header + ("…\n➖\n" if cut else "") + sep.join(rows)


async def update_board(bot, chat_id, game):
    """Общий список выпавших чисел: появляется после /close и обновляется после каждого /line."""
    text = render_board(game)
    mid = game.get("board_msg_id")
    if mid:
        try:
            await bot.edit_message_text(text, chat_id=chat_id, message_id=mid, parse_mode=ParseMode.HTML)
            return
        except BadRequest as e:
            if "not modified" in str(e).lower():
                return
    m = await bot.send_message(chat_id, text, parse_mode=ParseMode.HTML)
    game["board_msg_id"] = m.message_id
    try:  # закрепляем список строк, дальше он только дополняется
        await bot.pin_chat_message(chat_id, m.message_id, disable_notification=True)
    except Exception as e:
        log.warning("не удалось закрепить список строк: %s", e)
        await bot.send_message(
            chat_id,
            "⚠️ Не смог закрепить список строк. Дайте боту право «Закреплять сообщения».",
        )


def is_bot_admin(user) -> bool:
    return user is not None and user.id in ADMIN_IDS


def no_access_text(user) -> str:
    uid = user.id if user else "неизвестен"
    return (
        f"Нет доступа. Ваш Telegram ID: {uid}\n"
        "Если вы владелец бота, добавьте этот ID в переменную ADMIN_IDS на Render "
        "(несколько ID через запятую) и дождитесь перезапуска."
    )


async def require_bot_admin(update: Update) -> bool:
    """Проверка для /top, /untop, /tops: админ бота и разрешённый чат. Отказ — с понятным ответом."""
    chat, user, msg = update.effective_chat, update.effective_user, update.effective_message
    if chat.type not in (ChatType.PRIVATE, ChatType.GROUP, ChatType.SUPERGROUP):
        return False
    if not is_bot_admin(user):
        if chat.type == ChatType.PRIVATE:
            await msg.reply_text(no_access_text(user))
        elif chat.id in allowed_chats:
            await msg.reply_text("Эта команда только для админов бота.")
        return False
    if chat.type != ChatType.PRIVATE and chat.id not in allowed_chats:
        await msg.reply_text("Этот чат не добавлен в список. Напишите здесь /addchat.")
        return False
    return True


async def is_admin(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if msg and msg.sender_chat and msg.sender_chat.id == chat.id:
        return True  # админ, пишущий анонимно
    if user is None:
        return False
    if user.id in ADMIN_IDS:
        return True
    member = await context.bot.get_chat_member(chat.id, user.id)
    return member.status in (ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER)


def admin_only(func):
    @functools.wraps(func)
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        chat = update.effective_chat
        if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
            await update.effective_message.reply_text("Эта команда работает только в группе.")
            return
        if chat.id not in allowed_chats:
            return  # чат не в списке — бот молчит
        if not await is_admin(update, context):
            await update.effective_message.reply_text("Команда только для админов.")
            return
        await func(update, context)

    return wrapper


async def prompt_numbers(context, chat_id, user, game):
    """Просит человека прислать числа прямо в чат."""
    pending.add((chat_id, user.id))
    key, label = user_key_label(user)
    if key in game["players"] and is_top(game, key):
        how = str(BINGO_COUNT + 1)  # перезапись топа — только с 6 числами
    elif is_top(game, key):
        how = f"{BINGO_COUNT} или {BINGO_COUNT + 1}"
    else:
        how = str(BINGO_COUNT)
    await context.bot.send_message(
        chat_id,
        f"{label}, отправьте {how} разных чисел от {BINGO_MIN} до {BINGO_MAX} "
        f"через пробел, например: 7 23 45 68 91",
        parse_mode=ParseMode.HTML,
        reply_markup=ForceReply(selective=True, input_field_placeholder="7 23 45 68 91"),
    )


def register_bingo(game, key, label, nums):
    old = game["players"].get(key)
    game["players"][key] = {
        "label": label,
        "numbers": nums,
        "strikes": old["strikes"] if old else 0,
    }


def bingo_limit_error(game, key, nums):
    """Лимит записи в бинго: одна карточка. Перезаписаться может только топ — с 6 числами."""
    old = game["players"].get(key)
    if not old or len(nums) > len(old["numbers"]):
        return None
    if is_top(game, key) and len(old["numbers"]) == BINGO_COUNT:
        return "уже записан(а). Перезаписаться можно только с 6 числами."
    if is_top(game, key):
        return "уже записан(а) с 6 числами."
    return "уже записан(а), лимит — одна запись."


def bingo_prompt_error(game, key):
    """Можно ли вообще просить числа у этого человека (кнопка / «@»)."""
    old = game["players"].get(key)
    if not old:
        return None
    if is_top(game, key) and len(old["numbers"]) == BINGO_COUNT:
        return None  # топ может перезаписаться с 6 числами
    return "Вы уже записаны." if not is_top(game, key) else "Вы уже записаны с 6 числами."


def target_from(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Кого имеем в виду в /top, /vtop, /untop: @юзер в аргументе или ответ на сообщение."""
    if context.args:
        m = re.fullmatch(r"@(\w{3,})", context.args[0])
        if m:
            return "@" + m.group(1).lower(), "@" + m.group(1)
    r = update.effective_message.reply_to_message
    if r and r.from_user and not r.from_user.is_bot:
        return user_key_label(r.from_user)
    return None


# ---------------------------------------------------------------- commands

async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_chat.type != ChatType.PRIVATE:
        return
    arg = context.args[0] if context.args else ""
    m = re.fullmatch(r"cfg_(-?\d+)", arg)
    if m:  # переход из группы по кнопке «Открыть настройки»
        chat_id = int(m.group(1))
        if await can_manage(context.bot, chat_id, update.effective_user):
            text, markup = main_menu(chat_id)
            await update.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)
        else:
            await update.message.reply_text("Нет доступа к настройкам этого чата.")
        return
    await update.message.reply_text(
        "Привет! Я бот для игр и защиты группы. Игры запускают админы командой /games, "
        "настройки чата открываются здесь: /settings."
    )


GAME_NAMES = {"bingo": "🎯 Бинго", "roulette": "🎰 Рулетка"}


def new_game(kind: str) -> dict:
    return {
        "type": kind,
        "closed": False,
        "players": {},
        "msg_id": None,
        "board_msg_id": None,
        "drawn": [],
        "drawn_set": set(),
        "banned": set(),
        "vtops": set(),  # топы только на эту игру
    }


@admin_only
async def cmd_games(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/games — выбор игры кнопками."""
    chat_id = update.effective_chat.id
    game = games.get(chat_id)
    if game:
        await update.effective_message.reply_text(
            f"Сейчас идёт игра: {GAME_NAMES[game['type']]}. Завершить: /stopgame"
        )
        return
    kb = InlineKeyboardMarkup([
        [btn("🎯 Бинго", "game:bingo"), btn("🎰 Рулетка", "game:roulette")],
        [btn("✖️ Отмена", "game:cancel")],
    ])
    await update.effective_message.reply_text("🎮 Выберите игру:", reply_markup=kb)


async def on_game_choice(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Нажатие на игру в /games: это же сообщение превращается в список записи."""
    q = update.callback_query
    chat_id = q.message.chat_id
    m = re.fullmatch(r"game:(bingo|roulette|cancel)", q.data or "")
    if not m or chat_id not in allowed_chats:
        await q.answer()
        return
    if not await can_manage(context.bot, chat_id, q.from_user):
        await q.answer("Игры запускают только админы.", show_alert=True)
        return
    kind = m.group(1)
    if kind == "cancel":
        await q.answer()
        try:
            await q.message.delete()
        except Exception:
            await q.edit_message_text("Отменено.")
        return
    if chat_id in games:
        await q.answer("Игра уже идёт. Завершить: /stopgame", show_alert=True)
        return
    game = new_game(kind)
    game["msg_id"] = q.message.message_id
    games[chat_id] = game
    await q.answer()
    await q.edit_message_text(render(game), parse_mode=ParseMode.HTML, reply_markup=keyboard(game))


async def cmd_bingo(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/bingo во время игры — заявка на победу (как слово «бинго»). Запуск игр — через /games."""
    chat = update.effective_chat
    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
        await update.effective_message.reply_text("Эта команда работает только в группе.")
        return
    if chat.id not in allowed_chats:
        return
    game = games.get(chat.id)
    if game and game["type"] == "bingo":
        await bingo_claim(update, context, game)  # игрок написал /bingo вместо «бинго»
        return
    if await is_admin(update, context):
        await update.effective_message.reply_text("Игры запускаются командой /games.")


@admin_only
async def cmd_close(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    game = games.get(chat_id)
    if not game:
        await update.effective_message.reply_text("Нет активной игры.")
        return
    if game["closed"]:
        await update.effective_message.reply_text("Список уже закрыт.")
        return
    if not game["players"]:
        await update.effective_message.reply_text("Список пуст, закрывать нечего.")
        return
    game["closed"] = True
    pending.difference_update({p for p in pending if p[0] == chat_id})
    await refresh(context.bot, chat_id, game)
    nxt = "/random" if game["type"] == "roulette" else "/line n"
    await update.effective_message.reply_text(
        f"🔒 Список закрыт. Участников: {len(game['players'])}. Дальше: {nxt}"
    )
    if game["type"] == "bingo":
        await update_board(context.bot, chat_id, game)


@admin_only
async def cmd_random(update: Update, context: ContextTypes.DEFAULT_TYPE):
    game = games.get(update.effective_chat.id)
    if not game or game["type"] != "roulette":
        await update.effective_message.reply_text("Рулетка сейчас не запущена.")
        return
    if not game["closed"]:
        await update.effective_message.reply_text("Сначала закройте список: /close")
        return
    players = list(game["players"].values())
    n = random.randint(1, len(players))
    await update.effective_message.reply_text(
        f"🎲 Выпало число <b>{n}</b>",
        parse_mode=ParseMode.HTML,
    )


@admin_only
async def cmd_line(update: Update, context: ContextTypes.DEFAULT_TYPE):
    game = games.get(update.effective_chat.id)
    if not game or game["type"] != "bingo":
        await update.effective_message.reply_text("Бинго сейчас не запущено.")
        return
    if not game["closed"]:
        await update.effective_message.reply_text("Сначала закройте список: /close")
        return
    rows_count = 1
    if context.args:
        a = context.args[0]
        if not (is_num(a) and 1 <= int(a) <= 5):
            await update.effective_message.reply_text("Использование: /line n, где n от 1 до 5")
            return
        rows_count = int(a)
    lines = []
    for i in range(rows_count):
        # полный рандом: каждая строка выбирается независимо от прошлых, числа могут повторяться
        row = random.sample(range(BINGO_MIN, BINGO_MAX + 1), BINGO_COUNT)
        game["drawn"].extend(row)
        game["drawn_set"].update(row)
        lines.append(f"{i + 1}) " + "  ".join(f"{x}" for x in row))
    await update.effective_message.reply_text("🎯 Выпало:\n" + "\n".join(lines))
    await refresh(context.bot, update.effective_chat.id, game)
    await update_board(context.bot, update.effective_chat.id, game)


async def cmd_check(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP) or chat.id not in allowed_chats:
        return
    game = games.get(chat.id)
    if not game or game["type"] != "bingo":
        return
    if not context.args:
        # без аргументов: проверяем числа того, кто написал
        key, _ = user_key_label(update.effective_user)
        player = game["players"].get(key)
        if not player:
            await update.effective_message.reply_text("Вас нет в списке.")
            return
        drawn = game["drawn_set"]
        marks = " ".join(f"{n}{'✅' if n in drawn else '❌'}" for n in player["numbers"])
        text = f"{player['label']}: {marks}"
        if sum(1 for n in player["numbers"] if n in drawn) >= BINGO_COUNT:
            text += "\nМожно писать «бинго»!"
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML)
        return
    if len(context.args) > BINGO_COUNT or not all(is_num(a) for a in context.args):
        await update.effective_message.reply_text(f"Использование: /check n n n (от 1 до {BINGO_COUNT} чисел)")
        return
    parts = []
    for a in context.args:
        n = int(a)
        parts.append(f"{n} {'✅' if n in game['drawn_set'] else '❌'}")
    await update.effective_message.reply_text("  ".join(parts))


@admin_only
async def cmd_stopgame(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    game = games.pop(chat_id, None)
    if not game:
        await update.effective_message.reply_text("Нет активной игры.")
        return
    pending.difference_update({p for p in pending if p[0] == chat_id})
    try:
        await context.bot.edit_message_reply_markup(chat_id, game["msg_id"], reply_markup=None)
    except BadRequest:
        pass
    if game.get("board_msg_id"):  # открепляем список строк
        try:
            await context.bot.unpin_chat_message(chat_id, game["board_msg_id"])
        except Exception as e:
            log.warning("не удалось открепить: %s", e)
    await update.effective_message.reply_text(
        "🛑 Игра завершена. Бот не реагирует на сообщения, пока не запущена новая игра."
    )


# ---------------------------------------------------------------- топы

@admin_only
async def cmd_vtop(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Топ только на текущую игру."""
    msg = update.effective_message
    game = games.get(update.effective_chat.id)
    if not game:
        await msg.reply_text("Нет активной игры.")
        return
    t = target_from(update, context)
    if not t:
        await msg.reply_text("Использование: /vtop @юзер (или ответом на сообщение игрока)")
        return
    key, label = t
    game["vtops"].add(key)
    what = "2 записи в рулетке" if game["type"] == "roulette" else "запись с 6 числами"
    await msg.reply_text(f"⭐ {label} — топ на эту игру: {what}.", parse_mode=ParseMode.HTML)


async def cmd_top(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Топ на постоянной основе (только админы бота из ADMIN_IDS)."""
    chat, msg = update.effective_chat, update.effective_message
    if not await require_bot_admin(update):
        return
    t = target_from(update, context)
    if not t:
        await msg.reply_text("Использование: /top @юзер (или ответом на сообщение игрока)")
        return
    key, label = t
    ok = await storage_add_top(key, label)
    text = f"⭐ {label} теперь топ на постоянной основе."
    if not ok:
        text += "\n⚠️ Не удалось сохранить в базу, после перезапуска топ пропадёт."
    await msg.reply_text(text, parse_mode=ParseMode.HTML)


async def cmd_untop(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat, msg = update.effective_chat, update.effective_message
    if not await require_bot_admin(update):
        return
    t = target_from(update, context)
    if not t:
        await msg.reply_text("Использование: /untop @юзер (или ответом на сообщение игрока)")
        return
    key, label = t
    game = games.get(chat.id)
    if game:
        game["vtops"].discard(key)
    if key not in perm_tops:
        await msg.reply_text(f"{label} не в списке постоянных топов.", parse_mode=ParseMode.HTML)
        return
    ok = await storage_del_top(key)
    text = f"{label} больше не топ."
    if not ok:
        text += "\n⚠️ Не удалось удалить из базы."
    await msg.reply_text(text, parse_mode=ParseMode.HTML)


async def cmd_tops(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat, msg = update.effective_chat, update.effective_message
    if not await require_bot_admin(update):
        return
    if not perm_tops:
        await msg.reply_text("Постоянных топов пока нет. Добавить: /top @юзер")
        return
    lines = [f"{i}. {label}" for i, label in enumerate(perm_tops.values(), 1)]
    await msg.reply_text("⭐ Постоянные топы:\n" + "\n".join(lines), parse_mode=ParseMode.HTML)


# ---------------------------------------------------------------- должники и чёрный список (только админы бота)

def target_and_rest(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """(ключ, подпись, ID или None) и остаток аргументов: «@юзер текст», «ID текст» или ответом на сообщение."""
    args = list(context.args or [])
    if args:
        m = re.fullmatch(r"@(\w{3,})", args[0])
        if m:
            low = m.group(1).lower()
            return ("@" + low, "@" + m.group(1), seen_users.get(low)), args[1:]
        if re.fullmatch(r"\d{5,}", args[0]):
            uid = int(args[0])
            return (f"id:{uid}", f'<a href="tg://user?id={uid}">{uid}</a>', uid), args[1:]
    r = update.effective_message.reply_to_message
    if r and r.from_user and not r.from_user.is_bot:
        key, label = user_key_label(r.from_user)
        return (key, label, r.from_user.id), args
    return None, args


async def cmd_adolg(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not await require_bot_admin(update):
        return
    t, rest = target_and_rest(update, context)
    title = " ".join(rest).strip()[:100]
    if not t or not title:
        await msg.reply_text("Использование: /adolg @юзер название (или ID, или ответом на сообщение)")
        return
    key, label, uid = t
    new_id = await storage_add_debt(key, label, title, uid)
    if new_id is None:
        await msg.reply_text("⚠️ Не удалось сохранить в базу, попробуйте ещё раз.")
        return
    await msg.reply_text(
        f"💸 Долг №{new_id}: {label} — {html.escape(title)}", parse_mode=ParseMode.HTML
    )


async def cmd_dolg(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not await require_bot_admin(update):
        return
    if not debts:
        await msg.reply_text("Должников нет.")
        return
    lines = [
        f"№{i} — {d['label']} — {html.escape(d['title'])}" for i, d in sorted(debts.items())
    ]
    await msg.reply_text(
        "💸 Список должников:\n" + "\n".join(lines) + "\n\nУдалить: /ddolg номер",
        parse_mode=ParseMode.HTML,
    )


async def cmd_ddolg(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not await require_bot_admin(update):
        return
    if not context.args or not is_num(context.args[0]):
        await msg.reply_text("Использование: /ddolg номер_долга (номера в /dolg)")
        return
    n = int(context.args[0])
    d = debts.get(n)
    if not d:
        await msg.reply_text("Долга с таким номером нет. Смотрите /dolg")
        return
    ok = await storage_del_debt(n)
    text = f"✅ Долг №{n} удалён: {d['label']} — {html.escape(d['title'])}"
    if not ok:
        text += "\n⚠️ Не удалось удалить из базы."
    await msg.reply_text(text, parse_mode=ParseMode.HTML)


async def cmd_ablack(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not await require_bot_admin(update):
        return
    t, rest = target_and_rest(update, context)
    if not t:
        await msg.reply_text("Использование: /ablack @юзер [причина] (или ID, или ответом на сообщение)")
        return
    key, label, uid = t
    old_key, _ = find_black(key, uid)  # человек уже в списке под старым ником — обновляем ту же запись
    if old_key:
        key = old_key
    reason = " ".join(rest).strip()[:100]
    ok = await storage_add_black(key, label, reason, uid)
    text = f"🚫 {label} добавлен в черный список."
    if reason:
        text += f"\nПричина: {html.escape(reason)}"
    if not ok:
        text += "\n⚠️ Не удалось сохранить в базу, после перезапуска запись пропадёт."
    await msg.reply_text(text, parse_mode=ParseMode.HTML)


async def cmd_dblack(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not await require_bot_admin(update):
        return
    key = None
    arg = context.args[0] if context.args else ""
    items = list(blacklist)
    if is_num(arg) and 1 <= int(arg) <= len(items):  # номер из /black
        key = items[int(arg) - 1]
    else:
        t, _ = target_and_rest(update, context)
        if not t:
            await msg.reply_text("Использование: /dblack @юзер, ID или номер из /black")
            return
        key, _entry = find_black(t[0], t[2])
    if key is None or key not in blacklist:
        await msg.reply_text("Этого человека нет в черном списке. Смотрите /black")
        return
    label = blacklist[key]["label"]
    ok = await storage_del_black(key)
    text = f"✅ {label} убран из черного списка."
    if not ok:
        text += "\n⚠️ Не удалось удалить из базы."
    await msg.reply_text(text, parse_mode=ParseMode.HTML)


async def cmd_black(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not await require_bot_admin(update):
        return
    if not blacklist:
        await msg.reply_text("Черный список пуст.")
        return
    lines = []
    for i, b in enumerate(blacklist.values(), 1):
        line = f"{i}. {b['label']}"
        if b.get("reason"):
            line += f" — {html.escape(b['reason'])}"
        lines.append(line)
    await msg.reply_text(
        "🚫 Черный список:\n" + "\n".join(lines) + "\n\nУбрать: /dblack @юзер или номер",
        parse_mode=ParseMode.HTML,
    )


# ---------------------------------------------------------------- триггеры

KIND_NAMES = {
    "text": "текст",
    "sticker": "стикер",
    "photo": "фото",
    "animation": "гифка",
    "video": "видео",
    "video_note": "кружок",
    "voice": "голосовое",
    "audio": "аудио",
    "document": "файл",
    "forward": "сообщение",
}

TRIGGER_USAGE = (
    "Как добавить триггер:\n"
    "• ответьте на сообщение (стикер, фото, гифку, текст…) командой /atrigger слово — "
    "бот спросит, отправлять его от лица бота или пересланным\n"
    "• /atrigger слово | текст — простой текстовый ответ от лица бота\n"
    "Фраза может состоять из нескольких слов. Триггер срабатывает, только когда сообщение "
    "целиком совпадает с фразой (регистр букв не важен)."
)


def extract_content(r):
    """Что бот будет отправлять копией: (тип, file_id, текст/подпись в HTML) или None."""
    cap = r.caption_html if r.caption else None
    if r.sticker:
        return "sticker", r.sticker.file_id, None
    if r.photo:
        return "photo", r.photo[-1].file_id, cap
    if r.animation:  # гифка приходит и как animation, и как document — проверяем раньше
        return "animation", r.animation.file_id, cap
    if r.video:
        return "video", r.video.file_id, cap
    if r.video_note:
        return "video_note", r.video_note.file_id, None
    if r.voice:
        return "voice", r.voice.file_id, cap
    if r.audio:
        return "audio", r.audio.file_id, cap
    if r.document:
        return "document", r.document.file_id, cap
    if r.text:
        return "text", None, r.text_html
    return None


def trigger_mode_name(t) -> str:
    name = KIND_NAMES.get(t["kind"], t["kind"])
    if t.get("src_msg"):
        return "↪️ пересылка" + ("" if t["kind"] == "forward" else f" ({name})")
    return f"📤 от лица бота ({name})"


def trigger_saved_text(tid: int) -> str:
    t = triggers[tid]
    text = f"✅ Триггер №{tid}: «{html.escape(t['phrase'])}» → {trigger_mode_name(t)}"
    text += "\nСрабатывает, когда сообщение целиком совпадает с фразой (регистр не важен)."
    if t.get("src_msg"):
        text += (
            "\n\nНе удаляйте исходное сообщение из этого чата: бот пересылает именно его. "
            "Если оно пропадёт, бот отправит обычную копию без премиум-эффектов."
        )
    return text


async def cmd_atrigger(update: Update, context: ContextTypes.DEFAULT_TYPE):
    global trigger_seq
    msg = update.effective_message
    if not await require_bot_admin(update):
        return
    first = (msg.text or "").split(None, 1)
    raw = first[1] if len(first) > 1 else ""
    phrase, _, inline = raw.partition("|")
    phrase, inline = phrase.strip(), inline.strip()
    if not phrase:
        await msg.reply_text(TRIGGER_USAGE)
        return
    if not 2 <= len(phrase) <= 100:
        await msg.reply_text("Фраза должна быть от 2 до 100 символов.")
        return
    r = msg.reply_to_message

    if not r:
        if not inline:
            await msg.reply_text(TRIGGER_USAGE)
            return
        # текст прямо в команде — выбирать нечего, это сообщение от лица бота
        tid = await storage_set_trigger(phrase, "text", None, html.escape(inline))
        if tid is None:
            await msg.reply_text("⚠️ Не удалось сохранить в базу, попробуйте ещё раз.")
            return
        await msg.reply_text(trigger_saved_text(tid), parse_mode=ParseMode.HTML)
        return

    # ответ на сообщение: спрашиваем, как отправлять
    now = time.monotonic()
    for k in [k for k, v in pending_triggers.items() if now - v["ts"] > 900]:
        del pending_triggers[k]
    trigger_seq += 1
    content = extract_content(r)  # None, если это сообщение нельзя отправить копией
    pending_triggers[trigger_seq] = {
        "phrase": phrase,
        "content": content,
        "src_chat": r.chat.id,
        "src_msg": r.message_id,
        "ts": now,
    }
    row = []
    if content is not None:
        row.append(InlineKeyboardButton("📤 От лица бота", callback_data=f"tg:{trigger_seq}:bot"))
    row.append(InlineKeyboardButton("↪️ Пересланное", callback_data=f"tg:{trigger_seq}:fwd"))
    kb = InlineKeyboardMarkup([row, [InlineKeyboardButton("✖️ Отмена", callback_data=f"tg:{trigger_seq}:cancel")]])
    text = (
        f"Как отправлять триггер «{html.escape(phrase)}»?\n\n"
        "📤 <b>От лица бота</b> — бот пришлёт копию, без пометки «Переслано» "
        "(премиум-эффекты не сохраняются).\n"
        "↪️ <b>Пересланное</b> — бот перешлёт исходное сообщение целиком "
        "(сохраняются премиум-стикеры и эмодзи)."
    )
    if content is None:
        text += "\n\nЭто сообщение нельзя отправить копией, доступна только пересылка."
    await msg.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def on_trigger_choice(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not is_bot_admin(q.from_user):
        await q.answer("Только для админов бота.", show_alert=True)
        return
    m = re.fullmatch(r"tg:(\d+):(bot|fwd|cancel)", q.data or "")
    if not m:
        await q.answer()
        return
    token, action = int(m.group(1)), m.group(2)
    p = pending_triggers.get(token)
    if not p:
        await q.answer("Время вышло. Повторите /atrigger.", show_alert=True)
        try:
            await q.edit_message_reply_markup(reply_markup=None)
        except Exception:
            pass
        return
    if action == "cancel":
        pending_triggers.pop(token, None)
        await q.answer()
        await q.edit_message_text("Отменено.")
        return
    if action == "bot":
        if p["content"] is None:
            await q.answer("Это сообщение нельзя отправить копией. Выберите пересылку.", show_alert=True)
            return
        kind, file_id, text = p["content"]
        src_chat = src_msg = None
    else:
        kind, file_id, text = p["content"] or ("forward", None, None)
        src_chat, src_msg = p["src_chat"], p["src_msg"]
    tid = await storage_set_trigger(p["phrase"], kind, file_id, text, src_chat, src_msg)
    if tid is None:
        await q.answer("Не удалось сохранить в базу, попробуйте ещё раз.", show_alert=True)
        return
    pending_triggers.pop(token, None)
    await q.answer("Готово")
    await q.edit_message_text(trigger_saved_text(tid), parse_mode=ParseMode.HTML)


async def cmd_triggers(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not await require_bot_admin(update):
        return
    if not triggers:
        await msg.reply_text("Триггеров нет. Добавить: /atrigger слово (ответом на сообщение)")
        return
    lines = [
        f"№{i} — «{html.escape(t['phrase'])}» → {trigger_mode_name(t)}"
        for i, t in sorted(triggers.items())
    ]
    text = "🔔 Триггеры:\n" + "\n".join(lines)
    if len(text) > 3900:
        text = text[:3900] + "\n…"
    await msg.reply_text(text + "\n\nУдалить: /dtrigger номер", parse_mode=ParseMode.HTML)


async def cmd_dtrigger(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not await require_bot_admin(update):
        return
    first = (msg.text or "").split(None, 1)
    raw = first[1].strip() if len(first) > 1 else ""
    if not raw:
        await msg.reply_text("Использование: /dtrigger номер (или сама фраза). Список: /triggers")
        return
    if is_num(raw) and int(raw) in triggers:
        tid = int(raw)
    else:
        tid = next((i for i, t in triggers.items() if t["phrase"] == raw.lower()), None)
    if tid is None:
        await msg.reply_text("Такого триггера нет. Смотрите /triggers")
        return
    phrase = triggers[tid]["phrase"]
    ok = await storage_del_trigger(tid)
    text = f"🗑 Триггер №{tid} удалён: «{html.escape(phrase)}»"
    if not ok:
        text += "\n⚠️ Не удалось удалить из базы."
    await msg.reply_text(text, parse_mode=ParseMode.HTML)


async def send_trigger(bot, msg, t):
    # режим «пересланное»: пересылаем исходное сообщение, премиум-стикеры и эмодзи сохраняются
    if t.get("src_chat") and t.get("src_msg"):
        try:
            await bot.forward_message(
                chat_id=msg.chat_id,
                from_chat_id=t["src_chat"],
                message_id=t["src_msg"],
                message_thread_id=msg.message_thread_id if msg.is_topic_message else None,
            )
            return
        except Exception as e:
            log.warning("пересылка триггера «%s» не удалась, отправляю копию: %s", t["phrase"], e)
    if t["kind"] == "forward":
        return  # копировать нечего
    kind, fid, text = t["kind"], t["file_id"], t["text"]
    cap = {"caption": text, "parse_mode": ParseMode.HTML} if text else {}
    try:
        if kind == "text":
            await msg.reply_text(text, parse_mode=ParseMode.HTML)
        elif kind == "sticker":
            await msg.reply_sticker(fid)
        elif kind == "photo":
            await msg.reply_photo(fid, **cap)
        elif kind == "animation":
            await msg.reply_animation(fid, **cap)
        elif kind == "video":
            await msg.reply_video(fid, **cap)
        elif kind == "video_note":
            await msg.reply_video_note(fid)
        elif kind == "voice":
            await msg.reply_voice(fid, **cap)
        elif kind == "audio":
            await msg.reply_audio(fid, **cap)
        elif kind == "document":
            await msg.reply_document(fid, **cap)
    except Exception as e:
        log.warning("не удалось отправить триггер «%s»: %s", t["phrase"], e)


async def on_trigger(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Срабатывает в разрешённых чатах всегда, независимо от того, идёт ли игра."""
    msg = update.effective_message
    chat_id = update.effective_chat.id
    if not msg or chat_id not in allowed_chats or not triggers:
        return
    text = msg.text or msg.caption
    if not text:
        return
    # строгое совпадение: всё сообщение целиком равно фразе, регистр букв не важен
    norm = text.strip().lower()
    for tid, t in triggers.items():
        if t["phrase"] == norm:
            now = time.monotonic()
            if now - trigger_last.get((chat_id, tid), -1e9) < TRIGGER_COOLDOWN:
                return
            trigger_last[(chat_id, tid)] = now
            await send_trigger(context.bot, msg, t)
            return


# ---------------------------------------------------------------- защитник: ссылки, бан, мут, предупреждения

LINK_RX = re.compile(r"(https?://|www\.|(?:t|telegram)\.me/)", re.IGNORECASE)
DURATION_RX = re.compile(r"(\d+)(мин|min|м|m|ч|h|д|d|н|w)")
DURATION_UNITS = {
    "мин": 60, "min": 60, "м": 60, "m": 60,
    "ч": 3600, "h": 3600,
    "д": 86400, "d": 86400,
    "н": 604800, "w": 604800,
}
EMOJI_RX = re.compile("[\U0001F000-\U0001FAFF\u2600-\u27BF\uFE0F\u200D]")
NO_TARGET = (
    "Укажите пользователя: ответьте командой на его сообщение или напишите @юзер / ID.\n"
    "(@юзер работает, если бот уже видел сообщения этого человека в чате.)"
)
DEFAULT_PERMS = {
    "can_send_messages": True, "can_send_audios": True, "can_send_documents": True,
    "can_send_photos": True, "can_send_videos": True, "can_send_video_notes": True,
    "can_send_voice_notes": True, "can_send_polls": True, "can_send_other_messages": True,
    "can_add_web_page_previews": True, "can_invite_users": True,
}


def fmt_duration(sec: int) -> str:
    d, rem = divmod(int(sec), 86400)
    h, rem = divmod(rem, 3600)
    m = rem // 60
    parts = []
    if d:
        parts.append(f"{d} д")
    if h:
        parts.append(f"{h} ч")
    if m and not d:
        parts.append(f"{m} мин")
    return " ".join(parts) or "1 мин"


def parse_duration(tokens):
    """«30м», «2ч», «1д», «1н» (или m/h/d/w) в начале аргументов -> (секунды или None, остаток текстом)."""
    if tokens:
        m = DURATION_RX.fullmatch(tokens[0].lower())
        if m:
            secs = int(m.group(1)) * DURATION_UNITS[m.group(2)]
            if secs >= 60:
                return secs, " ".join(tokens[1:]).strip()
    return None, " ".join(tokens).strip()


def has_link(msg) -> bool:
    for e in list(msg.entities or ()) + list(msg.caption_entities or ()):
        if e.type in ("url", "text_link"):
            return True
    return bool(LINK_RX.search(msg.text or msg.caption or ""))


def link_allowed(chat_id: int, user) -> bool:
    allowed = link_allow.get(chat_id, {})
    if f"id:{user.id}" in allowed:
        return True
    return bool(user.username) and ("@" + user.username.lower()) in allowed


async def tg_api(method: str, **params):
    """Прямой вызов Bot API (для новых методов, которых нет в установленной версии библиотеки)."""
    async with httpx.AsyncClient(timeout=20) as client:
        r = await client.post(f"https://api.telegram.org/bot{TOKEN}/{method}", json=params)
    data = r.json()
    if not data.get("ok"):
        raise RuntimeError(data.get("description", "ошибка Telegram"))
    return data.get("result")


async def is_exempt(bot, chat_id: int, user) -> bool:
    """Админы чата и админы бота не наказываются (статус админа кэшируется на 5 минут)."""
    if user.id in ADMIN_IDS:
        return True
    key, now = (chat_id, user.id), time.monotonic()
    cached = admin_cache.get(key)
    if cached and now - cached[0] < 300:
        return cached[1]
    try:
        member = await bot.get_chat_member(chat_id, user.id)
        res = member.status in (ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER)
    except Exception as e:
        log.warning("не удалось проверить статус админа: %s", e)
        res = False
    admin_cache[key] = (now, res)
    return res


async def is_protected(bot, chat_id: int, uid: int) -> bool:
    """Нельзя банить/мутить: сам бот, админы бота и админы чата."""
    if uid == bot.id or uid in ADMIN_IDS:
        return True
    try:
        member = await bot.get_chat_member(chat_id, uid)
        return member.status in (ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER)
    except Exception:
        return False


async def delete_later(bot, chat_id: int, message_id: int, delay: int = NOTICE_SECONDS):
    await asyncio.sleep(delay)
    try:
        await bot.delete_message(chat_id, message_id)
    except Exception:
        pass


async def notice(bot, chat_id: int, text: str, thread=None):
    """Короткое сообщение бота, которое само удаляется."""
    try:
        m = await bot.send_message(chat_id, text, parse_mode=ParseMode.HTML, message_thread_id=thread)
        spawn(delete_later(bot, chat_id, m.message_id))
    except Exception as e:
        log.warning("не удалось отправить уведомление: %s", e)


async def do_mute(bot, chat_id: int, uid: int, seconds: int):
    until = datetime.now(timezone.utc) + timedelta(seconds=seconds)
    await bot.restrict_chat_member(chat_id, uid, ChatPermissions(can_send_messages=False), until_date=until)


async def chat_default_perms(chat_id: int) -> dict:
    """Права чата по умолчанию как есть (со всеми полями, в том числе новыми)."""
    chat = await tg_api("getChat", chat_id=chat_id)
    perms = chat.get("permissions") or {}
    return {k: v for k, v in perms.items() if isinstance(v, bool)} or dict(DEFAULT_PERMS)


async def do_unmute(bot, chat_id: int, uid: int):
    perms = await chat_default_perms(chat_id)
    await tg_api("restrictChatMember", chat_id=chat_id, user_id=uid, permissions=perms)


async def apply_warn(bot, chat_id: int, uid: int, label: str, reason: str) -> str:
    """Добавляет предупреждение; на лимите — мут и сброс счётчика. Возвращает текст для чата."""
    limit = setting(chat_id, "warn_limit")
    mute_s = setting(chat_id, "warn_mute_h") * 3600
    n = warns.get((chat_id, uid), 0) + 1
    if n >= limit:
        await storage_set_warns(chat_id, uid, 0)
        try:
            await do_mute(bot, chat_id, uid, mute_s)
            return f"🔇 {label}: {n}/{limit} предупреждений ({reason}). Мут на {fmt_duration(mute_s)}."
        except Exception as e:
            log.warning("автомут не удался: %s", e)
            return f"⚠️ {label}: {n}/{limit} предупреждений ({reason}), но замутить не вышло: проверьте права бота."
    await storage_set_warns(chat_id, uid, n)
    return f"⚠️ {label}: предупреждение {n}/{limit} ({reason})."


async def violation(bot, msg, chat_id: int, user, label: str, reason: str, thread=None):
    """Нарушение: удаляем сообщение, даём предупреждение, дальше обработчики не идут."""
    try:
        await msg.delete()
    except Exception as e:
        log.warning("не удалось удалить сообщение (нужно право «Удалять сообщения»): %s", e)
        raise ApplicationHandlerStop
    text = await apply_warn(bot, chat_id, user.id, label, reason)
    await notice(bot, chat_id, text, thread)
    raise ApplicationHandlerStop


async def on_moderation(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Проверка каждого сообщения в разрешённых чатах: стоп-слова и ссылки."""
    msg, chat, user = update.effective_message, update.effective_chat, update.effective_user
    if not msg or not user or user.is_bot or user.id == 777000:
        return
    if chat.id not in allowed_chats or msg.sender_chat:
        return
    bot = context.bot
    await track_user(user)  # ник -> ID для /ban @юзер; привязка к долгам и чёрному списку
    await check_name_change(bot, chat.id, user, msg.message_thread_id if msg.is_topic_message else None)
    text = msg.text or msg.caption or ""
    if text.startswith("/"):
        return
    label = user_key_label(user)[1]
    thread = msg.message_thread_id if msg.is_topic_message else None

    # стоп-слова
    words = stopwords.get(chat.id)
    if words and text:
        for w in words:
            if re.search(r"(?<!\w)" + re.escape(w) + r"(?!\w)", text, re.IGNORECASE):
                if not await is_exempt(bot, chat.id, user):
                    await violation(bot, msg, chat.id, user, label, "запрещённое слово", thread)
                break

    # ссылки
    if setting(chat.id, "antilink") and has_link(msg) and not link_allowed(chat.id, user):
        if not await is_exempt(bot, chat.id, user):
            await violation(bot, msg, chat.id, user, label, "ссылки запрещены", thread)


# ---------- команды (админы чата и админы бота, в разрешённых чатах)

def resolve_target(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Кого наказываем: @юзер (если бот его видел) / ID / ответ на сообщение -> (id, подпись, остаток) или None."""
    args = list(context.args or [])
    if args:
        a = args[0]
        m = re.fullmatch(r"@(\w{3,})", a)
        if m:
            uid = seen_users.get(m.group(1).lower())
            return (uid, "@" + m.group(1), args[1:]) if uid else None
        if re.fullmatch(r"\d{5,}", a):
            return int(a), f'<a href="tg://user?id={a}">{a}</a>', args[1:]
    r = update.effective_message.reply_to_message
    if r and r.from_user:
        return r.from_user.id, user_key_label(r.from_user)[1], args
    return None


def resolve_keys(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Для списка «ссылки разрешены»: ID знать не обязательно. -> (ключи, подпись) или None."""
    args = list(context.args or [])
    if args:
        a = args[0]
        m = re.fullmatch(r"@(\w{3,})", a)
        if m:
            keys = ["@" + m.group(1).lower()]
            uid = seen_users.get(m.group(1).lower())
            if uid:
                keys.append(f"id:{uid}")
            return keys, "@" + m.group(1)
        if re.fullmatch(r"\d{5,}", a):
            return [f"id:{a}"], f'<a href="tg://user?id={a}">{a}</a>'
    r = update.effective_message.reply_to_message
    if r and r.from_user:
        keys = [f"id:{r.from_user.id}"]
        if r.from_user.username:
            keys.append("@" + r.from_user.username.lower())
        return keys, user_key_label(r.from_user)[1]
    return None


async def fail(msg, e):
    await msg.reply_text(
        "⚠️ Не получилось. Проверьте, что бот — админ группы с правами «Удалять сообщения» "
        f"и «Блокировать пользователей».\nОшибка: {e}"
    )


@admin_only
async def cmd_ban(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    t = resolve_target(update, context)
    if not t:
        await msg.reply_text("Использование: /ban @юзер [время] [причина]\n" + NO_TARGET)
        return
    uid, label, rest = t
    dur, reason = parse_duration(rest)
    if await is_protected(context.bot, chat_id, uid):
        await msg.reply_text("Нельзя: это админ или сам бот.")
        return
    until = datetime.now(timezone.utc) + timedelta(seconds=dur) if dur else None
    try:
        await context.bot.ban_chat_member(chat_id, uid, until_date=until)
    except Exception as e:
        await fail(msg, e)
        return
    text = f"🚫 {label} забанен" + (f" на {fmt_duration(dur)}" if dur else " навсегда") + "."
    if reason:
        text += f"\nПричина: {html.escape(reason)}"
    await msg.reply_text(text, parse_mode=ParseMode.HTML)


@admin_only
async def cmd_unban(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    t = resolve_target(update, context)
    if not t:
        await msg.reply_text("Использование: /unban @юзер (или ID)\n" + NO_TARGET)
        return
    uid, label, _ = t
    try:
        await context.bot.unban_chat_member(chat_id, uid, only_if_banned=True)
    except Exception as e:
        await fail(msg, e)
        return
    await msg.reply_text(f"✅ {label} разбанен.", parse_mode=ParseMode.HTML)


@admin_only
async def cmd_kick(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    t = resolve_target(update, context)
    if not t:
        await msg.reply_text("Использование: /kick @юзер [причина]\n" + NO_TARGET)
        return
    uid, label, rest = t
    if await is_protected(context.bot, chat_id, uid):
        await msg.reply_text("Нельзя: это админ или сам бот.")
        return
    try:
        await context.bot.ban_chat_member(chat_id, uid)
        await context.bot.unban_chat_member(chat_id, uid)  # выгнан, но может вернуться по ссылке
    except Exception as e:
        await fail(msg, e)
        return
    text = f"👢 {label} исключён из чата."
    if rest:
        text += f"\nПричина: {html.escape(' '.join(rest))}"
    await msg.reply_text(text, parse_mode=ParseMode.HTML)


@admin_only
async def cmd_mute(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    t = resolve_target(update, context)
    if not t:
        await msg.reply_text("Использование: /mute @юзер [время: 30м, 2ч, 1д, 1н] [причина]\n" + NO_TARGET)
        return
    uid, label, rest = t
    dur, reason = parse_duration(rest)
    dur = dur or DEFAULT_MUTE_SECONDS
    if await is_protected(context.bot, chat_id, uid):
        await msg.reply_text("Нельзя: это админ или сам бот.")
        return
    try:
        await do_mute(context.bot, chat_id, uid, dur)
    except Exception as e:
        await fail(msg, e)
        return
    text = f"🔇 {label} в муте на {fmt_duration(dur)}."
    if reason:
        text += f"\nПричина: {html.escape(reason)}"
    await msg.reply_text(text, parse_mode=ParseMode.HTML)


@admin_only
async def cmd_unmute(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    t = resolve_target(update, context)
    if not t:
        await msg.reply_text("Использование: /unmute @юзер\n" + NO_TARGET)
        return
    uid, label, _ = t
    try:
        await do_unmute(context.bot, chat_id, uid)
    except Exception as e:
        await fail(msg, e)
        return
    await msg.reply_text(f"🔈 {label} снова может писать.", parse_mode=ParseMode.HTML)


@admin_only
async def cmd_warn(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    t = resolve_target(update, context)
    if not t:
        await msg.reply_text("Использование: /warn @юзер [причина]\n" + NO_TARGET)
        return
    uid, label, rest = t
    if await is_protected(context.bot, chat_id, uid):
        await msg.reply_text("Нельзя: это админ или сам бот.")
        return
    reason = html.escape(" ".join(rest).strip()) or "нарушение правил"
    text = await apply_warn(context.bot, chat_id, uid, label, reason)
    await msg.reply_text(text, parse_mode=ParseMode.HTML)


@admin_only
async def cmd_unwarn(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    t = resolve_target(update, context)
    if not t:
        await msg.reply_text("Использование: /unwarn @юзер\n" + NO_TARGET)
        return
    uid, label, _ = t
    n = max(warns.get((chat_id, uid), 0) - 1, 0)
    await storage_set_warns(chat_id, uid, n)
    await msg.reply_text(
        f"✅ У {label} снято предупреждение: {n}/{setting(chat_id, 'warn_limit')}.", parse_mode=ParseMode.HTML
    )


@admin_only
async def cmd_warns(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    t = resolve_target(update, context)
    if not t:
        await msg.reply_text("Использование: /warns @юзер\n" + NO_TARGET)
        return
    uid, label, _ = t
    await msg.reply_text(
        f"{label}: предупреждений {warns.get((chat_id, uid), 0)}/{setting(chat_id, 'warn_limit')}.",
        parse_mode=ParseMode.HTML,
    )


# ---------- /free: разрешение на ссылки

@admin_only
async def cmd_allowlink(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/free @юзер — человеку можно отправлять ссылки в этом чате."""
    msg, chat_id = update.effective_message, update.effective_chat.id
    t = resolve_keys(update, context)
    if not t:
        await msg.reply_text("Использование: /free @юзер (или ответом на сообщение, или ID)")
        return
    keys, label = t
    ok = await storage_allow_link(chat_id, keys, label)
    text = f"🔗 {label} может отправлять ссылки в этом чате."
    if not ok:
        text += "\n⚠️ Не удалось сохранить в базу."
    await msg.reply_text(text, parse_mode=ParseMode.HTML)


@admin_only
async def cmd_denylink(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/unfree @юзер — снова запретить ссылки."""
    msg, chat_id = update.effective_message, update.effective_chat.id
    t = resolve_keys(update, context)
    if not t:
        await msg.reply_text("Использование: /unfree @юзер (или ответом на сообщение, или ID)")
        return
    keys, label = t
    ok = await storage_deny_link(chat_id, keys)
    text = f"⛔ {label} больше не может отправлять ссылки."
    if not ok:
        text += "\n⚠️ Не удалось удалить из базы."
    await msg.reply_text(text, parse_mode=ParseMode.HTML)


@admin_only
async def cmd_links(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    labels = list(dict.fromkeys(link_allow.get(chat_id, {}).values()))
    if not labels:
        await msg.reply_text("Никому не разрешено. Добавить: /free @юзер")
        return
    lines = [f"{i}. {lb}" for i, lb in enumerate(labels, 1)]
    await msg.reply_text("🔗 Могут отправлять ссылки:\n" + "\n".join(lines), parse_mode=ParseMode.HTML)


@admin_only
async def cmd_antilink(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    arg = context.args[0].lower() if context.args else ""
    if arg in ("on", "вкл", "1", "да"):
        value = True
    elif arg in ("off", "выкл", "0", "нет"):
        value = False
    else:
        state = "включён ✅" if setting(chat_id, "antilink") else "выключен ⛔"
        await msg.reply_text(f"Запрет ссылок: {state}\nИзменить: /antilink on или off (или /settings)")
        return
    ok = await storage_set_setting(chat_id, "antilink", value)
    text = f"Запрет ссылок: {'включён ✅' if value else 'выключен ⛔'}"
    if not ok:
        text += "\n⚠️ Не удалось сохранить в базу."
    await msg.reply_text(text)


# ---------- стоп-слова

@admin_only
async def cmd_addword(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    first = (msg.text or "").split(None, 1)
    word = first[1].strip().lower() if len(first) > 1 else ""
    if not 2 <= len(word) <= 50:
        await msg.reply_text("Использование: /addword слово (от 2 до 50 символов, можно фразу)")
        return
    ok = await storage_add_word(chat_id, word)
    text = f"🤬 Стоп-слово добавлено: «{html.escape(word)}»"
    if not ok:
        text += "\n⚠️ Не удалось сохранить в базу."
    await msg.reply_text(text, parse_mode=ParseMode.HTML)


@admin_only
async def cmd_delword(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    first = (msg.text or "").split(None, 1)
    word = first[1].strip().lower() if len(first) > 1 else ""
    if not word or word not in stopwords.get(chat_id, []):
        await msg.reply_text("Такого стоп-слова нет. Список: /words")
        return
    ok = await storage_del_word(chat_id, word)
    text = f"✅ Стоп-слово удалено: «{html.escape(word)}»"
    if not ok:
        text += "\n⚠️ Не удалось удалить из базы."
    await msg.reply_text(text, parse_mode=ParseMode.HTML)


@admin_only
async def cmd_words(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    words = stopwords.get(chat_id, [])
    if not words:
        await msg.reply_text("Стоп-слов нет. Добавить: /addword слово")
        return
    lines = [f"{i}. {html.escape(w)}" for i, w in enumerate(words, 1)]
    await msg.reply_text(
        "🤬 Стоп-слова (сообщение удаляется, автору предупреждение):\n" + "\n".join(lines),
        parse_mode=ParseMode.HTML,
    )


@admin_only
async def cmd_protect(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    await msg.reply_text(
        "🛡 Защита чата\n" + chat_summary(chat_id)
        + "\n\nМенять настройки удобнее в личке: /settings\nАдмины чата и админы бота под защиту не попадают."
    )


@admin_only
async def cmd_who(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/who @юзер — кто это: ID, текущий ник и прошлые (работает и по старому нику)."""
    msg = update.effective_message
    t = resolve_target(update, context)
    if not t:
        await msg.reply_text("Использование: /who @юзер (или ID, или ответом на сообщение)\n" + NO_TARGET)
        return
    uid, label, _ = t
    rec = known_names.get(uid)
    lines = [f"🔎 {label}", f"ID: <code>{uid}</code>"]
    if rec:
        lines.append(f"Сейчас: {fmt_user(rec['username'])} · {html.escape(rec['name'])}")
        if rec["hist"]:
            lines.append("Раньше (до смены):")
            lines += [f"• {html.escape(h)}" for h in rec["hist"]]
        else:
            lines.append("Смен ника бот не замечал.")
    else:
        lines.append("Бот этого человека ещё не видел в чате.")
    await msg.reply_text("\n".join(lines), parse_mode=ParseMode.HTML)


# ---------- теги

def clean_tag(text: str):
    """Тег / должность: до 16 символов, без эмодзи. -> (текст, ошибка)."""
    text = text.strip()
    if len(text) > 16:
        return None, "Максимум 16 символов."
    if EMOJI_RX.search(text):
        return None, "Эмодзи в тегах нельзя."
    return text, None


@admin_only
async def cmd_tag(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/tag @юзер текст — тег обычному участнику (рядом с ником в чате)."""
    msg, chat_id = update.effective_message, update.effective_chat.id
    t = resolve_target(update, context)
    tag, err = clean_tag(" ".join(t[2])) if t else (None, None)
    if not t or not tag or err:
        await msg.reply_text(
            "Использование: /tag @юзер текст (до 16 символов, без эмодзи; можно ответом на сообщение)\n"
            + (err or "") + ("\n" if err else "") + NO_TARGET
        )
        return
    uid, label, _ = t
    try:
        await tg_api("setChatMemberTag", chat_id=chat_id, user_id=uid, tag=tag)
    except Exception as e:
        await msg.reply_text(
            "⚠️ Не получилось поставить тег. Боту нужны права админа с пунктом «Управление тегами»; "
            "тегом помечаются только обычные участники (для админов: /admintag).\n"
            f"Ошибка: {e}"
        )
        return
    await msg.reply_text(f"🏷 {label}: тег «{html.escape(tag)}».", parse_mode=ParseMode.HTML)


@admin_only
async def cmd_untag(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    t = resolve_target(update, context)
    if not t:
        await msg.reply_text("Использование: /untag @юзер\n" + NO_TARGET)
        return
    uid, label, _ = t
    try:
        await tg_api("setChatMemberTag", chat_id=chat_id, user_id=uid, tag="")
    except Exception as e:
        await msg.reply_text(f"⚠️ Не получилось снять тег: {e}")
        return
    await msg.reply_text(f"🏷 У {label} тег снят.", parse_mode=ParseMode.HTML)


@admin_only
async def cmd_admintag(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """/admintag @юзер текст — должность (тег) админа."""
    msg, chat_id = update.effective_message, update.effective_chat.id
    t = resolve_target(update, context)
    title, err = clean_tag(" ".join(t[2])) if t else (None, None)
    if not t or not title or err:
        await msg.reply_text(
            "Использование: /admintag @юзер текст (до 16 символов, без эмодзи; можно ответом на сообщение)\n"
            + (err or "") + ("\n" if err else "") + NO_TARGET
        )
        return
    uid, label, _ = t
    try:
        await context.bot.set_chat_administrator_custom_title(chat_id, uid, title)
    except Exception as e:
        await msg.reply_text(
            "⚠️ Не получилось. Тег админа ставится только в супергруппах и только админам, "
            "которых назначил сам бот.\n"
            f"Ошибка: {e}"
        )
        return
    await msg.reply_text(f"👑 {label}: тег админа «{html.escape(title)}».", parse_mode=ParseMode.HTML)


@admin_only
async def cmd_unadmintag(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg, chat_id = update.effective_message, update.effective_chat.id
    t = resolve_target(update, context)
    if not t:
        await msg.reply_text("Использование: /unadmintag @юзер\n" + NO_TARGET)
        return
    uid, label, _ = t
    try:
        await context.bot.set_chat_administrator_custom_title(chat_id, uid, "")
    except Exception as e:
        await msg.reply_text(f"⚠️ Не получилось снять тег админа: {e}")
        return
    await msg.reply_text(f"👑 У {label} тег админа снят.", parse_mode=ParseMode.HTML)


# ---------- ночной режим

NIGHT_PRESETS = [("22:00", "06:00"), ("23:00", "07:00"), ("00:00", "08:00"), ("01:00", "09:00")]
TZ_PRESETS = [
    ("Москва", "Europe/Moscow"), ("Киев", "Europe/Kyiv"), ("Минск", "Europe/Minsk"),
    ("Екатеринбург", "Asia/Yekaterinburg"), ("Новосибирск", "Asia/Novosibirsk"),
    ("Владивосток", "Asia/Vladivostok"), ("Алматы", "Asia/Almaty"),
]
NIGHT_TIME_RX = re.compile(r"(\d{1,2}):(\d{2})\s*[-–—]\s*(\d{1,2}):(\d{2})")
OFFSET_RX = re.compile(r"(?:UTC|GMT)?\s*([+-])(\d{1,2})(?::?(\d{2}))?", re.IGNORECASE)


def get_tz(name: str):
    """«Europe/Moscow» или «UTC+3» -> tzinfo (или None, если не понятно)."""
    name = (name or "").strip()
    m = OFFSET_RX.fullmatch(name)
    if m:
        sign = -1 if m.group(1) == "-" else 1
        hours, minutes = int(m.group(2)), int(m.group(3) or 0)
        if hours > 14 or minutes > 59:
            return None
        return timezone(sign * timedelta(hours=hours, minutes=minutes))
    try:
        return ZoneInfo(name)
    except Exception:
        return None


def norm_tz(name: str) -> str:
    m = OFFSET_RX.fullmatch(name.strip())
    if m:
        return f"UTC{m.group(1)}{int(m.group(2))}" + (f":{m.group(3)}" if m.group(3) and m.group(3) != "00" else "")
    return name.strip()


def chat_tz(chat_id: int):
    return (
        get_tz(setting(chat_id, "tz"))
        or get_tz(DEFAULT_TZ)
        or timezone(timedelta(hours=3))
    )


def to_minutes(hhmm: str) -> int:
    h, m = hhmm.split(":")
    return int(h) * 60 + int(m)


def in_night(chat_id: int, now=None) -> bool:
    now = now or datetime.now(timezone.utc)
    local = now.astimezone(chat_tz(chat_id))
    cur = local.hour * 60 + local.minute
    start, end = to_minutes(setting(chat_id, "night_start")), to_minutes(setting(chat_id, "night_end"))
    if start == end:
        return False
    if start < end:
        return start <= cur < end
    return cur >= start or cur < end  # ночь через полночь, например 23:00–07:00


async def night_lock(bot, chat_id: int):
    """Закрывает чат: обычным участникам нельзя писать, админы пишут как обычно."""
    saved = await chat_default_perms(chat_id)
    locked = {
        k: (False if k.startswith("can_send_") or k == "can_add_web_page_previews" else v)
        for k, v in saved.items()
    }
    # сначала запоминаем, как было, чтобы после перезапуска бота вернуть всё обратно
    chat_settings.setdefault(chat_id, {}).update(night_locked=True, night_perms=saved)
    await storage_save_cfg(chat_id)
    try:
        await tg_api("setChatPermissions", chat_id=chat_id, permissions=locked)
    except Exception:
        chat_settings[chat_id].update(night_locked=False, night_perms=None)
        await storage_save_cfg(chat_id)
        raise
    await bot.send_message(
        chat_id, f"🌙 Ночной режим: чат закрыт до {setting(chat_id, 'night_end')}. Админы могут писать."
    )


async def night_unlock(bot, chat_id: int):
    saved = setting(chat_id, "night_perms") or dict(DEFAULT_PERMS)
    await tg_api("setChatPermissions", chat_id=chat_id, permissions=saved)
    chat_settings.setdefault(chat_id, {}).update(night_locked=False, night_perms=None)
    await storage_save_cfg(chat_id)
    await bot.send_message(chat_id, "☀️ Ночной режим закончился — чат снова открыт.")


async def night_check(bot, chat_id: int):
    want = setting(chat_id, "night") and in_night(chat_id)
    locked = setting(chat_id, "night_locked")
    if want and not locked:
        await night_lock(bot, chat_id)
    elif locked and not want:
        await night_unlock(bot, chat_id)


async def night_loop(bot):
    """Каждые 30 секунд проверяет, не пора ли закрыть или открыть чаты."""
    while True:
        for chat_id in list(allowed_chats):
            if not (setting(chat_id, "night") or setting(chat_id, "night_locked")):
                continue
            if time.monotonic() < night_retry_at.get(chat_id, 0):
                continue
            try:
                await night_check(bot, chat_id)
            except Exception as e:
                log.warning("ночной режим в чате %s: %s", chat_id, e)
                night_retry_at[chat_id] = time.monotonic() + 600  # не долбим API, повтор через 10 минут
                try:
                    await bot.send_message(
                        chat_id,
                        "⚠️ Ночной режим не сработал. Боту нужны права админа «Блокировать пользователей» "
                        "(менять права чата).",
                    )
                except Exception:
                    pass
        await asyncio.sleep(30)


# ---------- настройки в личке (/settings)

def btn(text: str, data: str):
    return InlineKeyboardButton(text, callback_data=data)


def onoff(b) -> str:
    return "вкл ✅" if b else "выкл ⛔"


def cfg_title(chat_id: int) -> str:
    return html.escape(allowed_chats.get(chat_id, str(chat_id)))


def mark(b) -> str:
    return "✅" if b else "⛔"


def footer(c: int, back=None) -> list:
    """Нижний ряд кнопок: «Назад» (если есть куда) и «Закрыть»."""
    row = []
    if back:
        row.append(btn("◀️ Назад", f"cfg:{c}:{back}"))
    row.append(btn("✅ Закрыть", f"cfg:{c}:close"))
    return row


def chat_summary(chat_id: int) -> str:
    s = lambda n: setting(chat_id, n)
    people = len(set(link_allow.get(chat_id, {}).values()))
    return (
        f"🔗 Запрет ссылок: {onoff(s('antilink'))} (разрешено людям: {people})\n"
        f"🌙 Ночной режим: {onoff(s('night'))} ({s('night_start')}–{s('night_end')}, {html.escape(str(s('tz')))})\n"
        f"⚠️ Предупреждения: {s('warn_limit')} → мут на {fmt_duration(s('warn_mute_h') * 3600)}\n"
        f"🔤 Запрещённых слов: {len(stopwords.get(chat_id, []))}\n"
        f"🔄 Смена ника: {onoff(s('nickwatch'))}"
    )


def main_menu(chat_id: int):
    c = chat_id
    text = (
        f"⚙️ <b>Группа: {cfg_title(c)}</b>\n\n{chat_summary(c)}\n\n"
        "Выберите один из параметров, который вы хотите изменить."
    )
    rows = [
        [btn(f"🔗 Ссылки {mark(setting(c, 'antilink'))}", f"cfg:{c}:lk"),
         btn(f"🌙 Ночной режим {mark(setting(c, 'night'))}", f"cfg:{c}:nm")],
        [btn("⚠️ Предупреждения", f"cfg:{c}:wm"), btn("🔤 Запрещённые слова", f"cfg:{c}:wd")],
        [btn("🔓 Разрешения", f"cfg:{c}:fr"), btn("👥 Пользователи", f"cfg:{c}:um")],
        [btn(f"🔄 Смена ника {mark(setting(c, 'nickwatch'))}", f"cfg:{c}:nk"), btn("💬 Другой чат", "cfg:0:chats")],
        [btn("✅ Закрыть", f"cfg:{c}:close"), btn("▶️ Другие", f"cfg:{c}:more")],
    ]
    return text, InlineKeyboardMarkup(rows)


def more_menu(chat_id: int):
    c = chat_id
    rows = [
        [btn("📖 Команды защитника", f"cfg:{c}:cm")],
        [btn("🏷 Теги и должности", f"cfg:{c}:tgs")],
        footer(c, "menu"),
    ]
    return f"▶️ <b>Другие параметры: {cfg_title(c)}</b>\n\nВыберите один из параметров.", InlineKeyboardMarkup(rows)


def links_menu(chat_id: int):
    c = chat_id
    on = setting(c, "antilink")
    people = len(set(link_allow.get(c, {}).values()))
    text = (
        f"🔗 <b>Ссылки</b>\nЗапрет ссылок: {onoff(on)}\n\n"
        "Сообщения со ссылками (http, www, t.me, ссылки в тексте и подписях) удаляются, автор получает "
        "предупреждение. Админы и люди из списка «Разрешения» могут отправлять ссылки.\n"
        f"Разрешено людям: {people}"
    )
    rows = [
        [btn(f"Запрет ссылок: {onoff(on)}", f"cfg:{c}:al")],
        [btn("🔓 Разрешения", f"cfg:{c}:fr")],
        footer(c, "menu"),
    ]
    return text, InlineKeyboardMarkup(rows)


def night_menu(chat_id: int):
    c = chat_id
    on, locked = setting(c, "night"), setting(c, "night_locked")
    text = (
        f"🌙 <b>Ночной режим</b>\nСейчас: {onoff(on)}\n"
        f"Время: {setting(c, 'night_start')}–{setting(c, 'night_end')} ({html.escape(str(setting(c, 'tz')))})\n"
        f"Чат сейчас: {'закрыт 🔒' if locked else 'открыт'}\n\n"
        "В ночное время обычным участникам нельзя писать, админы пишут как обычно. "
        "Утром бот возвращает права чата как были.\nБоту нужно право админа «Блокировать пользователей»."
    )
    rows = [
        [btn(f"Ночной режим: {onoff(on)}", f"cfg:{c}:nt")],
        [btn("🕒 Время ночи", f"cfg:{c}:ntm"), btn("🌍 Часовой пояс", f"cfg:{c}:tzm")],
        footer(c, "menu"),
    ]
    return text, InlineKeyboardMarkup(rows)


def night_time_menu(chat_id: int):
    cur = (setting(chat_id, "night_start"), setting(chat_id, "night_end"))
    rows = []
    for i, (a, b) in enumerate(NIGHT_PRESETS):
        rows.append([btn(("✓ " if (a, b) == cur else "") + f"{a} – {b}", f"cfg:{chat_id}:nts:{i}")])
    rows.append([btn("✏️ Своё время", f"cfg:{chat_id}:ntc")])
    rows.append(footer(chat_id, "nm"))
    text = (
        f"🕒 <b>Время ночного режима</b>\nСейчас: {cur[0]}–{cur[1]} ({html.escape(str(setting(chat_id, 'tz')))})"
    )
    return text, InlineKeyboardMarkup(rows)


def tz_menu(chat_id: int):
    cur = setting(chat_id, "tz")
    rows = []
    for i in range(0, len(TZ_PRESETS), 2):
        row = []
        for j in (i, i + 1):
            if j < len(TZ_PRESETS):
                name, tz = TZ_PRESETS[j]
                row.append(btn(("✓ " if tz == cur else "") + name, f"cfg:{chat_id}:tz:{j}"))
        rows.append(row)
    rows.append([btn("✏️ Свой пояс", f"cfg:{chat_id}:tzc")])
    rows.append(footer(chat_id, "nm"))
    return f"🌍 <b>Часовой пояс</b>\nСейчас: {html.escape(str(cur))}", InlineKeyboardMarkup(rows)


def warn_menu(chat_id: int):
    lim, hrs = setting(chat_id, "warn_limit"), setting(chat_id, "warn_mute_h")
    limits = [btn(("✓ " if n == lim else "") + str(n), f"cfg:{chat_id}:wl:{n}") for n in (2, 3, 5)]
    mutes = [btn(("✓ " if h == hrs else "") + fmt_duration(h * 3600), f"cfg:{chat_id}:wh:{h}") for h in (1, 6, 24, 72)]
    rows = [limits, mutes, footer(chat_id, "menu")]
    text = (
        "⚠️ <b>Предупреждения</b>\n"
        f"Сколько предупреждений до мута: {lim}\nНа сколько мут: {fmt_duration(hrs * 3600)}\n\n"
        "Первая строка кнопок — лимит, вторая — длительность мута."
    )
    return text, InlineKeyboardMarkup(rows)


def words_menu(chat_id: int):
    words = stopwords.get(chat_id, [])
    rows = [[btn(f"❌ {w[:30]}", f"cfg:{chat_id}:dw:{i}")] for i, w in enumerate(words[:30])]
    rows.append([btn("➕ Добавить слово", f"cfg:{chat_id}:aw")])
    rows.append(footer(chat_id, "menu"))
    text = "🔤 <b>Запрещённые слова</b>\n" + (
        "Нажмите на слово, чтобы удалить.\n" if words else "Пока пусто.\n"
    ) + "Сообщение с таким словом удаляется, автор получает предупреждение."
    return text, InlineKeyboardMarkup(rows)


def free_labels(chat_id: int) -> list:
    return list(dict.fromkeys(link_allow.get(chat_id, {}).values()))


def free_menu(chat_id: int):
    labels = free_labels(chat_id)
    rows = [[btn(f"❌ {re.sub('<[^>]+>', '', lb)[:30]}", f"cfg:{chat_id}:uf:{i}")] for i, lb in enumerate(labels[:30])]
    rows.append(footer(chat_id, "menu"))
    text = "🔓 <b>Разрешения: кому можно ссылки</b>\n" + (
        "Нажмите на человека, чтобы убрать разрешение." if labels else "Пока никому."
    ) + "\nДобавить: в чате команда /free @юзер (или ответом на сообщение)."
    return text, InlineKeyboardMarkup(rows)


def warned_users(chat_id: int) -> list:
    items = [(uid, n) for (cid, uid), n in warns.items() if cid == chat_id and n > 0]
    items.sort(key=lambda x: (-x[1], x[0]))
    return items[:20]


def user_name(uid: int) -> str:
    for name, i in seen_users.items():
        if i == uid:
            return "@" + name
    return str(uid)


def users_menu(chat_id: int):
    items = warned_users(chat_id)
    lim = setting(chat_id, "warn_limit")
    rows = [[btn(f"❌ {user_name(uid)} — {n}/{lim}", f"cfg:{chat_id}:uw:{i}")] for i, (uid, n) in enumerate(items)]
    rows.append(footer(chat_id, "menu"))
    text = (
        "👥 <b>Пользователи</b>\n"
        + ("С предупреждениями (нажмите, чтобы снять все):" if items else "Сейчас ни у кого нет предупреждений.")
        + "\n\nБан, мут и предупреждения выдаются в чате командами (ответом на сообщение или @юзер): "
        "/ban, /unban, /kick, /mute, /unmute, /warn, /unwarn, /warns."
    )
    return text, InlineKeyboardMarkup(rows)


def commands_menu(chat_id: int):
    text = (
        "📖 <b>Команды защитника</b> (админы чата, в группе)\n\n"
        "🔓 /free @юзер — разрешить ссылки, /unfree — запретить, /links — список\n"
        "🚫 /ban, /unban, /kick @юзер [время] [причина]\n"
        "🔇 /mute @юзер [30м, 2ч, 1д, 1н], /unmute\n"
        "⚠️ /warn, /unwarn, /warns @юзер\n"
        "🔤 /addword, /delword, /words\n"
        "🏷 /tag, /untag, /admintag, /unadmintag\n"
        "🔎 /who @юзер — кто это: ID и прошлые ники\n"
        "⚙️ /settings — это меню\n\n"
        "@юзер работает, если бот уже видел сообщения человека; иначе ответьте командой на его сообщение или укажите ID."
    )
    return text, InlineKeyboardMarkup([footer(chat_id, "more")])


def tags_menu(chat_id: int):
    text = (
        "🏷 <b>Теги и должности</b>\n\n"
        "/tag @юзер текст — тег обычному участнику, /untag — снять. Боту нужно право админа «Управление тегами».\n"
        "/admintag @юзер текст — должность админа, /unadmintag — снять. Работает только в супергруппах и только "
        "для админов, которых назначил сам бот.\n\n"
        "Текст до 16 символов, без эмодзи. Можно ответом на сообщение."
    )
    return text, InlineKeyboardMarkup([footer(chat_id, "more")])


async def can_manage(bot, chat_id: int, user) -> bool:
    """Настройки чата: админы бота и админы этого чата."""
    if chat_id not in allowed_chats:
        return False
    if user.id in ADMIN_IDS:
        return True
    try:
        member = await bot.get_chat_member(chat_id, user.id)
        return member.status in (ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER)
    except Exception:
        return False


async def chats_menu(bot, user):
    chats = [cid for cid in list(allowed_chats) if await can_manage(bot, cid, user)]
    if not chats:
        return "У вас нет прав админа ни в одном из чатов, где работает бот.", None
    rows = [[btn(f"💬 {allowed_chats[cid][:40]}", f"cfg:{cid}:menu")] for cid in chats[:50]]
    return "⚙️ <b>Настройки</b>\nВыберите чат:", InlineKeyboardMarkup(rows)


async def show_menu(q, text, markup):
    try:
        await q.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)
    except BadRequest as e:
        if "not modified" not in str(e).lower():
            raise


async def cmd_settings(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat, msg, user = update.effective_chat, update.effective_message, update.effective_user
    if chat.type == ChatType.PRIVATE:
        text, markup = await chats_menu(context.bot, user)
        await msg.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=markup)
        return
    if chat.type not in (ChatType.GROUP, ChatType.SUPERGROUP) or chat.id not in allowed_chats:
        return
    if not await is_admin(update, context):
        return
    link = f"https://t.me/{context.bot.username}?start=cfg_{chat.id}"
    await msg.reply_text(
        "Настройки этого чата открываются в личке с ботом.",
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⚙️ Открыть настройки", url=link)]]),
    )


async def on_cfg(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    m = re.fullmatch(r"cfg:(-?\d+):(\w+)(?::(\d+))?", q.data or "")
    if not m:
        await q.answer()
        return
    chat_id, action, arg = int(m.group(1)), m.group(2), m.group(3)
    user, bot = q.from_user, context.bot

    if action == "chats":
        text, markup = await chats_menu(bot, user)
        await q.answer()
        await show_menu(q, text, markup)
        return
    if not await can_manage(bot, chat_id, user):
        await q.answer("Нет доступа к настройкам этого чата.", show_alert=True)
        return
    if action == "close":
        await q.answer()
        try:
            await q.message.delete()
        except Exception:
            await show_menu(q, "Настройки закрыты. Открыть снова: /settings", None)
        return

    note = None
    view = main_menu
    if action == "nk":
        await storage_set_setting(chat_id, "nickwatch", not setting(chat_id, "nickwatch"))
    elif action == "lk":
        view = links_menu
    elif action == "al":
        await storage_set_setting(chat_id, "antilink", not setting(chat_id, "antilink"))
        view = links_menu
    elif action == "nm":
        view = night_menu
    elif action == "nt":
        await storage_set_setting(chat_id, "night", not setting(chat_id, "night"))
        try:
            await night_check(bot, chat_id)
        except Exception as e:
            note = f"Не удалось закрыть/открыть чат: нужны права админа «Блокировать пользователей». ({e})"
        view = night_menu
    elif action == "ntm":
        view = night_time_menu
    elif action == "nts" and arg is not None and int(arg) < len(NIGHT_PRESETS):
        start, end = NIGHT_PRESETS[int(arg)]
        chat_settings.setdefault(chat_id, {}).update(night_start=start, night_end=end)
        await storage_save_cfg(chat_id)
        try:
            await night_check(bot, chat_id)
        except Exception as e:
            note = f"Не удалось закрыть/открыть чат: {e}"
        view = night_time_menu
    elif action == "ntc":
        dm_input[user.id] = {"chat_id": chat_id, "action": "nighttime", "ts": time.monotonic()}
        await q.answer()
        await show_menu(
            q, "✏️ Отправьте время ночного режима сообщением, например: <code>23:30-07:00</code>\n"
            "(или «отмена»)", InlineKeyboardMarkup([[btn("◀️ Назад", f"cfg:{chat_id}:ntm")]]),
        )
        return
    elif action == "tzm":
        view = tz_menu
    elif action == "tz" and arg is not None and int(arg) < len(TZ_PRESETS):
        await storage_set_setting(chat_id, "tz", TZ_PRESETS[int(arg)][1])
        try:
            await night_check(bot, chat_id)
        except Exception as e:
            note = f"Не удалось закрыть/открыть чат: {e}"
        view = tz_menu
    elif action == "tzc":
        dm_input[user.id] = {"chat_id": chat_id, "action": "tz", "ts": time.monotonic()}
        await q.answer()
        await show_menu(
            q, "✏️ Отправьте часовой пояс сообщением: например <code>Asia/Tashkent</code> или <code>UTC+5</code>\n"
            "(или «отмена»)", InlineKeyboardMarkup([[btn("◀️ Назад", f"cfg:{chat_id}:tzm")]]),
        )
        return
    elif action == "wm":
        view = warn_menu
    elif action == "wl" and arg in ("2", "3", "5"):
        await storage_set_setting(chat_id, "warn_limit", int(arg))
        view = warn_menu
    elif action == "wh" and arg in ("1", "6", "24", "72"):
        await storage_set_setting(chat_id, "warn_mute_h", int(arg))
        view = warn_menu
    elif action == "wd":
        view = words_menu
    elif action == "dw" and arg is not None:
        words = stopwords.get(chat_id, [])
        if int(arg) < len(words):
            await storage_del_word(chat_id, words[int(arg)])
        view = words_menu
    elif action == "aw":
        dm_input[user.id] = {"chat_id": chat_id, "action": "addword", "ts": time.monotonic()}
        await q.answer()
        await show_menu(
            q, "✏️ Отправьте стоп-слово или фразу сообщением (или «отмена»).",
            InlineKeyboardMarkup([[btn("◀️ Назад", f"cfg:{chat_id}:wd")]]),
        )
        return
    elif action == "fr":
        view = free_menu
    elif action == "uf" and arg is not None:
        labels = free_labels(chat_id)
        if int(arg) < len(labels):
            keys = [k for k, lb in link_allow.get(chat_id, {}).items() if lb == labels[int(arg)]]
            await storage_deny_link(chat_id, keys)
        view = free_menu
    elif action == "um":
        view = users_menu
    elif action == "uw" and arg is not None:
        items = warned_users(chat_id)
        if int(arg) < len(items):
            await storage_set_warns(chat_id, items[int(arg)][0], 0)
        view = users_menu
    elif action == "more":
        view = more_menu
    elif action == "cm":
        view = commands_menu
    elif action == "tgs":
        view = tags_menu
    elif action != "menu":
        await q.answer()
        return

    text, markup = view(chat_id)
    if note:
        text += f"\n\n⚠️ {html.escape(note)}"
    await q.answer()
    await show_menu(q, text, markup)


async def on_private_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Ответ админа на вопрос меню настроек (своё время, пояс, стоп-слово). Иначе бот молчит."""
    msg, user = update.effective_message, update.effective_user
    st = dm_input.get(user.id)
    if not st:
        return
    if time.monotonic() - st["ts"] > 600:
        dm_input.pop(user.id, None)
        return
    chat_id, action = st["chat_id"], st["action"]
    text = (msg.text or "").strip()
    if text.lower() in ("отмена", "cancel"):
        dm_input.pop(user.id, None)
        await msg.reply_text("Отменено.")
        return
    if not await can_manage(context.bot, chat_id, user):
        dm_input.pop(user.id, None)
        return
    note = None
    if action == "addword":
        word = text.lower()
        if not 2 <= len(word) <= 50:
            await msg.reply_text("Нужно от 2 до 50 символов. Попробуйте ещё раз или напишите «отмена».")
            return
        await storage_add_word(chat_id, word)
    elif action == "nighttime":
        m = NIGHT_TIME_RX.fullmatch(text)
        if not m or int(m.group(1)) > 23 or int(m.group(3)) > 23 or int(m.group(2)) > 59 or int(m.group(4)) > 59:
            await msg.reply_text("Не понял. Формат: 23:30-07:00. Попробуйте ещё раз или напишите «отмена».")
            return
        start = f"{int(m.group(1)):02d}:{m.group(2)}"
        end = f"{int(m.group(3)):02d}:{m.group(4)}"
        chat_settings.setdefault(chat_id, {}).update(night_start=start, night_end=end)
        await storage_save_cfg(chat_id)
    elif action == "tz":
        if get_tz(text) is None:
            await msg.reply_text("Не знаю такой пояс. Примеры: Europe/Moscow, Asia/Tashkent, UTC+5. Или «отмена».")
            return
        await storage_set_setting(chat_id, "tz", norm_tz(text))
    dm_input.pop(user.id, None)
    if action in ("nighttime", "tz"):
        try:
            await night_check(context.bot, chat_id)
        except Exception as e:
            note = f"Не удалось закрыть/открыть чат: {e}"
    view = words_menu if action == "addword" else night_menu
    mtext, markup = view(chat_id)
    if note:
        mtext += f"\n\n⚠️ {html.escape(note)}"
    await msg.reply_text("✅ Готово.\n\n" + mtext, parse_mode=ParseMode.HTML, reply_markup=markup)


# ---------------------------------------------------------------- управление чатами (лс)

def bot_admin_private(func):
    @functools.wraps(func)
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if update.effective_chat.type != ChatType.PRIVATE:
            return
        if not is_bot_admin(update.effective_user):
            await update.effective_message.reply_text(no_access_text(update.effective_user))
            return
        await func(update, context)

    return wrapper


async def cmd_addchat(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat, user, msg = update.effective_chat, update.effective_user, update.effective_message
    if not is_bot_admin(user):
        if chat.type == ChatType.PRIVATE:
            await msg.reply_text(no_access_text(user))
        return
    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP):
        target = chat  # /addchat прямо в группе добавляет эту группу
    elif chat.type == ChatType.PRIVATE:
        if not context.args:
            await msg.reply_text(
                "Использование: /addchat -1001234567890\n"
                "(или @юзернейм публичной группы; можно также написать /addchat прямо в группе)"
            )
            return
        arg = context.args[0]
        ref = int(arg) if re.fullmatch(r"-?\d+", arg) else arg
        try:
            target = await context.bot.get_chat(ref)
        except Exception:
            await msg.reply_text("Не нашёл чат. Сначала добавьте бота в группу.")
            return
        if target.type not in (ChatType.GROUP, ChatType.SUPERGROUP):
            await msg.reply_text("Это не группа.")
            return
    else:
        return
    title = target.title or str(target.id)
    ok = await storage_add_chat(target.id, title)
    text = f"✅ Добавлен: {title} ({target.id})"
    if not ok:
        text += "\n⚠️ Не удалось сохранить в базу, после перезапуска чат пропадёт."
    await msg.reply_text(text)


@bot_admin_private
async def cmd_chats(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not allowed_chats:
        await update.message.reply_text("Список чатов пуст. Добавьте: /addchat id")
        return
    lines = [f"{i}. {title} ({cid})" for i, (cid, title) in enumerate(allowed_chats.items(), 1)]
    await update.message.reply_text("Разрешённые чаты:\n" + "\n".join(lines) + "\n\nУдалить: /delchat номер или id")


@bot_admin_private
async def cmd_delchat(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.message
    if not context.args or not re.fullmatch(r"-?\d+", context.args[0]):
        await msg.reply_text("Использование: /delchat номер_из_списка или id чата")
        return
    n = int(context.args[0])
    if n in allowed_chats:
        chat_id = n
    elif 1 <= n <= len(allowed_chats):
        chat_id = list(allowed_chats)[n - 1]
    else:
        await msg.reply_text("Такого чата нет в списке. Смотрите /chats")
        return
    title = allowed_chats[chat_id]
    ok = await storage_del_chat(chat_id)
    games.pop(chat_id, None)
    pending.difference_update({p for p in pending if p[0] == chat_id})
    text = f"🗑 Удалён: {title} ({chat_id})"
    if not ok:
        text += "\n⚠️ Не удалось удалить из базы."
    await msg.reply_text(text)


# ---------------------------------------------------------------- кнопка

async def on_join(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    chat_id = q.message.chat_id
    if chat_id not in allowed_chats:
        await q.answer()
        return
    game = games.get(chat_id)
    if not game or q.message.message_id != game["msg_id"]:
        await q.answer("Эта игра уже завершена.", show_alert=True)
        return
    if game["closed"]:
        await q.answer("Список закрыт.", show_alert=True)
        return
    user = q.from_user
    key, label = user_key_label(user)
    await track_user(user)
    if black_entry(key, user.id):
        await q.answer(black_message(label, True), show_alert=True)
        return

    if game["type"] == "roulette":
        lim = roulette_add(game, key, label)
        if lim:
            await q.answer("Вы уже в списке." if lim == 1 else f"Лимит записей: {lim}.", show_alert=True)
            return
        await q.answer("Вы записаны ✅")
        await refresh(context.bot, chat_id, game)
        return

    # бинго
    if key in game["banned"]:
        await q.answer("Вы исключены из игры.", show_alert=True)
        return
    err = bingo_prompt_error(game, key)
    if err:
        await q.answer(err, show_alert=True)
        return
    await q.answer()
    await prompt_numbers(context, chat_id, user, game)


# ---------------------------------------------------------------- сообщения в группе

async def on_group_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if update.effective_chat.id not in allowed_chats:
        return
    game = games.get(update.effective_chat.id)
    if not game or not msg or not msg.text or msg.from_user is None:
        return  # игры нет — бот молчит
    text = msg.text.strip()
    if game["type"] == "roulette":
        await roulette_text(update, context, game, text)
    else:
        await bingo_text(update, context, game, text)


async def roulette_text(update, context, game, text):
    m = re.fullmatch(r"@(\w{3,})?", text)
    if not m:
        return
    msg = update.effective_message
    chat_id = update.effective_chat.id
    if game["closed"]:
        await msg.reply_text("Список закрыт.")
        return
    name = m.group(1)
    if name:
        key, label = "@" + name.lower(), "@" + name
    else:
        key, label = user_key_label(msg.from_user)
    if black_entry(key, self_uid(msg.from_user, key)):
        own = key == user_key_label(msg.from_user)[0]
        await msg.reply_text(black_message(label, own), parse_mode=ParseMode.HTML)
        return
    lim = roulette_add(game, key, label)
    if lim:
        txt = f"{label} уже в списке." if lim == 1 else f"{label}: лимит записей ({lim}) исчерпан."
        await msg.reply_text(txt, parse_mode=ParseMode.HTML)
        return
    await refresh(context.bot, chat_id, game)


async def bingo_text(update, context, game, text):
    msg = update.effective_message
    chat_id = update.effective_chat.id
    user = msg.from_user

    # «бинго» — проверка выигрыша
    if re.fullmatch(r"(бинго|bingo)\W*", text.lower()):
        await bingo_claim(update, context, game)
        return

    tokens = text.split()
    if not tokens:
        return
    uid = (chat_id, user.id)
    reply = msg.reply_to_message
    to_bot = bool(reply and reply.from_user and reply.from_user.id == context.bot.id)
    plausible = len(tokens) in (BINGO_COUNT, BINGO_COUNT + 1)

    # числа без «@»: после кнопки или ответом на сообщение бота
    if all(is_num(t) for t in tokens) and (uid in pending or to_bot):
        key, label = user_key_label(user)
        if black_entry(key, user.id):
            pending.discard(uid)
            await msg.reply_text(black_message(label, True), parse_mode=ParseMode.HTML)
            return
        top = is_top(game, key)
        if game["closed"]:
            pending.discard(uid)
            if plausible:
                await msg.reply_text("Список закрыт.")
            return
        nums = parse_numbers(tokens, top)
        if nums is None:
            if uid in pending or plausible:
                await msg.reply_text(numbers_hint(top))
            return
        if key in game["banned"]:
            pending.discard(uid)
            await msg.reply_text("Вы исключены из игры.")
            return
        err = bingo_limit_error(game, key, nums)
        if err:
            pending.discard(uid)
            await msg.reply_text(f"{label}: {err}", parse_mode=ParseMode.HTML)
            return
        register_bingo(game, key, label, nums)
        pending.discard(uid)
        await refresh(context.bot, chat_id, game)
        return

    # @ 1 2 3 4 5  и  @юзер 1 2 3 4 5
    if not re.fullmatch(r"@\w*", tokens[0]):
        return
    rest = tokens[1:]
    if rest and not all(is_num(t) for t in rest):
        return  # обычное сообщение с упоминанием — не трогаем
    name = tokens[0][1:]

    if game["closed"]:
        await msg.reply_text("Список закрыт.")
        return

    if name:
        key, label = "@" + name.lower(), "@" + name
    else:
        key, label = user_key_label(user)

    if not rest:
        if name:
            return  # "@юзер" без чисел игнорируем
        if black_entry(key, user.id):
            await msg.reply_text(black_message(label, True), parse_mode=ParseMode.HTML)
            return
        if key in game["banned"]:
            await msg.reply_text("Вы исключены из игры.")
            return
        err = bingo_prompt_error(game, key)
        if err:
            await msg.reply_text(err)
            return
        await prompt_numbers(context, chat_id, user, game)
        return

    if black_entry(key, self_uid(user, key)):
        own = key == user_key_label(user)[0]
        await msg.reply_text(black_message(label, own), parse_mode=ParseMode.HTML)
        return
    top = is_top(game, key)
    nums = parse_numbers(rest, top)
    if nums is None:
        await msg.reply_text(numbers_hint(top))
        return
    if key in game["banned"]:
        await msg.reply_text("Этот игрок исключён из игры.")
        return
    err = bingo_limit_error(game, key, nums)
    if err:
        await msg.reply_text(f"{label}: {err}", parse_mode=ParseMode.HTML)
        return
    register_bingo(game, key, label, nums)
    await refresh(context.bot, chat_id, game)


async def bingo_claim(update, context, game):
    """Игрок написал «бинго»: проверяем, выпали ли его числа (все 5, а у карточки из 6 — любые 5)."""
    msg = update.effective_message
    chat_id = update.effective_chat.id
    user = update.effective_user
    if user is None:
        return
    key, _ = user_key_label(user)
    if not game["closed"]:
        await msg.reply_text("Список ещё не закрыт — рано кричать «бинго» 🙂")
        return
    if key in game["banned"]:
        await msg.reply_text("Вы исключены из игры.")
        return
    player = game["players"].get(key)
    if not player:
        await msg.reply_text("Вас нет в списке.")
        return
    drawn = game["drawn_set"]
    hits = sum(1 for n in player["numbers"] if n in drawn)
    if hits >= BINGO_COUNT:
        marks = " ".join(f"{n}{'✅' if n in drawn else '❌'}" for n in player["numbers"])
        await msg.reply_text(
            f"{player['label']}: {marks}\n⏳ Ожидайте проверки администратора.",
            parse_mode=ParseMode.HTML,
        )
        return
    player["strikes"] += 1
    if player["strikes"] >= MAX_STRIKES:
        del game["players"][key]
        game["banned"].add(key)
        await msg.reply_text(
            f"{player['label']}, не обманывайте! Фальш {MAX_STRIKES}/{MAX_STRIKES} — "
            f"вы исключены из игры. 🚫",
            parse_mode=ParseMode.HTML,
        )
    else:
        await msg.reply_text(
            f"{player['label']}, не обманывайте! Фальш {player['strikes']}/{MAX_STRIKES}",
            parse_mode=ParseMode.HTML,
        )
    await refresh(context.bot, chat_id, game)


# ---------------------------------------------------------------- веб-сервер и самопинг для Render

async def health(request):
    return web.Response(text="OK")


async def self_ping():
    if not SELF_URL:
        log.info("RENDER_EXTERNAL_URL не задан, самопинг выключен")
        return
    async with httpx.AsyncClient(timeout=20) as client:
        while True:
            await asyncio.sleep(PING_INTERVAL)
            try:
                r = await client.get(SELF_URL)
                log.info("self-ping %s", r.status_code)
            except Exception as e:
                log.warning("self-ping failed: %s", e)


async def main():
    if not ADMIN_IDS:
        log.warning("ADMIN_IDS не задан — /addchat и /top будут недоступны")
    app = Application.builder().token(TOKEN).build()

    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("games", cmd_games))
    app.add_handler(CommandHandler("bingo", cmd_bingo))
    app.add_handler(CommandHandler("close", cmd_close))
    app.add_handler(CommandHandler("random", cmd_random))
    app.add_handler(CommandHandler("line", cmd_line))
    app.add_handler(CommandHandler("check", cmd_check))
    app.add_handler(CommandHandler("stopgame", cmd_stopgame))
    app.add_handler(CommandHandler("vtop", cmd_vtop))
    app.add_handler(CommandHandler("top", cmd_top))
    app.add_handler(CommandHandler("untop", cmd_untop))
    app.add_handler(CommandHandler("tops", cmd_tops))
    app.add_handler(CommandHandler("adolg", cmd_adolg))
    app.add_handler(CommandHandler("ddolg", cmd_ddolg))
    app.add_handler(CommandHandler("dolg", cmd_dolg))
    app.add_handler(CommandHandler("ablack", cmd_ablack))
    app.add_handler(CommandHandler("dblack", cmd_dblack))
    app.add_handler(CommandHandler("black", cmd_black))
    app.add_handler(CommandHandler("atrigger", cmd_atrigger))
    app.add_handler(CommandHandler("dtrigger", cmd_dtrigger))
    app.add_handler(CommandHandler("triggers", cmd_triggers))
    app.add_handler(CommandHandler("ban", cmd_ban))
    app.add_handler(CommandHandler("unban", cmd_unban))
    app.add_handler(CommandHandler("kick", cmd_kick))
    app.add_handler(CommandHandler("mute", cmd_mute))
    app.add_handler(CommandHandler("unmute", cmd_unmute))
    app.add_handler(CommandHandler("warn", cmd_warn))
    app.add_handler(CommandHandler("unwarn", cmd_unwarn))
    app.add_handler(CommandHandler("warns", cmd_warns))
    app.add_handler(CommandHandler("free", cmd_allowlink))
    app.add_handler(CommandHandler(["unfree", "denylink"], cmd_denylink))
    app.add_handler(CommandHandler("links", cmd_links))
    app.add_handler(CommandHandler("antilink", cmd_antilink))
    app.add_handler(CommandHandler("addword", cmd_addword))
    app.add_handler(CommandHandler("delword", cmd_delword))
    app.add_handler(CommandHandler("words", cmd_words))
    app.add_handler(CommandHandler("protect", cmd_protect))
    app.add_handler(CommandHandler("who", cmd_who))
    app.add_handler(CommandHandler("settings", cmd_settings))
    app.add_handler(CommandHandler("tag", cmd_tag))
    app.add_handler(CommandHandler("untag", cmd_untag))
    app.add_handler(CommandHandler("admintag", cmd_admintag))
    app.add_handler(CommandHandler("unadmintag", cmd_unadmintag))
    app.add_handler(CommandHandler("addchat", cmd_addchat))
    app.add_handler(CommandHandler("delchat", cmd_delchat))
    app.add_handler(CommandHandler("chats", cmd_chats))
    app.add_handler(CallbackQueryHandler(on_join, pattern="^join$"))
    app.add_handler(CallbackQueryHandler(on_game_choice, pattern="^game:"))
    app.add_handler(CallbackQueryHandler(on_trigger_choice, pattern="^tg:"))
    app.add_handler(CallbackQueryHandler(on_cfg, pattern="^cfg:"))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND & filters.ChatType.PRIVATE, on_private_text))
    app.add_handler(
        MessageHandler(filters.TEXT & ~filters.COMMAND & filters.ChatType.GROUPS, on_group_text)
    )

    # триггеры — отдельная группа обработчиков, работает параллельно с играми
    app.add_handler(
        MessageHandler(
            (filters.TEXT | filters.CAPTION) & ~filters.COMMAND & filters.ChatType.GROUPS,
            on_trigger,
        ),
        group=1,
    )

    # защитник: проверка флуда, стоп-слов и ссылок — раньше игр и триггеров
    app.add_handler(MessageHandler(filters.ChatType.GROUPS, on_moderation), group=-1)

    # веб-сервер поднимаем первым, чтобы Render сразу увидел открытый порт
    web_app = web.Application()
    web_app.router.add_get("/", health)
    web_app.router.add_get("/health", health)
    runner = web.AppRunner(web_app)
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", PORT).start()

    await init_storage()

    async with app:
        await app.start()
        await app.updater.start_polling(drop_pending_updates=True)
        ping_task = asyncio.create_task(self_ping())
        night_task = asyncio.create_task(night_loop(app.bot))
        log.info("Бот запущен")
        try:
            await asyncio.Event().wait()
        finally:
            ping_task.cancel()
            night_task.cancel()
            await app.updater.stop()
            await app.stop()
            await runner.cleanup()
            if pool is not None:
                await pool.close()


if __name__ == "__main__":
    asyncio.run(main())
