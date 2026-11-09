import asyncio
import functools
import html
import json
import logging
import os
import random
import re
import urllib.parse

import asyncpg
import httpx
from aiohttp import web
from telegram import ForceReply, InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ChatMemberStatus, ChatType, ParseMode
from telegram.error import BadRequest
from telegram.ext import (
    Application,
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

# ---------------------------------------------------------------- состояние

# разрешённые чаты: chat_id -> название (кэш, источник правды — база)
allowed_chats: dict[int, str] = {}
# постоянные топы (/top): ключ игрока -> подпись
perm_tops: dict[str, str] = {}
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
    except FileNotFoundError:
        pass
    except Exception as e:
        log.warning("не удалось прочитать %s: %s", DATA_FILE, e)


def save_file():
    try:
        with open(DATA_FILE, "w", encoding="utf-8") as f:
            json.dump(
                {"chats": {str(k): v for k, v in allowed_chats.items()}, "tops": perm_tops},
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
                " user_key TEXT PRIMARY KEY, label TEXT NOT NULL DEFAULT '')"
            )
            for r in await c.fetch("SELECT chat_id, title FROM chats"):
                allowed_chats[r["chat_id"]] = r["title"]
            for r in await c.fetch("SELECT user_key, label FROM tops"):
                perm_tops[r["user_key"]] = r["label"]
        log.info("База подключена: чатов %d, топов %d", len(allowed_chats), len(perm_tops))
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
    for i, p in enumerate(players.values(), 1):
        line = f"{i}. {p['label']}"
        if game["type"] == "bingo":
            nums = " ".join(f"{n}✅" if n in drawn else str(n) for n in p["numbers"])
            line += f" — {nums}"
            if p["strikes"]:
                line += f" ⚠️ {p['strikes']}/{MAX_STRIKES}"
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


def is_bot_admin(user) -> bool:
    return user is not None and user.id in ADMIN_IDS


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
    await update.message.reply_text(
        "Привет! Я бот для игр в группе: рулетка и бинго. "
        "Игры запускают админы группы командами /roulette и /bingo."
    )


async def start_game(update: Update, kind: str):
    chat_id = update.effective_chat.id
    if chat_id in games:
        await update.effective_message.reply_text("Игра уже идёт. Завершить: /stopgame")
        return
    game = {
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
    games[chat_id] = game
    m = await update.effective_message.reply_text(
        render(game), parse_mode=ParseMode.HTML, reply_markup=keyboard(game)
    )
    game["msg_id"] = m.message_id


@admin_only
async def cmd_roulette(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await start_game(update, "roulette")


async def cmd_bingo(update: Update, context: ContextTypes.DEFAULT_TYPE):
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
    if not await is_admin(update, context):
        await update.effective_message.reply_text("Команда только для админов.")
        return
    await start_game(update, "bingo")


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
        f"🎲 Выпало число <b>{n}</b> из {len(players)} — {players[n - 1]['label']}",
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
    if not is_bot_admin(update.effective_user):
        return
    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP) and chat.id not in allowed_chats:
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
    if not is_bot_admin(update.effective_user):
        return
    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP) and chat.id not in allowed_chats:
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
    if not is_bot_admin(update.effective_user):
        return
    if chat.type in (ChatType.GROUP, ChatType.SUPERGROUP) and chat.id not in allowed_chats:
        return
    if not perm_tops:
        await msg.reply_text("Постоянных топов пока нет. Добавить: /top @юзер")
        return
    lines = [f"{i}. {label}" for i, label in enumerate(perm_tops.values(), 1)]
    await msg.reply_text("⭐ Постоянные топы:\n" + "\n".join(lines), parse_mode=ParseMode.HTML)


# ---------------------------------------------------------------- управление чатами (лс)

def bot_admin_private(func):
    @functools.wraps(func)
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if update.effective_chat.type != ChatType.PRIVATE:
            return
        if not is_bot_admin(update.effective_user):
            return
        await func(update, context)

    return wrapper


async def cmd_addchat(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat, user, msg = update.effective_chat, update.effective_user, update.effective_message
    if not is_bot_admin(user):
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
        if key in game["banned"]:
            await msg.reply_text("Вы исключены из игры.")
            return
        err = bingo_prompt_error(game, key)
        if err:
            await msg.reply_text(err)
            return
        await prompt_numbers(context, chat_id, user, game)
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
    app.add_handler(CommandHandler("roulette", cmd_roulette))
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
    app.add_handler(CommandHandler("addchat", cmd_addchat))
    app.add_handler(CommandHandler("delchat", cmd_delchat))
    app.add_handler(CommandHandler("chats", cmd_chats))
    app.add_handler(CallbackQueryHandler(on_join, pattern="^join$"))
    app.add_handler(
        MessageHandler(filters.TEXT & ~filters.COMMAND & filters.ChatType.GROUPS, on_group_text)
    )

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
        log.info("Бот запущен")
        try:
            await asyncio.Event().wait()
        finally:
            ping_task.cancel()
            await app.updater.stop()
            await app.stop()
            await runner.cleanup()
            if pool is not None:
                await pool.close()


if __name__ == "__main__":
    asyncio.run(main())
