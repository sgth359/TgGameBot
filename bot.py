import asyncio
import functools
import html
import json
import logging
import os
import random
import re

import httpx
from aiohttp import web
from telegram import ForceReply, InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ChatMemberStatus, ChatType, ParseMode
from telegram.error import BadRequest, Forbidden
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
ADMIN_IDS = {int(x) for x in os.environ.get("ADMIN_IDS", "").split(",") if x.strip().isdigit()}

BINGO_MIN, BINGO_MAX, BINGO_COUNT = 1, 100, 5
MAX_STRIKES = 3
PING_INTERVAL = 600  # секунд
CHATS_FILE = os.environ.get("CHATS_FILE", "chats.json")

# разрешённые чаты: chat_id -> название
allowed_chats: dict[int, str] = {}


def load_chats():
    try:
        with open(CHATS_FILE, encoding="utf-8") as f:
            allowed_chats.update({int(k): v for k, v in json.load(f).items()})
    except FileNotFoundError:
        pass
    except Exception as e:
        log.warning("не удалось прочитать %s: %s", CHATS_FILE, e)
    for x in os.environ.get("ALLOWED_CHATS", "").split(","):
        x = x.strip()
        if re.fullmatch(r"-?\d+", x):
            allowed_chats.setdefault(int(x), "?")


def save_chats():
    try:
        with open(CHATS_FILE, "w", encoding="utf-8") as f:
            json.dump({str(k): v for k, v in allowed_chats.items()}, f, ensure_ascii=False)
    except Exception as e:
        log.warning("не удалось сохранить %s: %s", CHATS_FILE, e)

# chat_id -> состояние игры
games: dict[int, dict] = {}
# (chat_id, user_id): человек нажал «Записаться» и сейчас должен прислать 5 чисел в чат
pending: set[tuple[int, int]] = set()


# ---------------------------------------------------------------- helpers

def user_key_label(user):
    """Ключ для сравнения и подпись для списка."""
    if user.username:
        return "@" + user.username.lower(), "@" + user.username
    name = html.escape(user.full_name)
    return f"id:{user.id}", f'<a href="tg://user?id={user.id}">{name}</a>'


def is_num(token: str) -> bool:
    return token.isascii() and token.isdigit()


def parse_numbers(tokens):
    if len(tokens) != BINGO_COUNT or not all(is_num(t) for t in tokens):
        return None
    nums = [int(t) for t in tokens]
    if len(set(nums)) != BINGO_COUNT:
        return None
    if any(not BINGO_MIN <= n <= BINGO_MAX for n in nums):
        return None
    return nums


NUMBERS_HINT = f"Нужно ровно {BINGO_COUNT} разных чисел от {BINGO_MIN} до {BINGO_MAX}."


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


async def prompt_numbers(context, chat_id, user):
    """Просит человека прислать 5 чисел прямо в чат."""
    pending.add((chat_id, user.id))
    _, label = user_key_label(user)
    await context.bot.send_message(
        chat_id,
        f"{label}, отправьте {BINGO_COUNT} разных чисел от {BINGO_MIN} до {BINGO_MAX} "
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
        "drawn": [],
        "drawn_set": set(),
        "banned": set(),
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
    pool = [x for x in range(BINGO_MIN, BINGO_MAX + 1) if x not in game["drawn_set"]]
    if len(pool) < rows_count * BINGO_COUNT:
        await update.effective_message.reply_text("Числа заканчиваются, столько строк не выдать.")
        return
    random.shuffle(pool)
    lines = []
    for i in range(rows_count):
        row = pool[i * BINGO_COUNT:(i + 1) * BINGO_COUNT]
        game["drawn"].extend(row)
        game["drawn_set"].update(row)
        lines.append(f"{i + 1}) " + "  ".join(f"{x}" for x in row))
    lines.append(f"\nВсего выпало: {len(game['drawn'])}")
    await update.effective_message.reply_text("🎯 Выпало:\n" + "\n".join(lines))
    await refresh(context.bot, update.effective_chat.id, game)


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
        marks = " ".join(
            f"{n}{'✅' if n in game['drawn_set'] else '❌'}" for n in player["numbers"]
        )
        text = f"{player['label']}: {marks}"
        if all(n in game["drawn_set"] for n in player["numbers"]):
            text += "\nВсе выпали — можно писать «бинго»!"
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


# ---------------------------------------------------------------- управление чатами (лс)

def bot_admin_private(func):
    @functools.wraps(func)
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if update.effective_chat.type != ChatType.PRIVATE:
            return
        if update.effective_user.id not in ADMIN_IDS:
            return
        await func(update, context)

    return wrapper


async def cmd_addchat(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat, user, msg = update.effective_chat, update.effective_user, update.effective_message
    if user is None or user.id not in ADMIN_IDS:
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
    allowed_chats[target.id] = target.title or str(target.id)
    save_chats()
    await msg.reply_text(f"✅ Добавлен: {allowed_chats[target.id]} ({target.id})")


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
    title = allowed_chats.pop(chat_id)
    save_chats()
    games.pop(chat_id, None)
    pending.difference_update({p for p in pending if p[0] == chat_id})
    await msg.reply_text(f"🗑 Удалён: {title} ({chat_id})")


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
        if key in game["players"]:
            await q.answer("Вы уже в списке.")
            return
        game["players"][key] = {"label": label}
        await q.answer("Вы записаны ✅")
        await refresh(context.bot, chat_id, game)
        return

    # бинго
    if key in game["banned"]:
        await q.answer("Вы исключены из игры.", show_alert=True)
        return
    await q.answer()
    await prompt_numbers(context, chat_id, user)


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
    if key in game["players"]:
        await msg.reply_text(f"{label} уже в списке.", parse_mode=ParseMode.HTML)
        return
    game["players"][key] = {"label": label}
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

    # 5 чисел без «@»: после кнопки или ответом на сообщение бота
    if all(is_num(t) for t in tokens) and (uid in pending or to_bot):
        if game["closed"]:
            pending.discard(uid)
            if len(tokens) == BINGO_COUNT:
                await msg.reply_text("Список закрыт.")
            return
        nums = parse_numbers(tokens)
        if nums is None:
            if uid in pending or len(tokens) == BINGO_COUNT:
                await msg.reply_text(NUMBERS_HINT)
            return
        key, label = user_key_label(user)
        if key in game["banned"]:
            pending.discard(uid)
            await msg.reply_text("Вы исключены из игры.")
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

    if not rest:
        if name:
            return  # "@юзер" без чисел игнорируем
        key, _ = user_key_label(user)
        if key in game["banned"]:
            await msg.reply_text("Вы исключены из игры.")
            return
        await prompt_numbers(context, chat_id, user)
        return

    nums = parse_numbers(rest)
    if nums is None:
        await msg.reply_text(NUMBERS_HINT)
        return
    if name:
        key, label = "@" + name.lower(), "@" + name
    else:
        key, label = user_key_label(user)
    if key in game["banned"]:
        await msg.reply_text("Этот игрок исключён из игры.")
        return
    register_bingo(game, key, label, nums)
    await refresh(context.bot, chat_id, game)


async def bingo_claim(update, context, game):
    """Игрок написал «бинго»: проверяем, выпали ли все его числа."""
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
    if all(n in drawn for n in player["numbers"]):
        marks = " ".join(f"{n}✅" for n in player["numbers"])
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
    load_chats()
    if not ADMIN_IDS:
        log.warning("ADMIN_IDS не задан — управлять списком чатов (/addchat) будет некому")
    app = Application.builder().token(TOKEN).build()

    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("roulette", cmd_roulette))
    app.add_handler(CommandHandler("bingo", cmd_bingo))
    app.add_handler(CommandHandler("close", cmd_close))
    app.add_handler(CommandHandler("random", cmd_random))
    app.add_handler(CommandHandler("line", cmd_line))
    app.add_handler(CommandHandler("check", cmd_check))
    app.add_handler(CommandHandler("stopgame", cmd_stopgame))
    app.add_handler(CommandHandler("addchat", cmd_addchat))
    app.add_handler(CommandHandler("delchat", cmd_delchat))
    app.add_handler(CommandHandler("chats", cmd_chats))
    app.add_handler(CallbackQueryHandler(on_join, pattern="^join$"))
    app.add_handler(
        MessageHandler(filters.TEXT & ~filters.COMMAND & filters.ChatType.GROUPS, on_group_text)
    )

    web_app = web.Application()
    web_app.router.add_get("/", health)
    web_app.router.add_get("/health", health)
    runner = web.AppRunner(web_app)
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", PORT).start()

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


if __name__ == "__main__":
    asyncio.run(main())
