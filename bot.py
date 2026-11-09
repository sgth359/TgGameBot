"""
Телеграм-бот: Рулетка и Бинго (aiogram 3.x)

Установка:  pip install aiogram
Запуск:     BOT_TOKEN=123:ABC python games_bot.py
Neon:       переменная DATABASE_URL (строка подключения из Neon) для /top.
Render:     Web Service, Build: pip install -r requirements.txt
            Start: python games_bot.py, переменная BOT_TOKEN.
            Бот сам пингует свой адрес (RENDER_EXTERNAL_URL) раз в 10 минут.

BotFather: /setprivacy -> Disable (чтобы бот видел "@" и "бинго" в группе),
либо сделайте бота админом чата.
"""
import asyncio
import json
import logging
import os
import random
import re
from dataclasses import dataclass, field

import asyncpg
from aiohttp import ClientSession, ClientTimeout, web
from aiogram import Bot, Dispatcher, F, Router
from aiogram.exceptions import TelegramBadRequest
from aiogram.filters import Command, CommandObject, CommandStart
from aiogram.types import (CallbackQuery, InlineKeyboardButton,
                           InlineKeyboardMarkup, Message)

TOKEN = os.environ["BOT_TOKEN"]
NUM_MAX = 100       # числа бинго от 1 до NUM_MAX
MAX_FOULS = 3       # фальшей до исключения
GROUP = {"group", "supergroup"}

router = Router()
BOT_USERNAME = ""


# ───────────────────────── данные ─────────────────────────
@dataclass
class Player:
    name: str
    user_id: int | None = None
    username: str | None = None      # в нижнем регистре, без @
    numbers: list = field(default_factory=list)
    fouls: int = 0
    claimed: bool = False


@dataclass
class Game:
    kind: str                         # "roulette" | "bingo"
    chat_id: int
    msg_id: int = 0
    open: bool = True
    players: list = field(default_factory=list)
    drawn: list = field(default_factory=list)
    banned: set = field(default_factory=set)
    top: set = field(default_factory=set)      # кому админ дал /top (id и username)


games: dict[int, Game] = {}           # chat_id -> игра
dm_wait: dict[int, int] = {}          # user_id -> chat_id (ждём 5 чисел в личке)

# ── постоянный бонус (/top): chat_id -> {user_id | username} ──
# Хранится в Neon (Postgres), если задана DATABASE_URL; иначе в файле (на Render Free
# файл пропадает при перезапуске). В памяти — кэш, has_top() читает из него.
DATABASE_URL = os.environ.get("DATABASE_URL", "")
TOP_FILE = os.environ.get("TOP_FILE", "top.json")
perm_top: dict[int, set] = {}


def _enc(k):
    return f"id:{k}" if isinstance(k, int) else f"u:{k}"


def _dec(k):
    return int(k[3:]) if k.startswith("id:") else k[2:]


async def db(query, *args):
    # отдельное соединение на запрос: Neon усыпляет базу, а запросов мало
    dsn = DATABASE_URL.split("?")[0]          # параметры (sslmode и др.) убираем
    conn = await asyncpg.connect(dsn, ssl="require", timeout=20)
    try:
        return await conn.fetch(query, *args)
    finally:
        await conn.close()


def _file_save():
    try:
        with open(TOP_FILE, "w", encoding="utf-8") as f:
            json.dump({str(k): list(v) for k, v in perm_top.items()}, f, ensure_ascii=False)
        return True
    except Exception:
        return False


async def load_top():
    perm_top.clear()
    if DATABASE_URL:
        try:
            await db("CREATE TABLE IF NOT EXISTS top_users ("
                     "chat_id BIGINT NOT NULL, key TEXT NOT NULL, PRIMARY KEY (chat_id, key))")
            for r in await db("SELECT chat_id, key FROM top_users"):
                perm_top.setdefault(r["chat_id"], set()).add(_dec(r["key"]))
        except Exception as e:
            logging.warning("Neon: не удалось загрузить топы: %s", e)
        return
    try:
        with open(TOP_FILE, encoding="utf-8") as f:
            perm_top.update({int(k): set(v) for k, v in json.load(f).items()})
    except Exception:
        pass


async def top_add(chat_id, uid, uname):
    """Добавить постоянный бонус. True, если сохранено надёжно."""
    keys = [k for k in (uid, uname) if k]
    perm_top.setdefault(chat_id, set()).update(keys)
    if not DATABASE_URL:
        return _file_save()
    try:
        for k in keys:
            await db("INSERT INTO top_users (chat_id, key) VALUES ($1, $2) "
                     "ON CONFLICT DO NOTHING", chat_id, _enc(k))
        return True
    except Exception as e:
        logging.warning("Neon: ошибка записи: %s", e)
        return False


async def top_remove(chat_id, uid, uname):
    keys = [k for k in (uid, uname) if k]
    for k in keys:
        perm_top.get(chat_id, set()).discard(k)
    if not DATABASE_URL:
        return _file_save()
    try:
        for k in keys:
            await db("DELETE FROM top_users WHERE chat_id = $1 AND key = $2",
                     chat_id, _enc(k))
        return True
    except Exception as e:
        logging.warning("Neon: ошибка удаления: %s", e)
        return False


# ───────────────────────── помощники ─────────────────────────
def find(game, user_id=None, uname=None):
    for p in game.players:
        if user_id and p.user_id == user_id:
            return p
        if uname and p.username == uname:
            return p
    return None


def has_top(game, user_id=None, uname=None):
    pool = game.top | perm_top.get(game.chat_id, set())   # /vtop + /top
    return bool((user_id and user_id in pool) or (uname and uname in pool))


def entries(game, user_id, uname):
    return [p for p in game.players
            if (user_id and p.user_id == user_id) or (uname and p.username == uname)]


def add_player(game, user_id, username, name, numbers):
    """Лимит: 1 запись (рулетка) / 5 чисел (бинго); с /top — 2 записи / 6 чисел."""
    uname = username.lower() if username else None
    if (user_id and user_id in game.banned) or (uname and uname in game.banned):
        return "banned"
    top = has_top(game, user_id, uname)
    mine = entries(game, user_id, uname)
    for p in mine:
        if user_id and not p.user_id:
            p.user_id = user_id
    if not mine:
        game.players.append(Player(name, user_id, uname, numbers))
        return "ok"
    if game.kind == "roulette":
        if top and len(mine) < 2:
            game.players.append(Player(name, user_id, uname))
            return "ok"
        return "dup"
    p = mine[0]
    if top and len(p.numbers) == 5 and len(numbers) == 6:
        p.numbers = numbers
        return "upgrade"
    return "dup"


def user_name(u):
    return f"@{u.username}" if u.username else u.full_name


def parse_nums(s, max_count=5):
    if not re.fullmatch(r"[\d\s,]+", s or ""):
        return None
    nums = [int(x) for x in re.findall(r"\d+", s)]
    if not 5 <= len(nums) <= max_count or len(set(nums)) != len(nums):
        return None
    if any(not 1 <= n <= NUM_MAX for n in nums):
        return None
    return nums


def need_text(max_count):
    t = f"Нужно 5 разных чисел от 1 до {NUM_MAX}"
    if max_count == 6:
        t += " (или 6 — у вас бонус)"
    return t + ". Пример: 3 14 25 40 71"


async def is_admin(m: Message):
    if m.sender_chat and m.sender_chat.id == m.chat.id:   # админ анонимно
        return True
    if not m.from_user:
        return False
    cm = await m.bot.get_chat_member(m.chat.id, m.from_user.id)
    return cm.status in ("creator", "administrator")


def render(game: Game):
    names = "\n".join(
        f"{i}. {p.name}{' ⭐' if has_top(game, p.user_id, p.username) else ''}"
        for i, p in enumerate(game.players, 1)) or "пока никого"
    if game.kind == "roulette":
        head = "🎡 Рулетка"
        hint = "Запись: «@», «@юзер» или кнопка ниже"
    else:
        head = "🎯 Бинго"
        hint = f"Запись: «@ 1 2 3 4 5», «@юзер 1 2 3 4 5» или кнопка (числа 1–{NUM_MAX})"
    status = f"{hint}" if game.open else "🔒 Список закрыт"
    return f"{head}\n{status}\n\nУчастники ({len(game.players)}):\n{names}"


def keyboard(game: Game):
    if not game.open:
        return None
    if game.kind == "roulette":
        btn = InlineKeyboardButton(text="✍️ Записаться", callback_data="join")
    else:
        btn = InlineKeyboardButton(
            text="✍️ Записаться",
            url=f"https://t.me/{BOT_USERNAME}?start=bingo_{game.chat_id}")
    return InlineKeyboardMarkup(inline_keyboard=[[btn]])


async def refresh(bot: Bot, game: Game):
    try:
        await bot.edit_message_text(render(game), chat_id=game.chat_id,
                                    message_id=game.msg_id,
                                    reply_markup=keyboard(game))
    except TelegramBadRequest:
        pass


async def send_long(m: Message, text: str):
    for i in range(0, len(text), 3800):
        await m.answer(text[i:i + 3800])


async def start_game(m: Message, kind: str):
    if not await is_admin(m):
        return
    if m.chat.id in games:
        await m.answer("Игра уже идёт. Завершите её: /stopgame")
        return
    game = Game(kind, m.chat.id)
    games[m.chat.id] = game
    sent = await m.answer(render(game), reply_markup=keyboard(game))
    game.msg_id = sent.message_id


# ───────────────────────── команды админа ─────────────────────────
@router.message(Command("roulette"), F.chat.type.in_(GROUP))
async def cmd_roulette(m: Message):
    await start_game(m, "roulette")


@router.message(Command("bingo"), F.chat.type.in_(GROUP))
async def cmd_bingo(m: Message):
    await start_game(m, "bingo")


@router.message(Command("stopgame"), F.chat.type.in_(GROUP))
async def cmd_stopgame(m: Message):
    if not await is_admin(m):
        return
    game = games.pop(m.chat.id, None)
    if game:
        for uid, cid in list(dm_wait.items()):
            if cid == m.chat.id:
                dm_wait.pop(uid)
        await m.answer("Игра завершена.")


@router.message(Command("close"), F.chat.type.in_(GROUP))
async def cmd_close(m: Message):
    game = games.get(m.chat.id)
    if not game or not game.open or not await is_admin(m):
        return
    if not game.players:
        await m.answer("Список пуст, закрывать нечего.")
        return
    game.open = False
    await refresh(m.bot, game)
    if game.kind == "roulette":
        n = random.randint(1, len(game.players))
        winner = game.players[n - 1]
        await m.answer(f"🎲 Выпало число: {n} (из {len(game.players)})\n"
                       f"🏆 Победитель: {winner.name}")
        games.pop(m.chat.id, None)
    else:
        for uid, cid in list(dm_wait.items()):
            if cid == m.chat.id:
                dm_wait.pop(uid)
        await m.answer("🔒 Список закрыт. Админ: /line 1…5 — выдать строки чисел.")


@router.message(Command("line"), F.chat.type.in_(GROUP))
async def cmd_line(m: Message, command: CommandObject):
    game = games.get(m.chat.id)
    if not game or game.kind != "bingo" or game.open or not await is_admin(m):
        return
    try:
        n = int(command.args)
        assert 1 <= n <= 5
    except Exception:
        await m.answer("Использование: /line n  (n от 1 до 5)")
        return
    pool = [x for x in range(1, NUM_MAX + 1) if x not in game.drawn]
    if len(pool) < n * 5:
        await m.answer("Числа закончились.")
        return
    picked = random.sample(pool, n * 5)
    rows = []
    for i in range(n):
        row = sorted(picked[i * 5:(i + 1) * 5])
        rows.append(f"{i + 1}) " + "  ".join(map(str, row)))
    game.drawn += picked
    await m.answer("🎱 Выпало:\n" + "\n".join(rows))


def parse_target(m: Message, command: CommandObject):
    """Кого имеет в виду админ: ответ на сообщение, @юзер или id."""
    uid = uname = name = None
    r = m.reply_to_message
    if r and r.from_user and not r.from_user.is_bot:
        uid = r.from_user.id
        uname = (r.from_user.username or "").lower() or None
        name = user_name(r.from_user)
    elif command.args:
        arg = command.args.split()[0]
        if arg.startswith("@") and len(arg) > 1:
            uname, name = arg[1:].lower(), arg
        elif arg.isdigit():
            uid, name = int(arg), arg
    return uid, uname, name


@router.message(Command("vtop"), F.chat.type.in_(GROUP))
async def cmd_vtop(m: Message, command: CommandObject):
    """Админ: бонус на ОДНУ идущую игру (пока список открыт)."""
    game = games.get(m.chat.id)
    if not game or not await is_admin(m):
        return
    if not game.open:
        await m.reply("Список уже закрыт.")
        return
    uid, uname, name = parse_target(m, command)
    if not uid and not uname:
        await m.reply("Использование: /vtop ответом на сообщение, /vtop @юзер или /vtop id")
        return
    if uid:
        game.top.add(uid)
    if uname:
        game.top.add(uname)
    bonus = "2 записи" if game.kind == "roulette" else "бинго с 6 числами"
    await m.answer(f"⭐ {name}: бонус на эту игру — {bonus}")
    await refresh(m.bot, game)


@router.message(Command("top"), F.chat.type.in_(GROUP))
async def cmd_top(m: Message, command: CommandObject):
    """Админ: постоянный бонус во всех играх этого чата."""
    if not await is_admin(m):
        return
    uid, uname, name = parse_target(m, command)
    if not uid and not uname:
        await m.reply("Использование: /top ответом на сообщение, /top @юзер или /top id")
        return
    saved = await top_add(m.chat.id, uid, uname)
    note = "" if saved else "\n⚠️ В базу записать не удалось — бонус пропадёт при перезапуске."
    await m.answer(f"⭐ {name}: постоянный бонус во всех играх "
                   f"(2 записи в рулетке, 6 чисел в бинго)" + note)
    game = games.get(m.chat.id)
    if game and game.open:
        await refresh(m.bot, game)


@router.message(Command("untop"), F.chat.type.in_(GROUP))
async def cmd_untop(m: Message, command: CommandObject):
    """Админ: снять бонус (постоянный и разовый)."""
    if not await is_admin(m):
        return
    uid, uname, name = parse_target(m, command)
    if not uid and not uname:
        await m.reply("Использование: /untop ответом на сообщение, /untop @юзер или /untop id")
        return
    game = games.get(m.chat.id)
    if game:
        game.top.discard(uid)
        game.top.discard(uname)
    saved = await top_remove(m.chat.id, uid, uname)
    note = "" if saved else "\n⚠️ Из базы удалить не удалось — после перезапуска бонус может вернуться."
    await m.answer(f"{name}: бонус снят" + note)
    if game and game.open:
        await refresh(m.bot, game)


@router.message(Command("check"), F.chat.type.in_(GROUP))
async def cmd_check(m: Message, command: CommandObject):
    """Любой игрок: /check n n n (1–5 чисел) — какие из них уже выпали."""
    game = games.get(m.chat.id)
    if not game or game.kind != "bingo" or not m.from_user:
        return
    nums = []
    if command.args:
        if not re.fullmatch(r"[\d\s,]+", command.args):
            nums = None
        else:
            nums = [int(x) for x in re.findall(r"\d+", command.args)]
    else:
        p = find(game, m.from_user.id, (m.from_user.username or "").lower() or None)
        nums = list(p.numbers) if p else None   # без чисел — проверяем свою карточку
    if not nums or len(nums) > 6:
        await m.reply("Использование: /check n n n  (от 1 до 6 чисел)")
        return
    marks = "  ".join(f"{n}{'✅' if n in game.drawn else '❌'}" for n in nums)
    await m.reply(marks)


# ───────────────────────── запись в группе ─────────────────────────
@router.callback_query(F.data == "join")
async def cb_join(c: CallbackQuery):
    game = games.get(c.message.chat.id)
    if not game or game.kind != "roulette" or not game.open:
        await c.answer("Список закрыт", show_alert=True)
        return
    res = add_player(game, c.from_user.id, c.from_user.username,
                     user_name(c.from_user), [])
    if res == "banned":
        await c.answer("Вы исключены из игры", show_alert=True)
    elif res == "dup":
        await c.answer("Вы уже в списке")
    else:
        await c.answer("Записал!")
        await refresh(c.bot, game)


async def claim(m: Message, game: Game):
    if game.open:
        return
    p = find(game, m.from_user.id, (m.from_user.username or "").lower() or None)
    if not p or p.claimed:
        return
    if len(set(p.numbers) & set(game.drawn)) >= 5:   # при 6 числах хватает 5 совпадений
        p.claimed = True
        marks = "  ".join(f"{n}{'✅' if n in game.drawn else '❌'}" for n in p.numbers)
        await m.reply(f"{p.name}: {marks}\nОжидайте проверки администратора.")
        return
    p.fouls += 1
    if p.fouls >= MAX_FOULS:
        game.players.remove(p)
        if p.user_id:
            game.banned.add(p.user_id)
        if p.username:
            game.banned.add(p.username)
        await m.reply(f"Не обманывайте! Фальш {p.fouls}/{MAX_FOULS}. "
                      f"{p.name} исключён из игры.")
        await refresh(m.bot, game)
    else:
        await m.reply(f"Не обманывайте! Фальш {p.fouls}/{MAX_FOULS}")


@router.message(F.chat.type.in_(GROUP), F.text)
async def group_text(m: Message):
    game = games.get(m.chat.id)
    if not game or not m.from_user:
        return
    text = m.text.strip()

    if game.kind == "bingo" and text.lower() in ("бинго", "bingo"):
        await claim(m, game)
        return

    mt = re.fullmatch(r"@(\w{0,32})\s*([\d\s,]*)", text)
    if not mt or not game.open:
        return
    target, rest = mt.group(1), mt.group(2).strip()

    if game.kind == "roulette" and rest:
        return

    if target:   # @юзер
        uid, uname, pname = None, target.lower(), f"@{target}"
    else:        # просто @
        u = m.from_user
        uid, uname, pname = u.id, (u.username or "").lower() or None, user_name(u)

    numbers = []
    if game.kind == "bingo":
        max_count = 6 if has_top(game, uid, uname) else 5
        numbers = parse_nums(rest, max_count)
        if not numbers:
            await m.reply(need_text(max_count))
            return

    res = add_player(game, uid, uname, pname, numbers)
    if res == "banned":
        await m.reply("Этот игрок исключён из игры.")
    elif res == "dup":
        await m.reply("Уже в списке.")
    else:
        await refresh(m.bot, game)


# ───────────────────────── личка: числа для бинго ─────────────────────────
@router.message(CommandStart(), F.chat.type == "private")
async def start_private(m: Message, command: CommandObject):
    arg = command.args or ""
    if not arg.startswith("bingo_"):
        await m.answer("Я бот для игр в чате. Запись — кнопкой под списком.")
        return
    try:
        chat_id = int(arg[6:])
    except ValueError:
        return
    game = games.get(chat_id)
    if not game or game.kind != "bingo" or not game.open:
        await m.answer("Запись закрыта.")
        return
    if m.from_user.id in game.banned:
        await m.answer("Вы исключены из этой игры.")
        return
    dm_wait[m.from_user.id] = chat_id
    mc = 6 if has_top(game, m.from_user.id, (m.from_user.username or "").lower() or None) else 5
    await m.answer(need_text(mc).replace("Нужно", "Отправьте") + "\nЧерез пробел.")


@router.message(F.chat.type == "private", F.text)
async def private_numbers(m: Message):
    chat_id = dm_wait.get(m.from_user.id)
    if chat_id is None:
        return                      # ждём чисел не от этого человека — молчим
    game = games.get(chat_id)
    if not game or not game.open:
        dm_wait.pop(m.from_user.id, None)
        await m.answer("Запись закрыта.")
        return
    mc = 6 if has_top(game, m.from_user.id, (m.from_user.username or "").lower() or None) else 5
    nums = parse_nums(m.text, mc)
    if not nums:
        await m.answer(need_text(mc))
        return
    res = add_player(game, m.from_user.id, m.from_user.username,
                     user_name(m.from_user), nums)
    dm_wait.pop(m.from_user.id, None)
    if res == "dup":
        await m.answer("Вы уже записаны.")
    elif res == "banned":
        await m.answer("Вы исключены из игры.")
    else:
        await m.answer("✅ Записал: " + " ".join(map(str, nums)))
        await refresh(m.bot, game)


# ───────────────────────── запуск (Render) ─────────────────────────
async def health(request):
    return web.Response(text="ok")


async def self_ping():
    """Render Free засыпает через 15 мин без входящих запросов — пингуем себя."""
    url = os.environ.get("RENDER_EXTERNAL_URL")
    if not url:
        return
    async with ClientSession(timeout=ClientTimeout(total=20)) as session:
        while True:
            await asyncio.sleep(600)
            try:
                async with session.get(url):
                    pass
            except Exception:
                pass


async def main():
    global BOT_USERNAME
    bot = Bot(TOKEN)
    BOT_USERNAME = (await bot.get_me()).username
    await load_top()

    app = web.Application()
    app.router.add_get("/", health)
    runner = web.AppRunner(app)
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", int(os.environ.get("PORT", 10000))).start()
    ping_task = asyncio.create_task(self_ping())

    dp = Dispatcher()
    dp.include_router(router)
    try:
        await dp.start_polling(bot, allowed_updates=["message", "callback_query"])
    finally:
        ping_task.cancel()


if __name__ == "__main__":
    asyncio.run(main())
