"""Notix Slots — Python 3.12+, Discord, Railway PostgreSQL.

Required Railway variables: DISCORD_TOKEN, DATABASE_URL.
Recommended: OWNER_IDS=your_discord_user_id, TZ=Europe/Berlin.
Start: python main.py. No local data files or additional modules are required.
See README.md for variables, permissions, commands, and recovery procedures.

This is an independent implementation of a channel-rental workflow. Prices are
display labels; staff verify payment externally before issuing/renewing a slot.
"""

from __future__ import annotations

import asyncio
import contextlib
import copy
import hashlib
import io
import json
import logging
import os
import re
import secrets
import signal
import time
import uuid
from contextlib import asynccontextmanager
from datetime import datetime, timedelta, timezone
from typing import Any
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

import asyncpg
import discord
from aiohttp import web
from discord import app_commands
from discord.ext import commands, tasks
from PIL import Image, ImageDraw, ImageFont, ImageOps

UTC = timezone.utc
BRAND = "Notix Slots"
COLOUR = 0x8B5CF6
LOG = logging.getLogger("notix")
NO_MENTIONS = discord.AllowedMentions.none()
AUDIT_KINDS = ("slot-created", "slot-revoked", "ping-log", "slot-holds", "recovery-log")
TERMS = {"daily": 1, "weekly": 7, "monthly": 30, "quarterly": 90,
         "yearly": 365, "lifetime": None}
DEFAULT_PLANS = [
    {"name": "Weekly", "term": "weekly", "price": "$1", "here": 2, "everyone": 0, "category": 1},
    {"name": "Monthly", "term": "monthly", "price": "$2", "here": 2, "everyone": 1, "category": 1},
    {"name": "Lifetime", "term": "lifetime", "price": "$10", "here": 3, "everyone": 1, "category": 2},
]
DEFAULT_CONFIG = {
    "prefix": ".", "timezone": "UTC", "plans": DEFAULT_PLANS,
    "reminder_days": 2, "grace_days": 3, "expiry_minutes": 30,
    "autoclear": False, "autobackup": True, "backup_hours": 12,
    "backup_keep": 10, "banner_style": 1,
}
ENV_CONFIG = {
    "COMMAND_PREFIX": "prefix", "TZ": "timezone", "PLANS_JSON": "plans",
    "REMINDER_DAYS": "reminder_days", "GRACE_DAYS": "grace_days",
    "EXPIRY_CHECK_MINUTES": "expiry_minutes", "AUTO_CLEAR": "autoclear",
    "AUTO_BACKUP": "autobackup", "BACKUP_INTERVAL_HOURS": "backup_hours",
    "BACKUP_KEEP": "backup_keep", "BANNER_STYLE": "banner_style",
}


class UserError(commands.CommandError):
    """A safe, actionable error that may be shown to the caller."""


def now_utc() -> datetime:
    return datetime.now(UTC)


def stamp(value: datetime | None) -> str | None:
    return value.astimezone(UTC).isoformat() if value else None


def parse_time(value: str | None) -> datetime | None:
    if value is None:
        return None
    result = datetime.fromisoformat(value)
    if result.tzinfo is None:
        raise ValueError("timestamps must include a timezone")
    return result.astimezone(UTC)


def snowflake(value: Any, path: str = "ID") -> int:
    if isinstance(value, bool) or not re.fullmatch(r"[0-9]{1,19}", str(value)):
        raise ValueError(f"{path}: expected a Discord ID")
    result = int(value)
    if not 0 < result < 2**63:
        raise ValueError(f"{path}: outside the supported ID range")
    return result


def bounded_int(value: Any, path: str, low: int, high: int) -> int:
    if isinstance(value, bool) or not isinstance(value, (int, str)):
        raise ValueError(f"{path}: expected a whole number from {low} to {high}")
    try:
        result = int(value)
    except ValueError:
        raise ValueError(f"{path}: expected a whole number from {low} to {high}") from None
    if not low <= result <= high:
        raise ValueError(f"{path}: must be from {low} to {high}")
    return result


def boolean(value: Any, path: str) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, str) and value.lower() in ("true", "false", "1", "0"):
        return value.lower() in ("true", "1")
    raise ValueError(f"{path}: expected true or false")


def normalize_plan(raw: Any, path: str) -> dict:
    if not isinstance(raw, dict):
        raise ValueError(f"{path}: expected an object")
    unknown = set(raw) - {"name", "term", "days", "price", "here", "everyone", "category"}
    if unknown:
        raise ValueError(f"{path}: unknown keys {', '.join(sorted(unknown))}")
    name = raw.get("name")
    if not isinstance(name, str) or not 1 <= len(name.strip()) <= 40:
        raise ValueError(f"{path}.name: expected 1–40 characters")
    term = raw.get("term", raw.get("days", "monthly"))
    if isinstance(term, str) and term.lower() in TERMS:
        days = TERMS[term.lower()]
    elif term is None:
        days = None
    else:
        days = bounded_int(term, f"{path}.term", 1, 3650)
    price = raw.get("price", "$0")
    if not isinstance(price, str) or not 1 <= len(price) <= 40:
        raise ValueError(f"{path}.price: expected a short price label")
    return {"name": name.strip(), "days": days, "price": price,
            "here": bounded_int(raw.get("here", 0), f"{path}.here", 0, 1000),
            "everyone": bounded_int(raw.get("everyone", 0), f"{path}.everyone", 0, 1000),
            "category": bounded_int(raw.get("category", 1), f"{path}.category", 1, 25)}


def validate_config(raw: dict) -> dict:
    if not isinstance(raw, dict):
        raise ValueError("config: expected a JSON object")
    unknown = set(raw) - set(DEFAULT_CONFIG)
    if unknown:
        raise ValueError(f"config: unknown keys {', '.join(sorted(unknown))}")
    cfg = copy.deepcopy(DEFAULT_CONFIG)
    cfg.update(raw)
    if not isinstance(cfg["prefix"], str) or not 1 <= len(cfg["prefix"]) <= 5 or cfg["prefix"].isspace():
        raise ValueError("prefix: expected 1–5 nonblank characters")
    try:
        ZoneInfo(cfg["timezone"])
    except (ZoneInfoNotFoundError, TypeError, ValueError):
        raise ValueError("timezone: use an IANA timezone, e.g. Europe/Berlin or Asia/Kolkata") from None
    if not isinstance(cfg["plans"], list) or not 1 <= len(cfg["plans"]) <= 25:
        raise ValueError("plans: provide between 1 and 25 plans")
    cfg["plans"] = [normalize_plan(p, f"plans[{i}]") for i, p in enumerate(cfg["plans"])]
    names = [p["name"].casefold() for p in cfg["plans"]]
    if len(names) != len(set(names)):
        raise ValueError("plans: names must be unique, ignoring case")
    for key, low, high in (("reminder_days", 0, 365), ("grace_days", 1, 365),
                           ("expiry_minutes", 1, 60), ("backup_hours", 1, 720),
                           ("backup_keep", 1, 100), ("banner_style", 1, 3)):
        cfg[key] = bounded_int(cfg[key], key, low, high)
    for key in ("autoclear", "autobackup"):
        cfg[key] = boolean(cfg[key], key)
    return cfg


def environment_config() -> dict:
    result = copy.deepcopy(DEFAULT_CONFIG)
    for env_name, key in ENV_CONFIG.items():
        if env_name in os.environ:
            value = os.environ[env_name]
            if key == "plans":
                try:
                    value = json.loads(value)
                except json.JSONDecodeError:
                    raise ValueError("PLANS_JSON: invalid JSON") from None
            result[key] = value
    return validate_config(result)


def key_hash(key: str) -> str:
    return hashlib.sha256(key.encode("ascii")).hexdigest()


def new_key() -> tuple[str, str]:
    key = secrets.token_hex(16)
    return key, key_hash(key)


def day_and_reset(cfg: dict, at: datetime | None = None) -> tuple[str, datetime]:
    local = (at or now_utc()).astimezone(ZoneInfo(cfg["timezone"]))
    tomorrow = local.date() + timedelta(days=1)
    midnight = datetime.combine(tomorrow, datetime.min.time(), tzinfo=local.tzinfo)
    return local.date().isoformat(), midnight.astimezone(UTC)


def reset_usage(slot: dict, cfg: dict, at: datetime | None = None) -> bool:
    day, _ = day_and_reset(cfg, at)
    if slot.get("ping_day") == day:
        return False
    slot.update(ping_day=day, here_used=0, everyone_used=0)
    return True


def mention_counts(content: str) -> tuple[int, int]:
    # Conservative: even mentions in code/escaped text consume budget through /say.
    return len(re.findall(r"@here\b", content)), len(re.findall(r"@everyone\b", content))


def is_open(slot: dict, at: datetime | None = None) -> bool:
    expiry = parse_time(slot.get("expires_at"))
    return (slot.get("state") == "active" and not slot.get("held_at")
            and (expiry is None or expiry > (at or now_utc())))


def title_state(slot: dict) -> str:
    if slot["state"] != "active":
        return slot["state"].title()
    if slot.get("held_at"):
        return "On hold"
    return "Active" if is_open(slot) else "Expired — renewal window"


def display_time(value: str | None) -> str:
    return f"<t:{int(parse_time(value).timestamp())}:F>" if value else "Lifetime"


def embed(title: str, description: str = "") -> discord.Embed:
    result = discord.Embed(title=title[:256], description=description[:4096], colour=COLOUR)
    result.set_footer(text=BRAND)
    return result


SCHEMA = """
CREATE TABLE IF NOT EXISTS ns_settings (
    id SMALLINT PRIMARY KEY CHECK (id=1), data JSONB NOT NULL
);
CREATE TABLE IF NOT EXISTS ns_guilds (
    guild_id BIGINT PRIMARY KEY, data JSONB NOT NULL DEFAULT '{}'::jsonb,
    last_backup_check TIMESTAMPTZ, last_expiry_check TIMESTAMPTZ
);
CREATE TABLE IF NOT EXISTS ns_slots (
    id TEXT PRIMARY KEY, guild_id BIGINT NOT NULL REFERENCES ns_guilds(guild_id),
    owner_id BIGINT NOT NULL, plan_name TEXT NOT NULL,
    channel_id BIGINT UNIQUE, data JSONB NOT NULL
);
CREATE UNIQUE INDEX IF NOT EXISTS ns_owner_plan ON ns_slots(guild_id,owner_id,lower(plan_name));
CREATE INDEX IF NOT EXISTS ns_guild_slots ON ns_slots(guild_id);
CREATE INDEX IF NOT EXISTS ns_key_lookup ON ns_slots(guild_id,(data->>'key_hash'));
CREATE TABLE IF NOT EXISTS ns_backups (
    id BIGSERIAL PRIMARY KEY, guild_id BIGINT NOT NULL, automatic BOOLEAN NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT now(), fingerprint TEXT NOT NULL, payload JSONB NOT NULL
);
CREATE INDEX IF NOT EXISTS ns_backup_guild ON ns_backups(guild_id,created_at DESC);
CREATE TABLE IF NOT EXISTS ns_processed_messages (
    message_id BIGINT PRIMARY KEY, created_at TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE TABLE IF NOT EXISTS ns_audit (
    id BIGSERIAL PRIMARY KEY, guild_id BIGINT NOT NULL, kind TEXT NOT NULL,
    details JSONB NOT NULL, created_at TIMESTAMPTZ NOT NULL DEFAULT now()
);
CREATE TABLE IF NOT EXISTS ns_recovery_attempts (
    guild_id BIGINT NOT NULL, user_id BIGINT NOT NULL,
    attempts INTEGER NOT NULL, window_start TIMESTAMPTZ NOT NULL,
    PRIMARY KEY(guild_id,user_id)
);
"""


async def init_connection(conn: asyncpg.Connection) -> None:
    await conn.set_type_codec("jsonb", schema="pg_catalog", encoder=json.dumps,
                              decoder=json.loads, format="text")


class Store:
    def __init__(self, pool: asyncpg.Pool):
        self.pool = pool

    @asynccontextmanager
    async def lock(self, guild_id: int):
        """Session lock serializes DB and Discord side effects for a guild.

        Individual saves commit before external side effects. No SQL transaction
        is kept open during Discord requests. PostgreSQL releases locks on crash.
        """
        async with self.pool.acquire(timeout=30) as conn:
            locked = False
            try:
                deadline = time.monotonic() + 30
                while not locked:
                    locked = await conn.fetchval("SELECT pg_try_advisory_lock($1::bigint)", guild_id)
                    if not locked:
                        if time.monotonic() > deadline:
                            raise UserError("This server is processing another operation. Try again shortly.")
                        await asyncio.sleep(0.15)
                yield conn
            finally:
                if locked and not conn.is_closed():
                    await asyncio.shield(conn.execute("SELECT pg_advisory_unlock($1::bigint)", guild_id))

    async def guild(self, guild_id: int, conn=None) -> dict:
        db = conn or self.pool
        value = await db.fetchval("SELECT data FROM ns_guilds WHERE guild_id=$1", guild_id)
        return copy.deepcopy(value) if value is not None else {
            "admins": [], "categories": [], "next_category": 1, "logs": {},
        }

    async def save_guild(self, guild_id: int, data: dict, conn=None) -> None:
        await (conn or self.pool).execute(
            "INSERT INTO ns_guilds(guild_id,data) VALUES($1,$2) "
            "ON CONFLICT(guild_id) DO UPDATE SET data=EXCLUDED.data", guild_id, data)

    async def slots(self, guild_id: int | None = None, conn=None) -> list[dict]:
        db = conn or self.pool
        if guild_id is None:
            rows = await db.fetch("SELECT data FROM ns_slots ORDER BY guild_id,owner_id,id")
        else:
            rows = await db.fetch("SELECT data FROM ns_slots WHERE guild_id=$1 ORDER BY owner_id,id", guild_id)
        return [r["data"] for r in rows]

    async def slot(self, slot_id: str, conn=None) -> dict | None:
        return await (conn or self.pool).fetchval("SELECT data FROM ns_slots WHERE id=$1", slot_id)

    async def by_channel(self, channel_id: int, conn=None) -> dict | None:
        return await (conn or self.pool).fetchval("SELECT data FROM ns_slots WHERE channel_id=$1", channel_id)

    async def save_slot(self, slot: dict, conn=None) -> None:
        await (conn or self.pool).execute(
            "INSERT INTO ns_slots(id,guild_id,owner_id,plan_name,channel_id,data) VALUES($1,$2,$3,$4,$5,$6) "
            "ON CONFLICT(id) DO UPDATE SET owner_id=EXCLUDED.owner_id,plan_name=EXCLUDED.plan_name,"
            "channel_id=EXCLUDED.channel_id,data=EXCLUDED.data",
            slot["id"], slot["guild_id"], slot["owner_id"], slot["plan"]["name"], slot.get("channel_id"), slot)


def make_slot(guild_id: int, owner_id: int, plan: dict, cfg: dict) -> tuple[dict, str]:
    current = now_utc()
    key, digest = new_key()
    slot = {
        "id": uuid.uuid4().hex, "guild_id": guild_id, "owner_id": owner_id,
        "plan": copy.deepcopy(plan), "channel_id": None, "header_id": None,
        "created_at": stamp(current), "expires_at": stamp(current + timedelta(days=plan["days"])) if plan["days"] else None,
        "held_at": None, "hold_reason": None, "reminder_sent": False,
        "notice_at": None, "grace_until": None, "state": "provisioning",
        "here_used": 0, "everyone_used": 0, "ping_day": day_and_reset(cfg)[0],
        "last_clear_day": day_and_reset(cfg)[0], "key_hash": digest,
    }
    return slot, key


def shift_after_hold(slot: dict, at: datetime) -> None:
    held = parse_time(slot.get("held_at"))
    if not held:
        raise UserError("This slot is not on hold.")
    delta = at - held
    for field in ("expires_at", "grace_until", "notice_at"):
        if slot.get(field):
            slot[field] = stamp(parse_time(slot[field]) + delta)
    slot["held_at"] = None
    slot["hold_reason"] = None


def render_banner(slot: dict, name: str, avatar: bytes | None, style: int = 1) -> bytes:
    """Three original Pillow designs; all assets are generated in memory."""
    palettes = {1: ("#111127", "#8b5cf6"), 2: ("#061b25", "#22d3ee"), 3: ("#201609", "#fbbf24")}
    bg, accent = palettes[style]
    canvas = Image.new("RGB", (1200, 400), bg)
    draw = ImageDraw.Draw(canvas)
    if style == 1:
        for radius in (210, 270, 330):
            draw.ellipse((920-radius, 160-radius, 920+radius, 160+radius), outline=accent, width=3)
        draw.rounded_rectangle((35, 35, 1165, 365), radius=24, outline="#595579", width=2)
    elif style == 2:
        for x in range(0, 1200, 70):
            draw.line((x, 0, x+300, 400), fill="#123643", width=2)
        draw.rectangle((0, 0, 14, 400), fill=accent)
    else:
        draw.polygon([(850, 0), (1200, 0), (1200, 400), (1040, 400)], fill="#3b2911")
        draw.line((40, 70, 1160, 70), fill=accent, width=3)
        draw.line((40, 345, 1160, 345), fill=accent, width=3)

    def font(size: int):
        for path in ("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", "DejaVuSans.ttf"):
            with contextlib.suppress(OSError):
                return ImageFont.truetype(path, size)
        return ImageFont.load_default(size=size)

    def fitted(text: str, xy: tuple, size: int, width: int, fill: str):
        text = text.replace("\n", " ")
        while text and draw.textlength(text, font=font(size)) > width:
            text = text[:-2] + "…" if len(text) > 2 else ""
        draw.text(xy, text, font=font(size), fill=fill)

    draw.text((64, 36 if style != 3 else 30), BRAND.upper(), font=font(24), fill=accent)
    draw.ellipse((65, 116, 245, 296), fill=accent)
    if avatar:
        with contextlib.suppress(Exception):
            pic = ImageOps.fit(Image.open(io.BytesIO(avatar)).convert("RGB"), (164, 164))
            mask = Image.new("L", (164, 164))
            ImageDraw.Draw(mask).ellipse((0, 0, 164, 164), fill=255)
            canvas.paste(pic, (73, 124), mask)
    fitted(name, (284, 108), 44, 825, "#ffffff")
    fitted(f"{slot['plan']['name']}  ·  {slot['plan']['price']}", (286, 171), 30, 800, accent)
    expiry = parse_time(slot.get("expires_at"))
    created = parse_time(slot["created_at"]).strftime("%d %b %Y")
    due = expiry.strftime("%d %b %Y, %H:%M UTC") if expiry else "Never"
    fitted(f"Opened {created}  |  Expires {due}", (286, 228), 23, 820, "#e2e8f0")
    fitted(f"{title_state(slot)}  ·  @here {slot['plan']['here']}/day  ·  @everyone {slot['plan']['everyone']}/day",
           (286, 273), 22, 820, "#cbd5e1")
    result = io.BytesIO()
    canvas.save(result, format="PNG")
    return result.getvalue()


class NotixBot(commands.Bot):
    def __init__(self, cfg: dict, owner_ids: set[int]):
        intents = discord.Intents.default()
        intents.members = True
        intents.message_content = True
        super().__init__(command_prefix=lambda bot, msg: bot.cfg["prefix"],
                         intents=intents, help_command=None, allowed_mentions=NO_MENTIONS,
                         owner_ids=owner_ids or None,
                         activity=discord.Game(name="Notix Slots • /help"))
        self.cfg = cfg
        self.configured_owners = owner_ids
        self.pool: asyncpg.Pool | None = None
        self.store: Store | None = None
        self.http_runner: web.AppRunner | None = None
        self.last_cleanup = 0.0
        self.resource_roles: dict[tuple[int, int], discord.Role] = {}
        self.fatal_error = False

    async def setup_hook(self):
        for attempt in range(6):
            try:
                self.pool = await asyncpg.create_pool(
                    os.environ["DATABASE_URL"], min_size=2, max_size=10,
                    command_timeout=30, timeout=15, init=init_connection)
                break
            except (OSError, asyncpg.PostgresError, asyncio.TimeoutError):
                if attempt == 5:
                    raise
                LOG.warning("Database not ready; retry %s/5", attempt + 1)
                await asyncio.sleep(min(2**attempt, 8))
        self.store = Store(self.pool)
        async with self.store.lock(0) as conn:
            await conn.execute(SCHEMA)
            override = await conn.fetchval("SELECT data FROM ns_settings WHERE id=1") or {}
            self.cfg = validate_config({**environment_config(), **override})
        self.add_view(RecoveryView(self))
        await self.tree.sync()  # Global commands also support the bot's DM conversation.
        fast_guild = os.environ.get("GUILD_ID", "").strip()
        if fast_guild:
            target = discord.Object(id=snowflake(fast_guild, "GUILD_ID"))
            self.tree.copy_global_to(guild=target)
            await self.tree.sync(guild=target)
        app = web.Application()
        app.router.add_get("/health", self.health)
        self.http_runner = web.AppRunner(app, access_log=None)
        await self.http_runner.setup()
        await web.TCPSite(self.http_runner, "0.0.0.0", int(os.environ.get("PORT", "8080"))).start()
        self.maintenance.start()

    async def health(self, request):
        healthy = self.is_ready() and not self.is_closed()
        try:
            await asyncio.wait_for(self.pool.fetchval("SELECT 1"), timeout=3)
        except Exception:
            healthy = False
        return web.json_response({"service": BRAND, "ready": healthy}, status=200 if healthy else 503)

    async def close(self):
        self.maintenance.cancel()
        # Let an in-flight worker release its connection before closing the pool.
        job = self.maintenance.get_task()
        if job and job is not asyncio.current_task():
            with contextlib.suppress(asyncio.CancelledError):
                await job
        await super().close()
        if self.http_runner:
            await self.http_runner.cleanup()
        if self.pool:
            try:
                await asyncio.wait_for(self.pool.close(), 15)
            except asyncio.TimeoutError:
                self.pool.terminate()

    async def on_ready(self):
        LOG.info("%s connected as %s; %s guild(s)", BRAND, self.user, len(self.guilds))

    def owner(self, user_id: int, guild: discord.Guild | None) -> bool:
        return user_id in self.configured_owners or bool(guild and guild.owner_id == user_id)

    async def permitted(self, user, guild, level: str, conn=None) -> bool:
        if level == "any":
            return True
        if guild is None:
            return False
        if self.owner(user.id, guild):
            return True
        if level == "owner":
            return False
        data = await self.store.guild(guild.id, conn)
        member = guild.get_member(user.id)
        return user.id in data.get("admins", []) or bool(member and member.guild_permissions.administrator)

    async def require(self, ctx, level="any"):
        if not await self.permitted(ctx.author, ctx.guild, level):
            raise UserError("Server owner access is required." if level == "owner" else
                            "Notix admin access is required. Run this command in your server.")

    async def member(self, guild: discord.Guild, user_id: int) -> discord.Member | None:
        member = guild.get_member(user_id)
        if member:
            return member
        try:
            return await guild.fetch_member(user_id)
        except discord.NotFound:
            return None

    async def text_channel(self, guild: discord.Guild, channel_id: int | None):
        if not channel_id:
            return None
        channel = guild.get_channel(channel_id)
        if channel is None:
            try:
                channel = await guild.fetch_channel(channel_id)
            except discord.NotFound:
                return None
        return channel if isinstance(channel, discord.TextChannel) else None

    def role(self, guild, role_id):
        # Discord's create_role response is usable before its gateway cache event arrives.
        return guild.get_role(role_id) or self.resource_roles.get((guild.id, role_id))

    def overwrites(self, guild, data, owner=None, writing=False, private=False, webhook_only=False):
        base = dict(view_channel=not private, read_message_history=not private,
                    send_messages=False, send_messages_in_threads=False,
                    create_public_threads=False, create_private_threads=False,
                    add_reactions=False, mention_everyone=False)
        result = {guild.default_role: discord.PermissionOverwrite(**base)}
        role = self.role(guild, data.get("staff_role", 0))
        if role:
            result[role] = discord.PermissionOverwrite(
                view_channel=True, read_message_history=True, manage_messages=True,
                send_messages=False, send_messages_in_threads=False, mention_everyone=False)
        result[guild.me] = discord.PermissionOverwrite(
            view_channel=True, read_message_history=True, send_messages=not webhook_only,
            embed_links=True, attach_files=True, manage_messages=True, manage_webhooks=True,
            manage_channels=True, mention_everyone=True, add_reactions=True)
        if owner:
            result[owner] = discord.PermissionOverwrite(
                view_channel=True, read_message_history=True, send_messages=writing,
                embed_links=writing, attach_files=writing, add_reactions=writing,
                mention_everyone=writing, send_messages_in_threads=False,
                create_public_threads=False, create_private_threads=False,
                manage_messages=False, manage_channels=False, manage_webhooks=False)
        return result

    async def ensure_setup(self, guild, count: int, conn) -> dict:
        needed = ("manage_channels", "manage_roles", "manage_messages", "manage_webhooks",
                  "view_channel", "send_messages", "read_message_history", "embed_links", "attach_files", "mention_everyone")
        missing = [name for name in needed if not getattr(guild.me.guild_permissions, name)]
        if missing:
            raise UserError("The bot needs these server permissions: " + ", ".join(missing))
        data = await self.store.guild(guild.id, conn)
        await self.store.save_guild(guild.id, data, conn)
        roles = await guild.fetch_roles()
        self.resource_roles = {key: role for key, role in self.resource_roles.items() if key[0] != guild.id}
        self.resource_roles.update({(guild.id, role.id): role for role in roles})
        for key, name, colour in (("owner_role", "Slot Owners", COLOUR),
                                   ("hold_role", "Slot Owner (Hold)", 0xF59E0B),
                                   ("staff_role", "Notix Staff", 0x64748B)):
            role = self.role(guild, data.get(key, 0))
            if not role:
                role = await guild.create_role(name=name, colour=colour, permissions=discord.Permissions.none(),
                                               reason=f"{BRAND} setup")
                data[key] = role.id
                self.resource_roles[(guild.id, role.id)] = role
                await self.store.save_guild(guild.id, data, conn)
        owner_role, hold_role = self.role(guild, data["owner_role"]), self.role(guild, data["hold_role"])
        if hold_role.position <= owner_role.position:
            await hold_role.edit(position=owner_role.position + 1, reason=f"{BRAND} hold colour")
        for user_id in set(data.get("admins", [])) | self.configured_owners | {guild.owner_id}:
            member = await self.member(guild, user_id)
            if member and self.role(guild, data["staff_role"]) not in member.roles:
                await member.add_roles(self.role(guild, data["staff_role"]), reason=f"{BRAND} staff")
        # Fetch authoritative channels: a cached missing channel must never cause a duplicate.
        channels = await guild.fetch_channels()
        existing = {c.id: c for c in channels}
        data["categories"] = [c for c in data.get("categories", [])
                              if isinstance(existing.get(c["id"]), discord.CategoryChannel)]
        for group in range(1, max(count, max(p["category"] for p in self.cfg["plans"])) + 1):
            if not any(c["group"] == group for c in data["categories"]):
                await self.new_category(guild, data, group, conn)
        for c in data["categories"]:
            category = existing.get(c["id"]) or guild.get_channel(c["id"])
            if category:
                await category.edit(overwrites=self.overwrites(guild, data), reason=f"{BRAND} reconcile")
        for key, name, private in (("info_category", "Notix Slots · Information", False),
                                    ("log_category", "Notix Slots · Staff Logs", True)):
            category = existing.get(data.get(key))
            if not isinstance(category, discord.CategoryChannel):
                category = await guild.create_category(name, overwrites=self.overwrites(guild, data, private=private,
                                                        webhook_only=private), reason=f"{BRAND} setup")
                data[key] = category.id
                await self.store.save_guild(guild.id, data, conn)
            else:
                await category.edit(overwrites=self.overwrites(guild, data, private=private, webhook_only=private))
        for kind in AUDIT_KINDS:
            item = data.setdefault("logs", {}).get(kind, {})
            channel = await self.text_channel(guild, item.get("channel_id"))
            if not channel:
                channel = await guild.create_text_channel(kind, category=guild.get_channel(data["log_category"]),
                    overwrites=self.overwrites(guild, data, private=True, webhook_only=True), reason=f"{BRAND} audit")
                item = {"channel_id": channel.id}
                data["logs"][kind] = item
                await self.store.save_guild(guild.id, data, conn)
            else:
                await channel.edit(overwrites=self.overwrites(guild, data, private=True, webhook_only=True))
            hooks = await channel.webhooks()
            hook = next((h for h in hooks if h.user and h.user.id == self.user.id and h.name == BRAND), None)
            if not hook:
                hook = await channel.create_webhook(name=BRAND, reason=f"{BRAND} audit")
            item["webhook_url"] = hook.url
            await self.store.save_guild(guild.id, data, conn)
        for key, name, title in (("plans_panel", "slot-plans", "Available plans"),
                                  ("recovery_panel", "slot-recovery", "Recover your slot")):
            item = data.get(key, {})
            channel = await self.text_channel(guild, item.get("channel_id"))
            if not channel:
                channel = await guild.create_text_channel(name, category=guild.get_channel(data["info_category"]),
                    overwrites=self.overwrites(guild, data), reason=f"{BRAND} panel")
                item = {"channel_id": channel.id}
                data[key] = item
                await self.store.save_guild(guild.id, data, conn)
            else:
                await channel.edit(overwrites=self.overwrites(guild, data))
            card = self.plans_embed() if key == "plans_panel" else embed(title,
                "Lost access to your old account? Join this server, press **Recover slot**, and enter your recovery key.\n"
                "A valid key transfers the slot to your current account. Keep it secret.")
            view = RecoveryView(self) if key == "recovery_panel" else None
            message = None
            if item.get("message_id"):
                try:
                    message = await channel.fetch_message(item["message_id"])
                except discord.NotFound:
                    pass
            if message:
                await message.edit(embed=card, view=view)
            else:
                message = await channel.send(embed=card, view=view)
                item["message_id"] = message.id
            await self.store.save_guild(guild.id, data, conn)
        return data

    async def new_category(self, guild, data, group, conn):
        number = data.get("next_category", 1)
        category = await guild.create_category(f"Notix Slots · {number}",
            overwrites=self.overwrites(guild, data), reason=f"{BRAND} category")
        data.setdefault("categories", []).append({"group": group, "number": number, "id": category.id})
        data["next_category"] = number + 1
        await self.store.save_guild(guild.id, data, conn)
        return category

    async def category_for(self, guild, data, group, conn):
        for item in data.get("categories", []):
            if item["group"] == group:
                category = guild.get_channel(item["id"])
                if isinstance(category, discord.CategoryChannel) and len(category.channels) < 50:
                    return category
        return await self.new_category(guild, data, group, conn)

    def plans_embed(self):
        card = embed("Notix Slots · Plans", "Contact staff to purchase a slot. All daily allowances reset at midnight in "
                     + self.cfg["timezone"] + ".")
        for plan in self.cfg["plans"]:
            term = f"{plan['days']} days" if plan["days"] else "Lifetime"
            card.add_field(name=plan["name"], value=f"**{plan['price']}** · {term}\n"
                           f"@here: {plan['here']}/day · @everyone: {plan['everyone']}/day", inline=False)
        return card

    async def audit(self, guild, kind: str, text: str, conn=None, **details):
        """Auditing never turns a successful user action into a failed command."""
        try:
            await (conn or self.pool).execute("INSERT INTO ns_audit(guild_id,kind,details) VALUES($1,$2,$3)",
                                              guild.id, kind, {"text": text[:3500], **details})
            data = await self.store.guild(guild.id, conn)
            url = data.get("logs", {}).get(kind, {}).get("webhook_url")
            if url:
                webhook = discord.Webhook.from_url(url, client=self)
                await webhook.send(embed=embed(kind.replace("-", " ").title(), text),
                                   username=BRAND, allowed_mentions=NO_MENTIONS)
        except Exception as error:
            LOG.warning("Audit delivery failed for guild %s (%s)", guild.id, type(error).__name__)

    async def sync_roles(self, guild, data, user_id, conn):
        member = await self.member(guild, user_id)
        if not member:
            return
        slots = [s for s in await self.store.slots(guild.id, conn) if s["owner_id"] == user_id]
        for key, wanted in (("owner_role", bool(slots)), ("hold_role", any(s.get("held_at") for s in slots))):
            role = self.role(guild, data.get(key, 0))
            if role and wanted and role not in member.roles:
                await member.add_roles(role, reason=f"{BRAND} ownership")
            elif role and not wanted and role in member.roles:
                await member.remove_roles(role, reason=f"{BRAND} ownership")

    async def apply_permissions(self, guild, data, slot):
        channel = await self.text_channel(guild, slot.get("channel_id"))
        if not channel:
            return
        member = await self.member(guild, slot["owner_id"])
        permissions = self.overwrites(guild, data, member, writing=is_open(slot))
        if member and is_open(slot):
            permissions[member].mention_everyone = bool(slot["plan"]["here"] or slot["plan"]["everyone"])
        await channel.edit(overwrites=permissions, reason=f"{BRAND}: {title_state(slot)}")

    async def header(self, guild, slot, conn):
        channel = await self.text_channel(guild, slot.get("channel_id"))
        if not channel:
            return
        member = await self.member(guild, slot["owner_id"])
        name = member.display_name if member else f"Owner {slot['owner_id']}"
        avatar = None
        if member:
            with contextlib.suppress(discord.HTTPException):
                avatar = await member.display_avatar.with_size(256).with_format("png").read()
        png = await asyncio.to_thread(render_banner, slot, name, avatar, self.cfg["banner_style"])
        file = discord.File(io.BytesIO(png), filename="notix-slot.png")
        card = embed(f"{slot['plan']['name']} · {title_state(slot)}",
            f"Owner: <@{slot['owner_id']}>\nPrice at sale: **{slot['plan']['price']}**\n"
            f"Opened: {display_time(slot['created_at'])}\nExpires: {display_time(slot.get('expires_at'))}\n"
            f"Daily budget: **{slot['plan']['here']} @here** / **{slot['plan']['everyone']} @everyone**\n"
            f"Reset timezone: **{self.cfg['timezone']}**\n"
            "Only the owner may post. An over-budget direct ping closes the slot. Use `/say` for a checked post.")
        if slot.get("held_at"):
            card.add_field(name="On hold", value=(slot.get("hold_reason") or "Paused by staff")[:1024], inline=False)
        if slot.get("grace_until"):
            card.add_field(name="Renew by", value=display_time(slot["grace_until"]), inline=False)
        card.set_image(url="attachment://notix-slot.png")
        message = None
        if slot.get("header_id"):
            try:
                message = await channel.fetch_message(slot["header_id"])
            except discord.NotFound:
                pass
        if message:
            await message.edit(embed=card, attachments=[file])
        else:
            message = await channel.send(embed=card, file=file)
            slot["header_id"] = message.id
            await self.store.save_slot(slot, conn)

    async def notify_owner(self, guild, slot, title, text) -> bool:
        try:
            user = self.get_user(slot["owner_id"]) or await self.fetch_user(slot["owner_id"])
            await user.send(embed=embed(title, text))
            return True
        except discord.HTTPException:
            channel = await self.text_channel(guild, slot.get("channel_id"))
            if channel:
                try:
                    await channel.send(content=f"<@{slot['owner_id']}>", embed=embed(title, text),
                        allowed_mentions=discord.AllowedMentions(users=[discord.Object(slot["owner_id"])], roles=False, everyone=False))
                    return True
                except discord.HTTPException:
                    pass
        return False

    async def send_key(self, owner_id: int, key: str, channel_id: int) -> bool:
        try:
            user = self.get_user(owner_id) or await self.fetch_user(owner_id)
            await user.send(embed=embed("Notix Slots · Recovery key",
                f"Slot: <#{channel_id}>\n\n`{key}`\n\n"
                "Keep this key private. Anyone with it can take ownership through this server's recovery panel. "
                "Only a hash is retained, so staff cannot read this key back. A replacement invalidates the old key."))
            return True
        except discord.HTTPException:
            return False

    async def provision(self, guild, data, slot, conn):
        """Save an intent before channel creation; recover a crash via its topic tag."""
        await self.store.save_slot(slot, conn)
        channel = await self.text_channel(guild, slot.get("channel_id"))
        if not channel:
            # A crash can happen after Discord created the channel but before its ID was saved.
            marker = f"notix:{slot['id']}"
            channels = await guild.fetch_channels()
            channel = next((c for c in channels if isinstance(c, discord.TextChannel)
                            and marker in (c.topic or "").split()), None)
        created = False
        if not channel:
            member = await self.member(guild, slot["owner_id"])
            base = member.display_name if member else str(slot["owner_id"])
            name = re.sub(r"[^a-z0-9-]", "-", base.lower()).strip("-")[:65] or "owner"
            category = await self.category_for(guild, data, slot["plan"]["category"], conn)
            channel = await guild.create_text_channel(f"slot-{name}", category=category,
                topic=f"{BRAND} | notix:{slot['id']}", overwrites=self.overwrites(guild, data),
                reason=f"{BRAND} provision")
            created = True
        slot["channel_id"] = channel.id
        slot["state"] = "active"
        slot["permissions_dirty"] = True
        slot["header_dirty"] = True
        try:
            await self.store.save_slot(slot, conn)
        except Exception:
            # Retain provisioning intent if the compensating deletion also fails.
            if created:
                try:
                    await channel.delete(reason=f"{BRAND}: database save failed")
                except discord.HTTPException:
                    LOG.error("Provisioning requires repair for slot %s", slot["id"])
                else:
                    with contextlib.suppress(Exception):
                        await conn.execute("DELETE FROM ns_slots WHERE id=$1", slot["id"])
            raise
        await self.repair(guild, data, slot, conn)

    async def repair(self, guild, data, slot, conn):
        await self.apply_permissions(guild, data, slot)
        await self.sync_roles(guild, data, slot["owner_id"], conn)
        previous_owner = slot.get("previous_owner_id")
        if previous_owner:
            await self.sync_roles(guild, data, previous_owner, conn)
        slot.pop("previous_owner_id", None)
        slot["permissions_dirty"] = False
        await self.store.save_slot(slot, conn)
        try:
            await self.header(guild, slot, conn)
            slot["header_dirty"] = False
            await self.store.save_slot(slot, conn)
        except (discord.HTTPException, OSError, ValueError):
            slot["header_dirty"] = True
            await self.store.save_slot(slot, conn)
            LOG.warning("Header will be retried for slot %s", slot["id"])

    async def revoke(self, guild, data, slot, reason: str, conn):
        slot["state"] = "closing"
        slot["close_reason"] = reason[:500]
        await self.store.save_slot(slot, conn)
        channel = await self.text_channel(guild, slot.get("channel_id"))
        if channel:
            # Best-effort freeze; failure must not block a valid deletion attempt.
            with contextlib.suppress(discord.HTTPException):
                await self.apply_permissions(guild, data, slot)
            try:
                await channel.delete(reason=f"{BRAND}: {reason}"[:512])
            except discord.NotFound:
                pass
            except discord.HTTPException:
                raise UserError("Discord refused the channel deletion. The slot remains recorded and closure will retry.") from None
        await conn.execute("DELETE FROM ns_slots WHERE id=$1", slot["id"])
        with contextlib.suppress(discord.HTTPException):
            await self.sync_roles(guild, data, slot["owner_id"], conn)
        await self.audit(guild, "slot-revoked", f"Closed `{slot['id']}` for <@{slot['owner_id']}>.\n{reason}", conn)

    async def resolve_slot(self, user_id, guild=None, channel_id=None, allow_admin=False) -> dict:
        if channel_id:
            try:
                target = snowflake(re.sub(r"[<#>]", "", str(channel_id)), "channel")
            except ValueError as error:
                raise UserError(str(error)) from None
            slot = await self.store.by_channel(target)
            if not slot or (guild and slot["guild_id"] != guild.id):
                raise UserError("That channel is not a recorded slot in this server.")
            if slot["owner_id"] != user_id:
                member = guild.get_member(user_id) if guild else None
                if not allow_admin or not member or not await self.permitted(member, guild, "admin"):
                    raise UserError("You do not own that slot.")
            return slot
        rows = await self.pool.fetch("SELECT data FROM ns_slots WHERE owner_id=$1" +
                                     (" AND guild_id=$2" if guild else ""),
                                     *([user_id, guild.id] if guild else [user_id]))
        slots = [r["data"] for r in rows]
        if not slots:
            raise UserError("You do not own a slot here.")
        if len(slots) > 1:
            channels = ", ".join(f"<#{s['channel_id']}> (`{s['channel_id']}`)" for s in slots)[:1400]
            raise UserError("You have multiple slots. Provide channel_id: " + channels)
        return slots[0]

    async def clear_channel(self, guild, slot, conn) -> tuple[int, int]:
        if slot.get("held_at"):
            raise UserError("Held slots cannot be cleared; their hold notice must stay visible.")
        channel = await self.text_channel(guild, slot.get("channel_id"))
        if not channel:
            raise UserError("The slot channel is missing. Ask staff to run /setup to repair it.")
        header_exists = False
        if slot.get("header_id"):
            try:
                await channel.fetch_message(slot["header_id"])
                header_exists = True
            except discord.NotFound:
                pass
        if not header_exists:
            await self.header(guild, slot, conn)
        cutoff = now_utc() - timedelta(days=14) + timedelta(minutes=5)
        batch, deleted, old = [], 0, 0

        async def flush():
            nonlocal deleted
            if batch:
                await channel.delete_messages(batch, reason=f"{BRAND} clear")
                deleted += len(batch)
                batch.clear()

        async for message in channel.history(limit=None):
            if message.id == slot["header_id"]:
                continue
            if message.created_at <= cutoff:
                old += 1
            else:
                batch.append(message)
                if len(batch) == 100:
                    await flush()
        await flush()
        return deleted, old

    async def post_advert(self, guild, slot_id, actor_id, content, request_id):
        if not 1 <= len(content) <= 2000:
            raise UserError("Your message must contain 1–2,000 characters.")
        async with self.store.lock(guild.id) as conn:
            slot = await self.store.slot(slot_id, conn)
            if not slot or slot["owner_id"] != actor_id:
                raise UserError("You no longer own this slot.")
            if not is_open(slot):
                raise UserError("This slot is held, expired, or closing. It cannot accept posts.")
            reset_usage(slot, self.cfg)
            here, everyone = mention_counts(content)
            if slot["here_used"] + here > slot["plan"]["here"] or slot["everyone_used"] + everyone > slot["plan"]["everyone"]:
                raise UserError("That post exceeds your remaining ping allowance. No message was sent.")
            channel = await self.text_channel(guild, slot["channel_id"])
            if not channel:
                raise UserError("The slot channel is missing. Ask staff to run /setup.")
            # Reserve before sending; an ambiguous network failure must not permit a free repeat ping.
            async with conn.transaction():
                accepted = await conn.fetchval("INSERT INTO ns_processed_messages(message_id) VALUES($1) "
                    "ON CONFLICT DO NOTHING RETURNING message_id", request_id)
                if not accepted:
                    raise UserError("This request has already been handled.")
                slot["here_used"] += here
                slot["everyone_used"] += everyone
                await self.store.save_slot(slot, conn)
            owner = await self.member(guild, actor_id)
            attribution = embed("Notix Slots · " + (owner.display_name if owner else str(actor_id)))
            try:
                message = await channel.send(content=content, embed=attribution,
                    allowed_mentions=discord.AllowedMentions(everyone=True, users=False, roles=False, replied_user=False),
                    nonce=request_id)
            except discord.HTTPException as error:
                # A definitive client rejection is safe to refund. 5xx/timeouts are not.
                if 400 <= error.status < 500:
                    slot["here_used"] -= here
                    slot["everyone_used"] -= everyone
                    await self.store.save_slot(slot, conn)
                raise UserError("Discord could not confirm the post. Check your channel before retrying; "
                                "an uncertain send retains its ping reservation.") from None
            if here or everyone:
                await self.audit(guild, "ping-log", f"/say by <@{actor_id}> in <#{channel.id}>: "
                                 f"@here × {here}, @everyone × {everyone}.", conn)
            return message.jump_url

    async def on_message(self, message):
        if message.author.bot or not self.store:
            return
        if message.guild:
            try:
                slot = await self.store.by_channel(message.channel.id)
                if slot and slot["owner_id"] == message.author.id:
                    async with self.store.lock(message.guild.id) as conn:
                        slot = await self.store.slot(slot["id"], conn)
                        if not slot or slot["owner_id"] != message.author.id:
                            return
                        if not is_open(slot):
                            with contextlib.suppress(discord.HTTPException):
                                await message.delete()
                            return
                        if message.mention_everyone:
                            here, everyone = mention_counts(message.content)
                            reset_usage(slot, self.cfg)
                            async with conn.transaction():
                                first = await conn.fetchval("INSERT INTO ns_processed_messages(message_id) VALUES($1) "
                                    "ON CONFLICT DO NOTHING RETURNING message_id", message.id)
                                if not first:
                                    return
                                slot["here_used"] += here
                                slot["everyone_used"] += everyone
                                over = (slot["here_used"] > slot["plan"]["here"] or
                                        slot["everyone_used"] > slot["plan"]["everyone"])
                                if over:
                                    slot.update(state="closing", close_reason="Daily ping allowance exceeded")
                                await self.store.save_slot(slot, conn)
                            await self.audit(message.guild, "ping-log", f"Direct ping by <@{message.author.id}> "
                                f"in <#{message.channel.id}>: @here × {here}, @everyone × {everyone}. "
                                + ("Allowance exceeded; closing." if over else "Within allowance."), conn)
                            if over:
                                data = await self.store.guild(message.guild.id, conn)
                                await self.notify_owner(message.guild, slot, "Slot closed for exceeding ping allowance",
                                    "Your direct message exceeded the daily allowance. Contact staff for assistance.")
                                await self.revoke(message.guild, data, slot, slot["close_reason"], conn)
                                return
                # A prefix /say in a server already delivered its own broadcast mention.
                ctx = await self.get_context(message)
                if ctx.command and ctx.command.name == "say" and message.mention_everyone:
                    await message.channel.send("Use slash `/say` or DM the bot when your advert contains a broadcast mention.")
                    return
            except Exception as error:
                LOG.error("Message enforcement failed in guild %s (%s)", message.guild.id, type(error).__name__)
                return  # Fail closed: do not run a prefix command after an enforcement failure.
        await self.process_commands(message)

    async def on_member_join(self, member):
        if not self.store:
            return
        try:
            async with self.store.lock(member.guild.id) as conn:
                data = await self.store.guild(member.guild.id, conn)
                for slot in await self.store.slots(member.guild.id, conn):
                    if slot["owner_id"] == member.id:
                        await self.repair(member.guild, data, slot, conn)
                if member.id in data.get("admins", []) or self.owner(member.id, member.guild):
                    role = self.role(member.guild, data.get("staff_role", 0))
                    if role:
                        await member.add_roles(role, reason=f"{BRAND} staff return")
        except Exception as error:
            LOG.warning("Join repair failed for member %s (%s)", member.id, type(error).__name__)

    async def snapshot(self, guild, automatic, conn) -> dict | None:
        data = await self.store.guild(guild.id, conn)
        body = {
            "format": "notix-slots", "version": 1, "source_guild_id": str(guild.id),
            "config": copy.deepcopy(self.cfg),
            "categories": [{"group": c["group"], "number": c["number"]} for c in data.get("categories", [])],
            "slots": await self.store.slots(guild.id, conn),
        }
        fingerprint = hashlib.sha256(json.dumps(body, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        if automatic:
            previous = await conn.fetchval("SELECT fingerprint FROM ns_backups WHERE guild_id=$1 ORDER BY id DESC LIMIT 1", guild.id)
            if previous == fingerprint:
                await conn.execute("UPDATE ns_guilds SET last_backup_check=now() WHERE guild_id=$1", guild.id)
                return None
        body["captured_at"] = stamp(now_utc())
        row = await conn.fetchrow("INSERT INTO ns_backups(guild_id,automatic,fingerprint,payload) VALUES($1,$2,$3,$4) RETURNING *",
                                  guild.id, automatic, fingerprint, body)
        if automatic:
            await conn.execute("DELETE FROM ns_backups WHERE guild_id=$1 AND automatic=true AND id NOT IN "
                "(SELECT id FROM ns_backups WHERE guild_id=$1 AND automatic=true ORDER BY id DESC LIMIT $2)",
                guild.id, self.cfg["backup_keep"])
            await conn.execute("UPDATE ns_guilds SET last_backup_check=now() WHERE guild_id=$1", guild.id)
        return dict(row)

    async def restore_snapshot(self, guild, payload, conn):
        slots = validate_backup(payload)  # Entire file validates before any Discord mutations.
        categories = payload.get("categories", [])
        required = max([p["category"] for p in self.cfg["plans"]] + [s["plan"]["category"] for s in slots]
                       + [c["group"] for c in categories])
        data = await self.ensure_setup(guild, required, conn)
        for group in {c["group"] for c in categories}:
            expected = sum(c["group"] == group for c in categories)
            while sum(c["group"] == group for c in data["categories"]) < expected:
                await self.new_category(guild, data, group, conn)
        captured = parse_time(payload["captured_at"])
        created, repaired, missing, failures = 0, 0, 0, []
        current_slots = await self.store.slots(guild.id, conn)
        for source in slots:
            if source["state"] == "closing":
                continue  # A pending revocation must not be resurrected.
            match = next((s for s in current_slots if
                          s.get("lineage_id", s["id"]) == source.get("lineage_id", source["id"]) or
                          (s["owner_id"] == source["owner_id"] and
                           s["plan"]["name"].casefold() == source["plan"]["name"].casefold())), None)
            try:
                if match:
                    if match["state"] == "closing":
                        continue
                    # Existing records are authoritative: retries never extend time or undo recovery.
                    if not await self.text_channel(guild, match.get("channel_id")):
                        await self.provision(guild, data, match, conn)
                    else:
                        await self.repair(guild, data, match, conn)
                    repaired += 1
                else:
                    slot = restored_slot(source, guild.id, captured, now_utc())
                    await self.provision(guild, data, slot, conn)
                    current_slots.append(slot)
                    created += 1
                if not await self.member(guild, source["owner_id"]):
                    missing += 1
            except Exception as error:
                failures.append(f"{source['owner_id']} / {source['plan']['name']}: {type(error).__name__}")
                LOG.warning("Restore item failed for guild %s (%s)", guild.id, type(error).__name__)
        await self.audit(guild, "recovery-log", f"Restore: {created} created, {repaired} repaired, "
                         f"{missing} owners not yet in server, {len(failures)} failures.", conn)
        return created, repaired, missing, failures

    async def expiry_slot(self, guild, data, slot, conn):
        if slot["state"] == "closing":
            await self.revoke(guild, data, slot, slot.get("close_reason", "Pending closure"), conn)
            return
        if slot["state"] == "provisioning":
            await self.provision(guild, data, slot, conn)
        if slot.get("held_at") or not slot.get("expires_at"):
            return
        current, expiry = now_utc(), parse_time(slot["expires_at"])
        if expiry > current:
            if not slot.get("reminder_sent") and expiry - current <= timedelta(days=self.cfg["reminder_days"]):
                sent = await self.notify_owner(guild, slot, "Your slot expires soon",
                    f"<#{slot['channel_id']}> expires {display_time(slot['expires_at'])}. Contact staff to renew.")
                if sent:
                    slot["reminder_sent"] = True
                    await self.store.save_slot(slot, conn)
            return
        if not slot.get("notice_at"):
            # Attempt delivery first. No successful notice means no running grace deadline.
            sent = await self.notify_owner(guild, slot, "Your slot has expired",
                f"<#{slot['channel_id']}> is now read-only. You have {self.cfg['grace_days']} days from this notice to renew with staff. "
                "After that renewal window the channel will close.")
            if sent:
                delivered_at = now_utc()
                slot["notice_at"] = stamp(delivered_at)
                slot["grace_until"] = stamp(delivered_at + timedelta(days=self.cfg["grace_days"]))
            slot["permissions_dirty"] = True
            slot["header_dirty"] = True
            await self.store.save_slot(slot, conn)
            await self.repair(guild, data, slot, conn)
        elif parse_time(slot["grace_until"]) <= current:
            await self.revoke(guild, data, slot, "Renewal window ended", conn)

    async def wipe(self, guild, data, conn):
        # Only tracked resources are touched. Untracked channels prevent category deletion.
        for slot in await self.store.slots(guild.id, conn):
            await self.revoke(guild, data, slot, "Server owner requested wipeout", conn)
        ids = [item["channel_id"] for item in data.get("logs", {}).values()]
        ids += [data[k]["channel_id"] for k in ("plans_panel", "recovery_panel") if data.get(k)]
        for channel_id in ids:
            channel = await self.text_channel(guild, channel_id)
            if channel:
                await channel.delete(reason=f"{BRAND} wipeout")
        category_ids = [c["id"] for c in data.get("categories", [])]
        category_ids += [data[k] for k in ("info_category", "log_category") if data.get(k)]
        channels = await guild.fetch_channels()
        for category_id in category_ids:
            category = next((c for c in channels if c.id == category_id), None)
            if category and not any(getattr(c, "category_id", None) == category_id for c in channels):
                await category.delete(reason=f"{BRAND} wipeout")
        for key in ("owner_role", "hold_role", "staff_role"):
            role = self.role(guild, data.get(key, 0))
            if role:
                await role.delete(reason=f"{BRAND} wipeout")
        await conn.execute("DELETE FROM ns_guilds WHERE guild_id=$1", guild.id)

    @tasks.loop(seconds=60, reconnect=True)
    async def maintenance(self):
        if not self.is_ready():
            return
        rows = await self.pool.fetch("SELECT guild_id FROM ns_guilds")
        for row in rows:
            guild = self.get_guild(row["guild_id"])
            if not guild:
                continue
            try:
                async with self.store.lock(guild.id) as conn:
                    data = await self.store.guild(guild.id, conn)
                    if data.get("wiping"):
                        await self.wipe(guild, data, conn)
                        continue
                    schedule = await conn.fetchrow("SELECT last_backup_check,last_expiry_check FROM ns_guilds WHERE guild_id=$1", guild.id)
                    current = now_utc()
                    expiry_due = (self.maintenance.current_loop == 0 or not schedule["last_expiry_check"] or
                                  current - schedule["last_expiry_check"] >= timedelta(minutes=self.cfg["expiry_minutes"]))
                    for slot in await self.store.slots(guild.id, conn):
                        try:
                            if reset_usage(slot, self.cfg):
                                await self.store.save_slot(slot, conn)
                            if slot.get("permissions_dirty") or slot.get("header_dirty"):
                                await self.repair(guild, data, slot, conn)
                            if expiry_due or slot["state"] in ("closing", "provisioning"):
                                await self.expiry_slot(guild, data, slot, conn)
                            if not await self.store.slot(slot["id"], conn):
                                continue
                            if (self.cfg["autoclear"] and not slot.get("held_at") and slot["state"] == "active"
                                    and slot.get("last_clear_day") != slot["ping_day"]):
                                deleted, old = await self.clear_channel(guild, slot, conn)
                                slot["last_clear_day"] = slot["ping_day"]
                                await self.store.save_slot(slot, conn)
                                await self.audit(guild, "ping-log", f"Daily clear <#{slot['channel_id']}>: "
                                    f"{deleted} deleted; {old} too old for bulk deletion.", conn)
                        except Exception as error:
                            LOG.warning("Maintenance will retry slot %s (%s)", slot["id"], type(error).__name__)
                    if expiry_due:
                        await conn.execute("UPDATE ns_guilds SET last_expiry_check=now() WHERE guild_id=$1", guild.id)
                    if self.cfg["autobackup"] and (not schedule["last_backup_check"] or
                        current - schedule["last_backup_check"] >= timedelta(hours=self.cfg["backup_hours"])):
                        await self.snapshot(guild, True, conn)
            except Exception as error:
                LOG.warning("Server maintenance failed for %s (%s)", guild.id, type(error).__name__)
        if time.monotonic() - self.last_cleanup > 3600:
            await self.pool.execute("DELETE FROM ns_processed_messages WHERE created_at < now()-interval '7 days'")
            await self.pool.execute("DELETE FROM ns_recovery_attempts WHERE window_start < now()-interval '1 day'")
            self.last_cleanup = time.monotonic()

    @maintenance.before_loop
    async def before_maintenance(self):
        await self.wait_until_ready()

    @maintenance.error
    async def maintenance_error(self, error):
        LOG.error("Maintenance stopped (%s); exiting for the Railway restart policy", type(error).__name__)
        # Without the maintenance loop, serving new rentals would be unsafe.
        self.fatal_error = True
        asyncio.create_task(self.close())


def validate_backup(payload: Any) -> list[dict]:
    """Untrusted backup files are parsed fully before creating any resources."""
    if not isinstance(payload, dict) or payload.get("format") != "notix-slots" or payload.get("version") != 1:
        raise UserError("This is not a Notix Slots version 1 backup.")
    try:
        snowflake(payload["source_guild_id"], "source_guild_id")
        captured = parse_time(payload["captured_at"])
        if not captured or captured > now_utc() + timedelta(minutes=5):
            raise ValueError("captured_at: invalid or in the future")
        values = payload["slots"]
        categories = payload.get("categories", [])
        if not isinstance(categories, list) or len(categories) > 50:
            raise ValueError("categories: expected at most 50 categories")
        for i, category in enumerate(categories):
            if not isinstance(category, dict):
                raise ValueError(f"categories[{i}]: expected an object")
            category["group"] = bounded_int(category.get("group"), f"categories[{i}].group", 1, 25)
        if not isinstance(values, list) or len(values) > 500:
            raise ValueError("slots: expected a list of at most 500 slots")
        result, pairs, lineages = [], set(), set()
        for i, source in enumerate(values):
            path = f"slots[{i}]"
            if not isinstance(source, dict):
                raise ValueError(f"{path}: expected an object")
            slot = copy.deepcopy(source)
            if not re.fullmatch(r"[a-f0-9]{32}", slot.get("id", "")):
                raise ValueError(f"{path}.id: invalid slot ID")
            lineage = slot.get("lineage_id", slot["id"])
            if not re.fullmatch(r"[a-f0-9]{32}", lineage) or lineage in lineages:
                raise ValueError(f"{path}.lineage_id: invalid or duplicate")
            lineages.add(lineage)
            slot["owner_id"] = snowflake(slot["owner_id"], path + ".owner_id")
            slot["plan"] = normalize_plan(slot["plan"], path + ".plan")
            pair = (slot["owner_id"], slot["plan"]["name"].casefold())
            if pair in pairs:
                raise ValueError(f"{path}: duplicate owner and plan")
            pairs.add(pair)
            for key in ("created_at", "expires_at", "held_at", "notice_at", "grace_until"):
                parsed = parse_time(slot.get(key))
                if key == "created_at" and not parsed:
                    raise ValueError(f"{path}.created_at: missing")
            if bool(slot.get("notice_at")) != bool(slot.get("grace_until")):
                raise ValueError(f"{path}: notice and grace deadline must be paired")
            if not isinstance(slot.get("key_hash"), str) or not re.fullmatch(r"[a-f0-9]{64}", slot["key_hash"]):
                raise ValueError(f"{path}.key_hash: invalid SHA-256 hash")
            for counter in ("here_used", "everyone_used"):
                slot[counter] = bounded_int(slot.get(counter, 0), path + "." + counter, 0, 100000)
            for field in ("ping_day", "last_clear_day"):
                datetime.strptime(slot.get(field, ""), "%Y-%m-%d")
            if slot.get("state") not in ("active", "provisioning", "closing"):
                raise ValueError(f"{path}.state: invalid state")
            if not isinstance(slot.get("reminder_sent", False), bool):
                raise ValueError(f"{path}.reminder_sent: expected boolean")
            reason = slot.get("hold_reason")
            if reason is not None and (not isinstance(reason, str) or len(reason) > 500):
                raise ValueError(f"{path}.hold_reason: expected at most 500 characters")
            result.append(slot)
        return result
    except (ValueError, KeyError, TypeError, OverflowError) as error:
        raise UserError(f"Invalid backup: {error}") from None


def restored_slot(source: dict, guild_id: int, captured: datetime, current: datetime) -> dict:
    # Copy only recognized state. Webhook credentials and staff privileges never import.
    slot = {key: copy.deepcopy(source.get(key)) for key in (
        "owner_id", "plan", "created_at", "expires_at", "held_at", "hold_reason",
        "reminder_sent", "notice_at", "grace_until", "here_used", "everyone_used",
        "ping_day", "last_clear_day", "key_hash")}
    slot.update(id=uuid.uuid4().hex, guild_id=guild_id, channel_id=None, header_id=None,
                state="provisioning", lineage_id=source.get("lineage_id", source["id"]))
    base = parse_time(source.get("held_at")) or captured
    for field in ("expires_at", "grace_until"):
        if source.get(field):
            remaining = max(timedelta(0), parse_time(source[field]) - base)
            slot[field] = stamp(current + remaining)
    slot["held_at"] = stamp(current) if source.get("held_at") else None
    slot["notice_at"] = stamp(current) if source.get("notice_at") else None
    return slot


async def safe_error(target, error):
    actual = getattr(error, "original", error)
    if isinstance(actual, (UserError, commands.UserInputError, commands.CheckFailure, app_commands.CheckFailure)):
        message = str(actual)[:1800]
    elif isinstance(actual, discord.Forbidden):
        message = "Discord denied permission. Check the bot's permissions and move its role above the Notix roles."
    elif isinstance(actual, discord.NotFound):
        message = "That Discord resource is missing. Run /setup to repair managed resources."
    else:
        message = "The operation could not finish. Check Railway logs and try again. Recorded operations can be repaired with /setup."
        LOG.error("Command failed (%s)", type(actual).__name__, exc_info=(type(actual), actual, actual.__traceback__))
    try:
        if isinstance(target, discord.Interaction):
            if target.response.is_done():
                await target.followup.send(message, ephemeral=True)
            else:
                await target.response.send_message(message, ephemeral=True)
        else:
            await target.send(message, ephemeral=True)
    except discord.HTTPException:
        pass


class RecoveryModal(discord.ui.Modal, title="Notix Slots · Recover slot"):
    recovery_key = discord.ui.TextInput(label="32-character recovery key", min_length=32, max_length=32,
                                         placeholder="Paste the key from your private message")

    def __init__(self, bot: NotixBot):
        super().__init__(timeout=300)
        self.bot = bot

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True, thinking=True)
        guild = interaction.guild
        if not guild:
            raise UserError("Recover a slot through the panel in its server.")
        key = str(self.recovery_key).strip().lower()
        async with self.bot.store.lock(guild.id) as conn:
            # Count invalid keys too; this limiter survives process restarts.
            attempts = await conn.fetchval(
                "INSERT INTO ns_recovery_attempts(guild_id,user_id,attempts,window_start) VALUES($1,$2,1,now()) "
                "ON CONFLICT(guild_id,user_id) DO UPDATE SET "
                "attempts=CASE WHEN ns_recovery_attempts.window_start < now()-interval '1 minute' THEN 1 "
                "ELSE ns_recovery_attempts.attempts+1 END, "
                "window_start=CASE WHEN ns_recovery_attempts.window_start < now()-interval '1 minute' THEN now() "
                "ELSE ns_recovery_attempts.window_start END RETURNING attempts", guild.id, interaction.user.id)
            if attempts > 5:
                raise UserError("Too many recovery attempts. Wait one minute.")
            if not re.fullmatch(r"[a-f0-9]{32}", key):
                raise UserError("Invalid or already-used recovery key for this server.")
            slot = await conn.fetchval("SELECT data FROM ns_slots WHERE guild_id=$1 AND data->>'key_hash'=$2",
                                       guild.id, key_hash(key))
            if not slot or slot["state"] != "active":
                raise UserError("Invalid or already-used recovery key for this server.")
            data = await self.bot.store.guild(guild.id, conn)
            if data.get("wiping"):
                raise UserError("This server is being reset.")
            if slot["owner_id"] == interaction.user.id:
                raise UserError("You already own this slot. Ask staff for /slotkey if you need a new key.")
            others = await self.bot.store.slots(guild.id, conn)
            if any(s["owner_id"] == interaction.user.id and s["plan"]["name"].casefold() == slot["plan"]["name"].casefold() for s in others):
                raise UserError("You already own a slot on this plan. Contact staff before transferring another.")
            channel = await self.bot.text_channel(guild, slot["channel_id"])
            if not channel:
                raise UserError("The channel needs repair first. Ask staff to run /setup.")
            # Freeze the old owner's permissions before committing a transfer.
            await channel.edit(overwrites=self.bot.overwrites(guild, data), reason=f"{BRAND} recovery in progress")
            previous = copy.deepcopy(slot)
            replacement, digest = new_key()
            slot.update(owner_id=interaction.user.id, previous_owner_id=slot["owner_id"],
                        key_hash=digest, permissions_dirty=True, header_dirty=True)
            try:
                await self.bot.store.save_slot(slot, conn)
            except Exception:
                with contextlib.suppress(discord.HTTPException):
                    await self.bot.apply_permissions(guild, data, previous)
                raise
            # Supply the new key privately before optional Discord reconciliation.
            await interaction.followup.send(
                f"Ownership transferred to you: <#{slot['channel_id']}>. Your old key is now invalid.\n"
                f"**Save your new recovery key:** `{replacement}`", ephemeral=True)
            await self.bot.send_key(interaction.user.id, replacement, slot["channel_id"])
            try:
                await self.bot.repair(guild, data, slot, conn)
            except discord.HTTPException:
                await interaction.followup.send("Ownership is saved. Discord permissions will be retried automatically.", ephemeral=True)
            await self.bot.audit(guild, "recovery-log", f"<@{previous['owner_id']}> → <@{interaction.user.id}> "
                                 f"for <#{slot['channel_id']}>; recovery key rotated.", conn)
            with contextlib.suppress(discord.HTTPException):
                user = self.bot.get_user(previous["owner_id"]) or await self.bot.fetch_user(previous["owner_id"])
                await user.send(embed=embed("Slot recovered", f"Your recovery key was used to transfer <#{slot['channel_id']}>. "
                                            "Contact server staff if you did not request this."))

    async def on_error(self, interaction, error):
        await safe_error(interaction, error)


class RecoveryView(discord.ui.View):
    def __init__(self, bot):
        super().__init__(timeout=None)
        self.bot = bot

    @discord.ui.button(label="Recover slot", style=discord.ButtonStyle.primary, custom_id="notix:recover:v1")
    async def recover(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.send_modal(RecoveryModal(self.bot))

    async def on_error(self, interaction, error, item):
        await safe_error(interaction, error)


async def defer(ctx):
    await ctx.defer(ephemeral=True)


async def deletion_result(ctx, message):
    """Prefix commands can delete the very channel in which they were invoked."""
    try:
        await ctx.send(message, ephemeral=True)
    except (discord.NotFound, discord.Forbidden):
        with contextlib.suppress(discord.HTTPException):
            await ctx.author.send(message)


async def send_lines(ctx, title, lines):
    if not lines:
        await ctx.send(embed=embed(title, "No entries."), ephemeral=True)
        return
    text = ""
    for line in lines:
        if len(text) + len(line) + 1 > 3800:
            await ctx.send(embed=embed(title, text), ephemeral=True)
            text = ""
        text += line + "\n"
    if text:
        await ctx.send(embed=embed(title, text), ephemeral=True)


def register_commands(bot: NotixBot):
    """Both command surfaces call the same handlers and runtime permission checks."""
    def access(level="any", guild_only=False):
        async def predicate(ctx):
            if guild_only and not ctx.guild:
                raise UserError("Use this command in your server.")
            await bot.require(ctx, level)
            if ctx.guild:
                data = await bot.store.guild(ctx.guild.id)
                if data.get("wiping"):
                    raise UserError("A wipeout is in progress. Check the bot's permissions if it cannot finish.")
            return True
        return commands.check(predicate)

    async def staff_slot(ctx, channel):
        target = channel or ctx.channel
        slot = await bot.store.by_channel(target.id)
        if not slot or slot["guild_id"] != ctx.guild.id:
            raise UserError("Select a slot channel, or run this command inside one.")
        return slot

    @bot.hybrid_command(name="help", description="Show the commands available to you")
    @access()
    async def help_command(ctx):
        await defer(ctx)
        card = embed("Notix Slots · Help", f"Use slash commands or `{bot.cfg['prefix']}command`. "
                     "`/createslot` is slash-only. Slash replies are private unless noted.")
        card.add_field(name="Everyone", value="`/plans` `/ping` `/say` `/pings` `/clear`", inline=False)
        if await bot.permitted(ctx.author, ctx.guild, "admin"):
            card.add_field(name="Staff", value="`/setup` `/createslot` `/renewslot` `/revokeslot` `/hold` `/unhold` "
                           "`/holdlist` `/slots` `/slotkey` `/slotbanner` `/wipeout`", inline=False)
        if await bot.permitted(ctx.author, ctx.guild, "owner"):
            card.add_field(name="Server / bot owners", value="`/adminadd` `/adminremove` `/adminlist` `/reload` "
                           "`/backup` `/backups` `/restore`", inline=False)
        card.add_field(name="Ping policy", value="A direct broadcast mention over your budget closes your slot. "
                       "`/say` checks the allowance before sending. Recovery uses the server's button panel.", inline=False)
        await ctx.send(embed=card, ephemeral=True)

    @bot.hybrid_command(description="Display the current slot plans publicly")
    @access()
    async def plans(ctx):
        await ctx.send(embed=bot.plans_embed())

    @bot.hybrid_command(description="Check bot connection latency")
    @access()
    async def ping(ctx):
        await ctx.send(f"Notix Slots: {bot.latency * 1000:.0f} ms.", ephemeral=True)

    @bot.hybrid_command(description="Post an advert in your slot, including from DMs")
    @app_commands.describe(message="The text to post (2,000 characters maximum)", channel_id="Slot channel ID if you own several")
    @access()
    async def say(ctx, channel_id: str = "", *, message: str):
        # Prefix: .say CHANNEL_ID your message. Slash: message field + optional channel_id.
        await defer(ctx)
        slot = await bot.resolve_slot(ctx.author.id, ctx.guild, channel_id or None)
        guild = bot.get_guild(slot["guild_id"])
        if not guild:
            raise UserError("The bot cannot currently access that server.")
        request_id = ctx.interaction.id if ctx.interaction else ctx.message.id
        url = await bot.post_advert(guild, slot["id"], ctx.author.id, message, request_id)
        await ctx.send(f"[Your advert was posted.]({url})", ephemeral=True)

    @bot.hybrid_command(description="Show your remaining daily ping allowances")
    @access()
    async def pings(ctx, channel_id: str = ""):
        await defer(ctx)
        slot = await bot.resolve_slot(ctx.author.id, ctx.guild, channel_id or None)
        async with bot.store.lock(slot["guild_id"]) as conn:
            slot = await bot.store.slot(slot["id"], conn)
            if not slot or slot["owner_id"] != ctx.author.id:
                raise UserError("You no longer own this slot.")
            reset_usage(slot, bot.cfg)
            await bot.store.save_slot(slot, conn)
            _, reset = day_and_reset(bot.cfg)
            await ctx.send(embed=embed("Notix Slots · Ping balance",
                f"<#{slot['channel_id']}>\n"
                f"@here: **{max(0, slot['plan']['here']-slot['here_used'])} / {slot['plan']['here']} left**\n"
                f"@everyone: **{max(0, slot['plan']['everyone']-slot['everyone_used'])} / {slot['plan']['everyone']} left**\n"
                f"Resets <t:{int(reset.timestamp())}:R> · midnight in **{bot.cfg['timezone']}**"), ephemeral=True)

    @bot.hybrid_command(description="Clear your slot while preserving its header")
    @access()
    async def clear(ctx, channel_id: str = ""):
        await defer(ctx)
        slot = await bot.resolve_slot(ctx.author.id, ctx.guild, channel_id or None, allow_admin=True)
        guild = bot.get_guild(slot["guild_id"])
        if not guild:
            raise UserError("The slot's server is unavailable.")
        async with bot.store.lock(guild.id) as conn:
            slot = await bot.store.slot(slot["id"], conn)
            if not slot or (slot["owner_id"] != ctx.author.id and not await bot.permitted(ctx.author, ctx.guild, "admin", conn)):
                raise UserError("You no longer have access to that slot.")
            deleted, old = await bot.clear_channel(guild, slot, conn)
        await ctx.send(f"Deleted {deleted} messages. Header preserved. {old} old messages remain because Discord "
                       "does not bulk-delete messages older than 14 days.", ephemeral=True)

    @bot.hybrid_command(description="Build or repair Notix roles, categories, panels and slots")
    @access("admin", True)
    async def setup(ctx, categories: commands.Range[int, 1, 25] = 2):
        await defer(ctx)
        failures = []
        async with bot.store.lock(ctx.guild.id) as conn:
            data = await bot.ensure_setup(ctx.guild, categories, conn)
            for slot in await bot.store.slots(ctx.guild.id, conn):
                try:
                    if slot["state"] == "closing":
                        await bot.revoke(ctx.guild, data, slot, slot.get("close_reason", "Pending closure"), conn)
                    elif not await bot.text_channel(ctx.guild, slot.get("channel_id")) or slot["state"] == "provisioning":
                        await bot.provision(ctx.guild, data, slot, conn)
                    else:
                        await bot.repair(ctx.guild, data, slot, conn)
                except Exception as error:
                    failures.append(f"{slot['id'][:8]}: {type(error).__name__}")
        await ctx.send("Notix Slots setup finished. Use `/createslot` to issue a slot." +
                       ("\nSlots needing another repair: " + ", ".join(failures)[:1400] if failures else ""), ephemeral=True)

    @bot.tree.command(name="createslot", description="Issue a channel to a buyer on a configured plan")
    @app_commands.guild_only()
    @app_commands.describe(user="Buyer who has joined this server", plan="Choose a configured plan")
    async def createslot(interaction: discord.Interaction, user: discord.Member, plan: str):
        await interaction.response.defer(ephemeral=True, thinking=True)
        if not await bot.permitted(interaction.user, interaction.guild, "admin"):
            raise UserError("Notix admin access is required.")
        if user.bot:
            raise UserError("A slot must belong to a human member.")
        chosen = next((p for p in bot.cfg["plans"] if p["name"].casefold() == plan.casefold()), None)
        if not chosen:
            raise UserError("Unknown plan. Choose one from /plans.")
        async with bot.store.lock(interaction.guild_id) as conn:
            data = await bot.store.guild(interaction.guild_id, conn)
            if not data.get("owner_role") or data.get("wiping"):
                raise UserError("Run /setup first, or wait for the reset to finish.")
            duplicate = await conn.fetchval("SELECT id FROM ns_slots WHERE guild_id=$1 AND owner_id=$2 AND lower(plan_name)=lower($3)",
                                             interaction.guild_id, user.id, chosen["name"])
            if duplicate:
                raise UserError("That member already has this plan. Use /renewslot or choose another plan.")
            slot, key = make_slot(interaction.guild_id, user.id, chosen, bot.cfg)
            await bot.provision(interaction.guild, data, slot, conn)
            delivered = await bot.send_key(user.id, key, slot["channel_id"])
            await bot.audit(interaction.guild, "slot-created", f"<@{interaction.user.id}> issued "
                f"<#{slot['channel_id']}> to <@{user.id}> on **{chosen['name']}** ({chosen['price']}).", conn)
        await interaction.followup.send(f"Created <#{slot['channel_id']}> for {user.mention}. " +
            ("The recovery key was sent by DM." if delivered else
             "Their DMs are closed. Ask them to open DMs, then use `/slotkey` to issue a replacement key."), ephemeral=True)

    @createslot.autocomplete("plan")
    async def plan_autocomplete(interaction, current):
        return [app_commands.Choice(name=p["name"], value=p["name"]) for p in bot.cfg["plans"]
                if current.casefold() in p["name"].casefold()][:25]

    @bot.hybrid_command(description="Extend a slot using its original plan or a custom number of days")
    @access("admin", True)
    async def renewslot(ctx, channel: discord.TextChannel | None = None, days: commands.Range[int, 1, 3650] | None = None):
        await defer(ctx)
        initial = await staff_slot(ctx, channel)
        async with bot.store.lock(ctx.guild.id) as conn:
            slot = await bot.store.slot(initial["id"], conn)
            if not slot or slot["state"] != "active":
                raise UserError("This slot is not active or is already closing.")
            if not slot.get("expires_at"):
                raise UserError("Lifetime slots do not need renewal.")
            length = days or slot["plan"]["days"]
            base = parse_time(slot.get("held_at")) or now_utc()
            slot["expires_at"] = stamp(max(base, parse_time(slot["expires_at"])) + timedelta(days=length))
            slot.update(notice_at=None, grace_until=None, reminder_sent=False, permissions_dirty=True, header_dirty=True)
            await bot.store.save_slot(slot, conn)
            data = await bot.store.guild(ctx.guild.id, conn)
            await bot.repair(ctx.guild, data, slot, conn)
            await bot.audit(ctx.guild, "slot-created", f"<@{ctx.author.id}> renewed <#{slot['channel_id']}> by {length} days.", conn)
        await ctx.send(f"Renewed <#{slot['channel_id']}>. Expiry: {display_time(slot['expires_at'])}. "
                       "A held slot remains held until /unhold.", ephemeral=True)

    @bot.hybrid_command(description="Delete a slot channel and revoke ownership")
    @access("admin", True)
    async def revokeslot(ctx, channel: discord.TextChannel | None = None, *, reason: str = "Revoked by staff"):
        await defer(ctx)
        initial = await staff_slot(ctx, channel)
        async with bot.store.lock(ctx.guild.id) as conn:
            slot = await bot.store.slot(initial["id"], conn)
            if not slot:
                raise UserError("The slot has already been revoked.")
            data = await bot.store.guild(ctx.guild.id, conn)
            await bot.revoke(ctx.guild, data, slot, reason, conn)
        await deletion_result(ctx, "Slot revoked and channel deleted.")

    @bot.hybrid_command(name="hold", aliases=["holdslot"], description="Pause a slot and freeze its remaining time")
    @access("admin", True)
    async def hold(ctx, channel: discord.TextChannel | None = None, *, reason: str = "Paused by staff"):
        await defer(ctx)
        initial = await staff_slot(ctx, channel)
        async with bot.store.lock(ctx.guild.id) as conn:
            slot = await bot.store.slot(initial["id"], conn)
            if not slot or slot["state"] != "active":
                raise UserError("This slot cannot be held while it is being created or closed.")
            if slot.get("held_at"):
                raise UserError("This slot is already on hold.")
            slot.update(held_at=stamp(now_utc()), hold_reason=reason[:500], permissions_dirty=True, header_dirty=True)
            await bot.store.save_slot(slot, conn)
            data = await bot.store.guild(ctx.guild.id, conn)
            await bot.repair(ctx.guild, data, slot, conn)
            await bot.audit(ctx.guild, "slot-holds", f"<@{ctx.author.id}> held <#{slot['channel_id']}>.\n{reason[:500]}", conn)
        await ctx.send("Slot held. Posting and its expiry/renewal clocks are paused.", ephemeral=True)

    @bot.hybrid_command(name="unhold", aliases=["unholdslot"], description="Resume a held slot and return its frozen time")
    @access("admin", True)
    async def unhold(ctx, channel: discord.TextChannel | None = None):
        await defer(ctx)
        initial = await staff_slot(ctx, channel)
        async with bot.store.lock(ctx.guild.id) as conn:
            slot = await bot.store.slot(initial["id"], conn)
            if not slot:
                raise UserError("This slot no longer exists.")
            shift_after_hold(slot, now_utc())
            slot.update(permissions_dirty=True, header_dirty=True)
            await bot.store.save_slot(slot, conn)
            data = await bot.store.guild(ctx.guild.id, conn)
            await bot.repair(ctx.guild, data, slot, conn)
            await bot.audit(ctx.guild, "slot-holds", f"<@{ctx.author.id}> resumed <#{slot['channel_id']}>.", conn)
        await ctx.send(f"Slot resumed. Expiry: {display_time(slot.get('expires_at'))}.", ephemeral=True)

    @bot.hybrid_command(description="List held slots")
    @access("admin", True)
    async def holdlist(ctx):
        await defer(ctx)
        values = [s for s in await bot.store.slots(ctx.guild.id) if s.get("held_at")]
        await send_lines(ctx, "Held slots", [f"<#{s['channel_id']}> · <@{s['owner_id']}> · {s.get('hold_reason', '')}" for s in values])

    @bot.hybrid_command(description="List all slots sold in this server")
    @access("admin", True)
    async def slots(ctx):
        await defer(ctx)
        values = await bot.store.slots(ctx.guild.id)
        await send_lines(ctx, "Notix Slots · All slots", [f"<#{s['channel_id']}> · <@{s['owner_id']}> · "
            f"{s['plan']['name']} ({s['plan']['price']}) · {title_state(s)} · {display_time(s.get('expires_at'))}" for s in values])

    @bot.hybrid_command(description="DM a replacement recovery key to a slot's current owner")
    @access("admin", True)
    async def slotkey(ctx, channel: discord.TextChannel | None = None):
        await defer(ctx)
        initial = await staff_slot(ctx, channel)
        async with bot.store.lock(ctx.guild.id) as conn:
            slot = await bot.store.slot(initial["id"], conn)
            if not slot or slot["state"] != "active":
                raise UserError("This slot is not available for key rotation.")
            key, digest = new_key()
            # Deliver first; a failed DM must not invalidate a working key.
            if not await bot.send_key(slot["owner_id"], key, slot["channel_id"]):
                raise UserError("The owner must enable DMs first. Their existing key is unchanged.")
            slot["key_hash"] = digest
            await bot.store.save_slot(slot, conn)
            await bot.audit(ctx.guild, "recovery-log", f"<@{ctx.author.id}> rotated the key for <#{slot['channel_id']}>.", conn)
        await ctx.send("Replacement key delivered. The previous key is invalid.", ephemeral=True)

    @bot.hybrid_command(description="Preview one of three generated slot banner designs")
    @access("admin", True)
    async def slotbanner(ctx, design: commands.Range[int, 1, 3] = 1):
        await defer(ctx)
        slot, _ = make_slot(ctx.guild.id, ctx.author.id, bot.cfg["plans"][0], bot.cfg)
        slot["state"] = "active"
        avatar = await ctx.author.display_avatar.with_size(256).with_format("png").read()
        data = await asyncio.to_thread(render_banner, slot, ctx.author.display_name, avatar, design)
        await ctx.send(file=discord.File(io.BytesIO(data), filename=f"notix-banner-{design}.png"), ephemeral=True)

    @bot.hybrid_command(description="Grant Notix admin access in this server")
    @access("owner", True)
    async def adminadd(ctx, user: discord.Member):
        await defer(ctx)
        if user.bot:
            raise UserError("Choose a human member.")
        async with bot.store.lock(ctx.guild.id) as conn:
            data = await bot.store.guild(ctx.guild.id, conn)
            data["admins"] = sorted(set(data.get("admins", [])) | {user.id})
            await bot.store.save_guild(ctx.guild.id, data, conn)
            role = bot.role(ctx.guild, data.get("staff_role", 0))
            if role:
                await user.add_roles(role, reason=f"{BRAND} admin grant")
            await bot.audit(ctx.guild, "recovery-log", f"<@{ctx.author.id}> granted Notix admin to <@{user.id}>.", conn)
        await ctx.send(f"Notix admin granted to {user.mention}.", ephemeral=True)

    @bot.hybrid_command(description="Remove a granted Notix admin")
    @access("owner", True)
    async def adminremove(ctx, user: str):
        await defer(ctx)
        try:
            user_id = snowflake(re.sub(r"[<@!>]", "", user), "user")
        except ValueError as error:
            raise UserError(str(error)) from None
        if bot.owner(user_id, ctx.guild):
            raise UserError("Server and configured bot owners always retain owner access.")
        async with bot.store.lock(ctx.guild.id) as conn:
            data = await bot.store.guild(ctx.guild.id, conn)
            data["admins"] = [i for i in data.get("admins", []) if i != user_id]
            await bot.store.save_guild(ctx.guild.id, data, conn)
            member = await bot.member(ctx.guild, user_id)
            role = bot.role(ctx.guild, data.get("staff_role", 0))
            if member and role:
                await member.remove_roles(role, reason=f"{BRAND} admin removal")
            await bot.audit(ctx.guild, "recovery-log", f"<@{ctx.author.id}> removed Notix admin from <@{user_id}>.", conn)
        await ctx.send("Notix admin grant removed. Discord members with Administrator permission still have admin access.", ephemeral=True)

    @bot.hybrid_command(description="List this server's granted Notix admins and owners")
    @access("owner", True)
    async def adminlist(ctx):
        await defer(ctx)
        data = await bot.store.guild(ctx.guild.id)
        owners = bot.configured_owners | {ctx.guild.owner_id}
        await send_lines(ctx, "Notix Slots · Access", ["Owners: " + ", ".join(f"<@{i}>" for i in sorted(owners)),
            "Granted admins: " + (", ".join(f"<@{i}>" for i in data.get("admins", [])) or "None"),
            "Members with Discord Administrator permission also have admin access."])

    @bot.hybrid_command(description="Reload settings, or import a JSON settings attachment without restarting")
    @access("owner", True)
    async def reload(ctx, config: discord.Attachment | None = None, reset: bool = False):
        await defer(ctx)
        if ctx.author.id not in bot.configured_owners and (bot.configured_owners or len(bot.guilds) != 1):
            raise UserError("/reload changes global settings. Add your ID to OWNER_IDS to manage it.")
        if config is None and not ctx.interaction and ctx.message.attachments:
            config = ctx.message.attachments[0]
        if config and reset:
            raise UserError("Choose either a config attachment or reset=true.")
        patch = None
        if config:
            if config.size > 65536:
                raise UserError("Settings files must be smaller than 64 KiB.")
            try:
                patch = json.loads(await config.read())
                if not isinstance(patch, dict):
                    raise ValueError("expected a JSON object")
            except (json.JSONDecodeError, UnicodeDecodeError, ValueError):
                raise UserError("Attach a valid JSON object containing settings to update.") from None
        async with bot.store.lock(0) as conn:
            previous = bot.cfg
            overrides = {} if reset else (await conn.fetchval("SELECT data FROM ns_settings WHERE id=1") or {})
            if patch is not None:
                overrides.update(patch)
            try:
                candidate = validate_config({**environment_config(), **overrides})
            except ValueError as error:
                raise UserError(str(error)) from None
            await conn.execute("INSERT INTO ns_settings(id,data) VALUES(1,$1) ON CONFLICT(id) DO UPDATE SET data=EXCLUDED.data", overrides)
            bot.cfg = candidate
        changed = [k for k in candidate if candidate[k] != previous[k]]
        # A refreshed header explains the current reset timezone; commercial terms remain snapshots.
        if any(k in changed for k in ("timezone", "banner_style")):
            await bot.pool.execute("UPDATE ns_slots SET data=jsonb_set(data,'{header_dirty}','true'::jsonb)")
        await ctx.send("Settings loaded. Changed: " + (", ".join(changed) or "none") +
            ". Run /setup to refresh public panels. Railway variable edits require a service restart; "
            "a JSON attachment updates these settings immediately. Code changes require redeployment.", ephemeral=True)

    async def load_backup(ctx, identifier):
        try:
            number = bounded_int(identifier, "backup_id", 1, 2**63-1)
        except ValueError as error:
            raise UserError(str(error)) from None
        row = await bot.pool.fetchrow("SELECT * FROM ns_backups WHERE id=$1", number)
        if not row:
            raise UserError("Backup not found. Use /backups to see available IDs.")
        if row["guild_id"] != ctx.guild.id and not bot.owner(ctx.author.id, bot.get_guild(row["guild_id"])):
            raise UserError("You must own the source server to use this backup ID. Otherwise upload an authorized exported backup.")
        return dict(row)

    @bot.hybrid_command(description="Save and export a backup, or export an existing backup ID")
    @access("owner", True)
    async def backup(ctx, backup_id: str = ""):
        await defer(ctx)
        if backup_id:
            row = await load_backup(ctx, backup_id)
        else:
            async with bot.store.lock(ctx.guild.id) as conn:
                if not await conn.fetchval("SELECT 1 FROM ns_guilds WHERE guild_id=$1", ctx.guild.id):
                    raise UserError("Run /setup before taking the first backup.")
                row = await bot.snapshot(ctx.guild, False, conn)
        buffer = io.BytesIO(json.dumps(row["payload"], indent=2, ensure_ascii=False).encode())
        file = discord.File(buffer, filename=f"notix-backup-{row['id']}.json")
        message = f"Backup **{row['id']}** is stored in PostgreSQL. This export contains recovery-key hashes; keep it private."
        if ctx.interaction:
            await ctx.send(message, file=file, ephemeral=True)
        else:
            try:
                await ctx.author.send(message, file=file)
            except discord.Forbidden:
                raise UserError(f"Backup {row['id']} is saved. Enable DMs or use slash /backup backup_id:{row['id']} to download it privately.") from None
            await ctx.send(f"Backup {row['id']} saved; export sent by DM.")

    @bot.hybrid_command(description="List the newest 25 stored backups for this server")
    @access("owner", True)
    async def backups(ctx):
        await defer(ctx)
        rows = await bot.pool.fetch("SELECT id,automatic,created_at FROM ns_backups WHERE guild_id=$1 ORDER BY id DESC LIMIT 25", ctx.guild.id)
        await send_lines(ctx, "Notix Slots · Backups", [f"**{r['id']}** · {'Automatic' if r['automatic'] else 'Manual'} · "
            f"<t:{int(r['created_at'].timestamp())}:F>" for r in rows])

    @bot.hybrid_command(description="Rebuild or repair slots from a saved backup ID or JSON attachment")
    @access("owner", True)
    async def restore(ctx, backup_id: str = "", attachment: discord.Attachment | None = None):
        await defer(ctx)
        if attachment is None and not ctx.interaction and ctx.message.attachments:
            attachment = ctx.message.attachments[0]
        if bool(backup_id) == bool(attachment):
            raise UserError("Provide exactly one backup_id or JSON attachment.")
        if attachment:
            if attachment.size > 8 * 1024 * 1024:
                raise UserError("Backup exports must be 8 MiB or smaller.")
            try:
                payload = json.loads(await attachment.read())
            except (json.JSONDecodeError, UnicodeDecodeError):
                raise UserError("That attachment is not valid JSON.") from None
        else:
            payload = (await load_backup(ctx, backup_id))["payload"]
        validate_backup(payload)
        async with bot.store.lock(ctx.guild.id) as conn:
            created, repaired, missing, failures = await bot.restore_snapshot(ctx.guild, payload, conn)
        await ctx.send(f"Restore finished: **{created} created**, **{repaired} repaired**, **{missing} owners not yet in the server**. "
            "Returning owners get access when they join. Existing live slot terms were preserved." +
            ("\nRetry /restore to repair these failures:\n" + "\n".join(failures)[:1200] if failures else ""), ephemeral=True)

    @bot.hybrid_command(description="Delete all tracked Notix resources; type this server ID to confirm")
    @access("admin", True)
    async def wipeout(ctx, confirmation: str):
        await defer(ctx)
        if confirmation != str(ctx.guild.id):
            raise UserError(f"This permanently deletes all Notix slot channels, panels, log channels and roles. "
                            f"To confirm, run /wipeout confirmation:{ctx.guild.id}. Backups are retained.")
        async with bot.store.lock(ctx.guild.id) as conn:
            data = await bot.store.guild(ctx.guild.id, conn)
            if not await conn.fetchval("SELECT 1 FROM ns_guilds WHERE guild_id=$1", ctx.guild.id):
                raise UserError("No Notix setup is recorded in this server.")
            saved = await bot.snapshot(ctx.guild, False, conn)
            data["wiping"] = True
            await bot.store.save_guild(ctx.guild.id, data, conn)
            await bot.wipe(ctx.guild, data, conn)
        await deletion_result(ctx, f"Notix resources removed. Backup **{saved['id']}** remains available with /restore. "
                              "Untracked channels were preserved.")

    @bot.event
    async def on_command_error(ctx, error):
        if isinstance(error, commands.CommandNotFound):
            return
        await safe_error(ctx, error)

    @bot.tree.error
    async def on_app_command_error(interaction, error):
        await safe_error(interaction, error)


async def run():
    cfg = environment_config()
    for name in ("DISCORD_TOKEN", "DATABASE_URL"):
        if not os.environ.get(name, "").strip():
            raise ValueError(f"Missing Railway variable: {name}")
    if not os.environ["DATABASE_URL"].startswith(("postgres://", "postgresql://")):
        raise ValueError("DATABASE_URL must be a PostgreSQL connection URL")
    owners = {snowflake(value.strip(), "OWNER_IDS") for value in os.environ.get("OWNER_IDS", "").split(",") if value.strip()}
    bot = NotixBot(cfg, owners)
    register_commands(bot)
    loop = asyncio.get_running_loop()
    for sig in (signal.SIGINT, signal.SIGTERM):
        with contextlib.suppress(NotImplementedError):
            loop.add_signal_handler(sig, lambda: asyncio.create_task(bot.close()))
    async with bot:
        await bot.start(os.environ["DISCORD_TOKEN"].strip())
    if bot.fatal_error:
        raise RuntimeError("Maintenance stopped; restart required")


if __name__ == "__main__":
    logging.basicConfig(level=os.environ.get("LOG_LEVEL", "INFO").upper(),
                        format="%(asctime)s %(levelname)s %(name)s: %(message)s")
    try:
        asyncio.run(run())
    except (ValueError, discord.LoginFailure) as error:
        LOG.error("Startup failed: %s", error)
        raise SystemExit(1) from None
