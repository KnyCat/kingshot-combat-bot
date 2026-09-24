from __future__ import annotations

import copy
import csv
import hashlib
import html
import itertools
import json
import math
import os
import random
import re
import secrets
import sqlite3
import subprocess
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, time as dtime, timedelta, timezone
from io import BytesIO, StringIO
from pathlib import Path
from typing import Any
from urllib.parse import parse_qsl, quote, urlencode, urlparse

import requests
from openpyxl import Workbook
from openpyxl.utils import get_column_letter
from flask import Flask, abort, jsonify, redirect, render_template, request, send_from_directory, session, url_for

from simulator_web.coordinated_attack_storage import CoordinatedAttackStorage
from simulator_web.email_auth import (
    EmailAuthError,
    EmailDeliveryError,
    EmailRateLimitError,
    SmtpSettings,
    consume_email_challenge,
    create_email_challenge,
    initialize_email_auth_schema,
    normalize_email,
    send_verification_email,
)
from simulator_web.ac_simulator import optimize_lanes, simulate_lane, split_roster
from simulator_web.bear_capacity import calculate_buffed_march_capacity
from simulator_web.bear_engine import calculate_bear_hunt
from simulator_web.optimizer import BattleCompositionOptimizer
from models.troop_base_stats import get_troop_base_stats

HEROES_DATA_PATH = Path("data/heroes_kingshot_external.json")
HEROES_OVERRIDES_PATH = Path("data/heroes_manual_overrides.json")
HEROES_PROGRESSION_OVERRIDES_PATH = Path("data/heroes_progression_overrides.json")
STATIC_ROOT = Path("simulator_web/static")
ASSETS_ROOT = Path(__file__).resolve().parent.parent / "assets"
PROJECT_ROOT = Path(__file__).resolve().parent.parent
DISCORD_BOT_INVITE_URL = "https://discord.com/oauth2/authorize?client_id=1464811298758983760"
DISCORD_OAUTH_CLIENT_ID = os.getenv("DISCORD_CLIENT_ID", "1464811298758983760")
DISCORD_OAUTH_CLIENT_SECRET = os.getenv("DISCORD_CLIENT_SECRET", "")
DISCORD_OAUTH_REDIRECT_URI = os.getenv("DISCORD_OAUTH_REDIRECT_URI", "https://kingshot.es/discord-login/callback")
DISCORD_OAUTH_AUTHORIZE_URL = "https://discord.com/oauth2/authorize"
DISCORD_OAUTH_TOKEN_URL = "https://discord.com/api/oauth2/token"
DISCORD_API_USERS_ME_URL = "https://discord.com/api/users/@me"
DISCORD_BOT_API_BASE_URL = "https://discord.com/api/v10"
NOTIFICATIONS_BOT_GUILD_CONFIG_PATH = PROJECT_ROOT / "data" / "notifications" / "guild_config.json"
DEFAULT_BOT_PUBLIC_CHANNEL_KEYS = ("announcements", "bot_commands")
DEFAULT_PUBLIC_CHANNEL_NAME_PREFERENCES = (
    "announcements",
    "general",
    "chat",
    "lobby",
    "main",
    "public",
    "events",
)
JEABSPLUS_API_BASE_URL = os.getenv("JEABSPLUS_API_BASE_URL", "https://jeabslist.com/api/v1").rstrip("/")
PUBLIC_SITE_URL = os.getenv("PUBLIC_SITE_URL", "https://kingshot.es").rstrip("/")
PUBLIC_ROSTER_ALLIANCE_TAG = os.getenv("PUBLIC_ROSTER_ALLIANCE_TAG", "").strip()
JEABSPLUS_RETRYABLE_STATUS_CODES = {408, 425, 429, 500, 502, 503, 504}
JEABSPLUS_MAX_RETRIES = 3
JEABSPLUS_RETRY_BASE_DELAY_SECONDS = 0.7
JEABSPLUS_DETAIL_MAX_WORKERS = 10
JEABSPLUS_HERO_GEAR_CACHE_MINUTES = 15
JEABSPLUS_MIN_REQUEST_INTERVAL_SECONDS = 0.62
JEABS_SYNC_JOBS: dict[str, dict[str, Any]] = {}
JEABS_SYNC_JOBS_LOCK = threading.Lock()
JEABSPLUS_RATE_LOCK = threading.Lock()
JEABSPLUS_NEXT_REQUEST_AT = 0.0
COORDINATED_ATTACK_PRESETS_PATH = Path("data/coordinated_attack_presets.json")
COORDINATED_ATTACK_TARGETS = {"NORTH TOWER", "SOUTH TOWER", "EAST TOWER", "WEST TOWER", "CENTER", "OUTPOSTS", "OBJECTIVE"}
COORDINATED_ATTACK_MESSAGE_LIMIT = 450
SIMULATOR_PROGRESS_ALLOWED_IPS = {"79.117.53.7"}
COORDINATED_ATTACK_MAX_NICK_LENGTH = 20
COORDINATED_ATTACK_MAX_MARCH_SECONDS = 599
COORDINATED_ATTACK_HERO_LINE_MAX_CHARS = 140
COORDINATED_ATTACK_COMPLEMENTARY_MAX_CHARS = 450
MAX_OCR_COMBAT_BONUS = 5000.0
STATS_OWNER_DISCORD_ID = "100002913253859328"
COORDINATED_ATTACK_TARGET_ALIASES = {
    "TORRE NORTE": "NORTH TOWER",
    "TORRE SUR": "SOUTH TOWER",
    "TORRE ESTE": "EAST TOWER",
    "TORRE OESTE": "WEST TOWER",
    "CENTRO": "CENTER",
    "NORTH TOWER": "NORTH TOWER",
    "SOUTH TOWER": "SOUTH TOWER",
    "EAST TOWER": "EAST TOWER",
    "WEST TOWER": "WEST TOWER",
    "CENTER": "CENTER",
    "OUTPOSTS": "OUTPOSTS",
    "OBJECTIVE": "OBJECTIVE",
}
COORDINATED_ATTACK_RALLY_MINUTES = {1, 2, 5}
DATABASE_PATH = PROJECT_ROOT / "data" / "alliance_registry.sqlite3"
VIP_LEVEL_OPTIONS = list(range(0, 13))
TROOP_ICON_MAP = {
    "infantry": "🛡️",
    "cavalry": "🐎",
    "archer": "🏹",
    "mage": "✨",
    "siege": "🛠️",
}
RARITY_ORDER = {
    "legendary": 0,
    "epic": 1,
    "rare": 2,
    "common": 3,
}


def _alliance_invite_image_version() -> str:
    try:
        image_stat = (STATIC_ROOT / "alliance-invite.png").stat()
        return f"{image_stat.st_mtime_ns:x}-{image_stat.st_size:x}"
    except OSError:
        return "1"


def _alliance_invite_image_url() -> str:
    return f"{PUBLIC_SITE_URL}/static/alliance-invitation-banner.png"


def _local_static_exists(url: str) -> bool:
    if not url.startswith("/static/"):
        return False
    rel = url[len("/static/") :].strip("/")
    if not rel:
        return False
    return (STATIC_ROOT / rel).exists()


def _prefer_local(local_url: str, remote_url: str) -> str:
    if local_url and _local_static_exists(local_url):
        return local_url
    return remote_url


def _get_client_ip() -> str:
    forwarded_for = str(request.headers.get("CF-Connecting-IP") or request.headers.get("X-Forwarded-For") or "").strip()
    if forwarded_for:
        return forwarded_for.split(",", 1)[0].strip()
    return str(request.remote_addr or "").strip()


def _can_view_simulator_progress() -> bool:
    return _get_client_ip() in SIMULATOR_PROGRESS_ALLOWED_IPS


def _can_access_bear_calculator(user: dict[str, Any] | None) -> bool:
    return bool(user and user.get("alliance_id"))


def _can_access_usage_stats(user: dict[str, Any] | None) -> bool:
    return bool(user and str(user.get("discord_user_id") or "") == STATS_OWNER_DISCORD_ID)


def _build_usage_stats_context() -> dict[str, Any]:
    now = datetime.now(timezone.utc)
    since_30_days = (now - timedelta(days=29)).date().isoformat()
    with _get_db_connection() as connection:
        event_rows = connection.execute(
            """
            SELECT usage_events.*, alliance_users.username, alliance_users.discord_user_id,
                   alliances.tag AS alliance_tag
            FROM usage_events
            JOIN alliance_users ON alliance_users.id = usage_events.user_id
            LEFT JOIN alliances ON alliances.id = usage_events.alliance_id
            WHERE usage_events.occurred_at >= ?
              AND alliance_users.discord_user_id NOT LIKE 'jeabsplus:%'
            ORDER BY usage_events.occurred_at DESC
            """,
            (f"{since_30_days}T00:00:00+00:00",),
        ).fetchall()
        user_rows = connection.execute(
            """
            SELECT alliance_users.id, alliance_users.username, alliance_users.discord_user_id,
                   alliances.tag AS alliance_tag,
                   MAX(usage_events.occurred_at) AS last_used_at,
                   COUNT(usage_events.id) AS total_visits,
                   SUM(CASE WHEN usage_events.occurred_at >= ? THEN 1 ELSE 0 END) AS visits_30d
            FROM alliance_users
            LEFT JOIN alliances ON alliances.id = alliance_users.alliance_id
            LEFT JOIN usage_events ON usage_events.user_id = alliance_users.id
            WHERE alliance_users.discord_user_id NOT LIKE 'jeabsplus:%'
            GROUP BY alliance_users.id
            ORDER BY visits_30d DESC, total_visits DESC, last_used_at DESC, alliance_users.username COLLATE NOCASE ASC
            """,
            (f"{since_30_days}T00:00:00+00:00",),
        ).fetchall()

    events = [dict(row) for row in event_rows]
    daily_counts = {str((now - timedelta(days=offset)).date()): 0 for offset in range(29, -1, -1)}
    section_counts: dict[str, int] = {}
    active_today: set[int] = set()
    active_7d: set[int] = set()
    active_30d: set[int] = set()
    today = now.date()
    seven_days_ago = today - timedelta(days=6)
    for event in events:
        event_day = str(event["occurred_at"])[:10]
        if event_day in daily_counts:
            daily_counts[event_day] += 1
        section = str(event.get("section") or "other").replace("-", " ").title()
        section_counts[section] = section_counts.get(section, 0) + 1
        event_date = datetime.fromisoformat(str(event["occurred_at"])).date()
        active_30d.add(int(event["user_id"]))
        if event_date >= seven_days_ago:
            active_7d.add(int(event["user_id"]))
        if event_date == today:
            active_today.add(int(event["user_id"]))

    users = []
    for row in user_rows:
        item = dict(row)
        last_used_at = str(item.get("last_used_at") or "")
        if last_used_at:
            last_used = datetime.fromisoformat(last_used_at)
            item["days_inactive"] = max(0, (now - last_used).days)
        else:
            item["days_inactive"] = None
        users.append(item)

    top_users = sorted(users, key=lambda item: (-int(item.get("visits_30d") or 0), str(item.get("username") or "").casefold()))[:10]
    section_usage = sorted(
        ({"name": name, "visits": visits} for name, visits in section_counts.items()),
        key=lambda item: (-item["visits"], item["name"]),
    )
    max_daily = max(daily_counts.values(), default=1) or 1
    max_section = max((item["visits"] for item in section_usage), default=1) or 1
    return {
        "total_events_30d": len(events),
        "active_today": len(active_today),
        "active_7d": len(active_7d),
        "active_30d": len(active_30d),
        "daily_usage": [
            {"date": date, "label": date[5:], "visits": visits, "height": round(visits / max_daily * 100, 2)}
            for date, visits in daily_counts.items()
        ],
        "section_usage": [dict(item, width=round(item["visits"] / max_section * 100, 2)) for item in section_usage],
        "top_users": top_users,
        "users": users,
    }


def _default_hero_local_image(hero_id: str, filename: str) -> str:
    return f"/static/hero_assets/{hero_id}/{filename}"


def _read_heroes_file(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []

    with path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)

    heroes = payload.get("heroes", []) if isinstance(payload, dict) else []
    return heroes if isinstance(heroes, list) else []


def _deep_merge_dict(base: dict[str, Any], override: dict[str, Any]) -> dict[str, Any]:
    merged = dict(base)
    for key, value in override.items():
        if isinstance(value, dict) and isinstance(merged.get(key), dict):
            merged[key] = _deep_merge_dict(merged[key], value)
        else:
            merged[key] = value
    return merged


def _load_heroes() -> list[dict[str, Any]]:
    heroes = _read_heroes_file(HEROES_DATA_PATH)
    overrides = _read_heroes_file(HEROES_OVERRIDES_PATH)
    progression_overrides = _read_heroes_file(HEROES_PROGRESSION_OVERRIDES_PATH)

    merged_by_id: dict[str, dict[str, Any]] = {}
    for hero in heroes + overrides + progression_overrides:
        if not isinstance(hero, dict):
            continue
        hero_id = str(hero.get("id") or _normalize_slug(str(hero.get("name", ""))))
        if not hero_id:
            continue
        prev = merged_by_id.get(hero_id)
        merged_by_id[hero_id] = _deep_merge_dict(prev, hero) if isinstance(prev, dict) else hero

    out: list[dict[str, Any]] = []
    for hero in merged_by_id.values():
        hero_id = str(hero.get("id") or _normalize_slug(str(hero.get("name", ""))))
        if not hero_id:
            continue

        skills = hero.get("skills") if isinstance(hero.get("skills"), dict) else {}
        conquest_skills = skills.get("conquest", []) if isinstance(skills.get("conquest"), list) else []
        expedition_skills = skills.get("expedition", []) if isinstance(skills.get("expedition"), list) else []
        total_skill_count = len(conquest_skills) + len(expedition_skills)

        image_urls = hero.get("image_urls") if isinstance(hero.get("image_urls"), dict) else {}
        inferred_local_full = _default_hero_local_image(hero_id, "full.png")
        inferred_local_avatar = _default_hero_local_image(hero_id, "avatar.png")
        remote_card = image_urls.get("full") or image_urls.get("avatar") or image_urls.get("og")
        local_card = (
            image_urls.get("local_full")
            or image_urls.get("local_avatar")
            or (inferred_local_full if _local_static_exists(inferred_local_full) else "")
            or (inferred_local_avatar if _local_static_exists(inferred_local_avatar) else "")
        )
        card_image = _prefer_local(str(local_card or ""), str(remote_card or ""))
        full_image = _prefer_local(
            str(image_urls.get("local_full") or (inferred_local_full if _local_static_exists(inferred_local_full) else "") or ""),
            str(image_urls.get("full") or card_image or ""),
        )

        skills = hero.get("skills") if isinstance(hero.get("skills"), dict) else {}
        for skill_bucket in ("conquest", "expedition"):
            bucket_items = skills.get(skill_bucket, [])
            if not isinstance(bucket_items, list):
                continue
            for skill in bucket_items:
                if not isinstance(skill, dict):
                    continue
                skill["image_url"] = _prefer_local(
                    str(skill.get("local_image_url") or ""),
                    str(skill.get("image_url") or ""),
                )

        gear = hero.get("exclusive_gear") if isinstance(hero.get("exclusive_gear"), dict) else {}
        if gear:
            gear["image_url"] = _prefer_local(
                str(gear.get("local_image_url") or ""),
                str(gear.get("image_url") or ""),
            )
            gear_skills = gear.get("skills", [])
            if isinstance(gear_skills, list):
                for gear_skill in gear_skills:
                    if not isinstance(gear_skill, dict):
                        continue
                    gear_skill["image_url"] = _prefer_local(
                        str(gear_skill.get("local_image_url") or ""),
                        str(gear_skill.get("image_url") or ""),
                    )

        out.append(
            {
                **hero,
                "id": hero_id,
                "slug": hero_id,
                "name": str(hero.get("name", hero_id)).strip(),
                "rarity": str(hero.get("rarity", "")).strip(),
                "troop_type": str(hero.get("troop_type", "")).strip(),
                "hero_class": str(hero.get("hero_class", "")).strip(),
                "generation": int(hero.get("generation", 0) or 0),
                "total_skill_count": total_skill_count,
                "card_image": card_image,
                "full_image": full_image,
                "description": str(hero.get("description", "")).strip(),
                "troop_icon": TROOP_ICON_MAP.get(str(hero.get("troop_type", "")).lower(), ""),
            }
        )

    out.sort(
        key=lambda item: (
            -int(item.get("generation", 0) or 0),
            RARITY_ORDER.get(str(item.get("rarity", "")).lower(), 99),
            str(item.get("name", "")).lower(),
        )
    )
    return out


def _normalize_slug(value: str) -> str:
    cleaned = re.sub(r"[^a-z0-9]+", "-", str(value or "").strip().lower())
    return cleaned.strip("-")


def _extract_game_id_from_synthetic_discord_user_id(discord_user_id: Any) -> str:
    raw_value = str(discord_user_id or "").strip()
    if not _is_jeabs_synthetic_discord_user_id(raw_value):
        return ""
    parts = raw_value.split(":")
    if len(parts) < 3:
        return ""
    return str(parts[-1]).strip()


def _normalize_alliance_tag(value: str) -> str:
    text = str(value or "").strip()
    if not text:
        return ""
    cleaned = re.sub(r"[^a-zA-Z0-9]", "", text)
    return cleaned[:10]


def _alliance_url_key(alliance: dict[str, Any] | None) -> str:
    if not alliance:
        return ""

    tag = str(alliance.get("tag") or "").strip()
    if tag:
        return _normalize_slug(tag)

    name = str(alliance.get("name") or "").strip()
    return _normalize_slug(name)


def _filter_heroes(heroes: list[dict[str, Any]], q: str, generation: str, rarity: str, troop_type: str) -> list[dict[str, Any]]:
    needle = q.strip().lower()
    filtered = []

    for hero in heroes:
        if needle and needle not in str(hero.get("name", "")).lower():
            continue
        if generation and str(hero.get("generation", "")) != generation:
            continue
        if rarity and str(hero.get("rarity", "")).lower() != rarity.lower():
            continue
        if troop_type and str(hero.get("troop_type", "")).lower() != troop_type.lower():
            continue
        filtered.append(hero)

    return filtered


def _sort_heroes(heroes: list[dict[str, Any]], sort_by: str) -> list[dict[str, Any]]:
    rarity_rank = {"legendary": 0, "epic": 1, "rare": 2}

    if sort_by == "name":
        return sorted(heroes, key=lambda item: str(item.get("name", "")).lower())

    if sort_by == "rarity":
        return sorted(
            heroes,
            key=lambda item: (
                rarity_rank.get(str(item.get("rarity", "")).lower(), 99),
                -int(item.get("generation", 0) or 0),
                str(item.get("name", "")).lower(),
            ),
        )

    if sort_by == "generation":
        return sorted(
            heroes,
            key=lambda item: (
                -int(item.get("generation", 0) or 0),
                rarity_rank.get(str(item.get("rarity", "")).lower(), 99),
                str(item.get("name", "")).lower(),
            ),
        )

    return sorted(
        heroes,
        key=lambda item: (
            -int(item.get("generation", 0) or 0),
            rarity_rank.get(str(item.get("rarity", "")).lower(), 99),
            str(item.get("name", "")).lower(),
        ),
    )


def _validate_payload(payload: dict[str, Any]) -> tuple[bool, str]:
    if not isinstance(payload, dict):
        return False, "Payload must be a JSON object."

    player = payload.get("player")
    enemy = payload.get("enemy")

    if not isinstance(player, dict) or not isinstance(enemy, dict):
        return False, "Payload must include 'player' and 'enemy' objects."

    required_player = ["total_troops", "troop_level", "max_damage_boost", "max_defense_boost", "max_health_boost"]
    required_enemy = ["total_troops", "troop_level", "infantry_pct", "cavalry_pct", "archers_pct"]

    for field in required_player:
        if field not in player:
            return False, f"Missing player field: {field}"

    for field in required_enemy:
        if field not in enemy:
            return False, f"Missing enemy field: {field}"

    total_pct = int(enemy.get("infantry_pct", 0) or 0) + int(enemy.get("cavalry_pct", 0) or 0) + int(enemy.get("archers_pct", 0) or 0)
    if total_pct != 100:
        return False, "Enemy composition (INF/CAV/ARC) must sum to 100."

    return True, ""


def _as_float(value: Any) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return 0.0


def _extract_digits(value: str) -> list[int]:
    digits: list[int] = []
    current = ""
    for ch in value:
        if ch.isdigit():
            current += ch
            continue
        if current:
            digits.append(int(current))
            current = ""
    if current:
        digits.append(int(current))
    return digits


def _parse_town_hall_level(raw: Any, default: int = 30) -> int:
    text = str(raw or "").strip().lower().replace(" ", "")
    if not text:
        return _clamp_int(default, 1, 74, 30)

    # Accept direct numeric storage values.
    if text.isdigit():
        numeric = int(text)
        # Legacy persisted range 31..50 used the old TG5..TG8 encoding.
        if 31 <= numeric <= 50:
            return numeric + 24
        return _clamp_int(numeric, 1, 74, 30)

    # Accept TG variants like TG1, TG1-3, TG8-4.
    if "tg" in text:
        numbers = _extract_digits(text)
        if numbers:
            tg_tier = numbers[0]
            tg_tier = _clamp_int(tg_tier, 1, 8, 1)
            sub_level = 0
            if len(numbers) > 1:
                sub_level = _clamp_int(numbers[1], 0, 4, 0)
            return 35 + (tg_tier - 1) * 5 + sub_level

    # Accept strings like "Level 30-3".
    if "30-" in text:
        numbers = _extract_digits(text)
        if len(numbers) >= 2 and numbers[0] == 30:
            sub_level = _clamp_int(numbers[1], 1, 4, 1)
            return 30 + sub_level

    if text in {"truegold", "tg0", "t30"}:
        return 30

    parsed = _parse_loose_int(raw, default)
    if 31 <= parsed <= 50:
        return parsed + 24
    return _clamp_int(parsed, 1, 74, 30)


def _format_town_hall_level(level: Any) -> str:
    numeric = _parse_town_hall_level(level, 30)
    if numeric <= 29:
        return str(numeric)

    if numeric == 30:
        return "Truegold"

    if 31 <= numeric <= 34:
        return f"30-{numeric - 30}"

    relative = numeric - 35
    tg_tier = 1 + (relative // 5)
    sub_level = relative % 5
    return f"TG{tg_tier}" if sub_level == 0 else f"TG{tg_tier}-{sub_level}"


def _town_hall_to_troop_grade(level: Any) -> str:
    numeric = _parse_town_hall_level(level, 30)
    if numeric < 35:
        return ""
    relative = numeric - 35
    tg_tier = 1 + (relative // 5)
    return f"TG{tg_tier}"


def _extract_troop_grade_from_text(raw: Any) -> str:
    text = str(raw or "").strip().upper()
    if "TG" not in text:
        return ""
    numbers = _extract_digits(text)
    if not numbers:
        return ""
    tg_tier = numbers[0]
    tg_tier = _clamp_int(tg_tier, 1, 8, 0)
    return f"TG{tg_tier}" if tg_tier else ""


def _clamp_int(raw: Any, minimum: int, maximum: int, default: int) -> int:
    try:
        value = int(raw)
    except (TypeError, ValueError):
        value = default
    return max(minimum, min(maximum, value))


def _parse_loose_int(raw: Any, default: int) -> int:
    """Parse a user-typed number, tolerating thousand separators and comma decimals."""
    text = str(raw or "").strip()
    if not text:
        return default
    cleaned = "".join(ch for ch in text if ch.isdigit() or ch in ",.-")
    if not cleaned:
        return default
    if "," in cleaned and "." in cleaned:
        if cleaned.rfind(",") > cleaned.rfind("."):
            cleaned = cleaned.replace(".", "").replace(",", ".")
        else:
            cleaned = cleaned.replace(",", "")
    elif "," in cleaned:
        cleaned = cleaned.replace(",", ".")
    try:
        return int(round(float(cleaned)))
    except ValueError:
        return default


TROOP_LEVEL_OPTIONS = ["T10", "T11"] + [f"TG{i}" for i in range(1, 9)] + [f"T11-TG{i}" for i in range(5, 9)]
TOWN_HALL_LEVEL_OPTIONS = [
    {"value": level, "label": _format_town_hall_level(level)}
    for level in range(30, 75)
]
PUBLIC_ROSTER_TROOP_LEVEL_OPTIONS = [
    f"T{troop_tier}-TG{tg_tier}"
    for troop_tier in (10, 11)
    for tg_tier in range(5, 9)
]
PUBLIC_ROSTER_TOWN_HALL_LEVEL_OPTIONS = [
    {"value": 35 + (tg_tier - 1) * 5, "label": f"TG{tg_tier}"}
    for tg_tier in range(5, 9)
]
PUBLIC_ROSTER_HERO_NAMES = (
    "Amadeus", "Saul", "Jabel", "Zoe", "Hilde", "Marlin", "Jaeger", "Eric",
    "Petra", "Rosa", "Alcar", "Margot", "Long Fei", "Vivian", "Thrud", "Sophia",
    "Triton", "Yang",
)
PUBLIC_ROSTER_EXPEDITION_HERO_NAMES = ("Hilde", "Saul", "Chenko")
PUBLIC_ROSTER_HERO_STAR_OPTIONS = (
    "I don't have", "less than 3 stars", "3 stars", "3.1 stars", "3.2 stars",
    "3.3 stars", "3.4 stars", "3.5 stars", "4 stars", "4.1 stars", "4.2 stars",
    "4.3 stars", "4.4 stars", "4.5 stars", "5 stars",
)
PUBLIC_ROSTER_ACTIVITY_OPTIONS = (
    "Hardcore competitive", "Active", "Casual", "Occasional fun",
)
PUBLIC_ROSTER_KVK_OPTIONS = (
    "Full battle", "First half only", "Second half only", "Partially available",
    "Not sure", "Not available",
)


def _default_roster_form_schema() -> dict[str, Any]:
    required = True
    star_options = list(PUBLIC_ROSTER_HERO_STAR_OPTIONS)
    return {"sections": [
        {"title": "Levels", "fields": [
            {"name": "vip_level", "label": "VIP level", "type": "select", "required": required, "options": [f"VIP{i}" for i in range(1, 13)]},
            {"name": "town_hall_level", "label": "City level", "type": "select", "required": required, "options": [f"TG{i}" for i in range(5, 9)]},
            *[{"name": f"{troop}_troops", "label": label, "type": "select", "required": required, "options": list(PUBLIC_ROSTER_TROOP_LEVEL_OPTIONS)} for troop, label in (("infantry", "Infantry TG"), ("cavalry", "Cavalry TG"), ("archer", "Archers TG"))],
        ]},
        {"title": "Power breakdown", "fields": [
            {"name": name, "label": label, "type": "number", "required": required, "options": []}
            for name, label in (("total_power", "Current power"), ("troops_power", "Troops power"), ("building_power", "Building power"), ("tech_power", "Tech power"), ("governor_power", "Governor power"), ("hero_power", "Hero power"), ("pet_power", "Pet power"), ("power_ac", "Master power"))
        ]},
        {"title": "Expedition skill heroes", "fields": [
            *[{"name": f"expedition_{_normalize_slug(name)}", "label": f"{name}: first expedition skill level 5", "type": "checkbox", "required": False, "options": []} for name in PUBLIC_ROSTER_EXPEDITION_HERO_NAMES],
            {"name": "expedition_none", "label": "None of them", "type": "checkbox", "required": False, "options": []},
        ]},
        {"title": "Hero stars", "fields": [
            {"name": f"hero_{_normalize_slug(name)}_stars", "label": name, "type": "select", "required": required, "options": star_options}
            for name in PUBLIC_ROSTER_HERO_NAMES
        ]},
        {"title": "Plans and availability", "fields": [
            {"name": "mythic_shards", "label": "Mythic general shards", "type": "number", "required": required, "options": []},
            {"name": "next_upgrades", "label": "Heroes to upgrade next", "type": "text", "required": required, "options": []},
            {"name": "daily_activity", "label": "Daily activity", "type": "select", "required": required, "options": list(PUBLIC_ROSTER_ACTIVITY_OPTIONS)},
            {"name": "kvk_attendance", "label": "KVK attendance", "type": "select", "required": required, "options": list(PUBLIC_ROSTER_KVK_OPTIONS)},
        ]},
        {"title": "Capacity", "fields": [
            {"name": "march_capacity_base", "label": "March without buffs", "type": "number", "required": required, "options": []},
            {"name": "valora_level", "label": "Valora - Wild Advantage level", "type": "select", "required": required, "options": [str(level) for level in range(11)]},
            {"name": "cassia_level", "label": "Cassia - Inspirational Mobilization level", "type": "select", "required": required, "options": [str(level) for level in range(21)]},
            {"name": "bison_level", "label": "Imposing Bison - Fearless Roar level", "type": "select", "required": required, "options": [str(level) for level in range(11)]},
            {"name": "march_booster_percent", "label": "March capacity booster", "type": "select", "required": required, "options": ["0", "10", "20"]},
            {"name": "march_capacity_buffed", "label": "March with buffs", "type": "calculated", "required": required, "options": []},
            {"name": "rally_leader", "label": "Do you lead rallies?", "type": "select", "required": required, "options": ["No", "Yes"]},
            {"name": "rally_capacity_base", "label": "Rally without buffs", "type": "number", "required": False, "options": []},
            {"name": "rally_capacity_buffed", "label": "Rally with buffs", "type": "number", "required": False, "options": []},
        ]},
        {"title": "Notes", "fields": [
            {"name": "notes", "label": "Notes, constraints or suggestions", "type": "textarea", "required": False, "options": []},
        ]},
    ]}


def _transfer_application_schema() -> dict[str, Any]:
    required = True
    stars = list(PUBLIC_ROSTER_HERO_STAR_OPTIONS)
    heroes = ["Amadeus", "Saul", "Jabel", "Zoe", "Hilde", "Marlin", "Jaeger", "Eric", "Petra", "Rosa", "Alcar", "Margot", "Long Fie", "Vivian", "Thrud", "Sophia", "Triton", "Yang"]
    troop_levels = ["T10-TG5", "T10-TG6", "T10-TG7", "T10-TG8", "T11-TG5", "T11-TG6", "T11-TG7", "T11-TG8"]
    return {"sections": [
        {"title": "Who you are", "fields": [
            {"name": "player_name", "label": "Player name | اسم اللاعب", "type": "text", "required": required, "options": []},
            {"name": "game_id", "label": "Player ID | رقم اللاعب", "type": "text", "required": required, "options": []},
            {"name": "vip_level", "label": "VIP level | مستوى VIP", "type": "select", "required": required, "options": [f"VIP{i}" for i in range(1, 13)]},
        ]},
        {"title": "Transfer background", "fields": [
            {"name": "source_kingdom", "label": "Kingdom transferring from | المملكة الحالية", "type": "text", "required": required, "options": []},
            {"name": "source_alliance", "label": "Alliance transferring from | التحالف الحالي", "type": "text", "required": required, "options": []},
            {"name": "leadership_role", "label": "Leadership position | المنصب القيادي", "type": "select", "required": required, "options": ["No - regular member", "R4 / officer", "R5 / alliance leader", "Kingdom title holder", "Other leadership role"]},
            {"name": "leaving_reason", "label": "Reason for leaving | سبب المغادرة", "type": "textarea", "required": required, "options": []},
            {"name": "interest_reason", "label": "What attracted you to K745 and SUP? | ما الذي جذبك إلى K745 وSUP؟", "type": "textarea", "required": required, "options": []},
        ]},
        {"title": "Levels", "fields": [
            {"name": "town_hall_level", "label": "City TG level | مستوى المدينة", "type": "select", "required": required, "options": [f"TG{i}" for i in range(5, 9)]},
            *[{"name": f"{key}_troops", "label": f"{label} | مستوى القوات", "type": "select", "required": required, "options": troop_levels} for key, label in (("infantry", "Infantry TG"), ("cavalry", "Cavalry TG"), ("archer", "Archers TG"))],
        ]},
        {"title": "Power breakdown", "fields": [
            {"name": name, "label": label, "type": "number", "required": required, "options": []}
            for name, label in (("total_power", "Current power"), ("troops_power", "Troops power"), ("building_power", "Building power"), ("tech_power", "Tech power"), ("governor_power", "Governor power"), ("hero_power", "Hero power"), ("pet_power", "Pet power"), ("power_ac", "Master power"))
        ]},
        {"title": "Expedition skill heroes", "fields": [
            {"name": "expedition_heroes", "label": "Heroes with first expedition skill at level 5", "type": "multiselect", "required": required, "options": ["Hilde", "Saul", "Chenco", "None of them"]},
        ]},
        {"title": "Hero stars", "fields": [
            {"name": f"hero_{_normalize_slug(name)}_stars", "label": name, "type": "select", "required": required, "options": stars} for name in heroes
        ]},
        {"title": "Plans and activity", "fields": [
            {"name": "mythic_shards", "label": "Mythic general shards", "type": "number", "required": False, "options": []},
            {"name": "next_upgrades", "label": "Heroes to upgrade next", "type": "text", "required": False, "options": []},
            {"name": "daily_activity", "label": "Daily activity level", "type": "select", "required": required, "options": ["Hardcore competitive", "Active", "Casual", "Occasional fun"]},
            {"name": "timezone", "label": "Time zone (UTC offset)", "type": "text", "required": required, "options": []},
        ]},
        {"title": "Capacity", "fields": [
            {"name": "march_capacity_base", "label": "March capacity without buffs", "type": "number", "required": required, "options": []},
            {"name": "valora_level", "label": "Valora - Wild Advantage level", "type": "select", "required": required, "options": [str(level) for level in range(11)]},
            {"name": "cassia_level", "label": "Cassia - Inspirational Mobilization level", "type": "select", "required": required, "options": [str(level) for level in range(21)]},
            {"name": "bison_level", "label": "Imposing Bison - Fearless Roar level", "type": "select", "required": required, "options": [str(level) for level in range(11)]},
            {"name": "march_booster_percent", "label": "March capacity booster", "type": "select", "required": required, "options": ["0", "10", "20"]},
            {"name": "march_capacity_buffed", "label": "March capacity with buffs", "type": "calculated", "required": required, "options": []},
            {"name": "rally_capacity", "label": "Rally capacity without and with buffs", "type": "text", "required": False, "options": []},
            {"name": "notes", "label": "Notes for leadership | ملاحظات للقيادة", "type": "textarea", "required": False, "options": []},
        ]},
    ]}


def _parse_loose_float(raw: Any, default: float) -> float:
    """Same tolerant parsing as _parse_loose_int, but keeps the fractional part."""
    text = str(raw or "").strip()
    if not text:
        return default
    cleaned = "".join(ch for ch in text if ch.isdigit() or ch in ",.-")
    if not cleaned:
        return default
    if "," in cleaned and "." in cleaned:
        if cleaned.rfind(",") > cleaned.rfind("."):
            cleaned = cleaned.replace(".", "").replace(",", ".")
        else:
            cleaned = cleaned.replace(",", "")
    elif "," in cleaned:
        cleaned = cleaned.replace(",", ".")
    try:
        return float(cleaned)
    except ValueError:
        return default


def _normalize_ocr_combat_bonus(raw: Any) -> float:
    value = _parse_loose_float(raw, 0.0)
    if MAX_OCR_COMBAT_BONUS < value <= MAX_OCR_COMBAT_BONUS * 10:
        value /= 10
    return round(value, 1)


def _parse_bear_trap_config(raw: Any) -> dict[str, float]:
    if isinstance(raw, dict):
        payload = raw
    else:
        try:
            payload = json.loads(str(raw or "{}"))
        except (TypeError, ValueError):
            payload = {}
    if not isinstance(payload, dict):
        payload = {}

    return {
        "march_capacity": max(0.0, _parse_loose_float(payload.get("march_capacity"), 0.0)),
        "march_capacity_base": max(0, _parse_loose_int(payload.get("march_capacity_base"), 0)),
        "valora_level": _clamp_int(payload.get("valora_level"), 0, 10, 0),
        "cassia_level": _clamp_int(payload.get("cassia_level"), 0, 20, 0),
        "bison_level": _clamp_int(payload.get("bison_level"), 0, 10, 0),
        "march_booster_percent": _clamp_int(payload.get("march_booster_percent"), 0, 20, 0),
        "attack_booster_percent": _clamp_int(payload.get("attack_booster_percent"), 0, 20, 0),
        "lethality_booster_percent": _clamp_int(payload.get("lethality_booster_percent"), 0, 20, 0),
        "infantry_pct": _clamp_int(payload.get("infantry_pct"), 0, 100, 0),
        "cavalry_pct": _clamp_int(payload.get("cavalry_pct"), 0, 100, 0),
        "archer_pct": _clamp_int(payload.get("archer_pct"), 0, 100, 0),
        "infantry_troop_tier": str(payload.get("infantry_troop_tier") or "").strip().upper(),
        "cavalry_troop_tier": str(payload.get("cavalry_troop_tier") or "").strip().upper(),
        "archer_troop_tier": str(payload.get("archer_troop_tier") or "").strip().upper(),
        "infantry_attack_bonus": max(0.0, _parse_loose_float(payload.get("infantry_attack_bonus"), 0.0)),
        "infantry_lethality_bonus": max(0.0, _parse_loose_float(payload.get("infantry_lethality_bonus"), 0.0)),
        "cavalry_attack_bonus": max(0.0, _parse_loose_float(payload.get("cavalry_attack_bonus"), 0.0)),
        "cavalry_lethality_bonus": max(0.0, _parse_loose_float(payload.get("cavalry_lethality_bonus"), 0.0)),
        "archer_attack_bonus": max(0.0, _parse_loose_float(payload.get("archer_attack_bonus"), 0.0)),
        "archer_lethality_bonus": max(0.0, _parse_loose_float(payload.get("archer_lethality_bonus"), 0.0)),
        "bear_attack_bonus": max(0.0, _parse_loose_float(payload.get("bear_attack_bonus"), 0.0)),
        "stats_source": "TERROR_REPORT",
        "leader_stat_skills_in_report": str(payload.get("leader_stat_skills_in_report") or "UNKNOWN").strip().upper() if str(payload.get("leader_stat_skills_in_report") or "UNKNOWN").strip().upper() in {"YES", "NO", "UNKNOWN"} else "UNKNOWN",
        "attack_booster_in_report": False,
        "lethality_booster_in_report": False,
        "widget_stacking_strategy": str(payload.get("widget_stacking_strategy") or "GLOBAL_EFFECT_OP").strip().upper() if str(payload.get("widget_stacking_strategy") or "GLOBAL_EFFECT_OP").strip().upper() in {"GLOBAL_EFFECT_OP", "INDEPENDENT_MULTIPLICATIVE"} else "GLOBAL_EFFECT_OP",
        "lead_infantry": str(payload.get("lead_infantry") or "").strip(),
        "lead_cavalry": str(payload.get("lead_cavalry") or "").strip(),
        "lead_archer": str(payload.get("lead_archer") or "").strip(),
        "lead_infantry_skill": _clamp_int(payload.get("lead_infantry_skill"), 0, 5, 0),
        "lead_cavalry_skill": _clamp_int(payload.get("lead_cavalry_skill"), 0, 5, 0),
        "lead_archer_skill": _clamp_int(payload.get("lead_archer_skill"), 0, 5, 0),
        "lead_infantry_widget": _clamp_int(payload.get("lead_infantry_widget"), 0, 10, 0),
        "lead_cavalry_widget": _clamp_int(payload.get("lead_cavalry_widget"), 0, 10, 0),
        "lead_archer_widget": _clamp_int(payload.get("lead_archer_widget"), 0, 10, 0),
        "joiner_1": str(payload.get("joiner_1") or "chenko").strip(),
        "joiner_2": str(payload.get("joiner_2") or "amane").strip(),
        "joiner_3": str(payload.get("joiner_3") or "yeonwoo").strip(),
        "joiner_4": str(payload.get("joiner_4") or "margot").strip(),
        "best_composition_calculated": bool(payload.get("best_composition_calculated", False)),
        "best_infantry_pct": _clamp_int(payload.get("best_infantry_pct"), 0, 100, 0),
        "best_cavalry_pct": _clamp_int(payload.get("best_cavalry_pct"), 0, 100, 0),
        "best_archer_pct": _clamp_int(payload.get("best_archer_pct"), 0, 100, 0),
    }


BEAR_JOINER_EFFECTS = {
    "chenko": (101, 25.0),
    "yeonwoo": (101, 25.0),
    "amane": (102, 25.0),
    "margot": (102, 25.0),
}
BEAR_MONTE_CARLO_RUNS = 10_000
BEAR_ROUNDS = 10
_BEAR_WIDGET_SKILLS: dict[str, list[dict[str, Any]]] | None = None


def _get_bear_widget_skill_catalog() -> dict[str, list[dict[str, Any]]]:
    global _BEAR_WIDGET_SKILLS
    if _BEAR_WIDGET_SKILLS is None:
        _BEAR_WIDGET_SKILLS = {}
        for hero in _load_heroes():
            gear = hero.get("exclusive_gear") if isinstance(hero.get("exclusive_gear"), dict) else {}
            skills = gear.get("skills") if isinstance(gear.get("skills"), list) else []
            _BEAR_WIDGET_SKILLS[str(hero.get("id") or "")] = [skill for skill in skills if isinstance(skill, dict)]
    return _BEAR_WIDGET_SKILLS


def _get_bear_widget_modifiers(config: dict[str, Any], hero_data: Any) -> dict[str, float]:
    progress = _parse_hero_progress_data(hero_data)
    skill_catalog = _get_bear_widget_skill_catalog()
    modifiers = {
        "attack_pct": 0.0,
        "lethality_pct": 0.0,
        "damage_multiplier": 1.0,
        "fluctuating_effect_pct": 0.0,
    }
    for hero_id in (config["lead_infantry"], config["lead_cavalry"], config["lead_archer"]):
        widget_level = _clamp_int((progress.get(hero_id) or {}).get("widget"), 0, 10, 0)
        skill_level = widget_level // 2
        if skill_level <= 0:
            continue
        for skill in skill_catalog.get(hero_id, []):
            levels = skill.get("levels") if isinstance(skill.get("levels"), list) else []
            level_data = next(
                (item for item in levels if isinstance(item, dict) and _parse_loose_int(item.get("level"), 0) == skill_level),
                None,
            )
            if not level_data:
                continue
            values = level_data.get("scale_values") if isinstance(level_data.get("scale_values"), list) else []
            for scale in values:
                if not isinstance(scale, dict):
                    continue
                label = str(scale.get("label") or "").strip().lower()
                value = max(0.0, _parse_loose_float(scale.get("value"), 0.0))
                if "fluctuating" in label and "effect" in label:
                    modifiers["fluctuating_effect_pct"] += value
                elif "rally" not in label:
                    continue
                elif "attack" in label:
                    modifiers["attack_pct"] += value
                elif "lethality" in label:
                    modifiers["lethality_pct"] += value
                elif "damage" in label and "taken" not in label:
                    modifiers["damage_multiplier"] *= 1.0 + value / 100.0
    return modifiers


def _get_bear_lead_modifiers(config: dict[str, Any], hero_data: Any) -> dict[str, float]:
    """Expected damage modifiers from Bear lead skills, weighted by proc probability."""
    progress = _parse_hero_progress_data(hero_data)
    widget_modifiers = _get_bear_widget_modifiers(config, hero_data)
    modifiers = {"attack_pct": 0.0, "lethality_pct": 0.0, "damage_multiplier": 1.0, "archer_multiplier": 1.0}
    for hero_id in (config["lead_infantry"], config["lead_cavalry"], config["lead_archer"]):
        skill_level = _clamp_int((progress.get(hero_id) or {}).get("skill"), 0, 5, 0)
        if skill_level <= 0:
            continue
        if hero_id == "amadeus":
            modifiers["attack_pct"] += 5.0 * skill_level
            modifiers["lethality_pct"] += 5.0 * skill_level
            modifiers["damage_multiplier"] *= 1.0 + (8.0 * skill_level / 100.0) * 0.50
        elif hero_id == "petra":
            # Evil Eye and The Favor: chance (10% per skill level) of +50% expected damage.
            proc_multiplier = 1.0 + (10.0 * skill_level / 100.0) * 0.50
            modifiers["damage_multiplier"] *= proc_multiplier * proc_multiplier
        elif hero_id == "yang":
            # Avalanche adds a strike every four turns; Ice Zone is a 40% archer extra-damage proc.
            modifiers["damage_multiplier"] *= 1.0 + (20.0 * skill_level / 100.0) * 0.20
            modifiers["archer_multiplier"] *= 1.0 + 0.40 * (20.0 * skill_level / 100.0)
            modifiers["damage_multiplier"] *= 1.0 + (8.0 * skill_level / 100.0) * 0.50
            modifiers["attack_pct"] += widget_modifiers["attack_pct"]
            modifiers["lethality_pct"] += widget_modifiers["lethality_pct"]
            modifiers["damage_multiplier"] *= widget_modifiers["damage_multiplier"]
    return modifiers


def _get_bear_joiner_combinations(config: dict[str, Any], hero_data: Any) -> list[dict[str, Any]]:
    selected_ids = [config[f"joiner_{index}"] for index in range(1, 5)]
    if not all(hero_id in BEAR_JOINER_EFFECTS for hero_id in selected_ids):
        return []
    op_buckets: dict[int, float] = {}
    for hero_id in selected_ids:
        operation, bonus = BEAR_JOINER_EFFECTS[hero_id]
        op_buckets[operation] = op_buckets.get(operation, 0.0) + bonus
    damage_multiplier = math.prod(1.0 + bonus / 100.0 for bonus in op_buckets.values())
    return [{
        "heroes": selected_ids,
        "attack_pct": 0.0,
        "lethality_pct": 0.0,
        "damage_multiplier": damage_multiplier,
        "op_buckets": op_buckets,
    }]


def _get_bear_troop_levels(player: dict[str, Any]) -> tuple[str, str, str]:
    levels: list[str] = []
    for field_name in ("infantry_troops", "cavalry_troops", "archer_troops"):
        raw_value = str(player.get(field_name) or "").strip().lower()
        advanced_match = re.fullmatch(r"t(10|11)-tg([5-8])", raw_value)
        if advanced_match:
            levels.append(f"t{advanced_match.group(1)}-tg{advanced_match.group(2)}")
            continue
        tier_match = re.match(r"t(10|11)(?:-|$)", raw_value)
        if tier_match:
            levels.append(f"t{tier_match.group(1)}")
            continue
        if re.fullmatch(r"tg\d+(?:-\d+)?", raw_value):
            levels.append(raw_value)
            continue
        match = re.search(r"tg(\d+)", raw_value)
        if match:
            levels.append(f"tg{match.group(1)}")
            continue
        match = re.search(r"(?:^|[^a-z])t(\d+)(?:$|[^a-z])", raw_value)
        levels.append(f"t{match.group(1)}" if match else "")
    legacy_level = next((level for level in levels if level), "")
    normalized = [level or legacy_level for level in levels]
    return normalized[0], normalized[1], normalized[2]


def _get_bear_missing_stats(config: dict[str, Any]) -> list[str]:
    labels = {
        "infantry_attack_bonus": "Infantry ATK",
        "infantry_lethality_bonus": "Infantry LET",
        "cavalry_attack_bonus": "Cavalry ATK",
        "cavalry_lethality_bonus": "Cavalry LET",
        "archer_attack_bonus": "Archery ATK",
        "archer_lethality_bonus": "Archery LET",
    }
    return [label for field, label in labels.items() if _as_float(config.get(field)) < 0]


def _get_bear_resolved_leader_specs(levels: dict[str, int]) -> dict[str, dict[str, Any]]:
    heroes = {str(hero.get("id") or ""): hero for hero in _load_heroes()}
    resolved: dict[str, dict[str, Any]] = {}
    for hero_id, level in levels.items():
        if level <= 0:
            resolved[hero_id] = {}
            continue
        expedition = ((heroes.get(hero_id) or {}).get("skills") or {}).get("expedition", [])
        missing: list[str] = []

        def skill_value(skill_name: str, label: str) -> float | None:
            skill = next((item for item in expedition if str(item.get("name") or "") == skill_name), None)
            level_data = next((item for item in (skill or {}).get("levels", []) if _parse_loose_int(item.get("level"), 0) == level), None)
            scales = (level_data or {}).get("scale_values", [])
            scale = next((item for item in scales if str(item.get("label") or "") == label), None)
            if not scale:
                missing.append(f"{skill_name}:{label}")
                return None
            return _parse_loose_float(scale.get("value"), 0.0)

        spec: dict[str, Any] = {"events": [], "pending": missing}
        if hero_id == "amadeus":
            spec["lethality_all"] = skill_value("Battle Ready", "Lethality Up") or 0.0
            spec["attack_all"] = skill_value("Way of the Blade", "Attack Up") or 0.0
            chance = skill_value("Unrighteous Strike", "Damage Dealt Chance Up")
            if chance is not None:
                spec["events"].append(("amadeus_unrighteous_strike", "global", None, chance / 100.0, "damage_up", "generic_damage_up", 50.0))
        elif hero_id == "helga":
            spec["attack_all"] = skill_value("Echoes of Valhalla", "Attack Up") or 0.0
            spec["lethality_all"] = skill_value("Nature's Balance", "Lethality Up") or 0.0
        elif hero_id == "zoe":
            spec["attack_all"] = skill_value("Charisma", "Attack Up") or 0.0
            value = skill_value("Infinite Arsenal", "Enemy Damage Taken Up")
            if value is not None:
                spec["events"].append(("zoe_infinite_arsenal", "squad", None, 0.50, "defense_down", 211, value))
        elif hero_id == "petra":
            evil_eye = skill_value("Evil Eye", "Enemy Damage Taken Up")
            favor = skill_value("The Favor", "Damage Up")
            if evil_eye is not None:
                spec["events"].append(("petra_evil_eye", "squad", None, evil_eye / 100.0, "defense_down", 211, 50.0))
            if favor is not None:
                spec["events"].append(("petra_the_favor", "squad", None, favor / 100.0, "damage_up", "generic_damage_up", 50.0))
        elif hero_id == "hilde":
            spec["attack_all"] = skill_value("Noble Path", "Attack Up") or 0.0
            total_damage = skill_value("Elixir of Strength", "Damage Up")
            if total_damage is not None:
                spec["events"].append(("hilde_elixir", "squad", None, 0.25, "attack_total", None, max(0.0, total_damage - 100.0)))
        elif hero_id == "margot":
            spec["attack_all"] = skill_value("Warbringer", "Attack Up") or 0.0
            extra_attack = skill_value("Sleight Hand", "Damage Up")
            if extra_attack is not None:
                spec["events"].append(("margot_sleight_hand", "class", "cavalry", 0.25, "extra_attack", None, extra_attack))
        elif hero_id == "thrud":
            battle_hunger = skill_value("Battle Hunger", "Damage Up")
            reckless = skill_value("Reckless Charge", "Extra Damage Up")
            ancestral = skill_value("Ancestral Guidance", "Damage Up")
            if battle_hunger is not None:
                spec["passive_damage"] = {"targets": ("infantry", "archers"), "value": battle_hunger, "operation": "generic_damage_up", "name": "thrud_battle_hunger"}
            if reckless is not None:
                spec["events"].append(("thrud_reckless_charge", "class", "cavalry", 0.20, "extra_damage", None, reckless))
            if ancestral is not None:
                spec["ancestral_guidance"] = ancestral
        elif hero_id == "marlin":
            chance = skill_value("Wild Card", "Damage Dealt Chance Up")
            dynamo = skill_value("Dynamo", "Damage Up")
            if chance is not None:
                spec["events"].append(("marlin_wild_card", "global", None, chance / 100.0, "damage_up", 101, 50.0))
            if dynamo is not None:
                spec["events"].append(("marlin_dynamo", "squad", None, 0.50, "damage_up", "generic_damage_up", dynamo))
        elif hero_id == "rosa":
            spec["attack_archers"] = skill_value("Golden Rhythm", "Attack Up") or 0.0
            chaos = skill_value("Chaos Gambit", "Damage Up")
            if chaos is not None:
                spec["events"].append(("rosa_chaos", "global", None, 0.40, "damage_up", "generic_damage_up", chaos))
        elif hero_id == "yang":
            spec["avalanche_extra"] = skill_value("Avalanche", "Damage Up") or 0.0
            ice_zone = skill_value("Ice Zone", "Extra Damage Up")
            ambush_chance = skill_value("Ambush", "Probability Up")
            if ice_zone is not None:
                spec["events"].append(("yang_ice_zone", "class", "archers", 0.40, "extra_attack", None, ice_zone))
            if ambush_chance is not None:
                spec["events"].append(("yang_ambush", "global", None, ambush_chance / 100.0, "damage_up", "generic_damage_up", 50.0))
        resolved[hero_id] = spec
    return resolved


def _simulate_bear_damage_distribution(
    config: dict[str, Any],
    hero_data: Any,
    per_type_damage: tuple[float, float, float],
    lead_modifiers: dict[str, float],
    simulation_count: int,
) -> dict[str, Any]:
    progress = _parse_hero_progress_data(hero_data)
    selected = {
        hero_id: _clamp_int((progress.get(hero_id) or {}).get("skill"), 0, 5, 0)
        for hero_id in (config["lead_infantry"], config["lead_cavalry"], config["lead_archer"])
    }
    global_expected = max(lead_modifiers["damage_multiplier"], 0.000001)
    archer_expected = max(lead_modifiers["archer_multiplier"], 0.000001)
    regular_round_damage = (per_type_damage[0] + per_type_damage[1]) / BEAR_ROUNDS / global_expected
    archer_round_damage = per_type_damage[2] / BEAR_ROUNDS / global_expected / archer_expected
    seed_material = json.dumps({"config": config, "heroes": selected}, sort_keys=True).encode("utf-8")
    rng = random.Random(int.from_bytes(hashlib.sha256(seed_material).digest()[:8], "big"))
    values: list[float] = []

    for _ in range(simulation_count):
        total = 0.0
        for _round in range(BEAR_ROUNDS):
            global_multiplier = 1.0
            archer_multiplier = 1.0
            amadeus_level = selected.get("amadeus", 0)
            if amadeus_level and rng.random() < 0.50:
                global_multiplier *= 1.0 + 0.08 * amadeus_level
            petra_level = selected.get("petra", 0)
            if petra_level:
                proc_chance = min(1.0, 0.10 * petra_level)
                if rng.random() < proc_chance:
                    global_multiplier *= 1.50
                if rng.random() < proc_chance:
                    global_multiplier *= 1.50
            yang_level = selected.get("yang", 0)
            if yang_level:
                global_multiplier *= 1.0 + (0.20 * yang_level) * 0.20
                if rng.random() < 0.40:
                    archer_multiplier *= 1.0 + 0.20 * yang_level
                if rng.random() < 0.50:
                    global_multiplier *= 1.0 + 0.08 * yang_level
            total += global_multiplier * (regular_round_damage + archer_round_damage * archer_multiplier)
        values.append(total)

    values.sort()
    mean = sum(values) / simulation_count

    def percentile(fraction: float) -> float:
        index = min(simulation_count - 1, max(0, round((simulation_count - 1) * fraction)))
        return values[index]

    minimum, maximum = values[0], values[-1]
    bin_count = 20
    width = (maximum - minimum) / bin_count if maximum > minimum else 1.0
    counts = [0] * bin_count
    for value in values:
        index = min(bin_count - 1, int((value - minimum) / width))
        counts[index] += 1
    histogram = [
        {
            "from": minimum + index * width,
            "to": minimum + (index + 1) * width,
            "probability": count / simulation_count,
        }
        for index, count in enumerate(counts)
    ]
    return {
        "runs": simulation_count,
        "mean": mean,
        "p10": percentile(0.10),
        "p50": percentile(0.50),
        "p90": percentile(0.90),
        "minimum": minimum,
        "maximum": maximum,
        "mean_position": ((mean - minimum) / (maximum - minimum) * 100.0) if maximum > minimum else 50.0,
        "histogram": histogram,
        "max_probability": max(item["probability"] for item in histogram),
    }


def _calculate_bear_trap_result(player: dict[str, Any], simulation_count: int = 0) -> dict[str, Any] | None:
    """Adapt only the manually entered Bear configuration to the deterministic engine."""
    config = _parse_bear_trap_config(player.get("bear_trap_config_json"))
    march_capacity = config["march_capacity"]
    if config["march_capacity_base"] > 0:
        try:
            march_capacity = calculate_buffed_march_capacity(
                int(config["march_capacity_base"]),
                int(config["valora_level"]),
                int(config["cassia_level"]),
                int(config["bison_level"]),
                int(config["march_booster_percent"]),
            )
        except ValueError:
            return None
    leaders = (config["lead_infantry"], config["lead_cavalry"], config["lead_archer"])
    if march_capacity <= 0 or _get_bear_missing_stats(config):
        return None
    tiers = tuple(
        config[f"{troop_class}_troop_tier"]
        for troop_class in ("infantry", "cavalry", "archer")
    )
    if not all(tiers):
        return None
    configured = (config["infantry_pct"], config["cavalry_pct"], config["archer_pct"])
    ratios = tuple(value / 100.0 for value in configured) if sum(configured) == 100 else (0.05, 0.10, 0.85)
    troop_counts = tuple(round(march_capacity * ratio) for ratio in ratios)
    attack_stats = tuple(config[field] for field in ("infantry_attack_bonus", "cavalry_attack_bonus", "archer_attack_bonus"))
    lethality_stats = tuple(config[field] for field in ("infantry_lethality_bonus", "cavalry_lethality_bonus", "archer_lethality_bonus"))
    joiners = [config[f"joiner_{index}"] for index in range(1, 5)]
    leader_skill_levels = tuple(config[f"lead_{troop_class}_skill"] for troop_class in ("infantry", "cavalry", "archer"))
    resolved_leader_specs = _get_bear_resolved_leader_specs(dict(zip(leaders, leader_skill_levels)))
    try:
        result = calculate_bear_hunt(
            troop_counts=troop_counts,
            troop_tiers=tiers,
            attack_stats=attack_stats,
            lethality_stats=lethality_stats,
            attack_booster_percent=config["attack_booster_percent"],
            lethality_booster_percent=config["lethality_booster_percent"],
            leaders=leaders,
            joiners=joiners,
            widget_levels=(
                config["lead_infantry_widget"],
                config["lead_cavalry_widget"],
                config["lead_archer_widget"],
            ),
            leader_skill_levels=leader_skill_levels,
            resolved_leader_specs=resolved_leader_specs,
            widget_stacking_strategy=config["widget_stacking_strategy"],
            stats_source="TERROR_REPORT",
            leader_stat_skills_in_report=config["leader_stat_skills_in_report"],
            attack_booster_in_report=False,
            lethality_booster_in_report=False,
            pitfall_attack_points=config["bear_attack_bonus"],
            simulation_count=simulation_count,
            seed_config=config,
        )
    except (KeyError, ValueError):
        return None
    result.update({
        "ratio": ratios,
        "ratio_display": "/".join(f"{ratio * 100:.0f}" for ratio in ratios),
        "march_capacity": march_capacity,
        "troop_levels": tiers,
        "troop_counts": troop_counts,
        "bear_attack_bonus": config["bear_attack_bonus"],
        "boosted_attack_stats": tuple(round(value * (1.0 + config["attack_booster_percent"] / 100.0), 4) for value in attack_stats),
        "boosted_lethality_stats": tuple(round(value * (1.0 + config["lethality_booster_percent"] / 100.0), 4) for value in lethality_stats),
        "best_composition_calculated": config["best_composition_calculated"],
        "best_composition_display": "/".join(str(config[key]) for key in ("best_infantry_pct", "best_cavalry_pct", "best_archer_pct")),
    })
    return result


def _find_best_bear_composition(player: dict[str, Any], config: dict[str, Any]) -> tuple[tuple[int, int, int], float]:
    march_capacity = _as_float(config.get("march_capacity"))
    if march_capacity <= 0 and _as_float(config.get("march_capacity_base")) > 0:
        march_capacity = calculate_buffed_march_capacity(
            int(_as_float(config.get("march_capacity_base"))),
            _clamp_int(config.get("valora_level"), 0, 10, 0),
            _clamp_int(config.get("cassia_level"), 0, 20, 0),
            _clamp_int(config.get("bison_level"), 0, 10, 0),
            _clamp_int(config.get("march_booster_percent"), 0, 20, 0),
        )
    march_capacity = max(1.0, march_capacity)
    minimum_pct = max(1, math.ceil(500000.0 / march_capacity))
    best_percentages = (minimum_pct, minimum_pct, 100 - minimum_pct * 2)
    best_damage = -1.0
    for infantry_pct in range(minimum_pct, 11):
        for cavalry_pct in range(minimum_pct, 21):
            archer_pct = 100 - infantry_pct - cavalry_pct
            if round(march_capacity * archer_pct / 100.0) < 5000:
                continue
            candidate_config = {
                **config,
                "infantry_pct": infantry_pct,
                "cavalry_pct": cavalry_pct,
                "archer_pct": archer_pct,
            }
            candidate = _calculate_bear_trap_result({**player, "bear_trap_config_json": candidate_config})
            if candidate is not None and candidate["damage_avg"] > best_damage:
                best_percentages = (infantry_pct, cavalry_pct, archer_pct)
                best_damage = candidate["damage_avg"]
    return best_percentages, best_damage


def _find_best_bear_leaders(
    player: dict[str, Any],
    config: dict[str, Any],
) -> tuple[tuple[str, str, str], tuple[int, int, int], float]:
    leader_groups = (
        ("amadeus", "helga", "zoe"),
        ("petra", "hilde", "margot", "thrud"),
        ("marlin", "rosa", "yang"),
    )
    progress = _parse_hero_progress_data(player.get("hero_data"))
    required_heroes = tuple(itertools.chain.from_iterable(leader_groups))
    missing_heroes = []
    available_heroes: set[str] = set()
    for hero_id in required_heroes:
        state = progress.get(hero_id)
        explicitly_unowned = isinstance(state, dict) and (
            str(state.get("owned") or "").strip().lower() == "no"
            or str(state.get("stars") or "").strip().lower() == "i don't have"
        )
        if explicitly_unowned:
            continue
        if not isinstance(state, dict) or _clamp_int(state.get("skill"), 0, 5, 0) <= 0:
            missing_heroes.append(hero_id)
            continue
        available_heroes.add(hero_id)
    if missing_heroes:
        raise ValueError(
            "Complete your hero profile, including every Bear leader's skill level, "
            "before using Calculate Best Heroes."
        )

    available_groups = tuple(tuple(hero_id for hero_id in group if hero_id in available_heroes) for group in leader_groups)
    if any(not group for group in available_groups):
        raise ValueError("Record at least one owned Bear leader with a skill level for each troop class.")

    best_leaders = tuple(group[0] for group in available_groups)
    best_widgets = (0, 0, 0)
    best_damage = -1.0
    for leaders in itertools.product(*available_groups):
        widgets = tuple(_clamp_int((progress.get(hero_id) or {}).get("widget"), 0, 10, 0) for hero_id in leaders)
        skills = tuple(_clamp_int((progress.get(hero_id) or {}).get("skill"), 0, 5, 0) for hero_id in leaders)
        candidate_config = {
            **config,
            "lead_infantry": leaders[0],
            "lead_cavalry": leaders[1],
            "lead_archer": leaders[2],
            "lead_infantry_skill": skills[0],
            "lead_cavalry_skill": skills[1],
            "lead_archer_skill": skills[2],
            "lead_infantry_widget": widgets[0],
            "lead_cavalry_widget": widgets[1],
            "lead_archer_widget": widgets[2],
        }
        candidate = _calculate_bear_trap_result({**player, "bear_trap_config_json": candidate_config})
        if candidate is not None and candidate["damage_avg"] > best_damage:
            best_leaders = leaders
            best_widgets = widgets
            best_damage = candidate["damage_avg"]
    return best_leaders, best_widgets, best_damage


def _parse_total_power(raw: Any, default: int) -> int:
    """Parse full power values and shorthand inputs such as 263, 263M, or 1.2B."""
    text = str(raw or "").strip()
    if not text:
        return default

    suffix = text[-1:].lower()
    suffix_multiplier = {"k": 1_000, "m": 1_000_000, "b": 1_000_000_000}.get(suffix)
    if suffix_multiplier:
        text = text[:-1].strip()
    cleaned = "".join(ch for ch in text if ch.isdigit() or ch in ",.-")
    if not cleaned:
        return default

    parsed_float = _parse_loose_float(cleaned, float(default))
    if suffix_multiplier:
        return int(round(parsed_float * suffix_multiplier))
    if abs(parsed_float) < 10000:
        return int(round(parsed_float * 1_000_000))

    return _parse_loose_int(cleaned, default)


def _format_power(value: Any) -> str:
    """Format total power as millions with a comma decimal, e.g. 458800000 -> '458,8M'."""
    try:
        number = float(value)
    except (TypeError, ValueError):
        return "—"
    if number <= 0:
        return "—"
    millions = number / 1_000_000
    return f"{millions:.1f}".replace(".", ",") + "M"


def _format_stat_value(value: Any) -> str:
    """Format stat values with one decimal and comma separator."""
    try:
        number = float(value)
    except (TypeError, ValueError):
        return "—"
    return f"{number:.1f}".replace(".", ",")


def _format_whole_number(value: Any) -> str:
    """Abbreviate large integers with K (thousand), M (million), B (billion)."""
    try:
        number = int(float(value))
    except (TypeError, ValueError):
        return "0"
    return _abbreviate_number(number)


def _abbreviate_number(number: float) -> str:
    """Abbreviate with K/M/B — but only from 10.000 upward; 1.000-9.999 stay plain."""
    sign = "-" if number < 0 else ""
    magnitude = abs(number)
    if magnitude >= 1_000_000_000:
        text = f"{magnitude / 1_000_000_000:.1f}".replace(".", ",") + "B"
    elif magnitude >= 1_000_000:
        text = f"{magnitude / 1_000_000:.1f}".replace(".", ",") + "M"
    elif magnitude >= 10_000:
        text = f"{magnitude / 1_000:.1f}".replace(".", ",") + "K"
    else:
        return f"{sign}{int(magnitude):,}".replace(",", ".")
    if text.endswith(",0M") or text.endswith(",0K") or text.endswith(",0B"):
        text = text.replace(",0", "")
    return f"{sign}{text}"


def _format_signed_delta(value: Any) -> str:
    """Format change values with explicit sign, abbreviating large magnitudes."""
    try:
        number = float(value)
    except (TypeError, ValueError):
        return ""
    if abs(number) < 0.05:
        return "0,0"
    sign = "+" if number > 0 else ""
    if abs(number) >= 10_000:
        return f"{sign}{_abbreviate_number(number)}"
    return f"{sign}{number:.1f}".replace(".", ",")


def _normalize_alliance_rank(value: Any) -> str:
    candidate = str(value or "").strip().upper()
    if not candidate:
        return ""
    if candidate.startswith("R") and candidate[1:].isdigit():
        rank_number = int(candidate[1:])
        if 1 <= rank_number <= 5:
            return f"R{rank_number}"
    if candidate.isdigit():
        rank_number = int(candidate)
        if 1 <= rank_number <= 5:
            return f"R{rank_number}"
    return ""


def _extract_jeabs_members(payload: Any) -> list[dict[str, Any]]:
    if isinstance(payload, list):
        return [item for item in payload if isinstance(item, dict)]
    if not isinstance(payload, dict):
        return []

    candidates: list[Any] = []
    for key in ("members", "players", "roster"):
        value = payload.get(key)
        if isinstance(value, list):
            candidates = value
            break

    if not candidates:
        data_payload = payload.get("data")
        if isinstance(data_payload, list):
            candidates = data_payload
        elif isinstance(data_payload, dict):
            for key in ("members", "players", "roster"):
                value = data_payload.get(key)
                if isinstance(value, list):
                    candidates = value
                    break

    return [item for item in candidates if isinstance(item, dict)]


def _jeabs_payload_has_member_container(payload: Any) -> bool:
    if isinstance(payload, list):
        return True
    if not isinstance(payload, dict):
        return False

    for key in ("members", "players", "roster"):
        if key in payload:
            return True

    data_payload = payload.get("data")
    if isinstance(data_payload, list):
        return True
    if isinstance(data_payload, dict):
        for key in ("members", "players", "roster"):
            if key in data_payload:
                return True

    return False


def _extract_jeabs_player_payload(payload: Any) -> dict[str, Any] | None:
    if isinstance(payload, dict):
        for key in ("data", "result", "payload"):
            value = payload.get(key)
            if isinstance(value, dict):
                return value
            if isinstance(value, list):
                for item in value:
                    if isinstance(item, dict):
                        return item
        return payload
    if isinstance(payload, list):
        for item in payload:
            if isinstance(item, dict):
                return item
    return None


def _parse_retry_after_seconds(value: Any) -> float | None:
    text = str(value or "").strip()
    if not text:
        return None
    try:
        seconds = float(text)
    except (TypeError, ValueError):
        return None
    if seconds < 0:
        return None
    return seconds


def _jeabs_get_with_retry(url: str, headers: dict[str, str], timeout: float) -> tuple[requests.Response | None, str | None]:
    global JEABSPLUS_NEXT_REQUEST_AT
    last_error: str | None = None
    for attempt in range(JEABSPLUS_MAX_RETRIES + 1):
        with JEABSPLUS_RATE_LOCK:
            now = time.monotonic()
            wait_seconds = max(0.0, JEABSPLUS_NEXT_REQUEST_AT - now)
            JEABSPLUS_NEXT_REQUEST_AT = max(now, JEABSPLUS_NEXT_REQUEST_AT) + JEABSPLUS_MIN_REQUEST_INTERVAL_SECONDS
        if wait_seconds:
            time.sleep(wait_seconds)
        try:
            response = requests.get(url, headers=headers, timeout=timeout)
        except requests.RequestException as exc:
            last_error = str(exc)
            if attempt >= JEABSPLUS_MAX_RETRIES:
                return None, last_error
            delay = JEABSPLUS_RETRY_BASE_DELAY_SECONDS * (2 ** attempt) + random.uniform(0.0, 0.25)
            time.sleep(min(delay, 4.0))
            continue

        if response.status_code in JEABSPLUS_RETRYABLE_STATUS_CODES and attempt < JEABSPLUS_MAX_RETRIES:
            retry_after = _parse_retry_after_seconds(response.headers.get("Retry-After"))
            if retry_after is None:
                retry_after = JEABSPLUS_RETRY_BASE_DELAY_SECONDS * (2 ** attempt) + random.uniform(0.0, 0.25)
            time.sleep(min(max(retry_after, 0.15), 8.0))
            last_error = f"JeabsPlus error {response.status_code}"
            continue

        return response, None

    return None, last_error or "JeabsPlus request failed"


def _fetch_jeabs_player_details(
    player_id: str,
    token: str,
    preferred_template: str | None = None,
) -> tuple[dict[str, Any] | None, str | None]:
    cleaned_player_id = str(player_id or "").strip()
    if not cleaned_player_id:
        return None, None

    cleaned_token = str(token or "").strip()
    if not cleaned_token:
        return None, None

    headers = {
        "Authorization": f"Bearer {cleaned_token}",
        "Accept": "application/json",
    }
    encoded_player_id = quote(cleaned_player_id, safe="")

    candidate_bases = _build_jeabs_api_base_candidates(JEABSPLUS_API_BASE_URL)
    candidate_templates: list[str] = []
    for base in candidate_bases:
        candidate_templates.extend(
            [
                f"{base}/players/{{player_id}}",
                f"{base}/player/{{player_id}}",
                f"{base}/governors/{{player_id}}",
                f"{base}/governor/{{player_id}}",
                f"{base}/members/{{player_id}}",
                f"{base}/member/{{player_id}}",
                f"{base}/players?id={{player_id}}",
                f"{base}/player?id={{player_id}}",
            ]
        )

    if preferred_template and preferred_template in candidate_templates:
        candidate_templates = [preferred_template] + [
            template for template in candidate_templates if template != preferred_template
        ]

    for template in candidate_templates:
        url = template.format(player_id=encoded_player_id)
        response, request_error = _jeabs_get_with_retry(url, headers, timeout=12)
        if response is None:
            if request_error:
                continue
            continue

        if response.status_code in {404, 405}:
            continue
        if response.status_code in {401, 403}:
            raise ValueError("JeabsPlus rejected the token while reading player details.")
        if response.status_code >= 400:
            continue

        content_type = str(response.headers.get("Content-Type") or "").lower()
        if "json" not in content_type:
            continue
        try:
            payload = response.json()
        except ValueError:
            continue

        player_payload = _extract_jeabs_player_payload(payload)
        if isinstance(player_payload, dict):
            payload_player_id = str(
                player_payload.get("governor_id")
                or player_payload.get("governorId")
                or player_payload.get("player_id")
                or player_payload.get("playerId")
                or player_payload.get("id")
                or ""
            ).strip()
            if payload_player_id and payload_player_id != cleaned_player_id:
                continue
            return player_payload, template

    return None, None


def _fetch_jeabs_premium_payload(path: str, token: str, timeout: float = 10) -> dict[str, Any]:
    cleaned_token = str(token or "").strip()
    if not cleaned_token:
        raise ValueError("JEABSPLUS_API_TOKEN is missing.")

    url = f"{JEABSPLUS_API_BASE_URL}/{str(path or '').lstrip('/')}"
    response, request_error = _jeabs_get_with_retry(
        url,
        {"Authorization": f"Bearer {cleaned_token}", "Accept": "application/json"},
        timeout=timeout,
    )
    if response is None:
        raise ValueError(f"JeabsPlus request failed. {request_error or ''}".strip())
    if response.status_code in {401, 403}:
        raise ValueError("JeabsPlus rejected the Premium token.")
    if response.status_code >= 400:
        raise ValueError(f"JeabsPlus Premium endpoint returned {response.status_code}.")
    if "json" not in str(response.headers.get("Content-Type") or "").lower():
        raise ValueError("JeabsPlus Premium endpoint returned a non-JSON response.")
    try:
        payload = response.json()
    except ValueError as exc:
        raise ValueError("JeabsPlus Premium endpoint returned invalid JSON.") from exc
    if not isinstance(payload, dict):
        raise ValueError("JeabsPlus Premium endpoint returned an unexpected payload.")
    return payload


def _extract_radiant_spire_score(payload: dict[str, Any]) -> int | None:
    standings = payload.get("standings")
    if not isinstance(standings, list):
        return None
    for standing in standings:
        if not isinstance(standing, dict):
            continue
        board_type = _parse_loose_int(standing.get("board_type"), 0)
        label = str(standing.get("label") or "").strip().casefold()
        if board_type == 26 or label == "radiant spire":
            return max(0, _parse_loose_int(standing.get("score"), 0))
    return None


def _extract_radiant_spire_from_member_standings(member: dict[str, Any]) -> int | None:
    standings = member.get("standings")
    if not isinstance(standings, list):
        return None
    return _extract_radiant_spire_score({"standings": standings})


def _fetch_jeabs_radiant_spire(player_id: str, token: str) -> int | None:
    encoded_player_id = quote(str(player_id or "").strip(), safe="")
    if not encoded_player_id:
        return None
    payload = _fetch_jeabs_premium_payload(f"players/{encoded_player_id}/standings", token)
    return _extract_radiant_spire_score(payload)


def _fetch_jeabs_radiant_leaderboard(kingdom_id: str, token: str) -> dict[str, int]:
    encoded_kingdom_id = quote(str(kingdom_id or "").strip(), safe="")
    if not encoded_kingdom_id:
        return {}
    payload = _fetch_jeabs_premium_payload(f"kingdoms/{encoded_kingdom_id}/leaderboards/26", token)
    entries = payload.get("entries")
    if not isinstance(entries, list):
        return {}
    scores: dict[str, int] = {}
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        player_id = str(entry.get("player_id") or entry.get("id") or entry.get("uid") or "").strip()
        if player_id:
            scores[player_id] = max(0, _parse_loose_int(entry.get("score"), 0))
    return scores


def _fetch_jeabs_hero_gear(player_id: str, token: str) -> dict[str, Any]:
    encoded_player_id = quote(str(player_id or "").strip(), safe="")
    if not encoded_player_id:
        raise ValueError("Player ID is missing.")
    return _fetch_jeabs_premium_payload(f"players/{encoded_player_id}/hero-gear", token)


def _enrich_jeabs_members_with_player_details(
    members: list[dict[str, Any]],
    token: str,
    progress_callback: Any = None,
) -> tuple[list[dict[str, Any]], dict[str, int]]:
    enriched_members: list[dict[str, Any]] = [dict(item) if isinstance(item, dict) else {} for item in members]
    scanned_ids = 0
    detail_hits = 0
    detail_misses = 0

    indexed_candidates: list[tuple[int, str]] = []
    for index, member in enumerate(enriched_members):
        if not member:
            continue
        player_id_raw = (
            member.get("governor_id")
            or member.get("governorId")
            or member.get("player_id")
            or member.get("playerId")
            or member.get("id")
        )
        player_id = str(player_id_raw or "").strip()
        if not player_id:
            continue
        indexed_candidates.append((index, player_id))

    scanned_ids = len(indexed_candidates)
    if not indexed_candidates:
        return enriched_members, {
            "scanned_ids": 0,
            "detail_hits": 0,
            "detail_misses": 0,
        }

    preferred_template: str | None = None
    first_idx, first_player_id = indexed_candidates[0]
    first_details, first_template = _fetch_jeabs_player_details(first_player_id, token)
    if isinstance(first_details, dict):
        enriched_members[first_idx].update(first_details)
        detail_hits += 1
        preferred_template = first_template
    else:
        detail_misses += 1
    if progress_callback:
        progress_callback(1, scanned_ids)

    remaining_candidates = indexed_candidates[1:]

    def _fetch_one(indexed_item: tuple[int, str]) -> tuple[int, dict[str, Any] | None]:
        index, player_id = indexed_item
        details, _used_template = _fetch_jeabs_player_details(player_id, token, preferred_template)
        return index, details

    max_workers = min(JEABSPLUS_DETAIL_MAX_WORKERS, max(1, len(remaining_candidates)))
    if remaining_candidates:
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = [executor.submit(_fetch_one, candidate) for candidate in remaining_candidates]
            for future in as_completed(futures):
                try:
                    index, details = future.result()
                except Exception:
                    detail_misses += 1
                else:
                    if isinstance(details, dict):
                        enriched_members[index].update(details)
                        detail_hits += 1
                    else:
                        detail_misses += 1
                if progress_callback:
                    progress_callback(detail_hits + detail_misses, scanned_ids)

    return enriched_members, {
        "scanned_ids": scanned_ids,
        "detail_hits": detail_hits,
        "detail_misses": detail_misses,
    }


def _map_jeabs_member_fields(member: dict[str, Any]) -> dict[str, Any] | None:
    game_id_raw = (
        member.get("governor_id")
        or member.get("governorId")
        or member.get("player_id")
        or member.get("playerId")
        or member.get("id")
    )
    game_id = str(game_id_raw or "").strip()
    if not game_id:
        return None

    player_name = str(
        member.get("name")
        or member.get("nickname")
        or member.get("player_name")
        or member.get("playerName")
        or f"Player {game_id}"
    ).strip() or f"Player {game_id}"

    power_raw: Any = None
    has_total_power = False
    for key in ("total_power", "totalPower", "power", "personal_power", "personalPower"):
        if key in member and member.get(key) not in (None, ""):
            power_raw = member.get(key)
            has_total_power = True
            break
    total_power = int(_parse_total_power(power_raw, 0)) if has_total_power else None

    vip_raw: Any = None
    has_vip = False
    for key in ("vip_level", "vipLevel", "vip"):
        if key in member and member.get(key) not in (None, ""):
            vip_raw = member.get(key)
            has_vip = True
            break
    vip_level = _clamp_int(_parse_loose_int(vip_raw, 0), 0, 12, 0) if has_vip else None

    hall_raw: Any = None
    has_town_hall = False
    for key in ("town_hall_level", "townHallLevel", "city_level", "cityLevel", "hall_level", "hallLevel"):
        if key in member and member.get(key) not in (None, ""):
            hall_raw = member.get(key)
            has_town_hall = True
            break
    town_hall_level = _parse_town_hall_level(hall_raw, 30) if has_town_hall else None

    kingdom_raw: Any = None
    has_kingdom = False
    for key in ("kingdom_id", "kingdomId", "kid", "kingdom"):
        if key in member and member.get(key) not in (None, ""):
            kingdom_raw = member.get(key)
            has_kingdom = True
            break
    kingdom_id = str(kingdom_raw or "").strip() if has_kingdom else ""

    kills_raw: Any = None
    has_kills = False
    for key in ("kills", "kill", "kill_count", "killCount", "total_kills", "totalKills"):
        if key in member and member.get(key) not in (None, ""):
            kills_raw = member.get(key)
            has_kills = True
            break
    kills = max(0, _parse_loose_int(kills_raw, 0)) if has_kills else None

    mystic_raw: Any = None
    has_mystic_score = False
    for key in ("mystic_score", "mysticScore", "mystic_power", "mysticPower", "mystic_trial_score", "mysticTrialScore", "mystic"):
        if key in member and member.get(key) not in (None, ""):
            mystic_raw = member.get(key)
            has_mystic_score = True
            break
    mystic_score = max(0, _parse_loose_int(mystic_raw, 0)) if has_mystic_score else None

    radiant_spire_raw: Any = None
    has_radiant_spire = False
    for key in ("radiant_spire", "radiantSpire", "radiant_spire_score", "radiantSpireScore"):
        if key in member and member.get(key) not in (None, ""):
            radiant_spire_raw = member.get(key)
            has_radiant_spire = True
            break
    radiant_spire = max(0, _parse_loose_int(radiant_spire_raw, 0)) if has_radiant_spire else None
    if radiant_spire is None:
        standings_radiant = _extract_radiant_spire_from_member_standings(member)
        if standings_radiant is not None:
            radiant_spire = standings_radiant
            has_radiant_spire = True

    avatar_raw: Any = None
    has_avatar = False
    for key in ("avatar_url", "avatarUrl", "avatar"):
        if key in member and member.get(key) not in (None, ""):
            avatar_raw = member.get(key)
            has_avatar = True
            break
    avatar_url = str(avatar_raw or "").strip() if has_avatar else ""

    power_ac_raw: Any = None
    has_power_ac = False
    for key in ("power_ac", "powerAc", "ac_power", "acPower", "alliance_conquest_power"):
        if key in member and member.get(key) not in (None, ""):
            power_ac_raw = member.get(key)
            has_power_ac = True
            break
    power_ac = _parse_loose_int(power_ac_raw, 0) if has_power_ac else None

    rank_raw: Any = None
    has_alliance_rank = False
    for key in (
        "alliance_rank",
        "allianceRank",
        "rank",
        "member_rank",
        "memberRank",
        "role_level",
        "roleLevel",
    ):
        if key in member and member.get(key) not in (None, ""):
            rank_raw = member.get(key)
            has_alliance_rank = True
            break
    alliance_rank = _normalize_alliance_rank(rank_raw) if has_alliance_rank else ""

    return {
        "game_id": game_id,
        "player_name": player_name,
        "total_power": total_power,
        "vip_level": vip_level,
        "town_hall_level": town_hall_level,
        "kingdom_id": kingdom_id,
        "kills": kills,
        "mystic_score": mystic_score,
        "radiant_spire": radiant_spire,
        "power_ac": power_ac,
        "alliance_rank": alliance_rank,
        "avatar_url": avatar_url,
        "has_total_power": has_total_power,
        "has_vip": has_vip,
        "has_town_hall": has_town_hall,
        "has_kingdom": has_kingdom,
        "has_kills": has_kills,
        "has_mystic_score": has_mystic_score,
        "has_radiant_spire": has_radiant_spire,
        "has_power_ac": has_power_ac,
        "has_alliance_rank": has_alliance_rank,
        "has_avatar": has_avatar,
    }


def _normalize_jeabs_alliance_input(value: str) -> dict[str, str]:
    raw = str(value or "").strip()
    result = {
        "raw": raw,
        "alliance_id": raw,
        "kingdom_id": "",
        "origin_base_url": "",
    }
    if not raw:
        return result

    if raw.startswith("http://") or raw.startswith("https://"):
        parsed = urlparse(raw)
        if parsed.scheme and parsed.netloc:
            result["origin_base_url"] = f"{parsed.scheme}://{parsed.netloc}"
        parts = [part for part in (parsed.path or "").split("/") if part]
        for idx, part in enumerate(parts):
            lowered = part.lower()
            if lowered in {"alliance", "alliances"}:
                if idx + 1 < len(parts):
                    result["alliance_id"] = parts[-1]
                    if idx + 2 < len(parts):
                        result["kingdom_id"] = parts[-2]
                break
        else:
            if parts:
                result["alliance_id"] = parts[-1]

    result["alliance_id"] = str(result["alliance_id"] or "").strip()
    result["kingdom_id"] = str(result["kingdom_id"] or "").strip()
    return result


def _build_jeabs_api_base_candidates(*raw_bases: str) -> list[str]:
    candidates: list[str] = []
    seen: set[str] = set()

    for raw_base in raw_bases:
        base_value = str(raw_base or "").strip().rstrip("/")
        if not base_value:
            continue

        parsed = urlparse(base_value)
        ordered_bases: list[str]

        if parsed.scheme and parsed.netloc:
            parsed_path = (parsed.path or "").rstrip("/")
            if parsed_path.lower().endswith("/api/v1"):
                root_path = parsed_path[:-7].rstrip("/")
                root_base = f"{parsed.scheme}://{parsed.netloc}{root_path}" if root_path else f"{parsed.scheme}://{parsed.netloc}"
                ordered_bases = [base_value, root_base]
            else:
                host = str(parsed.netloc or "").lower()
                # Avoid calling website HTML routes on jeabslist.com when the API path is missing.
                if "jeabslist.com" in host:
                    ordered_bases = [f"{base_value}/api/v1"]
                else:
                    ordered_bases = [f"{base_value}/api/v1", base_value]
        else:
            ordered_bases = [f"{base_value}/api/v1", base_value]

        for candidate in ordered_bases:
            normalized_candidate = candidate.rstrip("/")
            if not normalized_candidate or normalized_candidate in seen:
                continue
            seen.add(normalized_candidate)
            candidates.append(normalized_candidate)

    return candidates


def _fetch_jeabs_members(jeabs_alliance_id: str, token: str) -> list[dict[str, Any]]:
    normalized = _normalize_jeabs_alliance_input(jeabs_alliance_id)
    cleaned_id = normalized["alliance_id"]
    if not cleaned_id:
        raise ValueError("JeabsPlus alliance ID is required.")
    cleaned_token = str(token or "").strip()
    if not cleaned_token:
        raise ValueError("JEABSPLUS_API_TOKEN is missing.")

    headers = {
        "Authorization": f"Bearer {cleaned_token}",
        "Accept": "application/json",
    }

    encoded_id = quote(cleaned_id, safe="")
    encoded_kingdom_id = quote(normalized["kingdom_id"], safe="") if normalized["kingdom_id"] else ""
    candidate_bases = _build_jeabs_api_base_candidates(JEABSPLUS_API_BASE_URL, normalized["origin_base_url"])

    candidate_urls = [
        f"{base}/alliances/{encoded_id}/members"
        for base in candidate_bases
    ]
    candidate_urls.extend([
        f"{base}/alliance/{encoded_id}/members"
        for base in candidate_bases
    ])
    if encoded_kingdom_id:
        candidate_urls.extend([
            f"{base}/alliances/{encoded_kingdom_id}/{encoded_id}/members"
            for base in candidate_bases
        ])
        candidate_urls.extend([
            f"{base}/alliance/{encoded_kingdom_id}/{encoded_id}/members"
            for base in candidate_bases
        ])
    candidate_urls.extend([
        f"{base}/alliances/{encoded_id}"
        for base in candidate_bases
    ])
    candidate_urls.extend([
        f"{base}/alliance/{encoded_id}"
        for base in candidate_bases
    ])
    if encoded_kingdom_id:
        candidate_urls.extend([
            f"{base}/alliances/{encoded_kingdom_id}/{encoded_id}"
            for base in candidate_bases
        ])
        candidate_urls.extend([
            f"{base}/alliance/{encoded_kingdom_id}/{encoded_id}"
            for base in candidate_bases
        ])
    candidate_urls.extend([
        f"{base}/members?alliance_id={encoded_id}"
        for base in candidate_bases
    ])
    candidate_urls.extend([
        f"{base}/players?alliance_id={encoded_id}"
        for base in candidate_bases
    ])

    # Preserve URL order but skip duplicates.
    deduped_candidate_urls: list[str] = []
    seen_urls: set[str] = set()
    for candidate in candidate_urls:
        if candidate in seen_urls:
            continue
        seen_urls.add(candidate)
        deduped_candidate_urls.append(candidate)

    last_error = ""
    for url in deduped_candidate_urls:
        response, request_error = _jeabs_get_with_retry(url, headers, timeout=20)
        if response is None:
            last_error = str(request_error or "Request failed")
            continue

        if response.status_code in {404, 405}:
            last_error = f"Endpoint not found ({response.status_code})"
            continue
        if response.status_code in {401, 403}:
            raise ValueError("JeabsPlus rejected the token. Verify your subscription token.")
        if response.status_code >= 400:
            body_preview = (response.text or "").strip()[:180]
            last_error = f"JeabsPlus error {response.status_code}: {body_preview}"
            continue

        content_type = str(response.headers.get("Content-Type") or "").lower()
        if "json" not in content_type:
            body_text = str(response.text or "")
            if "<html" in body_text.lower() or "<!doctype html" in body_text.lower():
                last_error = f"Invalid JeabsPlus response format at {url} ({content_type or 'no content-type'})"
            else:
                body_preview = body_text.strip().replace("\n", " ")[:180]
                last_error = f"Invalid JeabsPlus response format at {url} ({content_type or 'no content-type'}): {body_preview}"
            continue
        try:
            payload = response.json()
        except ValueError as exc:
            last_error = f"Invalid JeabsPlus JSON response at {url}: {exc}"
            continue

        members = _extract_jeabs_members(payload)
        if members:
            official_name = _extract_jeabs_alliance_name(payload, "")
            if official_name:
                return [
                    {**member, "_jeabs_official_name": official_name}
                    for member in members
                ]
            return members

        # Only treat as empty roster if this payload is explicitly a roster container.
        # Some endpoints return alliance metadata JSON without members; keep trying in that case.
        if _jeabs_payload_has_member_container(payload):
            return []

        last_error = f"Endpoint returned JSON without roster fields at {url}"
        continue

    if last_error:
        raise ValueError(f"Could not fetch JeabsPlus members. {last_error}")
    raise ValueError("Could not fetch JeabsPlus members from the configured API base URL.")


def _sync_jeabs_members_into_alliance(
    alliance_id: int,
    members: list[dict[str, Any]],
    reconcile_roster: bool = False,
) -> dict[str, int]:
    now = datetime.now(timezone.utc).isoformat()
    created_users = 0
    created_profiles = 0
    updated_profiles = 0
    skipped_rows = 0
    synced_game_ids: set[str] = set()

    with _get_db_connection() as connection:
        for raw_member in members:
            normalized = _map_jeabs_member_fields(raw_member)
            if not normalized:
                skipped_rows += 1
                continue

            game_id = normalized["game_id"]
            player_name = normalized["player_name"]
            synced_game_ids.add(game_id)
            synthetic_discord_id = f"jeabsplus:{alliance_id}:{game_id}"

            profile_row = connection.execute(
                "SELECT * FROM alliance_players WHERE alliance_id = ? AND game_id = ? ORDER BY id DESC LIMIT 1",
                (alliance_id, game_id),
            ).fetchone()

            target_user_id: int
            if profile_row:
                target_user_id = int(profile_row["user_id"])
            else:
                existing_user = connection.execute(
                    "SELECT id FROM alliance_users WHERE discord_user_id = ? LIMIT 1",
                    (synthetic_discord_id,),
                ).fetchone()
                if existing_user:
                    target_user_id = int(existing_user["id"])
                else:
                    user_cursor = connection.execute(
                        """
                        INSERT INTO alliance_users (discord_user_id, username, avatar_url, is_admin, alliance_id, created_at, updated_at)
                        VALUES (?, ?, NULL, 0, ?, ?, ?)
                        """,
                        (synthetic_discord_id, player_name, alliance_id, now, now),
                    )
                    target_user_id = int(user_cursor.lastrowid)
                    created_users += 1

            connection.execute(
                """
                UPDATE alliance_users
                SET username = COALESCE(NULLIF(?, ''), username),
                    alliance_id = ?,
                    updated_at = ?
                WHERE id = ?
                """,
                (player_name, alliance_id, now, target_user_id),
            )
            _detach_shadow_synthetic_alliance_users(connection, alliance_id, game_id, target_user_id, now)

            if profile_row:
                _insert_player_snapshot_if_not_first_ever(connection, alliance_id, profile_row, now)
                next_vip = int(profile_row["vip_level"] or 0)
                if normalized["has_vip"] and normalized["vip_level"] is not None:
                    next_vip = int(normalized["vip_level"])

                next_town_hall = _parse_town_hall_level(profile_row["town_hall_level"], 30)
                if normalized["has_town_hall"] and normalized["town_hall_level"] is not None:
                    next_town_hall = _parse_town_hall_level(normalized["town_hall_level"], 30)

                next_total_power = int(profile_row["total_power"] or 0)
                if normalized["has_total_power"] and normalized["total_power"] is not None:
                    next_total_power = int(normalized["total_power"])

                next_kingdom = profile_row["kingdom_id"]
                if normalized["has_kingdom"]:
                    next_kingdom = normalized["kingdom_id"] or None

                next_kills = max(0, _parse_loose_int(profile_row["kills"], 0))
                if normalized["has_kills"] and normalized["kills"] is not None:
                    next_kills = max(0, int(normalized["kills"]))

                next_mystic_score = max(0, _parse_loose_int(profile_row["mystic_score"], 0))
                if normalized["has_mystic_score"] and normalized["mystic_score"] is not None:
                    next_mystic_score = max(0, int(normalized["mystic_score"]))

                next_radiant_spire = max(0, _parse_loose_int(profile_row["radiant_spire"], 0))
                if normalized["has_radiant_spire"] and normalized["radiant_spire"] is not None:
                    next_radiant_spire = max(0, int(normalized["radiant_spire"]))

                next_power_ac = max(0, _parse_loose_int(profile_row["power_ac"], 0))
                if normalized["has_power_ac"] and normalized["power_ac"] is not None:
                    next_power_ac = max(0, int(normalized["power_ac"]))

                next_alliance_rank = str(profile_row["alliance_rank"] or "").strip()
                if normalized["has_alliance_rank"]:
                    next_alliance_rank = str(normalized["alliance_rank"] or "").strip()

                connection.execute(
                    """
                    UPDATE alliance_players
                    SET player_name = ?, player_avatar_url = ?, game_id = ?, vip_level = ?, town_hall_level = ?, total_power = ?, power_ac = ?, kills = ?, mystic_score = ?, radiant_spire = ?, alliance_rank = ?, kingdom_id = ?, updated_at = ?
                    WHERE id = ?
                    """,
                    (
                        player_name,
                        normalized["avatar_url"] if normalized["has_avatar"] else str(profile_row["player_avatar_url"] or ""),
                        game_id,
                        next_vip,
                        next_town_hall,
                        next_total_power,
                        next_power_ac,
                        next_kills,
                        next_mystic_score,
                        next_radiant_spire,
                        next_alliance_rank,
                        next_kingdom,
                        now,
                        int(profile_row["id"]),
                    ),
                )
                updated_profiles += 1
            else:
                connection.execute(
                    """
                    INSERT INTO alliance_players (
                        alliance_id, user_id, player_name, player_avatar_url, game_id, vip_level, town_hall_level, total_power, power_ac, kills, mystic_score, radiant_spire, alliance_rank,
                        kingdom_id, infantry_troops, cavalry_troops, archer_troops,
                        infantry_attack_bonus, infantry_defense_bonus, infantry_lethality_bonus, infantry_health_bonus,
                        cavalry_attack_bonus, cavalry_defense_bonus, cavalry_lethality_bonus, cavalry_health_bonus,
                        archer_attack_bonus, archer_defense_bonus, archer_lethality_bonus, archer_health_bonus,
                        hero_data, created_at, updated_at
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'TG4', 'TG4', 'TG4', 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, '{}', ?, ?)
                    """,
                    (
                        alliance_id,
                        target_user_id,
                        player_name,
                        normalized["avatar_url"] if normalized["has_avatar"] else "",
                        game_id,
                        int(normalized["vip_level"]) if normalized["vip_level"] is not None else 0,
                        _parse_town_hall_level(normalized["town_hall_level"], 30) if normalized["town_hall_level"] is not None else 30,
                        int(normalized["total_power"]) if normalized["total_power"] is not None else 0,
                        int(normalized["power_ac"]) if normalized["power_ac"] is not None else 0,
                        int(normalized["kills"]) if normalized["kills"] is not None else 0,
                        int(normalized["mystic_score"]) if normalized["mystic_score"] is not None else 0,
                        int(normalized["radiant_spire"]) if normalized["radiant_spire"] is not None else 0,
                        str(normalized["alliance_rank"] or "").strip(),
                        normalized["kingdom_id"] or None,
                        now,
                        now,
                    ),
                )
                created_profiles += 1

        removed_profiles = 0
        if reconcile_roster and synced_game_ids:
            placeholders = connection.execute(
                """
                SELECT alliance_players.id AS profile_id, alliance_players.user_id AS user_id, alliance_players.game_id
                FROM alliance_players
                JOIN alliance_users ON alliance_users.id = alliance_players.user_id
                WHERE alliance_players.alliance_id = ?
                  AND alliance_users.discord_user_id LIKE 'jeabsplus:%'
                """,
                (alliance_id,),
            ).fetchall()
            for placeholder in placeholders:
                profile_game_id = str(placeholder["game_id"] or "").strip()
                if profile_game_id in synced_game_ids:
                    continue
                connection.execute("DELETE FROM alliance_players WHERE id = ?", (int(placeholder["profile_id"]),))
                _detach_orphan_synthetic_alliance_user(connection, int(placeholder["user_id"]), now)
                removed_profiles += 1

    return {
        "created_users": created_users,
        "created_profiles": created_profiles,
        "updated_profiles": updated_profiles,
        "skipped_rows": skipped_rows,
        "removed_profiles": removed_profiles,
    }


def _update_jeabs_sync_job(job_id: str, **changes: Any) -> None:
    with JEABS_SYNC_JOBS_LOCK:
        job = JEABS_SYNC_JOBS.get(job_id)
        if not job:
            return
        job.update(changes)
        job["updated_at"] = time.time()


def _run_jeabs_sync_job(job_id: str, alliance_id: int, jeabs_alliance_id: str, token: str) -> None:
    try:
        _update_jeabs_sync_job(job_id, state="running", stage="Fetching alliance roster", completed=0, total=0, percent=0)
        raw_members = _fetch_jeabs_members(jeabs_alliance_id, token)
        total = len(raw_members)
        _update_jeabs_sync_job(job_id, stage="Fetching Radiant Spire", completed=0, total=total, percent=0)

        with _get_db_connection() as connection:
            kingdom_row = connection.execute(
                """
                SELECT COALESCE(NULLIF(alliances.kingdom, ''), MAX(alliance_players.kingdom_id)) AS kingdom_id
                FROM alliances
                LEFT JOIN alliance_players ON alliance_players.alliance_id = alliances.id
                WHERE alliances.id = ?
                """,
                (alliance_id,),
            ).fetchone()
        kingdom_id = str((kingdom_row["kingdom_id"] if kingdom_row else "") or "").strip()
        try:
            radiant_scores = _fetch_jeabs_radiant_leaderboard(kingdom_id, token)
        except (ValueError, requests.RequestException):
            radiant_scores = {}
        if radiant_scores:
            raw_members = [
                {
                    **member,
                    **(
                        {"radiant_spire": radiant_scores[player_id]}
                        if (player_id := str(
                            member.get("governor_id")
                            or member.get("governorId")
                            or member.get("player_id")
                            or member.get("playerId")
                            or member.get("id")
                            or ""
                        ).strip()) in radiant_scores
                        else {}
                    ),
                }
                for member in raw_members
                if isinstance(member, dict)
            ]

        def _progress(completed: int, progress_total: int) -> None:
            percent = min(99, max(1, int((completed * 100) / max(1, progress_total))))
            _update_jeabs_sync_job(
                job_id,
                stage="Updating player details",
                completed=completed,
                total=progress_total,
                percent=percent,
            )

        enriched_members, detail_stats = _enrich_jeabs_members_with_player_details(
            raw_members,
            token,
            progress_callback=_progress,
        )
        _update_jeabs_sync_job(job_id, stage="Saving player data", completed=total, total=total, percent=99)
        sync_result = _sync_jeabs_members_into_alliance(alliance_id, enriched_members, reconcile_roster=True)
        imported_count = int(sync_result["created_profiles"]) + int(sync_result["updated_profiles"])
        message = (
            "JeabsPlus sync completed. "
            f"Imported {imported_count} players "
            f"({sync_result['created_profiles']} new, {sync_result['updated_profiles']} updated, {sync_result['removed_profiles']} removed)."
        )
        _update_jeabs_sync_job(
            job_id,
            state="complete",
            stage="Synchronization complete",
            completed=total,
            total=total,
            percent=100,
            message=message,
            result=sync_result,
            detail_scan=detail_stats,
        )
    except Exception as exc:
        _update_jeabs_sync_job(
            job_id,
            state="error",
            stage="Synchronization failed",
            message=str(exc).strip() or "JeabsPlus synchronization failed.",
        )


def _create_jeabs_sync_job(alliance_id: int, jeabs_alliance_id: str, token: str) -> tuple[dict[str, Any] | None, str | None]:
    now = time.time()
    with JEABS_SYNC_JOBS_LOCK:
        expired_ids = [
            job_id
            for job_id, job in JEABS_SYNC_JOBS.items()
            if now - float(job.get("updated_at") or now) > 3600
        ]
        for expired_id in expired_ids:
            JEABS_SYNC_JOBS.pop(expired_id, None)
        for job in JEABS_SYNC_JOBS.values():
            if int(job.get("alliance_id") or 0) == alliance_id and job.get("state") in {"pending", "running"}:
                return None, "A synchronization is already running for this alliance."

        job_id = secrets.token_urlsafe(18)
        job = {
            "job_id": job_id,
            "alliance_id": alliance_id,
            "state": "pending",
            "stage": "Starting synchronization",
            "completed": 0,
            "total": 0,
            "percent": 0,
            "message": "",
            "created_at": now,
            "updated_at": now,
        }
        JEABS_SYNC_JOBS[job_id] = job

    worker = threading.Thread(
        target=_run_jeabs_sync_job,
        args=(job_id, alliance_id, jeabs_alliance_id, token),
        daemon=True,
        name=f"jeabs-sync-{alliance_id}",
    )
    worker.start()
    return dict(job), None


PLAYER_COMBAT_STAT_FIELDS: tuple[str, ...] = (
    "infantry_attack_bonus",
    "infantry_defense_bonus",
    "infantry_lethality_bonus",
    "infantry_health_bonus",
    "cavalry_attack_bonus",
    "cavalry_defense_bonus",
    "cavalry_lethality_bonus",
    "cavalry_health_bonus",
    "archer_attack_bonus",
    "archer_defense_bonus",
    "archer_lethality_bonus",
    "archer_health_bonus",
)


def _star_display_from_points(star_points: int) -> tuple[int, int]:
    points = _clamp_int(star_points, minimum=1, maximum=30, default=1)
    star_tier = ((points - 1) // 6) + 1
    sub_level = ((points - 1) % 6) + 1
    return star_tier, sub_level


def _get_generation_profile(hero: dict[str, Any]) -> dict[str, float] | None:
    generation = int(hero.get("generation", 0) or 0)
    rarity = str(hero.get("rarity", "")).strip().lower()
    by_generation = GENERATION_PROGRESS_PROFILES.get(generation, {})
    profile = by_generation.get(rarity) or by_generation.get("*")
    return profile if isinstance(profile, dict) else None


def _build_generated_star_curve(max_value: float) -> dict[int, float]:
    if max_value <= 0:
        return {level: 0.0 for level in range(1, 31)}
    base_max = STAR_POINT_CURVE_BASE_VALUES[-1]
    return {
        idx + 1: (STAR_POINT_CURVE_BASE_VALUES[idx] / base_max) * max_value
        for idx in range(len(STAR_POINT_CURVE_BASE_VALUES))
    }


def _build_generated_widget_curve(widget_10_value: float) -> dict[int, float]:
    if widget_10_value <= 0:
        return {level: 0.0 for level in range(0, 11)}
    return {level: (widget_10_value * (level / 10.0)) for level in range(0, 11)}


def _build_progressed_stats(hero: dict[str, Any], star_points: int, widget_level: int) -> dict[str, Any]:
    # IMPORTANT:
    # Do not invent progression formulas. Use only values present in hero DB.
    # Star/widget selections are kept in UI state, but no synthetic scaling is applied
    # until explicit per-level progression data exists in the dataset.
    points = _clamp_int(star_points, minimum=1, maximum=30, default=1)

    star_tier, sub_level = _star_display_from_points(points)

    gear = hero.get("exclusive_gear") if isinstance(hero.get("exclusive_gear"), dict) else {}
    gear_stats = gear.get("stats") if isinstance(gear.get("stats"), dict) else {}
    expedition_stats = gear_stats.get("expedition") if isinstance(gear_stats.get("expedition"), dict) else {}

    progression = hero.get("progression") if isinstance(hero.get("progression"), dict) else {}
    star_points_map = progression.get("star_points") if isinstance(progression.get("star_points"), dict) else {}
    widget_levels_map = progression.get("widget_levels") if isinstance(progression.get("widget_levels"), dict) else {}

    profile = _get_generation_profile(hero)
    profile_star_max = _as_float((profile or {}).get("max", 0))
    profile_widget_10 = _as_float((profile or {}).get("widget_10", 0))

    generated_star_curve = _build_generated_star_curve(profile_star_max) if profile_star_max > 0 else {}
    generated_widget_curve = _build_generated_widget_curve(profile_widget_10) if profile else {}

    star_keys = sorted([int(k) for k in star_points_map.keys() if str(k).isdigit()])
    max_star_key = star_keys[-1] if star_keys else 30

    widget_keys = sorted([int(k) for k in widget_levels_map.keys() if str(k).isdigit()])
    max_widget_key = widget_keys[-1] if widget_keys else 10

    def _value_from_progression(
        progression_map: dict[str, Any],
        level: int,
        field: str,
        max_level: int,
        fallback_max: float,
        generated_curve: dict[int, float] | None = None,
    ) -> float:
        anchor_by_level: dict[int, float] = {}
        for raw_level, entry in progression_map.items():
            if not str(raw_level).isdigit() or not isinstance(entry, dict) or field not in entry:
                continue
            anchor_by_level[int(raw_level)] = _as_float(entry.get(field, fallback_max))

        for curve_level, curve_value in (generated_curve or {}).items():
            if curve_level not in anchor_by_level:
                anchor_by_level[curve_level] = _as_float(curve_value)

        anchors = sorted(anchor_by_level.items(), key=lambda item: item[0])

        if not anchors:
            # Fallback behavior when no validated level table exists for this field.
            return fallback_max * (level / max(1, max_level))

        for anchor_level, anchor_value in anchors:
            if level == anchor_level:
                return anchor_value

        first_level, first_value = anchors[0]
        if level < first_level:
            return first_value * (level / max(1, first_level))

        for i in range(len(anchors) - 1):
            low_level, low_value = anchors[i]
            high_level, high_value = anchors[i + 1]
            if low_level <= level <= high_level:
                span = max(1, high_level - low_level)
                ratio = (level - low_level) / span
                return low_value + (high_value - low_value) * ratio

        last_level, last_value = anchors[-1]
        if level > last_level:
            return last_value * (level / max(1, last_level))

        return last_value

    weapon_lethality_pct = _value_from_progression(
        widget_levels_map,
        widget_level,
        "weapon_lethality_pct",
        max_widget_key,
        _as_float(expedition_stats.get("lethalityPct", 0)),
        generated_curve=generated_widget_curve,
    )
    weapon_health_pct = _value_from_progression(
        widget_levels_map,
        widget_level,
        "weapon_health_pct",
        max_widget_key,
        _as_float(expedition_stats.get("healthPct", 0)),
        generated_curve=generated_widget_curve,
    )

    attack = _value_from_progression(star_points_map, points, "attack", max_star_key, _as_float(hero.get("attack", 0)))
    defense = _value_from_progression(star_points_map, points, "defense", max_star_key, _as_float(hero.get("defense", 0)))
    health = _value_from_progression(star_points_map, points, "health", max_star_key, _as_float(hero.get("health", 0)))
    expedition_attack = _value_from_progression(
        star_points_map,
        points,
        "expedition_attack_pct",
        max_star_key,
        _as_float(hero.get("expedition_attack_pct", 0)),
        generated_curve=generated_star_curve,
    )
    expedition_defense = _value_from_progression(
        star_points_map,
        points,
        "expedition_defense_pct",
        max_star_key,
        _as_float(hero.get("expedition_defense_pct", 0)),
        generated_curve=generated_star_curve,
    )

    return {
        "name": str(hero.get("name", "Hero")).strip(),
        "star_points": points,
        "star_tier": star_tier,
        "star_sub_level": sub_level,
        "widget_level": widget_level,
        "star_bonus_pct": 0.0,
        "widget_bonus_pct": 0.0,
        "attack": attack,
        "defense": defense,
        "health": health,
        "expedition_attack_pct": expedition_attack,
        "expedition_defense_pct": expedition_defense,
        "weapon_lethality_pct": weapon_lethality_pct,
        "weapon_health_pct": weapon_health_pct,
        "total_skill_count": _as_float(hero.get("total_skill_count", 0)),
    }


def _build_hero_comparison(
    left: dict[str, Any],
    right: dict[str, Any],
    left_star_points: int,
    left_widget_level: int,
    right_star_points: int,
    right_widget_level: int,
) -> dict[str, Any]:
    left_profile = _build_progressed_stats(left, left_star_points, left_widget_level)
    right_profile = _build_progressed_stats(right, right_star_points, right_widget_level)

    stat_defs = [
        {"key": "attack", "label": "Conquest Attack", "suffix": "", "decimals": 0},
        {"key": "defense", "label": "Conquest Defense", "suffix": "", "decimals": 0},
        {"key": "health", "label": "Conquest Health", "suffix": "", "decimals": 0},
        {"key": "expedition_attack_pct", "label": "Expedition Attack", "suffix": "%", "decimals": 2},
        {"key": "expedition_defense_pct", "label": "Expedition Defense", "suffix": "%", "decimals": 2},
        {"key": "total_skill_count", "label": "Total Skills", "suffix": "", "decimals": 0},
    ]

    rows: list[dict[str, Any]] = []
    ranked_diff: list[dict[str, Any]] = []
    for meta in stat_defs:
        key = str(meta["key"])
        left_value = _as_float(left_profile.get(key, 0))
        right_value = _as_float(right_profile.get(key, 0))
        delta = abs(left_value - right_value)

        if left_value > right_value:
            winner = "left"
        elif right_value > left_value:
            winner = "right"
        else:
            winner = "tie"

        rows.append(
            {
                "key": key,
                "label": str(meta["label"]),
                "left": left_value,
                "right": right_value,
                "delta": delta,
                "winner": winner,
                "suffix": str(meta["suffix"]),
                "decimals": int(meta["decimals"]),
            }
        )

        ranked_diff.append({"label": str(meta["label"]), "delta": delta, "winner": winner})

    ranked_diff.sort(key=lambda item: float(item["delta"]), reverse=True)

    narrative: list[str] = []
    narrative.append(
        f"{left_profile['name']}: {left_profile['star_tier']} Star - Level {left_profile['star_sub_level']} / Widget Lv {left_profile['widget_level']} | "
        f"{right_profile['name']}: {right_profile['star_tier']} Star - Level {right_profile['star_sub_level']} / Widget Lv {right_profile['widget_level']}."
    )

    top_changes = [item for item in ranked_diff if item["delta"] > 0][:3]
    for item in top_changes:
        winner_name = left_profile.get("name") if item["winner"] == "left" else right_profile.get("name")
        narrative.append(f"{winner_name} leads in {item['label']}.")

    if str(left.get("troop_type", "")).lower() != str(right.get("troop_type", "")).lower():
        narrative.append(
            f"Different troop specialization: {left.get('name')} ({left.get('troop_type')}) vs {right.get('name')} ({right.get('troop_type')})."
        )

    if int(left.get("generation", 0) or 0) != int(right.get("generation", 0) or 0):
        newer = left if int(left.get("generation", 0) or 0) > int(right.get("generation", 0) or 0) else right
        narrative.append(f"{newer.get('name')} belongs to a newer generation.")

    if not narrative:
        narrative.append("These heroes have very similar overall profiles.")

    left_ad_score = _as_float(left_profile.get("expedition_attack_pct", 0)) + _as_float(left_profile.get("expedition_defense_pct", 0))
    right_ad_score = _as_float(right_profile.get("expedition_attack_pct", 0)) + _as_float(right_profile.get("expedition_defense_pct", 0))

    if left_ad_score > right_ad_score:
        stronger_name = str(left_profile.get("name", "Left Hero"))
    elif right_ad_score > left_ad_score:
        stronger_name = str(right_profile.get("name", "Right Hero"))
    else:
        stronger_name = "Both heroes are evenly matched"

    rows = {
        "left_attack_bonus_pct": _as_float(left_profile.get("expedition_attack_pct", 0)),
        "right_attack_bonus_pct": _as_float(right_profile.get("expedition_attack_pct", 0)),
        "left_defense_bonus_pct": _as_float(left_profile.get("expedition_defense_pct", 0)),
        "right_defense_bonus_pct": _as_float(right_profile.get("expedition_defense_pct", 0)),
        "left_attack_defense_bonus_pct": (_as_float(left_profile.get("expedition_attack_pct", 0)) + _as_float(left_profile.get("expedition_defense_pct", 0))) / 2,
        "right_attack_defense_bonus_pct": (_as_float(right_profile.get("expedition_attack_pct", 0)) + _as_float(right_profile.get("expedition_defense_pct", 0))) / 2,
        "left_weapon_health_bonus_pct": _as_float(left_profile.get("weapon_health_pct", 0)),
        "left_weapon_lethality_bonus_pct": _as_float(left_profile.get("weapon_lethality_pct", 0)),
        "right_weapon_health_bonus_pct": _as_float(right_profile.get("weapon_health_pct", 0)),
        "right_weapon_lethality_bonus_pct": _as_float(right_profile.get("weapon_lethality_pct", 0)),
        "diff_attack_pct": _as_float(right_profile.get("expedition_attack_pct", 0)) - _as_float(left_profile.get("expedition_attack_pct", 0)),
        "diff_defense_pct": _as_float(right_profile.get("expedition_defense_pct", 0)) - _as_float(left_profile.get("expedition_defense_pct", 0)),
        "diff_weapon_health_pct": _as_float(right_profile.get("weapon_health_pct", 0)) - _as_float(left_profile.get("weapon_health_pct", 0)),
        "diff_weapon_lethality_pct": _as_float(right_profile.get("weapon_lethality_pct", 0)) - _as_float(left_profile.get("weapon_lethality_pct", 0)),
        "stronger_name": stronger_name,
    }

    return {
        "rows": rows,
        "summary": narrative,
        "left_profile": left_profile,
        "right_profile": right_profile,
        "showcase": showcase,
    }


def _parse_hero_progress_data(raw_value: Any) -> dict[str, dict[str, Any]]:
    if isinstance(raw_value, dict):
        return raw_value
    if not raw_value:
        return {}
    try:
        payload = json.loads(str(raw_value))
    except (TypeError, ValueError):
        return {}
    return payload if isinstance(payload, dict) else {}


def _normalize_jeabs_dashboard_member(member: dict[str, Any]) -> dict[str, Any] | None:
    normalized = _map_jeabs_member_fields(member)
    if not normalized:
        return None
    return {
        **member,
        "player_name": str(normalized.get("player_name") or member.get("name") or "").strip(),
        "discord_username": str(normalized.get("player_name") or member.get("name") or "").strip(),
        "game_id": str(normalized.get("game_id") or "").strip(),
        "total_power": int(normalized.get("total_power") or 0),
        "power_ac": int(normalized.get("power_ac") or 0),
        "kills": int(normalized.get("kills") or 0),
        "mystic_score": int(normalized.get("mystic_score") or 0),
        "radiant_spire": int(normalized.get("radiant_spire") or 0),
        "vip_level": int(normalized.get("vip_level") or 0),
        "town_hall_level": int(normalized.get("town_hall_level") or 0),
        "kingdom_id": str(normalized.get("kingdom_id") or "").strip(),
        "alliance_rank": str(normalized.get("alliance_rank") or "").strip(),
        "avatar_url": str(normalized.get("avatar_url") or member.get("avatar_url") or "").strip(),
        "hero_data": member.get("hero_data") or "{}",
    }


def _default_nap4_entries(alliance: dict[str, Any]) -> list[dict[str, str]]:
    own_jeabs_id = str(alliance.get("jeabs_alliance_id") or "").strip()
    return [
        {"jeabs_id": own_jeabs_id},
        {"jeabs_id": ""},
        {"jeabs_id": ""},
        {"jeabs_id": ""},
    ]


def _parse_nap4_entries(raw_value: Any, alliance: dict[str, Any]) -> list[dict[str, str]]:
    defaults = _default_nap4_entries(alliance)
    if not raw_value:
        return defaults

    payload: Any = None
    if isinstance(raw_value, list):
        payload = raw_value
    else:
        try:
            payload = json.loads(str(raw_value))
        except (TypeError, ValueError):
            return defaults
    if not isinstance(payload, list):
        return defaults

    parsed: list[dict[str, str]] = []
    for item in payload[:4]:
        if isinstance(item, str):
            entry_id_raw = item.strip()
        elif isinstance(item, dict):
            entry_id_raw = str(item.get("jeabs_id") or item.get("alliance_id") or "").strip()
        else:
            parsed.append({"jeabs_id": ""})
            continue
        normalized = _normalize_jeabs_alliance_input(entry_id_raw)
        entry_id = str(normalized.get("alliance_id") or "").strip()
        parsed.append({"jeabs_id": entry_id})

    while len(parsed) < 4:
        parsed.append({"jeabs_id": ""})

    if not parsed[0].get("jeabs_id") and defaults[0].get("jeabs_id"):
        parsed[0]["jeabs_id"] = defaults[0]["jeabs_id"]
    return parsed


def _parse_kvk_server_entries(raw_value: Any) -> list[dict[str, str]]:
    values: list[Any]
    if isinstance(raw_value, list):
        values = raw_value
    else:
        try:
            parsed = json.loads(str(raw_value or ""))
            values = parsed if isinstance(parsed, list) else [raw_value]
        except (TypeError, ValueError):
            values = [raw_value] if raw_value else []
    entries = [{"jeabs_input": str(value or "").strip()} for value in values[:4]]
    while len(entries) < 4:
        entries.append({"jeabs_input": ""})
    return entries


def _merge_jeabs_server_rosters(rosters: list[list[dict[str, Any]]]) -> list[dict[str, Any]]:
    merged: dict[str, dict[str, Any]] = {}
    for roster in rosters:
        for member in roster:
            if not isinstance(member, dict):
                continue
            player_id = str(
                member.get("governor_id")
                or member.get("governorId")
                or member.get("player_id")
                or member.get("playerId")
                or member.get("id")
                or ""
            ).strip()
            if player_id:
                merged[player_id] = member
    return list(merged.values())


def _fetch_jeabs_server_members(
    entries: list[dict[str, str]], kingdom_id: str, token: str, progress_callback: Any = None
) -> list[dict[str, Any]]:
    rosters: list[list[dict[str, Any]]] = []
    for entry in entries:
        jeabs_input = str(entry.get("jeabs_input") or entry.get("jeabs_id") or "").strip()
        if not jeabs_input:
            continue
        fetch_input = jeabs_input
        normalized = _normalize_jeabs_alliance_input(jeabs_input)
        if kingdom_id and not normalized.get("kingdom_id") and not jeabs_input.startswith(("http://", "https://")):
            fetch_input = f"https://jeabslist.com/alliances/{kingdom_id}/{normalized.get('alliance_id') or jeabs_input}"
        rosters.append(_fetch_jeabs_members(fetch_input, token))
    merged = _merge_jeabs_server_rosters(rosters)
    enriched, _detail_stats = _enrich_jeabs_members_with_player_details(
        merged, token, progress_callback=progress_callback
    )
    return enriched


def _extract_jeabs_alliance_name(payload: Any, fallback: str) -> str:
    name_keys = (
        "_jeabs_official_name",
        "alliance_name",
        "allianceName",
        "alliance_tag",
        "allianceTag",
        "guild_name",
        "guildName",
    )
    nested_name_keys = ("name", "alliance_name", "allianceName", "tag")

    records = payload if isinstance(payload, list) else [payload]
    if isinstance(payload, dict):
        name_keys = ("name", *name_keys)
    for record in records:
        if not isinstance(record, dict):
            continue
        for key in name_keys:
            value = record.get(key)
            if isinstance(value, dict):
                continue
            text = str(value or "").strip()
            if text:
                return text

        metadata_records = [record.get(key) for key in ("alliance", "alliance_info", "allianceInfo", "guild")]
        data = record.get("data")
        if isinstance(data, dict):
            metadata_records.extend(data.get(key) for key in ("alliance", "alliance_info", "allianceInfo", "guild"))

        for metadata in metadata_records:
            if not isinstance(metadata, dict):
                continue
            for key in nested_name_keys:
                text = str(metadata.get(key) or "").strip()
                if text:
                    return text
    return fallback


def _build_nap4_snapshot(
    entries: list[dict[str, str]],
    kingdom_id: str,
    token: str,
    progress_callback: Any = None,
) -> dict[str, Any]:
    alliance_reports: list[dict[str, Any]] = []
    errors: list[str] = []
    prepared_rosters: list[tuple[str, str, list[dict[str, Any]]]] = []

    for index, entry in enumerate(entries, start=1):
        entry_name = f"Alliance {index}"
        entry_id = str(entry.get("jeabs_id") or "").strip()
        if not entry_id:
            continue

        fetch_input = entry_id
        if kingdom_id and not entry_id.startswith(("http://", "https://")):
            fetch_input = f"https://jeabslist.com/alliances/{kingdom_id}/{entry_id}"

        try:
            raw_members = _fetch_jeabs_members(fetch_input, token)
            prepared_rosters.append((entry_name, entry_id, raw_members))
        except Exception as exc:
            error_text = str(exc).strip() or "Unknown JeabsPlus error"
            if len(error_text) > 220:
                error_text = f"{error_text[:220]}..."
            errors.append(f"{entry_name}: {error_text}")

    total_players = sum(len(raw_members) for _, _, raw_members in prepared_rosters)
    completed_offset = 0
    if progress_callback:
        progress_callback(0, total_players)

    for entry_name, entry_id, raw_members in prepared_rosters:
        roster_count = len(raw_members)
        try:
            def _roster_progress(completed: int, _roster_total: int) -> None:
                if progress_callback:
                    progress_callback(completed_offset + completed, total_players)

            raw_members, _detail_stats = _enrich_jeabs_members_with_player_details(
                raw_members,
                token,
                progress_callback=_roster_progress,
            )
            standings_candidates = [
                (index, str(
                    member.get("governor_id")
                    or member.get("governorId")
                    or member.get("player_id")
                    or member.get("playerId")
                    or member.get("id")
                    or ""
                ).strip())
                for index, member in enumerate(raw_members)
                if isinstance(member, dict)
                and _extract_radiant_spire_from_member_standings(member) is None
            ]

            def _fetch_standings(candidate: tuple[int, str]) -> tuple[int, list[dict[str, Any]]]:
                index, player_id = candidate
                if not player_id:
                    return index, []
                try:
                    standings_payload = _fetch_jeabs_premium_payload(
                        f"players/{quote(player_id, safe='')}/standings",
                        token,
                    )
                    standings = standings_payload.get("standings") or []
                    return index, standings if isinstance(standings, list) else []
                except (ValueError, requests.RequestException):
                    return index, []

            with ThreadPoolExecutor(max_workers=min(JEABSPLUS_DETAIL_MAX_WORKERS, max(1, len(standings_candidates)))) as executor:
                futures = [executor.submit(_fetch_standings, candidate) for candidate in standings_candidates]
                standings_completed = 0
                for future in as_completed(futures):
                    index, standings = future.result()
                    raw_members[index]["standings"] = standings
                    standings_completed += 1
                    if progress_callback:
                        progress_callback(
                            completed_offset + min(roster_count, _detail_stats["scanned_ids"] + standings_completed),
                            total_players,
                        )
            official_name = _extract_jeabs_alliance_name(raw_members, entry_name)
            normalized_members = [
                normalized_member
                for normalized_member in (
                    _normalize_jeabs_dashboard_member(member)
                    for member in raw_members
                    if isinstance(member, dict)
                )
                if normalized_member is not None
            ]
        except Exception as exc:
            error_text = str(exc).strip() or "Unknown JeabsPlus error"
            if len(error_text) > 220:
                error_text = f"{error_text[:220]}..."
            errors.append(f"{entry_name}: {error_text}")
            if progress_callback:
                progress_callback(completed_offset + roster_count, total_players)
            completed_offset += roster_count
            continue

        completed_offset += roster_count

        ranked_mystic = _build_swordland_ranked_members(normalized_members)
        ranked_power = sorted(
            ranked_mystic,
            key=lambda item: (int(item.get("power") or 0), int(item.get("mystic_score") or 0), str(item.get("name") or "").lower()),
            reverse=True,
        )
        ranked_radiant = sorted(
            ranked_mystic,
            key=lambda item: (int(item.get("radiant_spire") or 0), int(item.get("power") or 0), str(item.get("name") or "").lower()),
            reverse=True,
        )

        players_fetched = len(ranked_mystic)
        total_power = sum(int(member.get("power") or 0) for member in ranked_mystic)
        total_mystic = sum(int(member.get("mystic_score") or 0) for member in ranked_mystic)
        total_radiant = sum(int(member.get("radiant_spire") or 0) for member in ranked_mystic)

        alliance_reports.append(
            {
                "name": official_name,
                "jeabs_id": entry_id,
                "players_fetched": players_fetched,
                "total_power": total_power,
                "total_mystic": total_mystic,
                "total_radiant": total_radiant,
                "avg_power": (total_power / players_fetched) if players_fetched else 0,
                "avg_mystic": (total_mystic / players_fetched) if players_fetched else 0,
                "top10_mystic": ranked_mystic[:10],
                "top10_power": ranked_power[:10],
                "top10_radiant": ranked_radiant[:10],
            }
        )

    metric_defs = [
        ("Players Fetched", "players_fetched", "int"),
        ("Total Power", "total_power", "power"),
        ("Total Mystic", "total_mystic", "int"),
        ("Total Radiant Spire", "total_radiant", "int"),
        ("Avg Power", "avg_power", "power"),
        ("Avg Mystic", "avg_mystic", "float"),
    ]
    general_rows: list[dict[str, Any]] = []
    for label, field, kind in metric_defs:
        raw_values = [_as_float(report.get(field, 0)) for report in alliance_reports]
        leader_value = max(raw_values) if raw_values else 0
        values = []
        for report in alliance_reports:
            raw_value = report.get(field, 0)
            values.append(
                {
                    "raw": _as_float(raw_value),
                    "display": _swordland_format_value(raw_value, kind),
                }
            )
        general_rows.append(
            {
                "label": label,
                "values": values,
                "leader_value": leader_value,
                "kind": kind,
            }
        )
    return {
        "alliances": alliance_reports,
        "general_rows": general_rows,
        "errors": errors,
    }


def _run_nap4_sync_job(job_id: str, alliance_id: int) -> None:
    try:
        with _get_db_connection() as connection:
            alliance_row = connection.execute("SELECT * FROM alliances WHERE id = ?", (alliance_id,)).fetchone()
        if not alliance_row:
            raise ValueError("Alliance not found.")
        alliance = dict(alliance_row)
        entries = _parse_nap4_entries(alliance.get("nap4_config_json"), alliance)
        token = _get_jeabs_token(alliance)
        kingdom_id = str(alliance.get("kingdom") or "").strip()
        _update_jeabs_sync_job(job_id, state="running", stage="Fetching NAP4 rosters", completed=0, total=0, percent=0)

        def _progress(completed: int, total: int) -> None:
            percent = min(99, max(0, int((completed * 100) / max(1, total))))
            _update_jeabs_sync_job(
                job_id,
                stage="Updating NAP4 players",
                completed=completed,
                total=total,
                percent=percent,
            )

        snapshot = _build_nap4_snapshot(entries, kingdom_id, token, progress_callback=_progress)
        with JEABS_SYNC_JOBS_LOCK:
            current_job = dict(JEABS_SYNC_JOBS.get(job_id) or {})
        total = int(current_job.get("total") or 0)
        _update_jeabs_sync_job(job_id, stage="Saving NAP4 comparison", completed=total, total=total, percent=99)
        now = datetime.now(timezone.utc).isoformat()
        payload = {
            "alliances": snapshot.get("alliances", []),
            "general_rows": snapshot.get("general_rows", []),
            "errors": snapshot.get("errors", []),
            "cached_at": now,
        }
        with _get_db_connection() as connection:
            connection.execute(
                "UPDATE alliances SET nap4_cache_json = ?, nap4_cache_updated_at = ?, updated_at = ? WHERE id = ?",
                (json.dumps(payload), now, now, alliance_id),
            )
        _update_jeabs_sync_job(
            job_id,
            state="complete",
            stage="NAP4 synchronization complete",
            completed=total,
            total=total,
            percent=100,
            message="NAP4 cache refreshed successfully.",
            errors=snapshot.get("errors", []),
        )
    except Exception as exc:
        _update_jeabs_sync_job(
            job_id,
            state="error",
            stage="NAP4 synchronization failed",
            message=str(exc).strip() or "NAP4 synchronization failed.",
        )


def _create_nap4_sync_job(alliance_id: int) -> tuple[dict[str, Any] | None, str | None]:
    now = time.time()
    with JEABS_SYNC_JOBS_LOCK:
        for job in JEABS_SYNC_JOBS.values():
            if int(job.get("alliance_id") or 0) == alliance_id and job.get("state") in {"pending", "running"}:
                return None, "A synchronization is already running for this alliance."
        job_id = secrets.token_urlsafe(18)
        job = {
            "job_id": job_id,
            "alliance_id": alliance_id,
            "job_type": "nap4",
            "state": "pending",
            "stage": "Starting NAP4 synchronization",
            "completed": 0,
            "total": 0,
            "percent": 0,
            "message": "",
            "created_at": now,
            "updated_at": now,
        }
        JEABS_SYNC_JOBS[job_id] = job
    threading.Thread(
        target=_run_nap4_sync_job,
        args=(job_id, alliance_id),
        daemon=True,
        name=f"nap4-sync-{alliance_id}",
    ).start()
    return dict(job), None


def _reformat_cached_nap4_general_rows(rows: list[Any]) -> list[dict[str, Any]]:
    """Re-render cached NAP4 general-comparison values with current number formatting."""
    reformatted: list[dict[str, Any]] = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        updated = dict(row)
        kind = str(row.get("kind") or "int")
        values = row.get("values")
        if isinstance(values, list):
            updated["values"] = [
                {**value, "display": _swordland_format_value(value.get("raw"), kind)}
                if isinstance(value, dict) and value.get("raw") is not None
                else value
                for value in values
            ]
        reformatted.append(updated)
    return reformatted


def _build_nap4_context(alliance: dict[str, Any], active_tab: str = "player-list") -> dict[str, Any]:
    entries = _parse_nap4_entries(alliance.get("nap4_config_json"), alliance)
    context: dict[str, Any] = {
        "entries": entries,
        "alliances": [],
        "general_rows": [],
        "message": "",
        "errors": [],
        "last_synced_at": "",
        "has_cache": False,
    }

    if active_tab != "nap4":
        return context

    cache_payload_raw = alliance.get("nap4_cache_json")
    cache_payload: dict[str, Any] = {}
    if isinstance(cache_payload_raw, dict):
        cache_payload = cache_payload_raw
    elif cache_payload_raw:
        try:
            parsed_cache = json.loads(str(cache_payload_raw))
            if isinstance(parsed_cache, dict):
                cache_payload = parsed_cache
        except (TypeError, ValueError):
            cache_payload = {}

    cached_alliances = cache_payload.get("alliances") if isinstance(cache_payload.get("alliances"), list) else []
    cached_general_rows = cache_payload.get("general_rows") if isinstance(cache_payload.get("general_rows"), list) else []
    cached_errors = cache_payload.get("errors") if isinstance(cache_payload.get("errors"), list) else []

    cache_ts = str(alliance.get("nap4_cache_updated_at") or cache_payload.get("cached_at") or "").strip()
    has_cache = bool(cached_alliances or cached_general_rows or cached_errors)
    context["has_cache"] = has_cache
    context["last_synced_at"] = cache_ts
    context["alliances"] = cached_alliances
    context["general_rows"] = _reformat_cached_nap4_general_rows(cached_general_rows)
    context["errors"] = cached_errors

    if has_cache:
        if cache_ts:
            context["message"] = f"Showing cached data from {cache_ts}. Click Refresh NAP4 Data to sync latest values."
        else:
            context["message"] = "Showing cached data. Click Refresh NAP4 Data to sync latest values."
    else:
        context["message"] = "No cached NAP4 data yet. Click Refresh NAP4 Data to synchronize from JeabsPlus."

    return context


def _swordland_format_value(value: Any, kind: str) -> str:
    if kind == "power":
        return _format_power(value)
    if kind == "float":
        return _format_stat_value(value)
    if kind == "level":
        return _format_town_hall_level(value)
    return _format_whole_number(value)


def _reformat_cached_comparison_rows(rows: list[Any]) -> list[dict[str, Any]]:
    """Re-render cached Swordland row strings with the current number formatting
    (so old caches pick up formatting changes without needing a fresh sync)."""
    reformatted: list[dict[str, Any]] = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        updated = dict(row)
        kind = str(row.get("kind") or "int")
        if row.get("left_raw") is not None:
            updated["left"] = _swordland_format_value(row["left_raw"], kind)
        if row.get("right_raw") is not None:
            updated["right"] = _swordland_format_value(row["right_raw"], kind)
        if row.get("delta_raw") is not None:
            delta_value = _as_float(row["delta_raw"])
            if abs(delta_value) < 0.0001:
                updated["delta"] = "0"
            else:
                sign = "+" if delta_value > 0 else "-"
                if kind == "float":
                    delta_core = _format_stat_value(abs(delta_value))
                else:
                    delta_core = _format_whole_number(int(round(abs(delta_value))))
                updated["delta"] = f"{sign}{delta_core}"
        reformatted.append(updated)
    return reformatted


def _swordland_metric_row(label: str, left_value: Any, right_value: Any, kind: str = "int") -> dict[str, Any]:
    left_number = _as_float(left_value)
    right_number = _as_float(right_value)
    if left_number > right_number:
        winner = "left"
    elif right_number > left_number:
        winner = "right"
    else:
        winner = "tie"
    delta_value = left_number - right_number
    if abs(delta_value) < 0.0001:
        delta_display = "0"
    else:
        sign = "+" if delta_value > 0 else "-"
        if kind == "float":
            delta_core = _format_stat_value(abs(delta_value))
        else:
            delta_core = _format_whole_number(int(round(abs(delta_value))))
        delta_display = f"{sign}{delta_core}"
    return {
        "label": label,
        "left": _swordland_format_value(left_value, kind),
        "right": _swordland_format_value(right_value, kind),
        "left_raw": left_number,
        "right_raw": right_number,
        "delta": delta_display,
        "delta_raw": delta_value,
        "winner": winner,
        "kind": kind,
    }


def _swordland_median(values: list[int]) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2 == 1:
        return float(ordered[middle])
    return (ordered[middle - 1] + ordered[middle]) / 2.0


def _build_swordland_ranked_members(member_rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    ranked_members: list[dict[str, Any]] = []
    for member in member_rows:
        display_name = str(member.get("player_name") or member.get("discord_username") or member.get("name") or "").strip()
        town_hall_level = member.get("town_hall_level")
        ranked_members.append(
            {
                "name": display_name or "—",
                "game_id": str(member.get("game_id") or "").strip(),
                "avatar": str(member.get("member_avatar_url") or member.get("avatar_url") or "").strip(),
                "power": max(0, int(_parse_total_power(member.get("total_power"), 0))),
                "power_ac": max(0, _parse_loose_int(member.get("power_ac"), 0)),
                "kills": max(0, int(_parse_loose_int(member.get("kills"), 0))),
                "mystic_score": max(0, int(_parse_loose_int(member.get("mystic_score"), 0))),
                "radiant_spire": max(0, int(_parse_loose_int(member.get("radiant_spire"), 0))),
                "combat_score": int(round(sum(_as_float(member.get(field)) for field in PLAYER_COMBAT_STAT_FIELDS))),
                "vip_level": max(0, int(_parse_loose_int(member.get("vip_level"), 0))),
                "level": _parse_town_hall_level(town_hall_level, 0) if town_hall_level not in (None, "") else 0,
                "rank": _normalize_alliance_rank(member.get("alliance_rank")),
                "kingdom_id": str(member.get("kingdom_id") or "").strip(),
                "hero_data": member.get("hero_data"),
            }
        )

    ranked_members.sort(
        key=lambda item: (
            int(item.get("mystic_score") or 0),
            int(item.get("power") or 0),
            str(item.get("name") or "").lower(),
        ),
        reverse=True,
    )
    for index, member in enumerate(ranked_members, start=1):
        member["position"] = index
    return ranked_members


def _build_swordland_side_summary(member_rows: list[dict[str, Any]], alliance_label: str, source_label: str) -> dict[str, Any]:
    rank_counts = {f"R{i}": 0 for i in range(1, 6)}
    top_members: list[dict[str, Any]] = []
    ranked_members = _build_swordland_ranked_members(member_rows)
    eligible_top_30 = ranked_members[:30]
    eligible_top_20 = ranked_members[:20]
    eligible_top_10 = ranked_members[:10]
    eligible_top_5 = ranked_members[:5]
    radiant_top_5 = sorted(
        ranked_members,
        key=lambda member: (int(member.get("radiant_spire") or 0), int(member.get("mystic_score") or 0)),
        reverse=True,
    )[:5]

    total_power = 0
    total_power_ac = 0
    total_kills = 0
    total_mystic_score = 0
    total_combat_score = 0.0
    vip_values: list[int] = []
    town_hall_values: list[int] = []
    kingdom_ids: set[str] = set()

    hero_profiles = 0
    hero_entries = 0
    hero_star_points = 0
    hero_widgets = 0
    hero_skills = 0

    for member in ranked_members:
        total_power_value = int(member.get("power") or 0)
        power_ac_value = int(member.get("power_ac") or 0)
        kills_value = int(member.get("kills") or 0)
        mystic_value = int(member.get("mystic_score") or 0)
        combat_score_value = _as_float(member.get("combat_score") or 0)
        vip_value = int(member.get("vip_level") or 0)
        if vip_value > 0:
            vip_values.append(vip_value)

        level_value = int(member.get("level") or 0)
        if level_value > 0:
            town_hall_values.append(level_value)

        kingdom_id = str(member.get("kingdom_id") or "").strip()
        if kingdom_id:
            kingdom_ids.add(kingdom_id)

        alliance_rank = _normalize_alliance_rank(member.get("rank"))
        if alliance_rank in rank_counts:
            rank_counts[alliance_rank] += 1

        hero_progress = _parse_hero_progress_data(member.get("hero_data"))
        if hero_progress:
            hero_profiles += 1
        for hero_state in hero_progress.values():
            if not isinstance(hero_state, dict):
                continue
            stars = _clamp_int(hero_state.get("stars"), 1, 30, 0)
            if stars > 0:
                hero_entries += 1
                hero_star_points += stars
            if str(hero_state.get("widget", "")).strip():
                hero_widgets += 1
            if str(hero_state.get("skill", "")).strip():
                hero_skills += 1

        top_members.append(member)

        total_power += total_power_value
        total_power_ac += power_ac_value
        total_kills += kills_value
        total_mystic_score += mystic_value
        total_combat_score += combat_score_value

    member_count = len(ranked_members)
    top30_count = len(eligible_top_30)
    max_town_hall = max(town_hall_values) if town_hall_values else 0
    mystic_values = [int(member.get("mystic_score") or 0) for member in eligible_top_30]
    top30_power_total = sum(int(member.get("power") or 0) for member in eligible_top_30)
    top30_mystic_total = sum(int(member.get("mystic_score") or 0) for member in eligible_top_30)

    threshold_values = [2500, 2250, 2000, 1800]
    threshold_counts: dict[int, int] = {
        threshold: sum(1 for value in mystic_values if value >= threshold)
        for threshold in threshold_values
    }

    def _sum_metric(rows: list[dict[str, Any]], metric: str) -> int:
        return sum(int(item.get(metric) or 0) for item in rows)

    return {
        "label": alliance_label,
        "source_label": source_label,
        "eligible_count": member_count,
        "top30_count": top30_count,
        "member_count": member_count,
        "total_power": total_power,
        "avg_power": (total_power / member_count) if member_count else 0,
        "total_power_ac": total_power_ac,
        "total_kills": total_kills,
        "total_mystic_score": total_mystic_score,
        "avg_vip": (sum(vip_values) / len(vip_values)) if vip_values else 0,
        "avg_town_hall": (sum(town_hall_values) / len(town_hall_values)) if town_hall_values else 0,
        "max_town_hall": max_town_hall,
        "combat_score_total": total_combat_score,
        "combat_score_avg": (total_combat_score / member_count) if member_count else 0,
        "hero_profiles": hero_profiles,
        "hero_entries": hero_entries,
        "hero_star_points": hero_star_points,
        "hero_widgets": hero_widgets,
        "hero_skills": hero_skills,
        "rank_counts": rank_counts,
        "unique_kingdoms": len(kingdom_ids),
        "top30_combined_power": top30_power_total,
        "top30_avg_power": (top30_power_total / top30_count) if top30_count else 0,
        "top30_combined_mystic": top30_mystic_total,
        "top30_avg_mystic": (top30_mystic_total / top30_count) if top30_count else 0,
        "top30_median_mystic": _swordland_median(mystic_values),
        "top30_highest_mystic": max(mystic_values) if mystic_values else 0,
        "top30_cutoff_mystic": mystic_values[-1] if mystic_values else 0,
        "elite_top5_mystic": _sum_metric(eligible_top_5, "mystic_score"),
        "elite_top10_mystic": _sum_metric(eligible_top_10, "mystic_score"),
        "elite_top5_power": _sum_metric(eligible_top_5, "power"),
        "elite_top10_power": _sum_metric(eligible_top_10, "power"),
        "elite_top5_radiant": _sum_metric(radiant_top_5, "radiant_spire"),
        "depth_top20_mystic": _sum_metric(eligible_top_20, "mystic_score"),
        "depth_top30_mystic": _sum_metric(eligible_top_30, "mystic_score"),
        "depth_top20_power": _sum_metric(eligible_top_20, "power"),
        "depth_top30_power": _sum_metric(eligible_top_30, "power"),
        "threshold_counts": threshold_counts,
        "top30_members": eligible_top_30,
        "top_names": eligible_top_5,
        "top_radiant": radiant_top_5,
        "top_members": top_members[:5],
    }


def _build_swordland_comparison_rows(left: dict[str, Any], right: dict[str, Any]) -> list[dict[str, Any]]:
    metric_defs = [
        ("Players Fetched", "member_count", "int"),
        ("Total Power", "total_power", "power"),
        ("Avg Power", "avg_power", "power"),
        ("Power AC", "total_power_ac", "power"),
        ("Combat Score", "combat_score_total", "int"),
        ("Avg Combat", "combat_score_avg", "float"),
        ("Kills", "total_kills", "int"),
        ("Mystic", "total_mystic_score", "int"),
        ("Avg VIP", "avg_vip", "float"),
        ("Avg LVL", "avg_town_hall", "float"),
        ("Top LVL", "max_town_hall", "level"),
        ("Hero Profiles", "hero_profiles", "int"),
        ("Hero Entries", "hero_entries", "int"),
        ("Hero Stars", "hero_star_points", "int"),
        ("Widget Selections", "hero_widgets", "int"),
        ("Skill Selections", "hero_skills", "int"),
        ("Unique Kingdoms", "unique_kingdoms", "int"),
        ("R1", "rank_r1", "int"),
        ("R2", "rank_r2", "int"),
        ("R3", "rank_r3", "int"),
        ("R4", "rank_r4", "int"),
        ("R5", "rank_r5", "int"),
    ]

    rows: list[dict[str, Any]] = []
    for label, key, kind in metric_defs:
        if key.startswith("rank_"):
            rank_key = f"R{key[-1]}"
            left_value = int((left.get("rank_counts") or {}).get(rank_key, 0))
            right_value = int((right.get("rank_counts") or {}).get(rank_key, 0))
        else:
            left_value = left.get(key, 0)
            right_value = right.get(key, 0)

        rows.append(_swordland_metric_row(label, left_value, right_value, kind))

    return rows


def _build_swordland_depth_rank_wins(
    left_members: list[dict[str, Any]],
    right_members: list[dict[str, Any]],
    field_name: str,
    limit: int = 30,
) -> dict[str, int]:
    wins_left = 0
    wins_right = 0
    ties = 0
    compared = min(limit, len(left_members), len(right_members))
    for index in range(compared):
        left_value = _as_float(left_members[index].get(field_name, 0))
        right_value = _as_float(right_members[index].get(field_name, 0))
        if left_value > right_value:
            wins_left += 1
        elif right_value > left_value:
            wins_right += 1
        else:
            ties += 1
    return {
        "wins_left": wins_left,
        "wins_right": wins_right,
        "ties": ties,
        "compared": compared,
    }


def _build_swordland_report(left: dict[str, Any], right: dict[str, Any]) -> dict[str, Any]:
    left_top30 = list(left.get("top30_members") or [])
    right_top30 = list(right.get("top30_members") or [])

    mystic_wins = _build_swordland_depth_rank_wins(left_top30, right_top30, "mystic_score", 30)
    power_wins = _build_swordland_depth_rank_wins(left_top30, right_top30, "power", 30)

    snapshot_rows = [
        _swordland_metric_row("Combined Power", left.get("top30_combined_power", 0), right.get("top30_combined_power", 0), "power"),
        _swordland_metric_row("Average Power", left.get("top30_avg_power", 0), right.get("top30_avg_power", 0), "power"),
        _swordland_metric_row("Combined Mystic", left.get("top30_combined_mystic", 0), right.get("top30_combined_mystic", 0), "int"),
        _swordland_metric_row("Average Mystic", left.get("top30_avg_mystic", 0), right.get("top30_avg_mystic", 0), "float"),
        _swordland_metric_row("Median Mystic", left.get("top30_median_mystic", 0), right.get("top30_median_mystic", 0), "float"),
        _swordland_metric_row("Highest Mystic", left.get("top30_highest_mystic", 0), right.get("top30_highest_mystic", 0), "int"),
        _swordland_metric_row("30th Player Mystic", left.get("top30_cutoff_mystic", 0), right.get("top30_cutoff_mystic", 0), "int"),
    ]

    elite_rows = [
        _swordland_metric_row("Top 5 Total Mystic", left.get("elite_top5_mystic", 0), right.get("elite_top5_mystic", 0), "int"),
        _swordland_metric_row("Top 10 Total Mystic", left.get("elite_top10_mystic", 0), right.get("elite_top10_mystic", 0), "int"),
        _swordland_metric_row("Top 5 Total Power", left.get("elite_top5_power", 0), right.get("elite_top5_power", 0), "power"),
        _swordland_metric_row("Top 10 Total Power", left.get("elite_top10_power", 0), right.get("elite_top10_power", 0), "power"),
        _swordland_metric_row("Top 5 Radiant Spire", left.get("elite_top5_radiant", 0), right.get("elite_top5_radiant", 0), "int"),
    ]

    depth_rows = [
        _swordland_metric_row("Top 20 Total Mystic", left.get("depth_top20_mystic", 0), right.get("depth_top20_mystic", 0), "int"),
        _swordland_metric_row("Top 30 Total Mystic", left.get("depth_top30_mystic", 0), right.get("depth_top30_mystic", 0), "int"),
        _swordland_metric_row("Top 20 Total Power", left.get("depth_top20_power", 0), right.get("depth_top20_power", 0), "power"),
        _swordland_metric_row("Top 30 Total Power", left.get("depth_top30_power", 0), right.get("depth_top30_power", 0), "power"),
    ]

    threshold_values = [2500, 2250, 2000, 1800]
    threshold_rows = [
        _swordland_metric_row(
            f"{threshold}+ Mystic",
            int((left.get("threshold_counts") or {}).get(threshold, 0)),
            int((right.get("threshold_counts") or {}).get(threshold, 0)),
            "int",
        )
        for threshold in threshold_values
    ]

    core_advantages = {
        "power": _as_float(left.get("top30_combined_power", 0)) - _as_float(right.get("top30_combined_power", 0)),
        "mystic": _as_float(left.get("top30_combined_mystic", 0)) - _as_float(right.get("top30_combined_mystic", 0)),
        "elite": _as_float(left.get("elite_top10_mystic", 0)) - _as_float(right.get("elite_top10_mystic", 0)),
    }
    left_core_wins = sum(1 for value in core_advantages.values() if value > 0)
    right_core_wins = sum(1 for value in core_advantages.values() if value < 0)

    left_label = str(left.get("label") or "Left")
    right_label = str(right.get("label") or "Right")

    if left_core_wins > right_core_wins:
        overall_line = f"{left_label} holds the clearer overall edge from Top 5 to Top 30."
    elif right_core_wins > left_core_wins:
        overall_line = f"{right_label} holds the clearer overall edge from Top 5 to Top 30."
    else:
        overall_line = "Both alliances are closely matched across the core Swordland metrics."

    executive_summary = [
        overall_line,
        (
            f"Top 30 power edge: {left_label if core_advantages['power'] > 0 else right_label if core_advantages['power'] < 0 else 'Tie'} "
            f"({ _format_power(abs(core_advantages['power'])) if core_advantages['power'] else '0' })."
        ),
        (
            f"Top 30 mystic edge: {left_label if core_advantages['mystic'] > 0 else right_label if core_advantages['mystic'] < 0 else 'Tie'} "
            f"({ _format_whole_number(abs(core_advantages['mystic'])) if core_advantages['mystic'] else '0' })."
        ),
        (
            f"Rank-by-rank mystic wins (Top 30): {left_label} {mystic_wins['wins_left']} - "
            f"{right_label} {mystic_wins['wins_right']} (ties {mystic_wins['ties']})."
        ),
    ]

    bottom_line = (
        f"Bottom line: {overall_line} "
        f"Depth check shows {left_label} {mystic_wins['wins_left']} vs {right_label} {mystic_wins['wins_right']} "
        "rank-by-rank mystic wins in Top 30."
    )

    return {
        "executive_summary": executive_summary,
        "snapshot_rows": snapshot_rows,
        "elite_rows": elite_rows,
        "depth_rows": depth_rows,
        "threshold_rows": threshold_rows,
        "top_names_left": list(left.get("top_names") or []),
        "top_names_right": list(right.get("top_names") or []),
        "top_radiant_left": list(left.get("top_radiant") or []),
        "top_radiant_right": list(right.get("top_radiant") or []),
        "rank_wins": {
            "mystic": mystic_wins,
            "power": power_wins,
        },
        "bottom_line": bottom_line,
    }


def _load_alliance_member_rows_for_swordland(alliance_id: int) -> list[dict[str, Any]]:
    with _get_db_connection() as connection:
        rows = connection.execute(
            """
            SELECT
                alliance_players.*, alliance_users.username AS discord_username,
                alliance_users.avatar_url AS member_avatar_url
            FROM alliance_players
            JOIN alliance_users ON alliance_users.id = alliance_players.user_id
            WHERE alliance_players.alliance_id = ?
            ORDER BY alliance_players.total_power DESC, alliance_players.id ASC
            """,
            (alliance_id,),
        ).fetchall()
    return [dict(row) for row in rows]


def _swordland_storage_fields(slot: int, event_key: str = "swordland") -> tuple[str, str, str, str]:
    if event_key == "kvk":
        return "kvk_rival_jeabs_id", "kvk_rival_name", "kvk_cache_json", "kvk_cache_updated_at"
    if slot == 2:
        return "swordland2_rival_jeabs_id", "swordland2_rival_name", "swordland2_cache_json", "swordland2_cache_updated_at"
    return "swordland_rival_jeabs_id", "swordland_rival_name", "swordland_cache_json", "swordland_cache_updated_at"


SWORDLAND_PRIMARY_PLAN_TEAMS = ("red", "blue", "green", "yellow")
SWORDLAND_PLAN_TEAMS = (*SWORDLAND_PRIMARY_PLAN_TEAMS, "loot")
SWORDLAND_PLAN_ROLES = ("captain_1", "captain_2", "starter_1", "starter_2", "starter_3", "starter_4", "starter_5", "reserve_1")
KVK_CASTLES = ("castle_1", "castle_2")
KVK_CASTLE_ROLES = ("captain", *(f"player_{index}" for index in range(1, 10)))
KVK_TURRET_ROLES = tuple(f"captain_{index}" for index in range(1, 4))
KVK_HEROES = ("Hilde", "Saul", "Chenko", "Yeonwoo")
KVK_ACTIONS = ("attack_1", "attack_2", "defense")
KVK_TROOPS = ("infantry", "cavalry", "archers")


def _swordland_plan_field(slot: int, event_key: str = "swordland") -> str:
    if event_key == "kvk":
        return "kvk_plan_json"
    return "swordland2_plan_json" if slot == 2 else "swordland_plan_json"


def _build_swordland_plan_context(
    alliance: dict[str, Any], members: list[dict[str, Any]], slot: int, event_key: str = "swordland"
) -> dict[str, Any]:
    ranked_members = _build_swordland_ranked_members(members)
    choices = [
        {
            "game_id": str(member.get("game_id") or "").strip(),
            "name": str(member.get("name") or "Player").strip(),
            "mystic_score": int(member.get("mystic_score") or 0),
        }
        for member in ranked_members
        if str(member.get("game_id") or "").strip()
    ]
    available_ids = {choice["game_id"] for choice in choices}
    default_aggressor = choices[0]["game_id"] if choices else ""
    choices.sort(key=lambda choice: str(choice["name"] or "").casefold())
    raw_plan = alliance.get(_swordland_plan_field(slot, event_key))
    try:
        stored_plan = json.loads(str(raw_plan)) if raw_plan else {}
    except (TypeError, ValueError):
        stored_plan = {}
    if not isinstance(stored_plan, dict):
        stored_plan = {}

    primary_selected: set[str] = set()
    loot_selected: set[str] = set()
    aggressor = str(stored_plan.get("aggressor") or default_aggressor).strip()
    if aggressor not in available_ids:
        aggressor = default_aggressor
    if aggressor:
        primary_selected.add(aggressor)

    teams: dict[str, dict[str, str]] = {}
    stored_teams = stored_plan.get("teams") if isinstance(stored_plan.get("teams"), dict) else {}
    for team in SWORDLAND_PLAN_TEAMS:
        selected = loot_selected if team == "loot" else primary_selected
        team_values = stored_teams.get(team) if isinstance(stored_teams.get(team), dict) else {}
        teams[team] = {}
        reserve_roles = sorted(
            (role for role in team_values if re.fullmatch(r"reserve_\d+", str(role))),
            key=lambda role: int(str(role).split("_", 1)[1]),
        )
        for role in (*SWORDLAND_PLAN_ROLES, *(role for role in reserve_roles if role not in SWORDLAND_PLAN_ROLES)):
            player_id = str(team_values.get(role) or "").strip()
            if player_id not in available_ids or player_id in selected:
                player_id = ""
            if player_id:
                selected.add(player_id)
            teams[team][role] = player_id

    return {"choices": choices, "aggressor": aggressor, "teams": teams}


def _build_kvk_plan_context(alliance: dict[str, Any], members: list[dict[str, Any]]) -> dict[str, Any]:
    ranked_members = _build_swordland_ranked_members(members)
    choices = [
        {
            "game_id": str(member.get("game_id") or "").strip(),
            "name": str(member.get("name") or "Player").strip(),
            "mystic_score": int(member.get("mystic_score") or 0),
        }
        for member in ranked_members
        if str(member.get("game_id") or "").strip()
    ]
    choices.sort(key=lambda choice: str(choice["name"]).casefold())
    available_ids = {choice["game_id"] for choice in choices}
    try:
        stored_plan = json.loads(str(alliance.get("kvk_plan_json"))) if alliance.get("kvk_plan_json") else {}
    except (TypeError, ValueError):
        stored_plan = {}
    if not isinstance(stored_plan, dict):
        stored_plan = {}

    selected_ids: set[str] = set()

    def clean_player_id(raw_value: Any) -> str:
        player_id = str(raw_value or "").strip()
        is_manual = player_id.startswith("manual:") and bool(player_id[7:].strip())
        if (player_id not in available_ids and not is_manual) or player_id.casefold() in selected_ids:
            return ""
        if player_id:
            selected_ids.add(player_id.casefold())
        return player_id

    castles: dict[str, Any] = {}
    stored_castles = stored_plan.get("castles") if isinstance(stored_plan.get("castles"), dict) else {}
    for castle in KVK_CASTLES:
        stored_castle = stored_castles.get(castle) if isinstance(stored_castles.get(castle), dict) else {}
        stored_rows = stored_castle.get("rows") if isinstance(stored_castle.get("rows"), dict) else {}
        rows: dict[str, dict[str, str]] = {}
        for role in KVK_CASTLE_ROLES:
            stored_row = stored_rows.get(role) if isinstance(stored_rows.get(role), dict) else {}
            attack_hero = str(stored_row.get("attack_hero") or "").strip()
            garrison_hero = str(stored_row.get("garrison_hero") or "").strip()
            if role != "captain":
                attack_hero = attack_hero if attack_hero in KVK_HEROES else ""
                garrison_hero = garrison_hero if garrison_hero in KVK_HEROES else ""
            rows[role] = {
                "player_id": clean_player_id(stored_row.get("player_id")),
                "attack_hero": attack_hero,
                "garrison_hero": garrison_hero,
                "troops": {
                    action: {
                        troop: max(0, _parse_loose_int(
                            ((stored_row.get("troops") or {}).get(action) or {}).get(troop), 0
                        ))
                        for troop in KVK_TROOPS
                    }
                    for action in KVK_ACTIONS
                },
            }
        castles[castle] = {
            "attack_1_formation": str(stored_castle.get("attack_1_formation") or stored_castle.get("attack_formation") or "50/20/30").strip(),
            "attack_2_formation": str(stored_castle.get("attack_2_formation") or "50/0/50").strip(),
            "defense_formation": str(stored_castle.get("defense_formation") or "60/40/0").strip(),
            "rows": rows,
        }

    stored_turrets = stored_plan.get("turrets") if isinstance(stored_plan.get("turrets"), dict) else {}
    stored_captains = stored_turrets.get("captains") if isinstance(stored_turrets.get("captains"), dict) else {}
    turrets = {
        "attack_formation": str(stored_turrets.get("attack_formation") or "50/10/40").strip(),
        "defense_formation": str(stored_turrets.get("defense_formation") or "60/40").strip(),
        "captains": {role: clean_player_id(stored_captains.get(role)) for role in KVK_TURRET_ROLES},
    }
    return {"choices": choices, "heroes": KVK_HEROES, "castles": castles, "turrets": turrets}


def _build_kvk_plan_infographic_prompt(plan: dict[str, Any], alliance_name: str = "Alliance") -> str:
    title = str(alliance_name or "Alliance").strip() or "Alliance"
    choices = {
        str(player.get("game_id") or ""): str(player.get("name") or "Player")
        for player in plan.get("choices") or []
    }

    def player_name(player_id: Any) -> str:
        value = str(player_id or "").strip()
        if value.startswith("manual:"):
            return value[7:].strip() or "Unassigned"
        return choices.get(value, "Unassigned")

    lines = [
        f"Create one polished 1920x1440 horizontal Kingshot KVK Castle Battle Plan infographic in English. Render this exact title prominently at the top: {title} KVK Castle Battle Plan.",
        "Art direction: premium Kingshot medieval war-room aesthetic, matching a high-quality in-game event infographic. Use a detailed but restrained fortress interior or kingdom battlefield background, stone and dark forged-metal framing, crimson military banners, antique gold trim, subtle firelight, and small heraldic ornaments. Keep the tables on solid high-contrast parchment or dark tactical panels so every value remains crisp. Do not use a plain corporate spreadsheet look, neon colors, sci-fi elements, modern office styling, or excessive decoration.",
        "Composition: stack the R3 and R2 groups vertically as two wide operational roster blocks. Keep all content inside the canvas with balanced margins; the roster data must occupy most of the image.",
        "For each Castle, create one wide table with grouped headers in this exact order: Role; Player; ATTACK 1 with Hero, Infantry, Cavalry, Archers; ATTACK 2 with Hero, Infantry, Cavalry, Archers; DEFENSE with Hero, Infantry, Cavalry, Archers. The same supplied Attack Hero applies to both Attack 1 and Attack 2. Visually emphasize the Captain row, then list Player 1 through Player 9 in order.",
        "Place each formation directly in its grouped header: Attack 1 Formation, Attack 2 Formation, and Defense Formation. Use crossed-sword accents for both attack groups and a shield accent for defense, while preserving strong visual separators between the three action groups.",
        "Use the supplied player names, hero names, formations, and troop quantities exactly as written. Troop quantities are ordered Infantry/Cavalry/Archers and must be printed as separate labeled values, never merged into one ambiguous number. Display zero as '-' and empty assignments as 'Unassigned'.",
        "Do not add portraits, avatars, logos, extra players, extra heroes, scores, tactical claims, or invented assignments. Never omit or summarize any roster row or troop quantity.",
    ]

    castles = plan.get("castles") if isinstance(plan.get("castles"), dict) else {}
    for castle_key, group_label in (("castle_1", "R3"), ("castle_2", "R2")):
        castle = castles.get(castle_key) if isinstance(castles.get(castle_key), dict) else {}
        rows = castle.get("rows") if isinstance(castle.get("rows"), dict) else {}
        captain_row = rows.get("captain") if isinstance(rows.get("captain"), dict) else {}
        castle_label = f"{player_name(captain_row.get('player_id'))} {group_label}"
        lines.extend(
            [
                "",
                f"{castle_label}",
                f"Attack 1 Formation: {castle.get('attack_1_formation') or '50/20/30'}",
                f"Attack 2 Formation: {castle.get('attack_2_formation') or '50/0/50'}",
                f"Defense Formation: {castle.get('defense_formation') or '60/40/0'}",
                "Rows (troops are Infantry/Cavalry/Archers):",
            ]
        )
        for role in KVK_CASTLE_ROLES:
            row = rows.get(role) if isinstance(rows.get(role), dict) else {}
            role_label = str(KVK_CASTLE_ROLES.index(role) + 1)
            assigned_player_name = player_name(row.get("player_id"))
            attack_hero = str(row.get("attack_hero") or "Unassigned")
            garrison_hero = str(row.get("garrison_hero") or "Unassigned")
            troops = row.get("troops") if isinstance(row.get("troops"), dict) else {}
            troop_text = " | ".join(
                f"{action.replace('_', ' ').title()}: "
                + ", ".join(
                    f"{troop.title()} {int(((troops.get(action) or {}).get(troop) or 0))}"
                    for troop in KVK_TROOPS
                )
                for action in KVK_ACTIONS
            )
            lines.append(
                f"- {role_label} | Player: {assigned_player_name} | Attack 1 Hero: {attack_hero} | "
                f"Attack 2 Hero: {attack_hero} | Defense Hero: {garrison_hero} | {troop_text}"
            )

    turrets = plan.get("turrets") if isinstance(plan.get("turrets"), dict) else {}
    captains = turrets.get("captains") if isinstance(turrets.get("captains"), dict) else {}
    lines.extend(
        [
            "",
            "TURRETS RALLY",
            f"Attack Formation: {turrets.get('attack_formation') or '50/10/40'}",
            f"Defense Formation: {turrets.get('defense_formation') or '60/40'}",
            "Show this as one concise table with columns Rally and Captain:",
        ]
    )
    for index, role in enumerate(KVK_TURRET_ROLES, start=1):
        captain_name = player_name(captains.get(role))
        lines.append(f"- Rally {index} | Captain: {captain_name}")

    lines.extend(
        [
            "",
            "Final quality requirements: use crisp grid lines, consistent row heights, large readable names and numbers, and unmistakable separation between Attack 1, Attack 2, and Defense. The medieval Kingshot artwork must frame and support the operational data, never sit behind text or reduce legibility. Ensure every supplied assignment and every troop value is visible at normal viewing size.",
        ]
    )
    return "\n".join(lines)


def _build_swordland_plan_infographic_prompt(plan: dict[str, Any]) -> str:
    choices = {str(player.get("game_id") or ""): str(player.get("name") or "Player") for player in plan.get("choices") or []}
    aggressor = choices.get(str(plan.get("aggressor") or ""), "Unassigned")
    team_lines: list[str] = []
    for team in SWORDLAND_PLAN_TEAMS:
        assignments = (plan.get("teams") or {}).get(team) or {}
        captains = [choices.get(str(assignments.get(role) or ""), "Unassigned") for role in ("captain_1", "captain_2")]
        starters = [choices.get(str(assignments.get(f"starter_{index}") or ""), "Unassigned") for index in range(1, 6)]
        reserve_roles = sorted(
            (role for role in assignments if re.fullmatch(r"reserve_\d+", str(role))),
            key=lambda role: int(str(role).split("_", 1)[1]),
        )
        reserves = [choices.get(str(assignments.get(role) or ""), "Unassigned") for role in reserve_roles] or ["Unassigned"]
        team_lines.append(f"- {team.title()} Team: Captains {', '.join(captains)} | Starters {', '.join(starters)} | Reserves {', '.join(reserves)}.")

    lines = [
        "Create one single 1440x1080 horizontal Kingshot Swordland master event plan infographic covering all three phases.",
        "The attached Swordland Phases Map is the sole sacred map reference. It already consolidates all three phases. Use it as one full, unmodified master map panel, preserving every team color code, numbered marker, building label, position, icon, and phase distinction exactly. Do not crop, redraw, recolor, blur, replace, simplify, or cover the map.",
        "Composition: keep the full master map clearly visible on the left. Use the full right side for the operational plan. Do not use player portraits or avatars, including no Ahab avatar. Do not repeat team rosters for every phase.",
        "Place a compact phase timeline across the top right: Phase I Opening Control (0-15 min), Phase II Expansion & Pressure (15-45 min), Phase III Endgame (45-60 min), each with only its unique objective and instruction. Use the complete remaining space efficiently; do not leave decorative empty panels or duplicate information.",
        "Below the timeline, place a prominent Solo Aggressor callout and one large five-column roster with red, blue, green, yellow, and white Loot Team codes. Show captains, starters, and every reserve only once within each roster column.",
        f"Solo Aggressor: {aggressor}.",
        "Unified team roster for the entire event:",
        *team_lines,
        "Phase I unique instruction: secure first control and opening occupation while Solo Aggressor operates independently.",
        "Phase II unique instruction: expand pressure, coordinate rallies, and move to high-value positions.",
        "Phase III unique instruction: hold valuable buildings, reinforce allied leaders, and follow endgame calls.",
        "The white Loot Team is a supplemental loot-collection squad assembled from members of the four primary teams. A player name may therefore appear once in a primary team and again in Loot Team; preserve these intentional overlaps exactly.",
        "Use compact panels for information not repeated between phases: event overview and key objectives, Target 1/Target 2 responsibility notes, reserve-team readiness, mutual team support, teleport discipline, loot collection, and concise general instructions.",
        "Use distinct red, blue, green, yellow, and white team pills and roster columns matching the unmodified map codes. Label the white column exactly 'Loot Team'. Team assignment names and roles must be large and legible without obscuring the map. Do not invent players, avatars, roles, objectives, scores, or tactical claims beyond this brief.",
    ]
    return "\n".join(lines)


def _build_swordland_live_snapshot(
    alliance: dict[str, Any],
    members: list[dict[str, Any]],
    slot: int = 1,
    progress_callback: Any = None,
    event_key: str = "swordland",
) -> dict[str, Any]:
    rival_id_field, rival_name_field, _, _ = _swordland_storage_fields(slot, event_key)
    left_side = _build_swordland_side_summary(members, str(alliance.get("name") or "Our alliance"), "Our alliance")
    rival_id = str(alliance.get(rival_id_field) or "").strip()
    rival_name = str(alliance.get(rival_name_field) or "").strip()
    alliance_kingdom_id = str(alliance.get("kingdom") or "").strip()

    rival_side: dict[str, Any] | None = None
    rival_message = "Configure the rival JeabsPlus alliance ID to generate the VS view."

    if rival_id:
        token = _get_jeabs_token(alliance)
        if token:
            try:
                if event_key == "kvk":
                    own_members_raw = _fetch_jeabs_server_members(
                        _parse_nap4_entries(alliance.get("nap4_config_json"), alliance),
                        alliance_kingdom_id,
                        token,
                        progress_callback=progress_callback,
                    )
                    rival_members_raw = _fetch_jeabs_server_members(
                        _parse_kvk_server_entries(rival_id),
                        "",
                        token,
                        progress_callback=progress_callback,
                    )
                    own_members = [
                        normalized
                        for normalized in (_normalize_jeabs_dashboard_member(member) for member in own_members_raw)
                        if normalized is not None
                    ]
                    rival_members = [
                        normalized
                        for normalized in (_normalize_jeabs_dashboard_member(member) for member in rival_members_raw)
                        if normalized is not None
                    ]
                    left_side = _build_swordland_side_summary(
                        own_members,
                        f"Kingdom {alliance_kingdom_id}" if alliance_kingdom_id else "Our server",
                        "NAP4 server",
                    )
                    rival_side = _build_swordland_side_summary(
                        rival_members,
                        rival_name or "Rival server",
                        "JeabsPlus rival server",
                    )
                    rival_message = ""
                    return {
                        "left_side": left_side,
                        "right_side": rival_side,
                        "comparison_rows": _build_swordland_comparison_rows(left_side, rival_side),
                        "report": _build_swordland_report(left_side, rival_side),
                        "rival_id": rival_id,
                        "rival_name": rival_name,
                        "rival_message": rival_message,
                    }
                fetch_input = rival_id
                if alliance_kingdom_id and not rival_id.startswith(("http://", "https://")):
                    fetch_input = f"https://jeabslist.com/alliances/{alliance_kingdom_id}/{rival_id}"
                rival_members_raw = _fetch_jeabs_members(fetch_input, token)
                rival_members, _detail_stats = _enrich_jeabs_members_with_player_details(
                    rival_members_raw,
                    token,
                    progress_callback=progress_callback,
                )
                rival_kingdom_id = next(
                    (
                        str(
                            member.get("kingdom_id")
                            or member.get("kingdomId")
                            or member.get("kid")
                            or member.get("kingdom")
                            or ""
                        ).strip()
                        for member in rival_members
                        if isinstance(member, dict)
                        and str(
                            member.get("kingdom_id")
                            or member.get("kingdomId")
                            or member.get("kid")
                            or member.get("kingdom")
                            or ""
                        ).strip()
                    ),
                    alliance_kingdom_id,
                )
                try:
                    rival_radiant_scores = _fetch_jeabs_radiant_leaderboard(rival_kingdom_id, token)
                except (ValueError, requests.RequestException):
                    rival_radiant_scores = {}
                if rival_radiant_scores:
                    rival_members = [
                        {
                            **member,
                            **(
                                {"radiant_spire": rival_radiant_scores[player_id]}
                                if (player_id := str(
                                    member.get("governor_id")
                                    or member.get("governorId")
                                    or member.get("player_id")
                                    or member.get("playerId")
                                    or member.get("id")
                                    or ""
                                ).strip()) in rival_radiant_scores
                                else {}
                            ),
                        }
                        for member in rival_members
                        if isinstance(member, dict)
                    ]
                normalized_rival_members = [
                    normalized_member
                    for normalized_member in (
                        _normalize_jeabs_dashboard_member(member)
                        for member in rival_members
                        if isinstance(member, dict)
                    )
                    if normalized_member is not None
                ]
                rival_side = _build_swordland_side_summary(
                    normalized_rival_members,
                    rival_name or rival_id,
                    "JeabsPlus rival",
                )
                rival_message = ""
            except Exception as exc:
                rival_message = str(exc)
        else:
            rival_message = "A JeabsPlus API token is not configured for this alliance."

    rows = []
    report = None
    if rival_side:
        rows = _build_swordland_comparison_rows(left_side, rival_side)
        report = _build_swordland_report(left_side, rival_side)

    return {
        "left_side": left_side,
        "right_side": rival_side,
        "comparison_rows": rows,
        "report": report,
        "rival_id": rival_id,
        "rival_name": rival_name,
        "rival_message": rival_message,
    }


def _run_swordland_sync_job(job_id: str, alliance_id: int, slot: int, event_key: str = "swordland") -> None:
    event_name = "KVK" if event_key == "kvk" else "Swordland"
    try:
        with _get_db_connection() as connection:
            alliance_row = connection.execute("SELECT * FROM alliances WHERE id = ?", (alliance_id,)).fetchone()
        if not alliance_row:
            raise ValueError("Alliance not found.")
        alliance = dict(alliance_row)
        members = _load_alliance_member_rows_for_swordland(alliance_id)
        _update_jeabs_sync_job(job_id, state="running", stage="Fetching rival roster", completed=0, total=0, percent=0)

        def _progress(completed: int, total: int) -> None:
            percent = min(99, max(1, int((completed * 100) / max(1, total))))
            _update_jeabs_sync_job(
                job_id,
                stage="Updating rival players",
                completed=completed,
                total=total,
                percent=percent,
            )

        snapshot = _build_swordland_live_snapshot(alliance, members, slot, progress_callback=_progress, event_key=event_key)
        if not snapshot.get("right_side"):
            raise ValueError(str(snapshot.get("rival_message") or f"Could not synchronize the {event_name} rival."))
        with JEABS_SYNC_JOBS_LOCK:
            current_job = dict(JEABS_SYNC_JOBS.get(job_id) or {})
        total = int(current_job.get("total") or 0)
        _update_jeabs_sync_job(job_id, stage=f"Saving {event_name} comparison", completed=total, total=total, percent=99)
        _, _, cache_field, cache_updated_field = _swordland_storage_fields(slot, event_key)
        now = datetime.now(timezone.utc).isoformat()
        payload = {
            "left_side": snapshot.get("left_side"),
            "right_side": snapshot.get("right_side"),
            "comparison_rows": snapshot.get("comparison_rows") or [],
            "report": snapshot.get("report"),
            "rival_message": snapshot.get("rival_message") or "",
            "cached_at": now,
        }
        with _get_db_connection() as connection:
            connection.execute(
                f"UPDATE alliances SET {cache_field} = ?, {cache_updated_field} = ?, updated_at = ? WHERE id = ?",
                (json.dumps(payload), now, now, alliance_id),
            )
        _update_jeabs_sync_job(
            job_id,
            state="complete",
            stage=f"{event_name} synchronization complete",
            completed=total,
            total=total,
            percent=100,
            message=f"{event_name} cache refreshed successfully.",
        )
    except Exception as exc:
        _update_jeabs_sync_job(
            job_id,
            state="error",
            stage=f"{event_name} synchronization failed",
            message=str(exc).strip() or f"{event_name} synchronization failed.",
        )


def _create_swordland_sync_job(
    alliance_id: int, slot: int, event_key: str = "swordland"
) -> tuple[dict[str, Any] | None, str | None]:
    event_name = "KVK" if event_key == "kvk" else "Swordland"
    now = time.time()
    with JEABS_SYNC_JOBS_LOCK:
        for job in JEABS_SYNC_JOBS.values():
            if int(job.get("alliance_id") or 0) == alliance_id and job.get("state") in {"pending", "running"}:
                return None, "A synchronization is already running for this alliance."
        job_id = secrets.token_urlsafe(18)
        job = {
            "job_id": job_id,
            "alliance_id": alliance_id,
            "job_type": event_key,
            "slot": slot,
            "state": "pending",
            "stage": f"Starting {event_name} synchronization",
            "completed": 0,
            "total": 0,
            "percent": 0,
            "message": "",
            "created_at": now,
            "updated_at": now,
        }
        JEABS_SYNC_JOBS[job_id] = job
    threading.Thread(
        target=_run_swordland_sync_job,
        args=(job_id, alliance_id, slot, event_key),
        daemon=True,
        name=f"{event_key}-sync-{alliance_id}-{slot}",
    ).start()
    return dict(job), None


def _build_swordland_infographic_prompt(context: dict[str, Any]) -> str:
    left, right, report = context.get("left_side") or {}, context.get("right_side") or {}, context.get("report") or {}
    if not left or not right or not report:
        return ""
    lines = [
        "Create a polished competitive gaming infographic in English for a Kingshot Swordland alliance comparison.",
        f"Title: {left.get('label')} VS {right.get('label')}.",
        "Use a strong horizontal versus composition and no invented statistics.",
        "If an alliance logo is attached, use it only as visual inspiration: derive the color palette, textures, typography mood, and graphic accents from it without altering or recreating the logo.",
        "Executive insights:",
    ]
    lines.extend(f"- {line}" for line in report.get("executive_summary") or [])
    for section, rows in (("Top 30 snapshot", report.get("snapshot_rows") or []), ("Elite Mystic comparison", report.get("elite_rows") or []), ("Mystic threshold distribution", report.get("threshold_rows") or [])):
        rows = [row for row in rows if "power" not in str(row.get("label") or "").lower()]
        lines.append(f"{section}:")
        lines.extend(f"- {row.get('label')}: {left.get('label')} {row.get('left')} | {right.get('label')} {row.get('right')} | difference {row.get('delta')}" for row in rows)
    lines.append(f"Top Names - {left.get('label')} (make this a prominent ranked roster panel):")
    lines.extend(
        f"- #{index}: {member.get('name')} | Mystic {member.get('mystic_score')}"
        for index, member in enumerate(report.get("top_names_left") or [], start=1)
    )
    lines.append(f"Top Names - {right.get('label')} (make this a prominent ranked roster panel):")
    lines.extend(
        f"- #{index}: {member.get('name')} | Mystic {member.get('mystic_score')}"
        for index, member in enumerate(report.get("top_names_right") or [], start=1)
    )
    lines.extend([f"Conclusion: {report.get('bottom_line', '')}", "Design for a shareable 1440x1080 horizontal social-media graphic. Keep every number legible and do not add logos or claims not provided above."])
    return "\n".join(lines)


def _build_swordland_context(
    alliance: dict[str, Any],
    members: list[dict[str, Any]],
    active_tab: str = "player-list",
    slot: int = 1,
    event_key: str = "swordland",
) -> dict[str, Any]:
    event_name = "KVK" if event_key == "kvk" else "Swordland"
    rival_id_field, rival_name_field, cache_field, cache_updated_field = _swordland_storage_fields(slot, event_key)
    rival_id = str(alliance.get(rival_id_field) or "").strip()
    rival_name = str(alliance.get(rival_name_field) or "").strip()

    context: dict[str, Any] = {
        "left_side": None,
        "right_side": None,
        "comparison_rows": [],
        "report": None,
        "rival_id": rival_id,
        "rival_entries": _parse_kvk_server_entries(rival_id) if event_key == "kvk" else [],
        "rival_name": rival_name,
        "rival_message": "",
        "has_cache": False,
        "last_synced_at": "",
        "slot": slot,
        "infographic_prompt": "",
        "plan": _build_kvk_plan_context(alliance, members) if event_key == "kvk" else _build_swordland_plan_context(alliance, members, slot),
        "plan_infographic_prompt": "",
    }

    if active_tab != event_key:
        return context

    if event_key == "kvk":
        context["plan_infographic_prompt"] = _build_kvk_plan_infographic_prompt(
            context["plan"], str(alliance.get("name") or "Alliance")
        )
    else:
        context["plan_infographic_prompt"] = _build_swordland_plan_infographic_prompt(context["plan"])

    cache_payload_raw = alliance.get(cache_field)
    cache_payload: dict[str, Any] = {}
    if isinstance(cache_payload_raw, dict):
        cache_payload = cache_payload_raw
    elif cache_payload_raw:
        try:
            parsed = json.loads(str(cache_payload_raw))
            if isinstance(parsed, dict):
                cache_payload = parsed
        except (TypeError, ValueError):
            cache_payload = {}

    cache_ts = str(alliance.get(cache_updated_field) or cache_payload.get("cached_at") or "").strip()
    has_cache = bool(cache_payload)
    context["has_cache"] = has_cache
    context["last_synced_at"] = cache_ts

    if has_cache:
        context["left_side"] = cache_payload.get("left_side")
        context["right_side"] = cache_payload.get("right_side")
        context["comparison_rows"] = _reformat_cached_comparison_rows(cache_payload.get("comparison_rows") or [])
        report = cache_payload.get("report")
        if isinstance(report, dict):
            report = dict(report)
            for rows_key in ("snapshot_rows", "elite_rows", "depth_rows", "threshold_rows"):
                if isinstance(report.get(rows_key), list):
                    report[rows_key] = _reformat_cached_comparison_rows(report[rows_key])
        context["report"] = report
        context["infographic_prompt"] = _build_swordland_infographic_prompt(context).replace("Swordland", event_name)
        cached_message = str(cache_payload.get("rival_message") or "").strip()
        if cached_message:
            context["rival_message"] = cached_message
        elif cache_ts:
            context["rival_message"] = f"Showing cached {event_name} data from {cache_ts}. Click Refresh {event_name} Data to sync latest values."
        else:
            context["rival_message"] = f"Showing cached {event_name} data. Click Refresh {event_name} Data to sync latest values."
        return context

    if not rival_id:
        context["rival_message"] = (
            "Configure at least one rival alliance JeabsPlus ID, then click Refresh KVK Data to compare both servers."
            if event_key == "kvk"
            else f"Configure the rival JeabsPlus alliance ID, then click Refresh {event_name} Data to generate the VS view."
        )
    else:
        context["rival_message"] = f"No cached {event_name} data yet. Click Refresh {event_name} Data to synchronize from JeabsPlus."
    return context


def _parse_utc_time(raw: Any) -> datetime | None:
    value = str(raw or "").strip()
    if not value:
        return None

    parsed_time: time | None = None
    for fmt in ("%H:%M", "%H:%M:%S"):
        try:
            parsed_time = datetime.strptime(value, fmt).time()
            break
        except ValueError:
            continue

    if parsed_time is None:
        return None

    today_utc = datetime.now(timezone.utc).date()
    return datetime.combine(today_utc, parsed_time, tzinfo=timezone.utc)


def _parse_duration_seconds(raw: Any) -> int | None:
    text = str(raw or "").strip()
    if not text:
        return None

    if text.isdigit():
        seconds = int(text)
        if seconds <= 0 or seconds > COORDINATED_ATTACK_MAX_MARCH_SECONDS:
            return None
        return seconds

    parts = text.split(":")
    if len(parts) != 2:
        return None
    if not all(part.isdigit() for part in parts):
        return None

    values = [int(part) for part in parts]
    minutes, seconds = values
    if minutes < 0 or seconds < 0 or seconds > 59:
        return None
    total_seconds = (minutes * 60) + seconds
    if total_seconds <= 0 or total_seconds > COORDINATED_ATTACK_MAX_MARCH_SECONDS:
        return None
    return total_seconds


def _format_utc_with_offset(value: datetime, anchor: datetime, *, include_seconds: bool = False) -> str:
    day_diff = (value.date() - anchor.date()).days
    suffix = ""
    if day_diff > 0:
        suffix = f" (+{day_diff}d)"
    elif day_diff < 0:
        suffix = f" ({day_diff}d)"
    time_format = "%H:%M:%S" if include_seconds else "%H:%M"
    return f"{value.strftime(time_format)} UTC{suffix}"


def _format_send_message_time(value: datetime, anchor: datetime) -> str:
    return _format_utc_with_offset(value, anchor, include_seconds=True)


def _split_coordinated_attack_message(lines: list[str], max_chars: int) -> list[str]:
    chunks: list[str] = []
    current_lines: list[str] = []

    for raw_line in lines:
        line = str(raw_line)
        candidate = "\n".join(current_lines + [line]) if current_lines else line
        if len(candidate) <= max_chars:
            current_lines.append(line)
            continue

        if current_lines:
            chunks.append("\n".join(current_lines))
            current_lines = []

        if len(line) <= max_chars:
            current_lines = [line]
            continue

        # Fallback for unexpectedly long single lines.
        pending = line
        while len(pending) > max_chars:
            split_at = pending.rfind(" ", 0, max_chars + 1)
            if split_at <= 0:
                split_at = max_chars
            piece = pending[:split_at].rstrip()
            if piece:
                chunks.append(piece)
            pending = pending[split_at:].lstrip()
        if pending:
            current_lines = [pending]

    if current_lines:
        chunks.append("\n".join(current_lines))

    return chunks or [""]


def _split_line_by_limit(text: str, max_chars: int) -> list[str]:
    line = str(text or "").strip()
    if not line:
        return [""]
    if len(line) <= max_chars:
        return [line]

    pieces: list[str] = []
    pending = line
    while len(pending) > max_chars:
        split_at = pending.rfind(" ", 0, max_chars + 1)
        if split_at <= 0:
            split_at = max_chars
        piece = pending[:split_at].rstrip()
        if piece:
            pieces.append(piece)
        pending = pending[split_at:].lstrip()
    if pending:
        pieces.append(pending)
    return pieces or [""]


def _truncate_with_ellipsis(text: str, max_chars: int) -> str:
    value = str(text or "").strip()
    if max_chars <= 0:
        return ""
    if len(value) <= max_chars:
        return value
    if max_chars <= 3:
        return value[:max_chars]
    return f"{value[:max_chars - 3].rstrip()}..."


def _split_coordinated_attack_entries(entries: list[dict[str, Any]], max_chars: int) -> list[str]:
    chunks: list[str] = []
    current_lines: list[str] = []
    current_length = 0

    def flush_current() -> None:
        nonlocal current_lines, current_length
        if current_lines:
            chunks.append("\n".join(current_lines))
        current_lines = []
        current_length = 0

    def can_add(line: str) -> bool:
        extra = len(line) + (1 if current_lines else 0)
        return (current_length + extra) <= max_chars

    def add_line(line: str) -> None:
        nonlocal current_length
        extra = len(line) + (1 if current_lines else 0)
        current_length += extra
        current_lines.append(line)

    for entry in entries:
        line = str(entry.get("line", "")).strip()
        section_header = str(entry.get("section_header", "")).strip()
        is_section_header = bool(entry.get("is_section_header", False))

        pieces = _split_line_by_limit(line, max_chars)
        for piece in pieces:
            while True:
                if not current_lines and section_header and not is_section_header:
                    if can_add(section_header):
                        add_line(section_header)
                    else:
                        flush_current()
                        continue

                if can_add(piece):
                    add_line(piece)
                    break

                flush_current()

    flush_current()
    return chunks or [""]


def _build_labeled_message_parts(entries: list[dict[str, Any]], title: str, max_chars: int) -> list[str]:
    base_parts = _split_coordinated_attack_entries(entries, max_chars)
    if len(base_parts) <= 1:
        return base_parts

    adjusted_parts = list(base_parts)
    for _ in range(6):
        total = len(adjusted_parts)
        label_len = len(f"{title} ({total}/{total})\n")
        effective_limit = max_chars - label_len
        if effective_limit <= 0:
            break
        recalculated = _split_coordinated_attack_entries(entries, effective_limit)
        if recalculated == adjusted_parts:
            break
        adjusted_parts = recalculated

    total = len(adjusted_parts)
    labeled_parts: list[str] = []
    for index, part in enumerate(adjusted_parts, start=1):
        header = f"{title} ({index}/{total})"
        part_text = str(part).strip()
        if index == 1 and part_text:
            part_lines = part_text.split("\n")
            if part_lines and part_lines[0].strip() == title:
                part_text = "\n".join(part_lines[1:]).strip()
        if part_text:
            labeled_parts.append(f"{header}\n{part_text}")
        else:
            labeled_parts.append(header)

    return labeled_parts


def _parse_ratio_block(raw: Any) -> tuple[bool, str, dict[str, int]]:
    if not isinstance(raw, dict):
        return False, "Invalid ratio format.", {}

    ratio: dict[str, int] = {}
    for key in ("infantry", "cavalry", "archers"):
        try:
            value = int(raw.get(key, 0))
        except (TypeError, ValueError):
            return False, f"Invalid value in ratio ({key}).", {}
        if value < 0 or value > 100:
            return False, f"Ratio value out of range ({key}).", {}
        ratio[key] = value

    if sum(ratio.values()) != 100:
        return False, "Ratio must add up to 100%.", {}

    return True, "", ratio


def _validate_coordinated_attack_payload(payload: dict[str, Any]) -> tuple[bool, str, dict[str, Any]]:
    if not isinstance(payload, dict):
        return False, "Invalid payload.", {}

    target_raw = str(payload.get("target", "")).strip().upper()
    target = COORDINATED_ATTACK_TARGET_ALIASES.get(target_raw, target_raw)
    if target not in COORDINATED_ATTACK_TARGETS:
        return False, "Invalid target.", {}

    coordinated_dt = _parse_utc_time(payload.get("coordinated_time_utc"))
    if coordinated_dt is None:
        return False, "Invalid UTC time. Use HH:MM or HH:MM:SS.", {}

    # Time mode is fixed: target time is always the synchronized impact time.
    time_mode = "start"

    try:
        rally_minutes = int(payload.get("rally_minutes", 0))
    except (TypeError, ValueError):
        return False, "Invalid rally value.", {}

    if rally_minutes not in COORDINATED_ATTACK_RALLY_MINUTES:
        return False, "Invalid rally value. Options: 1, 2 or 5.", {}

    raw_players = payload.get("players", [])
    if not isinstance(raw_players, list):
        return False, "Invalid players list.", {}
    if len(raw_players) < 2:
        return False, "You must provide at least 2 players.", {}
    if len(raw_players) > 10:
        return False, "Maximum supported players is 10.", {}

    players: list[dict[str, Any]] = []
    for idx, raw_player in enumerate(raw_players, start=1):
        if not isinstance(raw_player, dict):
            return False, f"Invalid player entry at row {idx}.", {}

        nick = str(raw_player.get("nick", "")).strip()
        if not nick:
            return False, f"Missing nick for Player {idx}.", {}
        if len(nick) > COORDINATED_ATTACK_MAX_NICK_LENGTH:
            return False, f"Nick too long for Player {idx}. Maximum: {COORDINATED_ATTACK_MAX_NICK_LENGTH} chars.", {}

        march_time_raw = raw_player.get("march_time")
        march_seconds = _parse_duration_seconds(march_time_raw)
        if march_seconds is None:
            return False, f"Invalid march time for Player {idx}. Use seconds or MM:SS (max 9:59).", {}

        players.append(
            {
                "position": idx,
                "nick": nick,
                "march_time": str(march_time_raw).strip(),
                "march_seconds": march_seconds,
            }
        )

    ok_attack, err_attack, attack_ratio = _parse_ratio_block(payload.get("attack_ratio", {}))
    if not ok_attack:
        return False, f"Invalid attack ratio: {err_attack}", {}

    ok_defense, err_defense, defense_ratio = _parse_ratio_block(payload.get("defense_ratio", {}))
    if not ok_defense:
        return False, f"Invalid defense ratio: {err_defense}", {}

    attack_line = str(payload.get("attack_line", "")).strip()
    defense_line = str(payload.get("defense_line", "")).strip()
    complementary_custom_message = str(payload.get("complementary_custom_message", "")).strip()

    if not attack_line:
        legacy_attack = [str(item).strip() for item in (payload.get("attack_heroes") or []) if str(item).strip()]
        attack_line = ", ".join(legacy_attack)
    if not defense_line:
        legacy_defense = [str(item).strip() for item in (payload.get("defense_heroes") or []) if str(item).strip()]
        defense_line = ", ".join(legacy_defense)

    if not attack_line:
        attack_line = "Chenko, Yeonwoo, Amadeus, Amane, Margot"
    if not defense_line:
        defense_line = "Hilde, Saul"

    if len(attack_line) > COORDINATED_ATTACK_HERO_LINE_MAX_CHARS:
        return False, f"First Hero for Attack is too long. Maximum: {COORDINATED_ATTACK_HERO_LINE_MAX_CHARS} chars.", {}
    if len(defense_line) > COORDINATED_ATTACK_HERO_LINE_MAX_CHARS:
        return False, f"First Hero for Defense is too long. Maximum: {COORDINATED_ATTACK_HERO_LINE_MAX_CHARS} chars.", {}
    if len(complementary_custom_message) > COORDINATED_ATTACK_COMPLEMENTARY_MAX_CHARS:
        return False, f"Complementary Custom Message is too long. Maximum: {COORDINATED_ATTACK_COMPLEMENTARY_MAX_CHARS} chars.", {}

    normalized = {
        "target": target,
        "time_mode": time_mode,
        "coordinated_time_utc": coordinated_dt.strftime("%H:%M:%S"),
        "coordinated_dt": coordinated_dt,
        "rally_minutes": rally_minutes,
        "players": players,
        "attack_ratio": attack_ratio,
        "defense_ratio": defense_ratio,
        "attack_line": attack_line,
        "defense_line": defense_line,
        "complementary_custom_message": complementary_custom_message,
    }
    return True, "", normalized


def _build_coordinated_attack_result(data: dict[str, Any]) -> dict[str, Any]:
    coordinated_dt: datetime = data["coordinated_dt"]
    rally_minutes = int(data["rally_minutes"])
    time_mode = "start"
    rally_seconds = rally_minutes * 60
    impact_dt = coordinated_dt
    now_utc = datetime.now(timezone.utc)
    timeline_header = "START TIMES UTC"

    schedule: list[dict[str, Any]] = []
    for player in data["players"]:
        march_seconds = int(player["march_seconds"])
        # Fixed flow:
        # target time = synchronized hit time
        # rally start = hit - march - rally
        depart_dt = impact_dt - timedelta(seconds=march_seconds)
        rally_start_dt = depart_dt - timedelta(seconds=rally_seconds)
        arrival_dt = impact_dt
        timeline_dt = rally_start_dt

        if rally_start_dt <= now_utc:
            raise ValueError(
                f"Impossible schedule in UTC: {player['nick']} should start rally at {rally_start_dt.strftime('%H:%M:%S')} UTC, "
                f"but current UTC is {now_utc.strftime('%H:%M:%S')}."
            )

        schedule.append(
            {
                "position": int(player["position"]),
                "nick": str(player["nick"]),
                "march_time": str(player["march_time"]),
                "arrival_utc": _format_utc_with_offset(arrival_dt, coordinated_dt),
                "send_utc": _format_utc_with_offset(rally_start_dt, coordinated_dt, include_seconds=True),
                "send_message": _format_send_message_time(timeline_dt, coordinated_dt),
            }
        )

    # Keep the user-defined weak -> strong order from the form.
    operation_order = sorted(schedule, key=lambda item: int(item["position"]))

    attack_ratio = data["attack_ratio"]
    defense_ratio = data["defense_ratio"]
    attack_ratio_text = f"{attack_ratio['infantry']}/{attack_ratio['cavalry']}/{attack_ratio['archers']}"
    defense_ratio_text = f"{defense_ratio['infantry']}/{defense_ratio['cavalry']}/{defense_ratio['archers']}"

    attack_line = _truncate_with_ellipsis(
        str(data.get("attack_line", "")).strip() or "Chenko, Yeonwoo, Amadeus, Amane, Margot",
        COORDINATED_ATTACK_HERO_LINE_MAX_CHARS,
    )
    defense_line = _truncate_with_ellipsis(
        str(data.get("defense_line", "")).strip() or "Hilde, Saul",
        COORDINATED_ATTACK_HERO_LINE_MAX_CHARS,
    )
    complementary_custom_message = _truncate_with_ellipsis(
        str(data.get("complementary_custom_message", "")).strip(),
        COORDINATED_ATTACK_COMPLEMENTARY_MAX_CHARS,
    )

    attack_header = f"🔴 Attack: {attack_ratio_text}"
    defense_header = f"🔵 Defense: {defense_ratio_text}"

    message_lines = [
        f"{data['target']}",
        f"Target: {coordinated_dt.strftime('%H:%M:%S')} UTC | Rally: {rally_minutes} min",
        "--------------------",
        timeline_header,
    ]
    for idx, item in enumerate(operation_order, start=1):
        message_lines.append(f"{idx}. {item['send_message']} - {item['nick']}")

    message_lines.extend(
        [
            "--------------------",
            attack_header,
            f"{attack_line}",
            defense_header,
            f"{defense_line}",
        ]
    )

    message_entries: list[dict[str, Any]] = [
        {"line": f"{data['target']}", "section_header": "", "is_section_header": False},
        {"line": f"Target: {coordinated_dt.strftime('%H:%M:%S')} UTC | Rally: {rally_minutes} min", "section_header": "", "is_section_header": False},
        {"line": "--------------------", "section_header": "", "is_section_header": False},
        {"line": timeline_header, "section_header": "", "is_section_header": False},
    ]
    for idx, item in enumerate(operation_order, start=1):
        message_entries.append({"line": f"{idx}. {item['send_message']} - {item['nick']}", "section_header": "", "is_section_header": False})

    message_entries.extend(
        [
            {"line": "--------------------", "section_header": "", "is_section_header": False},
            {"line": attack_header, "section_header": attack_header, "is_section_header": True},
            {"line": attack_line, "section_header": attack_header, "is_section_header": False},
            {"line": defense_header, "section_header": defense_header, "is_section_header": True},
            {"line": defense_line, "section_header": defense_header, "is_section_header": False},
        ]
    )

    primary_message_lines = list(message_lines)
    primary_message_text = "\n".join(primary_message_lines)

    if len(primary_message_text) > COORDINATED_ATTACK_MESSAGE_LIMIT:
        overflow = len(primary_message_text) - COORDINATED_ATTACK_MESSAGE_LIMIT
        # Reduce Defense line first, then Attack line, preserving readability.
        new_defense_max = max(20, len(defense_line) - overflow)
        defense_line = _truncate_with_ellipsis(defense_line, new_defense_max)
        primary_message_lines[-1] = defense_line
        primary_message_text = "\n".join(primary_message_lines)

    if len(primary_message_text) > COORDINATED_ATTACK_MESSAGE_LIMIT:
        overflow = len(primary_message_text) - COORDINATED_ATTACK_MESSAGE_LIMIT
        new_attack_max = max(20, len(attack_line) - overflow)
        attack_line = _truncate_with_ellipsis(attack_line, new_attack_max)
        primary_message_lines[-3] = attack_line
        primary_message_text = "\n".join(primary_message_lines)

    if len(primary_message_text) > COORDINATED_ATTACK_MESSAGE_LIMIT:
        primary_message_text = _truncate_with_ellipsis(primary_message_text, COORDINATED_ATTACK_MESSAGE_LIMIT)

    message_parts = [primary_message_text]
    message_parts_labeled = [primary_message_text]

    if complementary_custom_message:
        target = str(data["target"])
        primary_body = "\n".join(primary_message_lines[1:]).strip()
        part_one = f"{target} (1/2)"
        if primary_body:
            part_one = f"{part_one}\n{primary_body}"

        part_two = f"{target} (2/2)\n{complementary_custom_message}"
        message_parts = [primary_message_text, complementary_custom_message]
        message_parts_labeled = [
            _truncate_with_ellipsis(part_one, COORDINATED_ATTACK_MESSAGE_LIMIT),
            _truncate_with_ellipsis(part_two, COORDINATED_ATTACK_MESSAGE_LIMIT),
        ]

    return {
        "target": data["target"],
        "time_mode": time_mode,
        "coordinated_time_utc": data["coordinated_time_utc"],
        "rally_minutes": rally_minutes,
        "operation_order": operation_order,
        "attack_ratio": attack_ratio,
        "defense_ratio": defense_ratio,
        "attack_line": attack_line,
        "defense_line": defense_line,
        "complementary_custom_message": complementary_custom_message,
        "message": primary_message_text,
        "message_parts": message_parts,
        "message_parts_labeled": message_parts_labeled,
        "message_limit": COORDINATED_ATTACK_MESSAGE_LIMIT,
    }


def _get_db_connection() -> sqlite3.Connection:
    DATABASE_PATH.parent.mkdir(parents=True, exist_ok=True)
    connection = sqlite3.connect(DATABASE_PATH)
    connection.row_factory = sqlite3.Row
    return connection


def _get_jeabs_token(alliance: dict[str, Any] | int | None) -> str:
    """Resolve an alliance token, keeping the server token as a legacy fallback."""
    if isinstance(alliance, dict):
        alliance_token = str(alliance.get("jeabs_api_token") or "").strip()
        if alliance_token:
            return alliance_token
    elif alliance:
        with _get_db_connection() as connection:
            row = connection.execute(
                "SELECT jeabs_api_token FROM alliances WHERE id = ? LIMIT 1",
                (int(alliance),),
            ).fetchone()
        alliance_token = str((row["jeabs_api_token"] if row else "") or "").strip()
        if alliance_token:
            return alliance_token
    return os.getenv("JEABSPLUS_API_TOKEN", "").strip()


def _insert_player_snapshot_if_not_first_ever(
    connection: sqlite3.Connection,
    alliance_id: int,
    profile_row: Any,
    now: str,
) -> None:
    """Record a growth-history point from the player's CURRENT (pre-update) values.
    Skipped on a profile's very first update (still at its just-created state), so the
    initial registration never becomes a fake baseline for deltas/growth charts."""
    if profile_row["updated_at"] == profile_row["created_at"]:
        return
    connection.execute(
        """
        INSERT INTO alliance_player_snapshots (
            alliance_id, player_id, total_power, mystic_score,
            infantry_attack_bonus, infantry_defense_bonus, infantry_lethality_bonus, infantry_health_bonus,
            cavalry_attack_bonus, cavalry_defense_bonus, cavalry_lethality_bonus, cavalry_health_bonus,
            archer_attack_bonus, archer_defense_bonus, archer_lethality_bonus, archer_health_bonus,
            created_at
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            alliance_id,
            profile_row["id"],
            profile_row["total_power"],
            profile_row["mystic_score"],
            profile_row["infantry_attack_bonus"],
            profile_row["infantry_defense_bonus"],
            profile_row["infantry_lethality_bonus"],
            profile_row["infantry_health_bonus"],
            profile_row["cavalry_attack_bonus"],
            profile_row["cavalry_defense_bonus"],
            profile_row["cavalry_lethality_bonus"],
            profile_row["cavalry_health_bonus"],
            profile_row["archer_attack_bonus"],
            profile_row["archer_defense_bonus"],
            profile_row["archer_lethality_bonus"],
            profile_row["archer_health_bonus"],
            now,
        ),
    )


def _dedupe_alliance_players_by_game_id(connection: sqlite3.Connection) -> None:
    """One-time cleanup so alliance_players never has two rows for the same
    (alliance_id, game_id) — required before the unique index can be created."""
    duplicate_groups = connection.execute(
        """
        SELECT alliance_id, game_id
        FROM alliance_players
        WHERE game_id IS NOT NULL AND game_id != ''
        GROUP BY alliance_id, game_id
        HAVING COUNT(*) > 1
        """
    ).fetchall()

    now = datetime.now(timezone.utc).isoformat()
    for group in duplicate_groups:
        rows = connection.execute(
            """
            SELECT alliance_players.id AS profile_id, alliance_players.user_id AS user_id,
                   alliance_users.discord_user_id AS discord_user_id
            FROM alliance_players
            JOIN alliance_users ON alliance_users.id = alliance_players.user_id
            WHERE alliance_players.alliance_id = ? AND alliance_players.game_id = ?
            ORDER BY alliance_players.id ASC
            """,
            (group["alliance_id"], group["game_id"]),
        ).fetchall()
        if len(rows) < 2:
            continue

        # Prefer keeping the profile linked to a real Discord account over a
        # JeabsPlus placeholder; fall back to the most recently created row.
        real_rows = [row for row in rows if not _is_jeabs_synthetic_discord_user_id(row["discord_user_id"])]
        keep_row = real_rows[-1] if real_rows else rows[-1]

        for row in rows:
            if int(row["profile_id"]) == int(keep_row["profile_id"]):
                continue
            connection.execute("DELETE FROM alliance_players WHERE id = ?", (int(row["profile_id"]),))
            if int(row["user_id"]) != int(keep_row["user_id"]):
                _detach_orphan_synthetic_alliance_user(connection, int(row["user_id"]), now)


def _init_alliance_registry_db() -> None:
    with _get_db_connection() as connection:
        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS alliance_users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                discord_user_id TEXT UNIQUE NOT NULL,
                username TEXT NOT NULL,
                avatar_url TEXT,
                is_admin INTEGER DEFAULT 0,
                alliance_id INTEGER,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            )
            """
        )
        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS usage_events (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                alliance_id INTEGER,
                section TEXT NOT NULL,
                path TEXT NOT NULL,
                method TEXT NOT NULL,
                occurred_at TEXT NOT NULL
            )
            """
        )
        connection.execute("CREATE INDEX IF NOT EXISTS idx_usage_events_user_time ON usage_events(user_id, occurred_at)")
        connection.execute("CREATE INDEX IF NOT EXISTS idx_usage_events_section_time ON usage_events(section, occurred_at)")
        initialize_email_auth_schema(connection)
        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS alliances (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL,
                tag TEXT,
                kingdom TEXT,
                description TEXT,
                avatar_url TEXT,
                created_by_user_id INTEGER,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            )
            """
        )
        alliance_columns = {
            row[1] for row in connection.execute("PRAGMA table_info(alliances)").fetchall()
        }
        if "jeabs_alliance_id" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN jeabs_alliance_id TEXT")
        if "jeabs_api_token" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN jeabs_api_token TEXT")
        if "description" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN description TEXT")
        if "swordland_rival_jeabs_id" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN swordland_rival_jeabs_id TEXT")
        if "swordland_rival_name" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN swordland_rival_name TEXT")
        if "swordland_cache_json" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN swordland_cache_json TEXT")
        if "swordland_cache_updated_at" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN swordland_cache_updated_at TEXT")
        if "swordland2_rival_jeabs_id" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN swordland2_rival_jeabs_id TEXT")
        if "swordland2_rival_name" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN swordland2_rival_name TEXT")
        if "swordland2_cache_json" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN swordland2_cache_json TEXT")
        if "swordland2_cache_updated_at" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN swordland2_cache_updated_at TEXT")
        if "swordland_plan_json" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN swordland_plan_json TEXT")
        if "swordland2_plan_json" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN swordland2_plan_json TEXT")
        if "kvk_rival_jeabs_id" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN kvk_rival_jeabs_id TEXT")
        if "kvk_rival_name" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN kvk_rival_name TEXT")
        if "kvk_cache_json" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN kvk_cache_json TEXT")
        if "kvk_cache_updated_at" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN kvk_cache_updated_at TEXT")
        if "kvk_plan_json" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN kvk_plan_json TEXT")
        if "nap4_config_json" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN nap4_config_json TEXT")
        if "nap4_cache_json" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN nap4_cache_json TEXT")
        if "nap4_cache_updated_at" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN nap4_cache_updated_at TEXT")
        if "ac_plan_json" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN ac_plan_json TEXT")
        if "ac_lock_token" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN ac_lock_token TEXT")
        if "ac_lock_user_id" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN ac_lock_user_id INTEGER")
        if "ac_lock_updated_at" not in alliance_columns:
            connection.execute("ALTER TABLE alliances ADD COLUMN ac_lock_updated_at TEXT")
        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS alliance_players (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                alliance_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                player_name TEXT,
                game_id TEXT,
                vip_level INTEGER,
                town_hall_level INTEGER,
                total_power INTEGER,
                power_ac INTEGER DEFAULT 0,
                kills INTEGER DEFAULT 0,
                mystic_score INTEGER DEFAULT 0,
                radiant_spire INTEGER DEFAULT 0,
                bt TEXT DEFAULT '',
                bt_time INTEGER DEFAULT 0,
                hero_gear_json TEXT DEFAULT '{}',
                hero_gear_updated_at TEXT,
                kingdom_id TEXT,
                infantry_troops TEXT,
                cavalry_troops TEXT,
                archer_troops TEXT,
                infantry_attack_bonus REAL DEFAULT 0,
                infantry_defense_bonus REAL DEFAULT 0,
                infantry_lethality_bonus REAL DEFAULT 0,
                infantry_health_bonus REAL DEFAULT 0,
                cavalry_attack_bonus REAL DEFAULT 0,
                cavalry_defense_bonus REAL DEFAULT 0,
                cavalry_lethality_bonus REAL DEFAULT 0,
                cavalry_health_bonus REAL DEFAULT 0,
                archer_attack_bonus REAL DEFAULT 0,
                archer_defense_bonus REAL DEFAULT 0,
                archer_lethality_bonus REAL DEFAULT 0,
                archer_health_bonus REAL DEFAULT 0,
                giftcode_player_id TEXT,
                hero_data TEXT,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            )
            """
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_alliance_players_alliance ON alliance_players(alliance_id)"
        )
        _dedupe_alliance_players_by_game_id(connection)
        connection.execute(
            """
            CREATE UNIQUE INDEX IF NOT EXISTS idx_alliance_players_unique_game_id
            ON alliance_players(alliance_id, game_id)
            WHERE game_id IS NOT NULL AND game_id != ''
            """
        )

        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS alliance_player_snapshots (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                alliance_id INTEGER NOT NULL,
                player_id INTEGER NOT NULL,
                total_power INTEGER,
                infantry_attack_bonus REAL DEFAULT 0,
                infantry_defense_bonus REAL DEFAULT 0,
                infantry_lethality_bonus REAL DEFAULT 0,
                infantry_health_bonus REAL DEFAULT 0,
                cavalry_attack_bonus REAL DEFAULT 0,
                cavalry_defense_bonus REAL DEFAULT 0,
                cavalry_lethality_bonus REAL DEFAULT 0,
                cavalry_health_bonus REAL DEFAULT 0,
                archer_attack_bonus REAL DEFAULT 0,
                archer_defense_bonus REAL DEFAULT 0,
                archer_lethality_bonus REAL DEFAULT 0,
                archer_health_bonus REAL DEFAULT 0,
                created_at TEXT NOT NULL
            )
            """
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_alliance_player_snapshots_player ON alliance_player_snapshots(alliance_id, player_id, id DESC)"
        )
        snapshot_columns = {
            row[1] for row in connection.execute("PRAGMA table_info(alliance_player_snapshots)").fetchall()
        }
        if "mystic_score" not in snapshot_columns:
            connection.execute("ALTER TABLE alliance_player_snapshots ADD COLUMN mystic_score INTEGER DEFAULT 0")

        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS alliance_join_requests (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                alliance_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                status TEXT NOT NULL DEFAULT 'pending',
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            )
            """
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_join_requests_alliance ON alliance_join_requests(alliance_id, status)"
        )

        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS alliance_invites (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                alliance_id INTEGER NOT NULL,
                invited_by_user_id INTEGER NOT NULL,
                invited_discord_user_id TEXT NOT NULL,
                invited_username TEXT,
                status TEXT NOT NULL DEFAULT 'pending',
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            )
            """
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_invites_alliance ON alliance_invites(alliance_id, status)"
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_invites_discord_user ON alliance_invites(invited_discord_user_id, status)"
        )

        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS alliance_invite_links (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                alliance_id INTEGER NOT NULL,
                created_by_user_id INTEGER NOT NULL,
                token TEXT UNIQUE NOT NULL,
                status TEXT NOT NULL DEFAULT 'active',
                created_at TEXT NOT NULL,
                revoked_at TEXT
            )
            """
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_invite_links_alliance ON alliance_invite_links(alliance_id, status, id DESC)"
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_invite_links_token ON alliance_invite_links(token, status)"
        )
        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS alliance_roster_forms (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                alliance_id INTEGER NOT NULL,
                created_by_user_id INTEGER NOT NULL,
                token TEXT UNIQUE NOT NULL,
                title TEXT NOT NULL,
                schema_json TEXT NOT NULL DEFAULT '{"sections":[]}',
                status TEXT NOT NULL DEFAULT 'active',
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            )
            """
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_roster_forms_alliance ON alliance_roster_forms(alliance_id, status, id DESC)"
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_roster_forms_token ON alliance_roster_forms(token, status)"
        )
        roster_form_columns = {
            row[1] for row in connection.execute("PRAGMA table_info(alliance_roster_forms)").fetchall()
        }
        if "schema_json" not in roster_form_columns:
            connection.execute(
                "ALTER TABLE alliance_roster_forms ADD COLUMN schema_json TEXT NOT NULL DEFAULT '{\"sections\":[]}'"
            )
        if "form_type" not in roster_form_columns:
            connection.execute(
                "ALTER TABLE alliance_roster_forms ADD COLUMN form_type TEXT NOT NULL DEFAULT 'roster'"
            )
        if "target_scope" not in roster_form_columns:
            connection.execute(
                "ALTER TABLE alliance_roster_forms ADD COLUMN target_scope TEXT NOT NULL DEFAULT 'all'"
            )
        if "target_list_json" not in roster_form_columns:
            connection.execute(
                "ALTER TABLE alliance_roster_forms ADD COLUMN target_list_json TEXT NOT NULL DEFAULT '[]'"
            )
        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS alliance_roster_submissions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                alliance_id INTEGER NOT NULL,
                roster_form_id INTEGER NOT NULL,
                player_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                payload_json TEXT NOT NULL DEFAULT '{}',
                submitted_at TEXT NOT NULL,
                UNIQUE(roster_form_id, player_id)
            )
            """
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_roster_submissions_form ON alliance_roster_submissions(roster_form_id, submitted_at DESC)"
        )
        roster_submission_columns = {
            row[1] for row in connection.execute("PRAGMA table_info(alliance_roster_submissions)").fetchall()
        }
        if "payload_json" not in roster_submission_columns:
            connection.execute("ALTER TABLE alliance_roster_submissions ADD COLUMN payload_json TEXT NOT NULL DEFAULT '{}'")
        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS alliance_transfer_applications (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                alliance_id INTEGER NOT NULL,
                roster_form_id INTEGER NOT NULL,
                game_id TEXT NOT NULL,
                player_name TEXT NOT NULL,
                payload_json TEXT NOT NULL DEFAULT '{}',
                submitted_at TEXT NOT NULL,
                UNIQUE(roster_form_id, game_id)
            )
            """
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_transfer_applications_form ON alliance_transfer_applications(roster_form_id, submitted_at DESC)"
        )
        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS alliance_roster_suggestions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                alliance_id INTEGER NOT NULL,
                roster_form_id INTEGER,
                player_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                note TEXT NOT NULL,
                submitted_at TEXT NOT NULL
            )
            """
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_roster_suggestions_alliance ON alliance_roster_suggestions(alliance_id, submitted_at DESC)"
        )

        join_request_columns = {
            row[1] for row in connection.execute("PRAGMA table_info(alliance_join_requests)").fetchall()
        }
        if "invite_link_id" not in join_request_columns:
            connection.execute(
                "ALTER TABLE alliance_join_requests ADD COLUMN invite_link_id INTEGER"
            )
        if "invite_link_token" not in join_request_columns:
            connection.execute(
                "ALTER TABLE alliance_join_requests ADD COLUMN invite_link_token TEXT"
            )

        existing_columns = {
            row[1] for row in connection.execute("PRAGMA table_info(alliance_players)").fetchall()
        }
        new_columns = {
            "infantry_attack_bonus",
            "infantry_defense_bonus",
            "infantry_lethality_bonus",
            "infantry_health_bonus",
            "cavalry_attack_bonus",
            "cavalry_defense_bonus",
            "cavalry_lethality_bonus",
            "cavalry_health_bonus",
            "archer_attack_bonus",
            "archer_defense_bonus",
            "archer_lethality_bonus",
            "archer_health_bonus",
        }
        for column_name in sorted(new_columns - existing_columns):
            connection.execute(
                f"ALTER TABLE alliance_players ADD COLUMN {column_name} REAL DEFAULT 0"
            )

        extra_player_columns: dict[str, str] = {
            "att_troops": "REAL DEFAULT 0",
            "power_ac": "INTEGER DEFAULT 0",
            "formation_infantry_pct": "REAL DEFAULT 0",
            "formation_cavalry_pct": "REAL DEFAULT 0",
            "formation_archer_pct": "REAL DEFAULT 0",
            "kills": "INTEGER DEFAULT 0",
            "mystic_score": "INTEGER DEFAULT 0",
            "radiant_spire": "INTEGER DEFAULT 0",
            "bt": "TEXT DEFAULT ''",
            "bt_time": "INTEGER DEFAULT 0",
            "hero_gear_json": "TEXT DEFAULT '{}'",
            "hero_gear_updated_at": "TEXT",
            "alliance_rank": "TEXT DEFAULT ''",
            "bear_trap_config_json": "TEXT DEFAULT '{}'",
            "player_avatar_url": "TEXT DEFAULT ''",
            "public_roster_json": "TEXT DEFAULT '{}'",
            "profile_update_source": "TEXT DEFAULT ''",
            "public_roster_updated_at": "TEXT",
        }
        for column_name, column_type in extra_player_columns.items():
            if column_name not in existing_columns:
                connection.execute(
                    f"ALTER TABLE alliance_players ADD COLUMN {column_name} {column_type}"
                )

        # Early alliance profile builds stored shorthand power inputs like "462" instead of 462,000,000.
        # In Kingshot this field is expected to be in the millions, so tiny persisted values are upgraded once.
        connection.execute(
            """
            UPDATE alliance_players
            SET total_power = total_power * 1000000
            WHERE total_power IS NOT NULL AND total_power > 0 AND total_power < 10000
            """
        )
        connection.execute(
            """
            UPDATE alliance_player_snapshots
            SET total_power = total_power * 1000000
            WHERE total_power IS NOT NULL AND total_power > 0 AND total_power < 10000
            """
        )

        # Legacy Town Hall encoding stored TG5..TG8 as 31..50.
        # New encoding reserves 31..34 for Level 30-* and maps TG1..TG8 to 35..74.
        # Upgrade legacy persisted values once to preserve the same semantic tier.
        connection.execute(
            """
            UPDATE alliance_players
            SET town_hall_level = town_hall_level + 24
            WHERE town_hall_level BETWEEN 31 AND 50
            """
        )


def _set_notice(message: str | None) -> None:
    if message:
        session["notice"] = message
    else:
        session.pop("notice", None)


def _set_error(message: str | None) -> None:
    if message:
        session["error"] = message
    else:
        session.pop("error", None)


def _sanitize_post_login_next(value: Any) -> str:
    candidate = str(value or "").strip()
    if not candidate.startswith("/"):
        return ""
    if candidate.startswith("//"):
        return ""
    return candidate


def _is_discord_cdn_avatar(url: str | None) -> bool:
    normalized = str(url or "").strip().lower()
    return normalized.startswith("https://cdn.discordapp.com/avatars/") or normalized.startswith("http://cdn.discordapp.com/avatars/")


def _get_current_user() -> dict[str, Any] | None:
    internal_user_id = session.get("user_id")
    discord_user_id = session.get("discord_user_id")
    if not internal_user_id and not discord_user_id:
        return None
    # Keep authenticated users on a persistent cookie so mobile browsers do not
    # drop the login when the tab/app is backgrounded.
    session.permanent = True
    with _get_db_connection() as connection:
        if internal_user_id:
            row = connection.execute(
                "SELECT * FROM alliance_users WHERE id = ?",
                (int(internal_user_id),),
            ).fetchone()
        else:
            row = connection.execute(
                "SELECT * FROM alliance_users WHERE discord_user_id = ?",
                (str(discord_user_id),),
            ).fetchone()

    if not row and discord_user_id:
        username = str(session.get("discord_username") or "Discord User").strip() or "Discord User"
        avatar_url = str(session.get("discord_avatar") or "").strip() or None
        row = _ensure_user_record(str(discord_user_id), username, avatar_url)
        session["user_id"] = row["id"]
        return row

    return dict(row) if row else None


def _get_email_identity(user_id: int) -> dict[str, Any] | None:
    with _get_db_connection() as connection:
        row = connection.execute(
            "SELECT * FROM alliance_email_identities WHERE user_id = ?",
            (int(user_id),),
        ).fetchone()
    return dict(row) if row else None


def _ensure_email_user(email: str) -> dict[str, Any]:
    normalized_email = normalize_email(email)
    now = datetime.now(timezone.utc).isoformat()
    with _get_db_connection() as connection:
        identity = connection.execute(
            "SELECT user_id FROM alliance_email_identities WHERE email_normalized = ?",
            (normalized_email,),
        ).fetchone()
        if identity:
            row = connection.execute(
                "SELECT * FROM alliance_users WHERE id = ?",
                (int(identity["user_id"]),),
            ).fetchone()
            if row:
                return dict(row)

        username = normalized_email.split("@", 1)[0][:80] or "Kingshot Player"
        internal_identity = f"email:{secrets.token_urlsafe(24)}"
        cursor = connection.execute(
            """
            INSERT INTO alliance_users (
                discord_user_id, username, avatar_url, is_admin, alliance_id, created_at, updated_at
            ) VALUES (?, ?, NULL, 0, NULL, ?, ?)
            """,
            (internal_identity, username, now, now),
        )
        user_id = int(cursor.lastrowid)
        connection.execute(
            """
            INSERT INTO alliance_email_identities (
                user_id, email_normalized, email_display, verified_at, created_at, updated_at
            ) VALUES (?, ?, ?, ?, ?, ?)
            """,
            (user_id, normalized_email, normalized_email, now, now, now),
        )
        row = connection.execute("SELECT * FROM alliance_users WHERE id = ?", (user_id,)).fetchone()
    return dict(row)


def _link_email_identity(user_id: int, email: str) -> bool:
    normalized_email = normalize_email(email)
    now = datetime.now(timezone.utc).isoformat()
    with _get_db_connection() as connection:
        conflict = connection.execute(
            "SELECT user_id FROM alliance_email_identities WHERE email_normalized = ?",
            (normalized_email,),
        ).fetchone()
        if conflict and int(conflict["user_id"]) != int(user_id):
            return False
        connection.execute(
            """
            INSERT INTO alliance_email_identities (
                user_id, email_normalized, email_display, verified_at, created_at, updated_at
            ) VALUES (?, ?, ?, ?, ?, ?)
            ON CONFLICT(user_id) DO UPDATE SET
                email_normalized = excluded.email_normalized,
                email_display = excluded.email_display,
                verified_at = excluded.verified_at,
                updated_at = excluded.updated_at
            """,
            (int(user_id), normalized_email, normalized_email, now, now, now),
        )
    return True


def _complete_email_login_by_game_id(email: str, game_id: str) -> dict[str, Any]:
    normalized_email = normalize_email(email)
    normalized_game_id = str(game_id or "").strip()
    if not normalized_game_id or not normalized_game_id.isdigit():
        raise ValueError("Enter a valid numeric Game ID.")

    now = datetime.now(timezone.utc).isoformat()
    with _get_db_connection() as connection:
        identity = connection.execute(
            "SELECT user_id FROM alliance_email_identities WHERE email_normalized = ?",
            (normalized_email,),
        ).fetchone()
        email_user_id = int(identity["user_id"]) if identity else None
        profile = connection.execute(
            """
            SELECT alliance_players.user_id, alliance_players.player_name
            FROM alliance_players
            WHERE alliance_players.game_id = ?
            ORDER BY alliance_players.updated_at DESC, alliance_players.id DESC
            LIMIT 1
            """,
            (normalized_game_id,),
        ).fetchone()

        if profile:
            target_user_id = int(profile["user_id"])
            player_name = str(profile["player_name"] or "").strip()
            if identity and email_user_id != target_user_id:
                connection.execute(
                    "DELETE FROM alliance_email_identities WHERE email_normalized = ?",
                    (normalized_email,),
                )
            target_identity = connection.execute(
                "SELECT email_normalized FROM alliance_email_identities WHERE user_id = ?",
                (target_user_id,),
            ).fetchone()
            if target_identity and str(target_identity["email_normalized"]) != normalized_email:
                raise ValueError("That player profile already belongs to another email.")
            connection.execute(
                """
                INSERT INTO alliance_email_identities (
                    user_id, email_normalized, email_display, verified_at, created_at, updated_at
                ) VALUES (?, ?, ?, ?, ?, ?)
                ON CONFLICT(user_id) DO UPDATE SET
                    email_normalized = excluded.email_normalized,
                    email_display = excluded.email_display,
                    verified_at = excluded.verified_at,
                    updated_at = excluded.updated_at
                """,
                (target_user_id, normalized_email, normalized_email, now, now, now),
            )
            if player_name:
                connection.execute(
                    "UPDATE alliance_users SET username = ?, updated_at = ? WHERE id = ?",
                    (player_name, now, target_user_id),
                )
            if email_user_id and email_user_id != target_user_id:
                orphan = connection.execute(
                    """
                    SELECT alliance_users.id
                    FROM alliance_users
                    LEFT JOIN alliance_players ON alliance_players.user_id = alliance_users.id
                    WHERE alliance_users.id = ?
                      AND alliance_users.alliance_id IS NULL
                      AND alliance_users.is_admin = 0
                    GROUP BY alliance_users.id
                    HAVING COUNT(alliance_players.id) = 0
                    """,
                    (email_user_id,),
                ).fetchone()
                if orphan:
                    connection.execute("DELETE FROM alliance_users WHERE id = ?", (email_user_id,))
        else:
            user = _ensure_email_user(normalized_email)
            target_user_id = int(user["id"])

        row = connection.execute("SELECT * FROM alliance_users WHERE id = ?", (target_user_id,)).fetchone()
    if not row:
        raise ValueError("Could not complete registration.")
    return dict(row)


def _get_current_alliance_for_user(user: dict[str, Any]) -> dict[str, Any] | None:
    alliance_id = user.get("alliance_id")
    if not alliance_id:
        return None
    with _get_db_connection() as connection:
        row = connection.execute("SELECT * FROM alliances WHERE id = ?", (int(alliance_id),)).fetchone()
    if not row:
        return None
    return dict(row)


def _ensure_user_record(discord_user_id: str, username: str, avatar_url: str | None) -> dict[str, Any]:
    now = datetime.now(timezone.utc).isoformat()
    with _get_db_connection() as connection:
        existing = connection.execute(
            "SELECT * FROM alliance_users WHERE discord_user_id = ?",
            (str(discord_user_id),),
        ).fetchone()
        if existing:
            existing_avatar = str(existing["avatar_url"] or "").strip()
            next_avatar = existing_avatar or None
            new_avatar = str(avatar_url or "").strip() or None

            # Keep game avatars when present; Discord avatar is only a fallback.
            if new_avatar and (not existing_avatar or _is_discord_cdn_avatar(existing_avatar)):
                next_avatar = new_avatar

            connection.execute(
                "UPDATE alliance_users SET username = ?, avatar_url = ?, updated_at = ? WHERE discord_user_id = ?",
                (username, next_avatar, now, str(discord_user_id)),
            )
            row = connection.execute(
                "SELECT * FROM alliance_users WHERE discord_user_id = ?",
                (str(discord_user_id),),
            ).fetchone()
            return dict(row)

        cursor = connection.execute(
            """
            INSERT INTO alliance_users (discord_user_id, username, avatar_url, is_admin, alliance_id, created_at, updated_at)
            VALUES (?, ?, ?, 0, NULL, ?, ?)
            """,
            (str(discord_user_id), username, avatar_url, now, now),
        )
        user_id = cursor.lastrowid
        row = connection.execute("SELECT * FROM alliance_users WHERE id = ?", (user_id,)).fetchone()
        return dict(row)


def _is_jeabs_synthetic_discord_user_id(discord_user_id: Any) -> bool:
    return str(discord_user_id or "").strip().lower().startswith("jeabsplus:")


def _find_unique_real_alliance_user_without_profile(
    connection: sqlite3.Connection,
    alliance_id: int,
    username: str,
) -> dict[str, Any] | None:
    normalized_username = str(username or "").strip()
    if not normalized_username:
        return None

    rows = connection.execute(
        """
        SELECT alliance_users.*
        FROM alliance_users
        LEFT JOIN alliance_players
            ON alliance_players.alliance_id = alliance_users.alliance_id
            AND alliance_players.user_id = alliance_users.id
        WHERE alliance_users.alliance_id = ?
          AND LOWER(alliance_users.username) = LOWER(?)
          AND alliance_users.discord_user_id NOT LIKE 'jeabsplus:%'
        GROUP BY alliance_users.id
        HAVING COUNT(alliance_players.id) = 0
        ORDER BY alliance_users.id DESC
        """,
        (alliance_id, normalized_username),
    ).fetchall()

    if len(rows) != 1:
        return None
    return dict(rows[0])


def _detach_orphan_synthetic_alliance_user(connection: sqlite3.Connection, user_id: int, now: str) -> None:
    row = connection.execute(
        "SELECT id, discord_user_id, is_admin FROM alliance_users WHERE id = ? LIMIT 1",
        (int(user_id),),
    ).fetchone()
    if not row or row["is_admin"]:
        return
    if not _is_jeabs_synthetic_discord_user_id(row["discord_user_id"]):
        return

    linked_profile = connection.execute(
        "SELECT 1 FROM alliance_players WHERE user_id = ? LIMIT 1",
        (int(user_id),),
    ).fetchone()
    if linked_profile:
        return

    connection.execute(
        "UPDATE alliance_users SET alliance_id = NULL, updated_at = ? WHERE id = ?",
        (now, int(user_id)),
    )


def _detach_shadow_synthetic_alliance_users(
    connection: sqlite3.Connection,
    alliance_id: int,
    game_id: str,
    protected_user_id: int,
    now: str,
) -> None:
    normalized_game_id = str(game_id or "").strip()
    if not normalized_game_id:
        return

    synthetic_discord_id = f"jeabsplus:{alliance_id}:{normalized_game_id}"
    rows = connection.execute(
        """
        SELECT alliance_users.id
        FROM alliance_users
        LEFT JOIN alliance_players
            ON alliance_players.alliance_id = alliance_users.alliance_id
            AND alliance_players.user_id = alliance_users.id
        WHERE alliance_users.alliance_id = ?
          AND alliance_users.id != ?
          AND alliance_users.discord_user_id = ?
        GROUP BY alliance_users.id
        HAVING COUNT(alliance_players.id) = 0
        """,
        (alliance_id, int(protected_user_id), synthetic_discord_id),
    ).fetchall()

    for row in rows:
        _detach_orphan_synthetic_alliance_user(connection, int(row["id"]), now)


def _get_alliance_by_id(alliance_id: int) -> dict[str, Any] | None:
    with _get_db_connection() as connection:
        row = connection.execute("SELECT * FROM alliances WHERE id = ?", (alliance_id,)).fetchone()
    return dict(row) if row else None


def _list_alliances_with_member_counts() -> list[dict[str, Any]]:
    with _get_db_connection() as connection:
        rows = connection.execute(
            """
            SELECT alliances.*, COUNT(alliance_users.id) AS member_count
            FROM alliances
            LEFT JOIN alliance_users ON alliance_users.alliance_id = alliances.id
            GROUP BY alliances.id
            ORDER BY member_count DESC, alliances.name ASC
            """
        ).fetchall()
    return [dict(row) for row in rows]


def _claim_or_create_profile_by_game_id(
    alliance_id: int,
    target_user_id: int,
    game_id: str,
    preferred_player_name: str | None = None,
) -> dict[str, Any]:
    normalized_game_id = str(game_id or "").strip()
    if not normalized_game_id:
        raise ValueError("Game ID is required.")

    now = datetime.now(timezone.utc).isoformat()
    with _get_db_connection() as connection:
        existing_by_game = connection.execute(
            """
            SELECT * FROM alliance_players
            WHERE alliance_id = ? AND game_id = ?
            ORDER BY id DESC
            LIMIT 1
            """,
            (alliance_id, normalized_game_id),
        ).fetchone()

        existing_for_target = connection.execute(
            """
            SELECT * FROM alliance_players
            WHERE alliance_id = ? AND user_id = ?
            ORDER BY id DESC
            LIMIT 1
            """,
            (alliance_id, target_user_id),
        ).fetchone()

        if existing_by_game:
            selected_id = int(existing_by_game["id"])
            selected_user_id = int(existing_by_game["user_id"])

            if existing_for_target and int(existing_for_target["id"]) != selected_id:
                connection.execute("DELETE FROM alliance_players WHERE id = ?", (int(existing_for_target["id"]),))

            connection.execute(
                """
                UPDATE alliance_players
                SET user_id = ?,
                    player_name = CASE WHEN ? != '' THEN ? ELSE player_name END,
                    updated_at = ?
                WHERE id = ?
                """,
                (
                    target_user_id,
                    str(preferred_player_name or "").strip(),
                    str(preferred_player_name or "").strip(),
                    now,
                    selected_id,
                ),
            )

            if selected_user_id != target_user_id:
                _detach_orphan_synthetic_alliance_user(connection, selected_user_id, now)
            _detach_shadow_synthetic_alliance_users(
                connection,
                alliance_id,
                normalized_game_id,
                target_user_id,
                now,
            )

            # Ensure one profile per game_id inside the alliance.
            connection.execute(
                "DELETE FROM alliance_players WHERE alliance_id = ? AND game_id = ? AND id != ?",
                (alliance_id, normalized_game_id, selected_id),
            )

            row = connection.execute("SELECT * FROM alliance_players WHERE id = ?", (selected_id,)).fetchone()
            return {
                "row": dict(row) if row else None,
                "mode": "claimed_existing" if selected_user_id != target_user_id else "updated_existing",
            }

        if existing_for_target:
            target_id = int(existing_for_target["id"])
            connection.execute(
                """
                UPDATE alliance_players
                SET game_id = ?,
                    player_name = CASE WHEN ? != '' THEN ? ELSE player_name END,
                    updated_at = ?
                WHERE id = ?
                """,
                (
                    normalized_game_id,
                    str(preferred_player_name or "").strip(),
                    str(preferred_player_name or "").strip(),
                    now,
                    target_id,
                ),
            )
            row = connection.execute("SELECT * FROM alliance_players WHERE id = ?", (target_id,)).fetchone()
            return {
                "row": dict(row) if row else None,
                "mode": "updated_target",
            }

        cursor = connection.execute(
            """
            INSERT INTO alliance_players (
                alliance_id, user_id, player_name, game_id, vip_level, town_hall_level, total_power,
                power_ac, kills, mystic_score, kingdom_id,
                infantry_troops, cavalry_troops, archer_troops,
                infantry_attack_bonus, infantry_defense_bonus, infantry_lethality_bonus, infantry_health_bonus,
                cavalry_attack_bonus, cavalry_defense_bonus, cavalry_lethality_bonus, cavalry_health_bonus,
                archer_attack_bonus, archer_defense_bonus, archer_lethality_bonus, archer_health_bonus,
                hero_data, created_at, updated_at
            ) VALUES (?, ?, ?, ?, 0, 30, 0, 0, 0, 0, NULL, 'TG4', 'TG4', 'TG4', 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, '{}', ?, ?)
            """,
            (
                alliance_id,
                target_user_id,
                str(preferred_player_name or "").strip() or f"Player {normalized_game_id}",
                normalized_game_id,
                now,
                now,
            ),
        )
        row = connection.execute("SELECT * FROM alliance_players WHERE id = ?", (int(cursor.lastrowid),)).fetchone()
        return {
            "row": dict(row) if row else None,
            "mode": "created_new",
        }


def _process_join_request(user: dict[str, Any], alliance_id: int, invite_link_id: int | None = None) -> None:
    alliance = _get_alliance_by_id(alliance_id)
    if not alliance:
        _set_error("That alliance no longer exists.")
        return

    now = datetime.now(timezone.utc).isoformat()
    discord_user_id = str(user.get("discord_user_id"))
    invite_link_token: str | None = None

    if invite_link_id:
        with _get_db_connection() as connection:
            invite_link_row = connection.execute(
                "SELECT token FROM alliance_invite_links WHERE id = ? AND alliance_id = ?",
                (int(invite_link_id), alliance_id),
            ).fetchone()
        if invite_link_row:
            invite_link_token = str(invite_link_row["token"] or "").strip() or None
        else:
            invite_link_id = None

    if user.get("alliance_id"):
        if invite_link_id:
            with _get_db_connection() as connection:
                existing_pending = connection.execute(
                    "SELECT id, invite_link_id FROM alliance_join_requests WHERE alliance_id = ? AND user_id = ? AND status = 'pending' ORDER BY id DESC LIMIT 1",
                    (alliance_id, user["id"]),
                ).fetchone()
                if existing_pending and not existing_pending["invite_link_id"]:
                    connection.execute(
                        """
                        UPDATE alliance_join_requests
                        SET invite_link_id = ?, invite_link_token = ?, updated_at = ?
                        WHERE id = ?
                        """,
                        (invite_link_id, invite_link_token, now, existing_pending["id"]),
                    )

        if int(user.get("alliance_id") or 0) == int(alliance_id):
            _set_notice(f"You are already in {alliance['name']}.")
        else:
            _set_error("You are already in an alliance.")
        return

    with _get_db_connection() as connection:
        matching_invite = connection.execute(
            """
            SELECT * FROM alliance_invites
            WHERE alliance_id = ? AND invited_discord_user_id = ? AND status = 'pending'
            """,
            (alliance_id, discord_user_id),
        ).fetchone()

        if matching_invite:
            connection.execute(
                "UPDATE alliance_invites SET status = 'accepted', updated_at = ? WHERE id = ?",
                (now, matching_invite["id"]),
            )
            connection.execute(
                "UPDATE alliance_users SET alliance_id = ?, updated_at = ? WHERE id = ?",
                (alliance_id, now, user["id"]),
            )
            existing_request = connection.execute(
                "SELECT * FROM alliance_join_requests WHERE alliance_id = ? AND user_id = ? AND status = 'pending'",
                (alliance_id, user["id"]),
            ).fetchone()
            if existing_request:
                connection.execute(
                    """
                    UPDATE alliance_join_requests
                    SET status = 'accepted', updated_at = ?, invite_link_id = COALESCE(invite_link_id, ?), invite_link_token = COALESCE(invite_link_token, ?)
                    WHERE id = ?
                    """,
                    (now, invite_link_id, invite_link_token, existing_request["id"]),
                )
            else:
                connection.execute(
                    """
                    INSERT INTO alliance_join_requests (alliance_id, user_id, status, created_at, updated_at, invite_link_id, invite_link_token)
                    VALUES (?, ?, 'accepted', ?, ?, ?, ?)
                    """,
                    (alliance_id, user["id"], now, now, invite_link_id, invite_link_token),
                )
            _set_notice(f"You matched a pending invite — welcome to {alliance['name']}!")
            return

        if invite_link_id:
            existing_request = connection.execute(
                "SELECT * FROM alliance_join_requests WHERE alliance_id = ? AND user_id = ? AND status = 'pending'",
                (alliance_id, user["id"]),
            ).fetchone()
            if existing_request:
                connection.execute(
                    """
                    UPDATE alliance_join_requests
                    SET status = 'accepted', updated_at = ?, invite_link_id = COALESCE(invite_link_id, ?), invite_link_token = COALESCE(invite_link_token, ?)
                    WHERE id = ?
                    """,
                    (now, invite_link_id, invite_link_token, existing_request["id"]),
                )
            else:
                connection.execute(
                    """
                    INSERT INTO alliance_join_requests (alliance_id, user_id, status, created_at, updated_at, invite_link_id, invite_link_token)
                    VALUES (?, ?, 'accepted', ?, ?, ?, ?)
                    """,
                    (alliance_id, user["id"], now, now, invite_link_id, invite_link_token),
                )

            connection.execute(
                "UPDATE alliance_users SET alliance_id = ?, updated_at = ? WHERE id = ?",
                (alliance_id, now, user["id"]),
            )
            _set_notice(f"Welcome to {alliance['name']}! You joined via invitation link.")
            return

        existing_request = connection.execute(
            "SELECT * FROM alliance_join_requests WHERE alliance_id = ? AND user_id = ? AND status = 'pending'",
            (alliance_id, user["id"]),
        ).fetchone()
        if existing_request:
            if invite_link_id and not existing_request["invite_link_id"]:
                connection.execute(
                    """
                    UPDATE alliance_join_requests
                    SET invite_link_id = ?, invite_link_token = ?, updated_at = ?
                    WHERE id = ?
                    """,
                    (invite_link_id, invite_link_token, now, existing_request["id"]),
                )
            _set_notice("Your join request is already pending admin approval.")
            return

        connection.execute(
            """
            INSERT INTO alliance_join_requests (alliance_id, user_id, status, created_at, updated_at, invite_link_id, invite_link_token)
            VALUES (?, ?, 'pending', ?, ?, ?, ?)
            """,
            (alliance_id, user["id"], now, now, invite_link_id, invite_link_token),
        )
    _set_notice(f"Join request sent to {alliance['name']}. Waiting for admin approval.")


def _resolve_discord_user_display_name(discord_user_id: str) -> str | None:
    bot_token = (
        os.getenv("ALLIANCE_DISCORD_BOT_TOKEN")
        or os.getenv("NOTIFICATIONS_BOT_TOKEN")
        or os.getenv("DISCORD_TOKEN")
        or ""
    ).strip()
    if not bot_token:
        return None

    target_discord_id = str(discord_user_id or "").strip()
    if not target_discord_id:
        return None

    try:
        response = requests.get(
            f"{DISCORD_BOT_API_BASE_URL}/users/{target_discord_id}",
            headers={"Authorization": f"Bot {bot_token}"},
            timeout=10,
        )
        if response.status_code >= 400:
            return None

        payload = response.json() or {}
        display_name = str(payload.get("global_name") or payload.get("username") or "").strip()
        return display_name or None
    except requests.RequestException:
        return None


def create_app() -> Flask:
    app = Flask(__name__, template_folder="templates")
    app.config["SECRET_KEY"] = os.getenv("FLASK_SECRET_KEY", "kingshot-alliance-dev-secret")
    app.config["PERMANENT_SESSION_LIFETIME"] = timedelta(days=30)
    app.config["SESSION_REFRESH_EACH_REQUEST"] = True
    app.config["SESSION_COOKIE_HTTPONLY"] = True
    app.config["SESSION_COOKIE_SAMESITE"] = "Lax"
    app.config["SESSION_COOKIE_SECURE"] = True
    app.jinja_env.filters["format_power"] = _format_power
    app.jinja_env.filters["format_stat"] = _format_stat_value
    app.jinja_env.filters["format_delta"] = _format_signed_delta
    app.jinja_env.filters["format_int"] = _format_whole_number
    _init_alliance_registry_db()
    optimizer = BattleCompositionOptimizer()
    coordinated_storage = CoordinatedAttackStorage(COORDINATED_ATTACK_PRESETS_PATH)
    heroes = _load_heroes()
    heroes_by_slug = {str(item["slug"]): item for item in heroes}

    @app.before_request
    def _redirect_public_http_to_https() -> Any:
        forwarded_proto = str(request.headers.get("X-Forwarded-Proto") or request.scheme).split(",", 1)[0].strip()
        if request.host.split(":", 1)[0].lower() == "kingshot.es" and forwarded_proto != "https":
            return redirect(f"{PUBLIC_SITE_URL}{request.full_path.rstrip('?')}", code=301)
        return None

    @app.after_request
    def _disable_alliance_page_cache(response: Any) -> Any:
        if request.path.startswith("/alliance"):
            response.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0"
            response.headers["Pragma"] = "no-cache"
            response.headers["Expires"] = "0"
        return response

    def _auth_csrf_token() -> str:
        token = str(session.get("auth_csrf_token") or "")
        if not token:
            token = secrets.token_urlsafe(32)
            session["auth_csrf_token"] = token
        return token

    def _valid_auth_csrf() -> bool:
        submitted = str(request.headers.get("X-CSRF-Token") or request.form.get("csrf_token") or "")
        expected = str(session.get("auth_csrf_token") or "")
        return bool(submitted and expected and secrets.compare_digest(submitted, expected))

    def _smtp_settings() -> SmtpSettings:
        return SmtpSettings(
            host=os.getenv("SMTP_HOST", "").strip(),
            port=_parse_loose_int(os.getenv("SMTP_PORT"), 587),
            username=os.getenv("SMTP_USERNAME", "").strip(),
            password=os.getenv("SMTP_PASSWORD", ""),
            from_email=os.getenv("SMTP_FROM_EMAIL", "").strip(),
            use_ssl=os.getenv("SMTP_USE_SSL", "").strip().lower() in {"1", "true", "yes"},
            use_starttls=os.getenv("SMTP_USE_STARTTLS", "1").strip().lower() in {"1", "true", "yes"},
        )

    def _start_authenticated_session(user: dict[str, Any], method: str) -> None:
        preserved = {
            key: session.get(key)
            for key in ("pending_join_alliance_id", "pending_join_invite_link_id")
            if session.get(key) is not None
        }
        session.clear()
        session.update(preserved)
        session["user_id"] = int(user["id"])
        session["auth_method"] = method
        session["is_admin"] = bool(user.get("is_admin"))
        session.permanent = True
        _auth_csrf_token()

    @app.context_processor
    def _inject_auth_template_context() -> dict[str, Any]:
        user_id = session.get("user_id")
        email_identity = _get_email_identity(int(user_id)) if user_id else None
        return {
            "auth_csrf_token": _auth_csrf_token(),
            "email_identity": email_identity,
            "email_auth_available": _smtp_settings().configured,
        }

    @app.post("/alliance/usage-event")
    def alliance_usage_event() -> tuple[str, int]:
        user = _get_current_user()
        if not user:
            return "", 401
        payload = request.get_json(silent=True) or {}
        section = str(payload.get("section") or "").strip().lower()
        allowed_sections = {
            "player-list", "my-profile", "admin", "forms", "ac", "swordland",
            "kvk", "bear-calculator", "nap4", "stats",
        }
        if section not in allowed_sections:
            return "", 400
        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            connection.execute(
                """
                INSERT INTO usage_events (user_id, alliance_id, section, path, method, occurred_at)
                VALUES (?, ?, ?, ?, ?, ?)
                """,
                (
                    int(user["id"]),
                    int(user["alliance_id"]) if user.get("alliance_id") else None,
                    section,
                    str(payload.get("path") or request.path)[:300],
                    "VIEW",
                    now,
                ),
            )
        return "", 204

    def _build_hero_progress_from_form(form_data: Any) -> dict[str, dict[str, str]]:
        hero_progress: dict[str, dict[str, str]] = {}
        for hero in heroes:
            slug = str(hero.get("slug") or _normalize_slug(str(hero.get("name", ""))))
            has_widget = str(hero.get("rarity", "")).strip().lower() == "legendary"
            stars = str(form_data.get(f"hero_{slug}_stars", "")).strip()
            widget = str(form_data.get(f"hero_{slug}_widget", "")).strip() if has_widget else ""
            skill = str(form_data.get(f"hero_{slug}_skill", "")).strip()
            if not stars and not widget and not skill:
                continue
            hero_progress[slug] = {
                "stars": stars,
                "widget": widget,
                "skill": skill,
            }
        return hero_progress

    def _build_hero_summary(hero_progress: dict[str, dict[str, str]] | None) -> dict[str, dict[str, str]]:
        return hero_progress if isinstance(hero_progress, dict) else {}

    def _get_hero_progression_choices() -> dict[str, list[str]]:
        # Keep a stable fallback so alliance pages never fail if dynamic progression helpers are removed.
        return {
            "widgets": [str(level) for level in range(0, 11)],
            "skills": [str(level) for level in range(1, 6)],
        }

    def _format_hero_star_summary(star_points: Any) -> str:
        normalized = _clamp_int(star_points, minimum=1, maximum=30, default=0)
        if normalized <= 0:
            return "-"
        star_tier = ((normalized - 1) // 6) + 1
        star_level = ((normalized - 1) % 6) + 1
        return f"{star_tier}★ L{star_level}"

    def _build_member_hero_overview(member_row: dict[str, Any]) -> dict[str, Any]:
        featured_slugs = [
            _normalize_slug("Hilde"),
            _normalize_slug("Saul"),
            _normalize_slug("Chenko"),
            _normalize_slug("Yeonwoo"),
        ]
        featured_lookup = set(featured_slugs)

        try:
            parsed_progress = json.loads(member_row.get("hero_data") or "{}")
        except (TypeError, ValueError):
            parsed_progress = {}
        if not isinstance(parsed_progress, dict):
            parsed_progress = {}

        star_counts = {tier: 0 for tier in range(1, 6)}
        hero_rows: list[dict[str, Any]] = []
        heroes_with_stars = 0

        for hero in heroes:
            slug = str(hero.get("slug") or _normalize_slug(str(hero.get("name", ""))))
            values = parsed_progress.get(slug, {}) if isinstance(parsed_progress.get(slug), dict) else {}
            raw_stars = str(values.get("stars", "")).strip()
            star_points = _clamp_int(raw_stars, minimum=1, maximum=30, default=0) if raw_stars else 0
            star_tier = ((star_points - 1) // 6) + 1 if star_points else 0
            if 1 <= star_tier <= 5:
                star_counts[star_tier] += 1
                heroes_with_stars += 1

            has_widget = str(hero.get("rarity", "")).strip().lower() == "legendary"
            widget_value = str(values.get("widget", "")).strip() if has_widget else ""
            skill_value = str(values.get("skill", "")).strip()

            hero_rows.append(
                {
                    "slug": slug,
                    "name": str(hero.get("name", "")),
                    "image": hero.get("card_image") or "/static/favicon.webp",
                    "stars": _format_hero_star_summary(star_points),
                    "skill": skill_value or "-",
                    "widget": widget_value or "-",
                    "has_any_data": bool(star_points or widget_value or skill_value),
                    "is_featured": slug in featured_lookup,
                }
            )

        featured_rows: list[dict[str, Any]] = []
        for featured_slug in featured_slugs:
            featured_rows.extend([hero_row for hero_row in hero_rows if hero_row["slug"] == featured_slug])

        remaining_rows = [
            hero_row for hero_row in hero_rows if not hero_row["is_featured"] and hero_row["has_any_data"]
        ]

        total_for_graph = heroes_with_stars or 1
        return {
            "featured": featured_rows,
            "remaining": remaining_rows,
            "star_bars": [
                {
                    "label": f"{tier}★",
                    "count": star_counts[tier],
                    "pct": int(round((star_counts[tier] / total_for_graph) * 100)),
                }
                for tier in range(1, 6)
            ],
            "tracked_total": heroes_with_stars,
        }

    def _build_home_context() -> dict[str, Any]:
        featured_heroes = sorted(
            [hero for hero in heroes if str(hero.get("card_image", "")).strip()],
            key=lambda item: (-int(item.get("generation", 0) or 0), str(item.get("name", "")).lower()),
        )[:4]

        latest_generation = max((int(hero.get("generation", 0) or 0) for hero in heroes), default=0)
        compare_candidates = [hero for hero in heroes if str(hero.get("troop_type", "")).strip().lower() == "infantry"]
        compare_candidates = sorted(
            compare_candidates,
            key=lambda item: (-int(item.get("generation", 0) or 0), str(item.get("name", "")).lower()),
        )

        compare_url = "/heroes/compare"
        if len(compare_candidates) >= 2:
            compare_url = (
                f"/heroes/compare?left={compare_candidates[0]['slug']}"
                f"&right={compare_candidates[1]['slug']}"
                "&left_star_points=30&right_star_points=30&left_widget=5&right_widget=5"
            )

        return {
            "featured_heroes": featured_heroes,
            "hero_total": len(heroes),
            "generation_total": len({int(hero.get("generation", 0) or 0) for hero in heroes if int(hero.get("generation", 0) or 0) > 0}),
            "latest_generation": latest_generation,
            "compare_url": compare_url,
            "discord_invite_url": DISCORD_BOT_INVITE_URL,
            "registered_alliances": _list_alliances_with_member_counts(),
        }

    @app.get("/")
    def home_page() -> Any:
        return render_template(
            "home.html", notice=session.pop("notice", None), error=session.pop("error", None), **_build_home_context()
        )

    @app.get("/home")
    def landing_page() -> Any:
        return render_template(
            "home.html", notice=session.pop("notice", None), error=session.pop("error", None), **_build_home_context()
        )

    @app.get("/discord-login")
    def discord_login() -> Any:
        if not DISCORD_OAUTH_CLIENT_SECRET:
            _set_error("Discord login is not configured on this server yet.")
            return redirect(url_for("alliance_page"))

        post_login_next = _sanitize_post_login_next(request.args.get("next"))
        if post_login_next:
            session["oauth_next_url"] = post_login_next
        else:
            session.pop("oauth_next_url", None)

        sync_input = str(request.args.get("sync_jeabs_id", "")).strip()
        if sync_input:
            normalized_sync_id = str(_normalize_jeabs_alliance_input(sync_input).get("alliance_id") or "").strip()
            if normalized_sync_id:
                session["oauth_sync_jeabs_id"] = normalized_sync_id
            else:
                session.pop("oauth_sync_jeabs_id", None)
        else:
            session.pop("oauth_sync_jeabs_id", None)

        state = secrets.token_urlsafe(24)
        session["oauth_state"] = state
        params = {
            "client_id": DISCORD_OAUTH_CLIENT_ID,
            "redirect_uri": DISCORD_OAUTH_REDIRECT_URI,
            "response_type": "code",
            "scope": "identify",
            "state": state,
            "prompt": "consent",
        }
        return redirect(f"{DISCORD_OAUTH_AUTHORIZE_URL}?{urlencode(params)}")

    @app.post("/auth/email/request")
    def request_email_auth_code() -> Any:
        if not _valid_auth_csrf():
            return jsonify({"ok": False, "message": "Your session expired. Refresh and try again."}), 403

        payload = request.get_json(silent=True) or request.form
        purpose = str(payload.get("purpose") or "login").strip().lower()
        current_user = _get_current_user()
        if purpose == "link" and not current_user:
            return jsonify({"ok": False, "message": "Sign in before linking an email."}), 401
        if purpose not in {"login", "link"}:
            return jsonify({"ok": False, "message": "Invalid verification request."}), 400

        try:
            email = normalize_email(payload.get("email"))
            settings = _smtp_settings()
            if not settings.configured:
                raise EmailDeliveryError("Email delivery is not configured")
            with _get_db_connection() as connection:
                code = create_email_challenge(
                    connection,
                    email=email,
                    purpose=purpose,
                    target_user_id=int(current_user["id"]) if current_user and purpose == "link" else None,
                    request_ip=str(request.remote_addr or "unknown"),
                    secret_key=str(app.config["SECRET_KEY"]),
                )
            send_verification_email(settings, email, code)
        except ValueError:
            return jsonify({"ok": False, "message": "Enter a valid email address."}), 400
        except EmailRateLimitError:
            return jsonify({"ok": False, "message": "Please wait before requesting another code."}), 429
        except EmailDeliveryError:
            if "email" in locals():
                with _get_db_connection() as connection:
                    connection.execute(
                        """
                        DELETE FROM email_auth_challenges
                        WHERE id = (
                            SELECT id FROM email_auth_challenges
                            WHERE email_normalized = ? AND purpose = ? AND used_at IS NULL
                            ORDER BY id DESC LIMIT 1
                        )
                        """,
                        (email, purpose),
                    )
            app.logger.exception("Verification email delivery failed")
            return jsonify({"ok": False, "message": "Email could not be sent. Please try again later."}), 503
        except EmailAuthError:
            return jsonify({"ok": False, "message": "Verification could not be started."}), 400

        session["pending_email"] = email
        session["pending_email_purpose"] = purpose
        return jsonify({"ok": True, "message": "If delivery is available, the code is on its way."})

    @app.post("/auth/email/verify")
    def verify_email_auth_code() -> Any:
        if not _valid_auth_csrf():
            return jsonify({"ok": False, "message": "Your session expired. Refresh and try again."}), 403

        payload = request.get_json(silent=True) or request.form
        purpose = str(session.get("pending_email_purpose") or payload.get("purpose") or "login").strip().lower()
        current_user = _get_current_user()
        target_user_id = int(current_user["id"]) if current_user and purpose == "link" else None
        try:
            email = normalize_email(payload.get("email") or session.get("pending_email"))
            with _get_db_connection() as connection:
                valid = consume_email_challenge(
                    connection,
                    email=email,
                    code=str(payload.get("code") or ""),
                    purpose=purpose,
                    target_user_id=target_user_id,
                    secret_key=str(app.config["SECRET_KEY"]),
                )
        except ValueError:
            valid = False

        if not valid:
            return jsonify({"ok": False, "message": "The code is invalid or has expired."}), 401

        if purpose == "link":
            if not current_user:
                return jsonify({"ok": False, "message": "Sign in again before linking an email."}), 401
            if not _link_email_identity(int(current_user["id"]), email):
                return jsonify({"ok": False, "message": "That email belongs to another account."}), 409
            session.pop("pending_email", None)
            session.pop("pending_email_purpose", None)
            return jsonify({"ok": True, "message": "Email linked successfully.", "redirect": request.referrer or "/alliance"})

        session["pending_verified_email"] = email
        session.pop("pending_email", None)
        session.pop("pending_email_purpose", None)
        return jsonify({"ok": True, "message": "Email verified. Enter your Game ID.", "requires_game_id": True})

    @app.post("/auth/email/complete")
    def complete_email_auth() -> Any:
        if not _valid_auth_csrf():
            return jsonify({"ok": False, "message": "Your session expired. Refresh and try again."}), 403

        email = session.get("pending_verified_email")
        if not email:
            return jsonify({"ok": False, "message": "Verify your email again first."}), 401
        payload = request.get_json(silent=True) or request.form
        try:
            user = _complete_email_login_by_game_id(str(email), str(payload.get("game_id") or ""))
        except ValueError as exc:
            return jsonify({"ok": False, "message": str(exc)}), 400

        _start_authenticated_session(user, "email")
        alliance = _get_current_alliance_for_user(user)
        alliance_key = _alliance_url_key(alliance)
        redirect_url = (
            url_for("alliance_page_by_tag", tag=alliance_key, tab="my-profile")
            if alliance_key
            else url_for("alliance_page")
        )
        return jsonify({"ok": True, "message": "Signed in successfully.", "redirect": redirect_url})

    @app.get("/discord-login/callback")
    def discord_login_callback() -> Any:
        if request.args.get("error"):
            _set_error("Discord login was cancelled.")
            return redirect(url_for("alliance_page"))

        code = request.args.get("code")
        state = request.args.get("state")
        expected_state = session.pop("oauth_state", None)
        if not code or not state or not expected_state or state != expected_state:
            _set_error("Login could not be verified. Please try again.")
            return redirect(url_for("alliance_page"))

        if not DISCORD_OAUTH_CLIENT_SECRET:
            _set_error("Discord login is not configured on this server yet.")
            return redirect(url_for("alliance_page"))

        try:
            token_response = requests.post(
                DISCORD_OAUTH_TOKEN_URL,
                data={
                    "client_id": DISCORD_OAUTH_CLIENT_ID,
                    "client_secret": DISCORD_OAUTH_CLIENT_SECRET,
                    "grant_type": "authorization_code",
                    "code": code,
                    "redirect_uri": DISCORD_OAUTH_REDIRECT_URI,
                },
                headers={"Content-Type": "application/x-www-form-urlencoded"},
                timeout=10,
            )
            token_response.raise_for_status()
            access_token = token_response.json().get("access_token")
            if not access_token:
                raise ValueError("Missing access_token in Discord response.")

            user_response = requests.get(
                DISCORD_API_USERS_ME_URL,
                headers={"Authorization": f"Bearer {access_token}"},
                timeout=10,
            )
            user_response.raise_for_status()
            profile = user_response.json()
        except (requests.RequestException, ValueError):
            _set_error("Discord login failed. Please try again.")
            return redirect(url_for("alliance_page"))

        discord_user_id = str(profile.get("id") or "").strip()
        if not discord_user_id:
            _set_error("Could not verify your Discord account. Please try again.")
            return redirect(url_for("alliance_page"))

        username = str(profile.get("global_name") or profile.get("username") or "Discord User").strip() or "Discord User"
        avatar_hash = profile.get("avatar")
        avatar_url = None
        if avatar_hash:
            ext = "gif" if str(avatar_hash).startswith("a_") else "png"
            avatar_url = f"https://cdn.discordapp.com/avatars/{discord_user_id}/{avatar_hash}.{ext}"

        user = _ensure_user_record(discord_user_id, username, avatar_url)
        pending_oauth_values = {
            key: session.get(key)
            for key in (
                "pending_join_alliance_id",
                "pending_join_invite_link_id",
                "oauth_next_url",
                "oauth_sync_jeabs_id",
            )
            if session.get(key) is not None
        }
        _start_authenticated_session(user, "discord")
        session.update(pending_oauth_values)
        session["discord_user_id"] = discord_user_id
        session["discord_username"] = username
        session["discord_avatar"] = avatar_url or ""

        pending_alliance_id = session.pop("pending_join_alliance_id", None)
        pending_invite_link_id = _parse_loose_int(session.pop("pending_join_invite_link_id", None), 0)
        if pending_alliance_id:
            _process_join_request(
                user,
                int(pending_alliance_id),
                invite_link_id=pending_invite_link_id if pending_invite_link_id > 0 else None,
            )
            return _redirect_to_alliance_dashboard(user, tab="my-profile")

        post_login_next = _sanitize_post_login_next(session.pop("oauth_next_url", ""))
        sync_jeabs_id = str(session.pop("oauth_sync_jeabs_id", "") or "").strip()
        if post_login_next:
            if sync_jeabs_id:
                separator = "&" if "?" in post_login_next else "?"
                encoded_sync_id = quote(sync_jeabs_id, safe="")
                post_login_next = f"{post_login_next}{separator}auto_sync=1&sync_jeabs_id={encoded_sync_id}"
            return redirect(post_login_next)

        return _redirect_to_alliance_dashboard(user)

    @app.get("/logout")
    def logout() -> Any:
        session.clear()
        return redirect(url_for("alliance_page"))

    def _build_alliance_dashboard_context(
        user: dict[str, Any] | None,
        alliance: dict[str, Any] | None,
        selected_user_id: int | None = None,
        player_list_filters: dict[str, Any] | None = None,
        active_tab: str = "player-list",
        swordland_slot: int = 1,
        selected_profile_id: int = 0,
    ) -> dict[str, Any]:
        members: list[dict[str, Any]] = []
        ac_roster: list[dict[str, Any]] = []
        filter_payload = player_list_filters or {}
        sort_by = str(filter_payload.get("sort_by") or "score").strip().lower()
        if sort_by not in {"score", "power", "lvl", "kills", "mystic", "radiant_spire", "power_ac", "name"}:
            sort_by = "score"
        sort_dir = str(filter_payload.get("sort_dir") or "desc").strip().lower()
        if sort_dir not in {"asc", "desc"}:
            sort_dir = "desc"
        search_query = str(filter_payload.get("search") or "").strip()
        min_power = max(0, _parse_total_power(filter_payload.get("min_power"), 0))
        min_kills = max(0, _parse_loose_int(filter_payload.get("min_kills"), 0))
        min_mystic = max(0, _parse_loose_int(filter_payload.get("min_mystic"), 0))
        min_radiant_spire = max(0, _parse_loose_int(filter_payload.get("min_radiant_spire"), 0))
        min_power_ac = max(0, _parse_loose_int(filter_payload.get("min_power_ac"), 0))
        min_level = max(0, _parse_town_hall_level(filter_payload.get("min_level"), 0))
        diff_window_days = _parse_loose_int(filter_payload.get("diff_window"), 7)
        if diff_window_days not in (7, 14, 30):
            diff_window_days = 7
        if alliance:
            with _get_db_connection() as connection:
                member_rows = connection.execute(
                    """
                    SELECT
                        alliance_users.id AS user_id,
                        alliance_users.username AS discord_username,
                        alliance_users.discord_user_id AS discord_user_id,
                        alliance_users.avatar_url AS member_avatar_url,
                        alliance_users.is_admin AS is_admin,
                        alliance_players.*
                    FROM alliance_users
                    LEFT JOIN alliance_players
                        ON alliance_players.alliance_id = alliance_users.alliance_id
                        AND alliance_players.user_id = alliance_users.id
                    WHERE alliance_users.alliance_id = ?
                    ORDER BY (alliance_players.total_power IS NULL) ASC, alliance_players.total_power DESC, alliance_players.player_name ASC, alliance_users.username ASC
                    """,
                    (alliance["id"],),
                ).fetchall()
                previous_snapshot_rows = connection.execute(
                    """
                    SELECT * FROM alliance_player_snapshots
                    WHERE alliance_id = ? AND created_at >= ?
                    ORDER BY player_id ASC, id ASC
                    """,
                    (alliance["id"], (datetime.now(timezone.utc) - timedelta(days=diff_window_days)).isoformat()),
                ).fetchall()
            # Snapshots within the selected diff window, oldest first, grouped per player —
            # used to find each metric's baseline (see below), not just the latest snapshot.
            snapshots_by_player: dict[int, list[dict[str, Any]]] = {}
            for snapshot in previous_snapshot_rows:
                if snapshot["player_id"] is None:
                    continue
                snapshots_by_player.setdefault(int(snapshot["player_id"]), []).append(dict(snapshot))

            for row in member_rows:
                member = dict(row)
                player_id = member.get("id")
                player_snapshots = snapshots_by_player.get(int(player_id), []) if player_id is not None else []

                # Baseline = earliest snapshot in the last 7 days where the metric was
                # already non-zero (real data), never the just-registered zero state.
                # This also means the very first registration never counts as a "gain".
                combat_baseline = None
                for snapshot in player_snapshots:
                    combined = sum(_as_float(snapshot.get(field)) for field in PLAYER_COMBAT_STAT_FIELDS)
                    if abs(combined) > 0.0001:
                        combat_baseline = snapshot
                        break

                power_baseline = None
                for snapshot in player_snapshots:
                    if _as_float(snapshot.get("total_power")) > 0.0001:
                        power_baseline = snapshot
                        break

                member_combat_score = 0.0
                baseline_combat_score = 0.0
                for stat_field in PLAYER_COMBAT_STAT_FIELDS:
                    member_value = _as_float(member.get(stat_field))
                    member_combat_score += member_value

                    delta_key = f"{stat_field}_delta"
                    if combat_baseline is None:
                        member[delta_key] = None
                        continue

                    baseline_value = _as_float(combat_baseline.get(stat_field))
                    baseline_combat_score += baseline_value
                    member[delta_key] = member_value - baseline_value

                member["combat_score"] = int(round(member_combat_score)) if player_id is not None else None
                if combat_baseline is None:
                    member["combat_score_delta"] = None
                else:
                    member["combat_score_delta"] = member_combat_score - baseline_combat_score

                current_power = _as_float(member.get("total_power"))
                if power_baseline is None:
                    member["total_power_delta"] = None
                else:
                    member["total_power_delta"] = current_power - _as_float(power_baseline.get("total_power"))

                member["level_label"] = _format_town_hall_level(member.get("town_hall_level"))
                member["level_sort_key"] = _parse_town_hall_level(member.get("town_hall_level"), 30)
                troop_grade = _town_hall_to_troop_grade(member.get("town_hall_level"))
                if not troop_grade:
                    troop_grade = (
                        _extract_troop_grade_from_text(member.get("infantry_troops"))
                        or _extract_troop_grade_from_text(member.get("cavalry_troops"))
                        or _extract_troop_grade_from_text(member.get("archer_troops"))
                    )
                member["troop_grade"] = troop_grade or "—"
                member["kills"] = _parse_loose_int(member.get("kills"), 0)
                member["mystic_score"] = _parse_loose_int(member.get("mystic_score"), 0)
                member["power_ac"] = _parse_loose_int(member.get("power_ac"), 0)
                member["hero_overview"] = _build_member_hero_overview(member)
                member["bear_trap_config"] = _parse_bear_trap_config(member.get("bear_trap_config_json"))
                member["bear_missing_stats"] = _get_bear_missing_stats(member["bear_trap_config"])
                member["bear_trap"] = _calculate_bear_trap_result(member)

                members.append(member)

            profiled_members = [member for member in members if member.get("id") is not None]
            profiled_game_ids = {
                str(member.get("game_id") or "").strip()
                for member in profiled_members
                if str(member.get("game_id") or "").strip()
            }

            def _is_shadow_duplicate_member(member_row: dict[str, Any]) -> bool:
                if member_row.get("id") is not None:
                    return False
                synthetic_game_id = _extract_game_id_from_synthetic_discord_user_id(member_row.get("discord_user_id"))
                if not synthetic_game_id:
                    return False
                return synthetic_game_id in profiled_game_ids

            members = [member for member in members if not _is_shadow_duplicate_member(member)]
            ac_roster = sorted(
                [member for member in members if member.get("id") is not None],
                key=lambda member: (
                    -_parse_loose_int(member.get("power_ac"), 0),
                    str(member.get("player_name") or member.get("discord_username") or "").casefold(),
                ),
            )

            if search_query:
                lowered_query = search_query.lower()

                def _match_member(member_row: dict[str, Any]) -> bool:
                    haystack = " ".join(
                        [
                            str(member_row.get("player_name") or ""),
                            str(member_row.get("discord_username") or ""),
                            str(member_row.get("game_id") or ""),
                        ]
                    ).lower()
                    return lowered_query in haystack

                members = [member for member in members if _match_member(member)]

            if min_power > 0:
                members = [member for member in members if _parse_total_power(member.get("total_power"), 0) >= min_power]
            if min_kills > 0:
                members = [member for member in members if _parse_loose_int(member.get("kills"), 0) >= min_kills]
            if min_mystic > 0:
                members = [member for member in members if _parse_loose_int(member.get("mystic_score"), 0) >= min_mystic]
            if min_radiant_spire > 0:
                members = [member for member in members if _parse_loose_int(member.get("radiant_spire"), 0) >= min_radiant_spire]
            if min_power_ac > 0:
                members = [member for member in members if _parse_loose_int(member.get("power_ac"), 0) >= min_power_ac]
            if min_level > 0:
                members = [member for member in members if _parse_town_hall_level(member.get("town_hall_level"), 0) >= min_level]

            sort_extractors: dict[str, Any] = {
                "score": lambda item: int(item.get("combat_score") or 0),
                "power": lambda item: int(_parse_total_power(item.get("total_power"), 0)),
                "lvl": lambda item: int(_parse_town_hall_level(item.get("town_hall_level"), 0)),
                "kills": lambda item: int(_parse_loose_int(item.get("kills"), 0)),
                "mystic": lambda item: int(_parse_loose_int(item.get("mystic_score"), 0)),
                "radiant_spire": lambda item: int(_parse_loose_int(item.get("radiant_spire"), 0)),
                "power_ac": lambda item: _parse_loose_int(item.get("power_ac"), 0),
                "name": lambda item: str(item.get("player_name") or item.get("discord_username") or "").lower(),
            }
            sort_key = sort_extractors.get(sort_by, sort_extractors["score"])
            members.sort(
                key=lambda item: (
                    sort_key(item),
                    str(item.get("player_name") or item.get("discord_username") or "").lower(),
                ),
                reverse=sort_dir == "desc",
            )

        editable_user_id = int(user["id"]) if user else None
        if user and alliance and user.get("is_admin") and selected_user_id:
            member_user_ids = {int(member["user_id"]) for member in members if member.get("user_id") is not None}
            if int(selected_user_id) in member_user_ids:
                editable_user_id = int(selected_user_id)

        editable_member = None
        if editable_user_id is not None:
            editable_member = next(
                (member for member in members if int(member.get("user_id") or 0) == int(editable_user_id)),
                None,
            )

        requested_profile_id = _parse_loose_int(request.args.get("profile_id"), 0)
        current_profile = None
        editable_profiles: list[dict[str, Any]] = []
        hero_progress = {}
        if user and alliance and editable_user_id is not None:
            with _get_db_connection() as connection:
                profile_rows = connection.execute(
                    "SELECT * FROM alliance_players WHERE alliance_id = ? AND user_id = ? ORDER BY id ASC",
                    (alliance["id"], editable_user_id),
                ).fetchall()
                editable_profiles = [dict(profile) for profile in profile_rows]
                if selected_profile_id:
                    row = connection.execute(
                        "SELECT * FROM alliance_players WHERE id = ? AND alliance_id = ? AND user_id = ?",
                        (selected_profile_id, alliance["id"], editable_user_id),
                    ).fetchone()
                elif requested_profile_id and editable_user_id == int(user["id"]):
                    row = connection.execute(
                        "SELECT * FROM alliance_players WHERE id = ? AND alliance_id = ? AND user_id = ?",
                        (requested_profile_id, alliance["id"], editable_user_id),
                    ).fetchone()
                else:
                    row = connection.execute(
                        "SELECT * FROM alliance_players WHERE alliance_id = ? AND user_id = ? ORDER BY id ASC LIMIT 1",
                        (alliance["id"], editable_user_id),
                    ).fetchone()
            if row:
                current_profile = dict(row)
                try:
                    hero_progress = json.loads(current_profile.get("hero_data") or "{}")
                except (TypeError, ValueError):
                    hero_progress = {}
                try:
                    current_profile["public_roster"] = json.loads(current_profile.get("public_roster_json") or "{}")
                except (TypeError, ValueError):
                    current_profile["public_roster"] = {}

        requires_game_id_link = False
        own_profile_game_id = ""
        own_profile_count = 0
        if user and alliance:
            with _get_db_connection() as connection:
                own_profile_row = connection.execute(
                    """
                    SELECT id, game_id, COUNT(*) OVER () AS profile_count FROM alliance_players
                    WHERE alliance_id = ? AND user_id = ?
                    ORDER BY id DESC
                    LIMIT 1
                    """,
                    (alliance["id"], int(user["id"])),
                ).fetchone()
            own_profile_game_id = str((own_profile_row["game_id"] if own_profile_row else "") or "").strip()
            own_profile_count = int((own_profile_row["profile_count"] if own_profile_row else 0) or 0)
            requires_game_id_link = not bool(own_profile_game_id)

        hero_progression_choices = _get_hero_progression_choices()
        hero_catalog = []
        for hero in heroes:
            slug = str(hero.get("slug") or _normalize_slug(str(hero.get("name", ""))))
            has_widget = str(hero.get("rarity", "")).strip().lower() == "legendary"
            selected_values = hero_progress.get(slug, {}) if isinstance(hero_progress, dict) else {}
            star_points = _clamp_int(selected_values.get("stars"), minimum=1, maximum=30, default=1)
            hero_catalog.append(
                {
                    "slug": slug,
                    "name": str(hero.get("name", "")),
                    "image": hero.get("card_image") or "/static/favicon.webp",
                    "has_widget": has_widget,
                    "progression": hero_progression_choices,
                    "selected": {
                        "stars": star_points,
                        "widget": str(selected_values.get("widget", "")) if has_widget else "",
                        "skill": str(selected_values.get("skill", "")),
                    },
                }
            )

        own_bear_member = max(
            (
                member for member in members
                if user and int(member.get("user_id") or 0) == int(user["id"])
            ),
            key=lambda member: int(member.get("id") or 0),
            default=None,
        )
        own_bear_heroes: list[dict[str, Any]] = []
        if own_bear_member:
            own_bear_member["bear_trap"] = _calculate_bear_trap_result(own_bear_member, BEAR_MONTE_CARLO_RUNS)
            own_bear_heroes = [
                {"id": hero_id, "label": hero_id.replace("-", " ").title()}
                for hero_id in (
                    "amadeus", "helga", "zoe",
                    "petra", "hilde", "margot", "thrud",
                    "marlin", "rosa", "yang",
                )
            ]
            own_bear_heroes.sort(key=lambda hero: hero["label"].casefold())

        pending_join_requests: list[dict[str, Any]] = []
        accepted_join_requests: list[dict[str, Any]] = []
        invite_link_registered_users: list[dict[str, Any]] = []
        invite_link_url: str | None = None
        roster_forms: list[dict[str, Any]] = []
        roster_suggestions: list[dict[str, Any]] = []
        if alliance and user and user.get("is_admin"):
            with _get_db_connection() as connection:
                request_rows = connection.execute(
                    """
                    SELECT alliance_join_requests.*, alliance_users.username, alliance_users.discord_user_id
                    FROM alliance_join_requests
                    JOIN alliance_users ON alliance_users.id = alliance_join_requests.user_id
                    WHERE alliance_join_requests.alliance_id = ? AND alliance_join_requests.status = 'pending'
                    ORDER BY alliance_join_requests.created_at ASC
                    """,
                    (alliance["id"],),
                ).fetchall()
                accepted_request_rows = connection.execute(
                    """
                    SELECT req.*, alliance_users.id AS member_user_id, alliance_users.username, alliance_users.discord_user_id, alliance_users.is_admin
                    FROM alliance_users
                    LEFT JOIN (
                        SELECT req.*
                        FROM alliance_join_requests AS req
                        JOIN (
                            SELECT user_id, MAX(id) AS latest_id
                            FROM alliance_join_requests
                            WHERE alliance_id = ? AND status = 'accepted'
                            GROUP BY user_id
                        ) AS latest ON latest.latest_id = req.id
                    ) AS req ON req.user_id = alliance_users.id
                    WHERE alliance_users.alliance_id = ?
                    ORDER BY COALESCE(req.updated_at, alliance_users.updated_at) DESC
                    LIMIT 50
                    """,
                    (alliance["id"], alliance["id"]),
                ).fetchall()
                invite_link_registered_rows = connection.execute(
                    """
                    SELECT req.*, alliance_users.username, alliance_users.discord_user_id, alliance_users.is_admin
                    FROM alliance_join_requests AS req
                    JOIN alliance_users ON alliance_users.id = req.user_id
                    JOIN (
                        SELECT user_id, MAX(id) AS latest_id
                        FROM alliance_join_requests
                        WHERE alliance_id = ?
                          AND status = 'pending'
                          AND (invite_link_id IS NOT NULL OR invite_link_token IS NOT NULL)
                        GROUP BY user_id
                    ) AS latest ON latest.latest_id = req.id
                    WHERE req.alliance_id = ?
                    ORDER BY req.updated_at DESC
                    """,
                    (alliance["id"], alliance["id"]),
                ).fetchall()
                invite_link_row = connection.execute(
                    """
                    SELECT token FROM alliance_invite_links
                    WHERE alliance_id = ? AND status = 'active'
                    ORDER BY id DESC
                    LIMIT 1
                    """,
                    (alliance["id"],),
                ).fetchone()
                roster_form_rows = connection.execute(
                    """
                          SELECT id, token, title, form_type, target_scope, target_list_json,
                              status, created_at, updated_at
                    FROM alliance_roster_forms
                    WHERE alliance_id = ?
                    ORDER BY id DESC
                    """,
                    (alliance["id"],),
                ).fetchall()
                roster_player_rows = connection.execute(
                    """
                    SELECT alliance_players.id AS player_id,
                           alliance_players.player_name,
                           alliance_players.game_id,
                           alliance_users.username
                    FROM alliance_players
                    LEFT JOIN alliance_users ON alliance_users.id = alliance_players.user_id
                    WHERE alliance_players.alliance_id = ?
                      AND alliance_players.game_id IS NOT NULL
                      AND alliance_players.game_id != ''
                    ORDER BY COALESCE(alliance_players.player_name, alliance_users.username) COLLATE NOCASE
                    """,
                    (alliance["id"],),
                ).fetchall()
                roster_submission_rows = connection.execute(
                    """
                    SELECT submissions.roster_form_id, submissions.player_id,
                           players.game_id, submissions.submitted_at
                    FROM alliance_roster_submissions AS submissions
                    JOIN alliance_players AS players ON players.id = submissions.player_id
                    WHERE submissions.alliance_id = ?
                    """,
                    (alliance["id"],),
                ).fetchall()
                transfer_application_rows = connection.execute(
                    """
                    SELECT roster_form_id, game_id, player_name, submitted_at
                    FROM alliance_transfer_applications
                    WHERE alliance_id = ?
                    ORDER BY submitted_at DESC
                    """,
                    (alliance["id"],),
                ).fetchall()
                roster_suggestion_rows = connection.execute(
                    """
                    SELECT suggestions.id, suggestions.note, suggestions.submitted_at,
                           alliance_players.player_name,
                           alliance_users.username,
                           COALESCE(alliance_roster_forms.title, 'Legacy roster form') AS form_title
                    FROM alliance_roster_suggestions AS suggestions
                    LEFT JOIN alliance_players ON alliance_players.id = suggestions.player_id
                    LEFT JOIN alliance_users ON alliance_users.id = suggestions.user_id
                    LEFT JOIN alliance_roster_forms ON alliance_roster_forms.id = suggestions.roster_form_id
                    WHERE suggestions.alliance_id = ?
                    ORDER BY suggestions.submitted_at DESC, suggestions.id DESC
                    """,
                    (alliance["id"],),
                ).fetchall()
            pending_join_requests = [dict(row) for row in request_rows]
            accepted_join_requests = [dict(row) for row in accepted_request_rows]
            for accepted in accepted_join_requests:
                accepted["user_id"] = accepted.get("member_user_id") or accepted.get("user_id")
            invite_link_registered_users = [dict(row) for row in invite_link_registered_rows]
            if invite_link_row and invite_link_row["token"]:
                invite_link_url = (
                    f"{PUBLIC_SITE_URL}/alliance/invite/{invite_link_row['token']}"
                    f"?v={_alliance_invite_image_version()}"
                )
            roster_players = [dict(row) for row in roster_player_rows]
            submissions_by_form: dict[int, dict[str, dict[str, Any]]] = {}
            for submission in roster_submission_rows:
                submissions_by_form.setdefault(int(submission["roster_form_id"]), {})[
                    str(submission["game_id"] or "").strip()
                ] = {
                    "player_id": int(submission["player_id"]),
                    "submitted_at": str(submission["submitted_at"] or ""),
                }
            roster_forms = []
            for row in roster_form_rows:
                form = dict(row)
                try:
                    target_entries = json.loads(str(form.get("target_list_json") or "[]"))
                except (TypeError, ValueError):
                    target_entries = []
                form["target_list"] = ", ".join(str(entry) for entry in target_entries)
                if form.get("target_scope") == "custom":
                    players_by_game_id = {str(player.get("game_id") or "").strip(): player for player in roster_players}
                    target_players = []
                    seen_targets = set()
                    for entry in target_entries:
                        label = str(entry or "").strip()
                        if not label:
                            continue
                        player = players_by_game_id.get(label)
                        target = dict(player) if player else {
                            "player_id": None,
                            "game_id": label,
                            "player_name": "Unknown player",
                            "username": "",
                        }
                        target_key = str(target.get("game_id") or "").strip()
                        if target_key and target_key not in seen_targets:
                            seen_targets.add(target_key)
                            target_players.append(target)
                else:
                    target_players = roster_players
                if form.get("form_type") == "transfer":
                    applications = [dict(item) for item in transfer_application_rows if int(item["roster_form_id"]) == int(form["id"])]
                    applications_by_game_id = {
                        str(item.get("game_id") or "").strip(): item for item in applications
                    }
                    target_game_ids = {
                        str(player.get("game_id") or "").strip() for player in target_players
                    }
                    form["completed_players"] = [
                        item for game_id, item in applications_by_game_id.items()
                        if form.get("target_scope") != "custom" or game_id in target_game_ids
                    ]
                    form["completed_count"] = len(form["completed_players"])
                    form["pending_players"] = [
                        player for player in target_players
                        if str(player.get("game_id") or "").strip() not in applications_by_game_id
                    ]
                    form["pending_count"] = len(form["pending_players"])
                    form["url"] = f"{PUBLIC_SITE_URL}/transfer-apply/{form['token']}"
                    roster_forms.append(form)
                    continue
                completed_by_game_id = submissions_by_form.get(int(form["id"]), {})
                form["completed_players"] = [
                    {**player, "submitted_at": completed_by_game_id[str(player.get("game_id") or "").strip()]["submitted_at"]}
                    for player in target_players
                    if str(player.get("game_id") or "").strip() in completed_by_game_id
                ]
                form["completed_count"] = len(form["completed_players"])
                form["pending_players"] = [
                    player for player in target_players
                    if str(player.get("game_id") or "").strip() not in completed_by_game_id
                ]
                form["pending_count"] = len(form["pending_players"])
                form["url"] = f"{PUBLIC_SITE_URL}/roster-update/{form['token']}"
                roster_forms.append(form)
            roster_suggestions = [dict(row) for row in roster_suggestion_rows]

        return {
            "members": members,
            "ac_roster": ac_roster,
            "ac_plan": json.loads(str(alliance.get("ac_plan_json") or "{}")) if alliance else {},
            "current_profile": current_profile,
            "editable_profiles": editable_profiles,
            "has_secondary_profile": own_profile_count > 1,
            "own_profile_count": own_profile_count,
            "current_profile_id": int(current_profile["id"]) if current_profile else 0,
            "editable_user_id": editable_user_id,
            "editable_member": editable_member,
            "heroes": hero_catalog,
            "own_bear_member": own_bear_member,
            "own_bear_heroes": own_bear_heroes,
            "can_access_bear_calculator": _can_access_bear_calculator(user),
            "can_access_usage_stats": _can_access_usage_stats(user),
            "usage_stats": _build_usage_stats_context() if active_tab == "stats" and _can_access_usage_stats(user) else None,
            "pending_join_requests": pending_join_requests,
            "accepted_join_requests": accepted_join_requests,
            "invite_link_registered_users": invite_link_registered_users,
            "invite_link_url": invite_link_url,
            "roster_forms": roster_forms,
            "roster_suggestions": roster_suggestions,
            "jeabs_sync_enabled": bool(_get_jeabs_token(alliance)),
            "jeabs_token_configured": bool(str(alliance.get("jeabs_api_token") or "").strip()) if alliance else False,
            "jeabs_alliance_id": str(alliance.get("jeabs_alliance_id") or "") if alliance else "",
            "requires_game_id_link": requires_game_id_link,
            "own_profile_game_id": own_profile_game_id,
            "default_tab": "my-profile" if requires_game_id_link else (active_tab or "player-list"),
            "player_list_filters": {
                "sort_by": sort_by,
                "sort_dir": sort_dir,
                "search": search_query,
                "min_power": _format_whole_number(min_power) if min_power > 0 else "",
                "min_kills": str(min_kills) if min_kills > 0 else "",
                "min_mystic": str(min_mystic) if min_mystic > 0 else "",
                "min_radiant_spire": str(min_radiant_spire) if min_radiant_spire > 0 else "",
                "min_power_ac": _format_whole_number(min_power_ac) if min_power_ac > 0 else "",
                "min_level": str(min_level) if min_level > 0 else "",
                "diff_window": str(diff_window_days),
            },
            "event_key": "kvk" if active_tab == "kvk" else "swordland",
            "event_name": "KVK" if active_tab == "kvk" else "Swordland",
            "swordland": _build_swordland_context(
                alliance,
                members,
                active_tab,
                1 if active_tab == "kvk" else swordland_slot,
                "kvk" if active_tab == "kvk" else "swordland",
            ),
            "nap4": _build_nap4_context(alliance, active_tab),
        }

    def _redirect_to_alliance_dashboard(user: dict[str, Any] | None, **params: Any) -> Any:
        return_to = str(request.form.get("return_to") or request.args.get("return_to") or "").strip()
        if return_to.startswith("/alliance/"):
            return_params = dict(parse_qsl(urlparse(return_to).query, keep_blank_values=True))
            return_params.pop("return_to", None)
            return_params.update(params)
            params = return_params
        alliance = _get_current_alliance_for_user(user) if user else None
        alliance_key = _alliance_url_key(alliance)
        if alliance_key:
            return redirect(url_for("alliance_page_by_tag", tag=alliance_key, **params))
        return redirect(url_for("alliance_page", **params))

    def _get_alliance_by_key(key: str) -> dict[str, Any] | None:
        normalized_key = _normalize_slug(key)
        with _get_db_connection() as connection:
            row = connection.execute(
                "SELECT * FROM alliances WHERE LOWER(tag) = LOWER(?) ORDER BY id DESC LIMIT 1",
                (key,),
            ).fetchone()
            if row:
                return dict(row)

            name_rows = connection.execute("SELECT * FROM alliances ORDER BY id DESC").fetchall()
            for candidate in name_rows:
                candidate_dict = dict(candidate)
                if _normalize_slug(str(candidate_dict.get("name") or "")) == normalized_key:
                    return candidate_dict
        return None

    @app.get("/alliance")
    @app.get("/alliance/")
    def alliance_page() -> str:
        user = _get_current_user()
        alliance = _get_current_alliance_for_user(user) if user else None
        swordland = _build_swordland_context(alliance, []) if alliance else {
            "left_side": None,
            "right_side": None,
            "comparison_rows": [],
            "report": None,
            "rival_id": "",
            "rival_name": "",
            "rival_message": "",
            "has_cache": False,
            "last_synced_at": "",
        }
        nap4 = _build_nap4_context(alliance, "player-list") if alliance else {
            "entries": [
                {"jeabs_id": ""},
                {"jeabs_id": ""},
                {"jeabs_id": ""},
                {"jeabs_id": ""},
            ],
            "alliances": [],
            "general_rows": [],
            "message": "",
            "errors": [],
            "last_synced_at": "",
            "has_cache": False,
        }
        return render_template(
            "alliance.html",
            user=user,
            alliance=alliance,
            alliance_url_key=_alliance_url_key(alliance),
            is_portal_view=True,
            public_alliance=None,
            troop_level_options=TROOP_LEVEL_OPTIONS,
            vip_level_options=VIP_LEVEL_OPTIONS,
            town_hall_level_options=TOWN_HALL_LEVEL_OPTIONS,
            registered_alliances=_list_alliances_with_member_counts(),
            notice=session.pop("notice", None),
            error=session.pop("error", None),
            discord_username=session.get("discord_username"),
            discord_avatar=session.get("discord_avatar"),
            members=[],
            current_profile=None,
            editable_user_id=None,
            editable_member=None,
            heroes=[],
            pending_join_requests=[],
            accepted_join_requests=[],
            invite_link_registered_users=[],
            invite_link_url=None,
            jeabs_sync_enabled=False,
            jeabs_alliance_id="",
            requires_game_id_link=False,
            own_profile_game_id="",
            default_tab="player-list",
            swordland=swordland,
            nap4=nap4,
            player_list_filters={},
        )

    @app.get("/alliance/player-list.xlsx")
    def alliance_player_list_xlsx() -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id"):
            return redirect(url_for("alliance_page"))

        alliance_id = int(user["alliance_id"])
        with _get_db_connection() as connection:
            rows = connection.execute(
                """
                SELECT player_name, town_hall_level, infantry_attack_bonus, infantry_defense_bonus,
                       infantry_lethality_bonus, infantry_health_bonus, cavalry_attack_bonus,
                       cavalry_defense_bonus, cavalry_lethality_bonus, cavalry_health_bonus,
                       archer_attack_bonus, archer_defense_bonus, archer_lethality_bonus,
                       archer_health_bonus, total_power, kills, mystic_score, radiant_spire,
                       bt, bt_time, att_troops, power_ac, public_roster_json,
                       profile_update_source, public_roster_updated_at, updated_at
                FROM alliance_players
                WHERE alliance_id = ?
                ORDER BY player_name COLLATE NOCASE ASC, id ASC
                """,
                (alliance_id,),
            ).fetchall()

        headers = (
            "Player", "LVL", "I.ATT", "I.DEF", "I.LET", "I.HP", "C.ATT", "C.DEF",
            "C.LET", "C.HP", "A.ATT", "A.DEF", "A.LET", "A.HP", "SCORE", "POWER",
            "KILLS", "MYSTIC", "RADIANT SPIRE", "BT", "BTtime", "ATT TROOPS", "POWER AC",
            "ROSTER DATA", "UPDATE SOURCE", "PUBLIC ROSTER UPD", "UPD",
        )
        workbook = Workbook()
        worksheet = workbook.active
        worksheet.title = "Player List"
        worksheet.append(headers)
        for row in rows:
            worksheet.append(tuple(row))
        worksheet.freeze_panes = "A2"
        worksheet.auto_filter.ref = worksheet.dimensions
        for index, header in enumerate(headers, start=1):
            worksheet.column_dimensions[get_column_letter(index)].width = max(12, len(header) + 2)

        output = BytesIO()
        workbook.save(output)
        output.seek(0)
        response = app.make_response(output.getvalue())
        response.headers["Content-Type"] = "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"
        response.headers["Content-Disposition"] = 'attachment; filename="alliance_player_list.xlsx"'
        return response

    def _get_public_roster_alliance(token: str | None = None) -> tuple[dict[str, Any] | None, dict[str, Any] | None]:
        if token:
            with _get_db_connection() as connection:
                row = connection.execute(
                    """
                          SELECT alliance_roster_forms.id AS form_id, alliance_roster_forms.title AS form_title,
                              alliance_roster_forms.schema_json AS form_schema_json,
                              alliance_roster_forms.form_type AS form_type,
                              alliance_roster_forms.token AS form_token,
                           alliances.*
                    FROM alliance_roster_forms
                    JOIN alliances ON alliances.id = alliance_roster_forms.alliance_id
                    WHERE alliance_roster_forms.token = ? AND alliance_roster_forms.status = 'active'
                    LIMIT 1
                    """,
                    (str(token).strip(),),
                ).fetchone()
            if not row:
                return None, None
            data = dict(row)
            return data, {
                "id": data.pop("form_id"), "title": data.pop("form_title"),
                "schema_json": data.pop("form_schema_json"),
                "form_type": data.pop("form_type"),
                "token": data.pop("form_token"),
            }
        if not PUBLIC_ROSTER_ALLIANCE_TAG:
            return None, None
        alliance = _get_alliance_by_key(PUBLIC_ROSTER_ALLIANCE_TAG)
        return (dict(alliance), {"id": None, "title": "Season roster - September 2026"}) if alliance else (None, None)

    def _public_roster_profile(alliance_id: int, game_id: str) -> dict[str, Any] | None:
        with _get_db_connection() as connection:
            row = connection.execute(
                "SELECT * FROM alliance_players WHERE alliance_id = ? AND game_id = ? LIMIT 1",
                (alliance_id, game_id),
            ).fetchone()
        return dict(row) if row else None

    public_roster_heroes = [hero for hero in heroes if hero.get("name") in PUBLIC_ROSTER_HERO_NAMES]
    public_roster_heroes.sort(key=lambda hero: PUBLIC_ROSTER_HERO_NAMES.index(hero["name"]))
    public_roster_expedition_heroes = [
        hero for hero in heroes if hero.get("name") in PUBLIC_ROSTER_EXPEDITION_HERO_NAMES
    ]
    public_roster_expedition_heroes.sort(
        key=lambda hero: PUBLIC_ROSTER_EXPEDITION_HERO_NAMES.index(hero["name"])
    )

    def _roster_form_sections(roster_form: dict[str, Any] | None) -> list[dict[str, Any]]:
        if not roster_form:
            return []
        try:
            schema = json.loads(str(roster_form.get("schema_json") or "{}"))
        except (TypeError, json.JSONDecodeError):
            return []
        sections = schema.get("sections", []) if isinstance(schema, dict) else []
        return sections if isinstance(sections, list) else []

    def _calculate_submitted_march_capacity(values: dict[str, str]) -> str | None:
        calculation_fields = {
            "valora_level", "cassia_level", "bison_level", "march_booster_percent",
        }
        if not calculation_fields.intersection(values):
            return None
        try:
            values["march_capacity_buffed"] = str(calculate_buffed_march_capacity(
                int(values.get("march_capacity_base", "")),
                int(values.get("valora_level", "")),
                int(values.get("cassia_level", "")),
                int(values.get("bison_level", "")),
                int(values.get("march_booster_percent", "")),
            ))
        except (TypeError, ValueError) as exc:
            return str(exc)
        return None

    @app.route("/transfer-apply/<token>", methods=["GET", "POST"])
    def public_transfer_application(token: str) -> Any:
        alliance, roster_form = _get_public_roster_alliance(token)
        if not alliance or not roster_form or roster_form.get("form_type") != "transfer":
            abort(404)
        sections = _roster_form_sections(roster_form)
        values = {
            key: ", ".join(request.form.getlist(key))
            for key in request.form.keys()
        } if request.method == "POST" else {}
        error = None
        submitted = False
        if request.method == "POST":
            capacity_error = _calculate_submitted_march_capacity(values)
            required_names = [
                str(field.get("name") or "")
                for section in sections for field in section.get("fields", [])
                if field.get("required")
            ]
            missing = [name for name in required_names if not values.get(name, "").strip()]
            game_id = values.get("game_id", "").strip()
            if capacity_error:
                error = capacity_error
            elif missing:
                error = "Please answer every required question."
            elif not game_id.isdigit():
                error = "Enter a valid numeric Player ID."
            else:
                now = datetime.now(timezone.utc).isoformat()
                with _get_db_connection() as connection:
                    connection.execute(
                        """
                        INSERT INTO alliance_transfer_applications
                            (alliance_id, roster_form_id, game_id, player_name, payload_json, submitted_at)
                        VALUES (?, ?, ?, ?, ?, ?)
                        ON CONFLICT(roster_form_id, game_id) DO UPDATE SET
                            player_name = excluded.player_name,
                            payload_json = excluded.payload_json,
                            submitted_at = excluded.submitted_at
                        """,
                        (int(alliance["id"]), int(roster_form["id"]), game_id,
                         values.get("player_name", "").strip(), json.dumps(values), now),
                    )
                submitted = True
                values = {}
        return render_template(
            "transfer_application.html", alliance=alliance, roster_form=roster_form,
            sections=sections, values=values, error=error, submitted=submitted,
        ), 400 if error else 200

    @app.post("/forms/<token>/extract-power-breakdown")
    def public_extract_power_breakdown(token: str) -> Any:
        alliance, roster_form = _get_public_roster_alliance(token)
        if not alliance or not roster_form:
            abort(404)
        image_file = request.files.get("image")
        if not image_file or not image_file.filename:
            return jsonify({"ok": False, "message": "Upload a screenshot first."}), 400
        image_bytes = image_file.read()
        if not image_bytes:
            return jsonify({"ok": False, "message": "Uploaded image is empty."}), 400
        if len(image_bytes) > 10 * 1024 * 1024:
            return jsonify({"ok": False, "message": "Image is too large. Max size is 10 MB."}), 400

        from utils.ocr_power_breakdown import extract_power_breakdown

        extraction = extract_power_breakdown(image_bytes)
        if not extraction.get("success"):
            return jsonify({
                "ok": False,
                "message": extraction.get("error") or "Could not read the power screenshot.",
            }), 400
        return jsonify({"ok": True, "fields": extraction["fields"]})

    def _public_roster_template_context(roster_form: dict[str, Any] | None = None) -> dict[str, Any]:
        return {
            "heroes": public_roster_heroes,
            "expedition_heroes": public_roster_expedition_heroes,
            "hero_star_options": PUBLIC_ROSTER_HERO_STAR_OPTIONS,
            "activity_options": PUBLIC_ROSTER_ACTIVITY_OPTIONS,
            "kvk_options": PUBLIC_ROSTER_KVK_OPTIONS,
            "troop_level_options": PUBLIC_ROSTER_TROOP_LEVEL_OPTIONS,
            "town_hall_level_options": PUBLIC_ROSTER_TOWN_HALL_LEVEL_OPTIONS,
            "custom_sections": _roster_form_sections(roster_form),
            "form_token": str(roster_form.get("token") or "") if roster_form else "",
        }

    @app.get("/roster-update")
    @app.get("/roster-update/<token>")
    def public_roster_update(token: str | None = None) -> Any:
        alliance, roster_form = _get_public_roster_alliance(token)
        if not alliance:
            return render_template("public_player_profile.html", configured=False), 503
        game_id = str(request.args.get("game_id") or "").strip()
        profile = _public_roster_profile(int(alliance["id"]), game_id) if game_id else None
        roster_data: dict[str, Any] = {}
        if profile:
            try:
                roster_data = json.loads(profile.get("public_roster_json") or "{}")
            except (TypeError, ValueError):
                roster_data = {}
            for field in ("infantry_troops", "cavalry_troops", "archer_troops", "total_power", "power_ac"):
                roster_data.setdefault(field, str(profile.get(field) or ""))
            roster_data.setdefault("vip_level", f"VIP{profile.get('vip_level')}" if profile.get("vip_level") else "")
            roster_data.setdefault("town_hall_level", _format_town_hall_level(profile.get("town_hall_level")))
            hero_progress = _parse_hero_progress_data(profile.get("hero_data"))
            for hero in public_roster_heroes:
                slug = str(hero.get("slug") or _normalize_slug(str(hero.get("name", ""))))
                saved_hero = hero_progress.get(slug, {})
                roster_data.setdefault(f"hero_{slug}_stars", "I don't have" if saved_hero.get("owned") == "no" else str(saved_hero.get("stars") or ""))
                if slug in {str(item["slug"]) for item in public_roster_expedition_heroes}:
                    roster_data.setdefault(f"expedition_{slug}", str(saved_hero.get("expedition_skill_5") or "no"))
            if roster_form and roster_form.get("id"):
                with _get_db_connection() as connection:
                    prior_submission = connection.execute(
                        "SELECT payload_json FROM alliance_roster_submissions WHERE roster_form_id = ? AND player_id = ?",
                        (int(roster_form["id"]), int(profile["id"])),
                    ).fetchone()
                if prior_submission:
                    try:
                        roster_data.update(json.loads(prior_submission["payload_json"] or "{}"))
                    except (TypeError, json.JSONDecodeError):
                        pass
        return render_template(
            "public_player_profile.html", configured=True, alliance=alliance,
            game_id=game_id, profile=profile, roster_data=roster_data,
            form_title=roster_form["title"] if roster_form else "Alliance roster",
            hero_progress=_parse_hero_progress_data(profile.get("hero_data")) if profile else {},
            submitted=request.args.get("submitted") == "1",
            error="Player ID was not found in this alliance." if game_id and not profile else None,
            **_public_roster_template_context(roster_form),
        )

    @app.post("/roster-update")
    @app.post("/roster-update/<token>")
    def public_roster_save(token: str | None = None) -> Any:
        alliance, roster_form = _get_public_roster_alliance(token)
        if not alliance:
            return render_template("public_player_profile.html", configured=False), 503
        game_id = str(request.form.get("game_id") or "").strip()
        profile = _public_roster_profile(int(alliance["id"]), game_id) if game_id else None
        if not profile:
            return redirect(url_for("public_roster_update", token=token, game_id=game_id))

        submitted_values = {key: str(value) for key, value in request.form.items()}
        custom_sections = _roster_form_sections(roster_form)
        required_fields = ("player_name",) if custom_sections else (
            "player_name", "vip_level", "town_hall_level", "infantry_troops", "cavalry_troops",
            "archer_troops", "total_power", "troops_power", "building_power", "tech_power",
            "governor_power", "hero_power", "pet_power", "power_ac", "mythic_shards",
            "next_upgrades", "daily_activity", "kvk_attendance", "march_capacity_base",
            "march_capacity_buffed", "rally_leader",
        )
        missing = [field for field in required_fields if not str(request.form.get(field) or "").strip()]
        schema_field_names: set[str] = set()
        for section in custom_sections:
            for field in section.get("fields", []):
                schema_field_names.add(str(field.get("name") or ""))
                if field.get("required") and not str(request.form.get(str(field.get("name") or "")) or "").strip():
                    missing.append(str(field.get("name") or "custom_field"))
        capacity_error = _calculate_submitted_march_capacity(submitted_values)
        if capacity_error:
            return render_template(
                "public_player_profile.html", configured=True, alliance=alliance,
                game_id=game_id, profile=profile, roster_data=submitted_values,
                form_title=roster_form["title"] if roster_form else "Alliance roster",
                hero_progress=_parse_hero_progress_data(profile.get("hero_data")),
                submitted=False, error=capacity_error,
                **_public_roster_template_context(roster_form),
            ), 400
        if missing:
            return render_template(
                "public_player_profile.html", configured=True, alliance=alliance,
                game_id=game_id, profile=profile, roster_data=request.form,
                form_title=roster_form["title"] if roster_form else "Alliance roster",
                hero_progress=_parse_hero_progress_data(profile.get("hero_data")),
                submitted=False, error="Please answer every required question.",
                **_public_roster_template_context(roster_form),
            ), 400

        expedition_values = [
            str(request.form.get(f"expedition_{hero['slug']}") or "").strip()
            for hero in public_roster_expedition_heroes
        ]
        expedition_none = str(request.form.get("expedition_none") or "").strip()
        if any(name.startswith("expedition_") for name in schema_field_names) and not any(expedition_values) and not expedition_none:
            return render_template(
                "public_player_profile.html", configured=True, alliance=alliance,
                game_id=game_id, profile=profile, roster_data=request.form,
                form_title=roster_form["title"] if roster_form else "Alliance roster",
                hero_progress=_parse_hero_progress_data(profile.get("hero_data")), submitted=False,
                error="Select at least one expedition hero or None of them.",
                **_public_roster_template_context(roster_form),
            ), 400

        rally_leader = str(request.form.get("rally_leader")).casefold() == "yes"
        if rally_leader and (not request.form.get("rally_capacity_base") or not request.form.get("rally_capacity_buffed")):
            return render_template(
                "public_player_profile.html", configured=True, alliance=alliance,
                game_id=game_id, profile=profile, roster_data=request.form,
                form_title=roster_form["title"] if roster_form else "Alliance roster",
                hero_progress=_parse_hero_progress_data(profile.get("hero_data")), submitted=False,
                error="Rally leaders must provide both rally capacities.",
                **_public_roster_template_context(roster_form),
            ), 400

        hero_progress = _parse_hero_progress_data(profile.get("hero_data"))
        expedition_slugs = {str(hero["slug"]) for hero in public_roster_expedition_heroes}
        for hero in public_roster_heroes:
            slug = str(hero.get("slug") or _normalize_slug(str(hero.get("name", ""))))
            stars = str(request.form.get(f"hero_{slug}_stars") or "").strip()
            if stars not in PUBLIC_ROSTER_HERO_STAR_OPTIONS:
                continue
            current = dict(hero_progress.get(slug) or {})
            current["owned"] = "no" if stars == "I don't have" else "yes"
            current["stars"] = stars
            current["expedition_skill_5"] = "yes" if slug in expedition_slugs and request.form.get(f"expedition_{slug}") else "no"
            hero_progress[slug] = current
        for hero in public_roster_expedition_heroes:
            slug = str(hero["slug"])
            current = dict(hero_progress.get(slug) or {})
            current["expedition_skill_5"] = "yes" if request.form.get(f"expedition_{slug}") else "no"
            hero_progress[slug] = current

        roster_fields = (
            "troops_power", "building_power", "tech_power", "governor_power",
            "hero_power", "pet_power", "mythic_shards", "next_upgrades",
            "daily_activity", "kvk_attendance", "march_capacity_base",
            "march_capacity_buffed", "rally_leader", "rally_capacity_base",
            "rally_capacity_buffed", "valora_level", "cassia_level", "bison_level",
            "march_booster_percent", "notes",
        )
        try:
            roster_data = json.loads(profile.get("public_roster_json") or "{}")
        except (TypeError, json.JSONDecodeError):
            roster_data = {}
        for field in roster_fields:
            if field in submitted_values:
                roster_data[field] = submitted_values[field].strip()
        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            current = connection.execute("SELECT * FROM alliance_players WHERE id = ?", (int(profile["id"]),)).fetchone()
            _insert_player_snapshot_if_not_first_ever(connection, int(alliance["id"]), current, now)
            connection.execute(
                """
                UPDATE alliance_players
                SET player_name = ?, vip_level = ?, town_hall_level = ?, total_power = ?, power_ac = ?,
                    infantry_troops = ?, cavalry_troops = ?, archer_troops = ?, hero_data = ?,
                    public_roster_json = ?, profile_update_source = 'public_roster',
                    public_roster_updated_at = ?, updated_at = ?
                WHERE id = ?
                """,
                (
                    str(request.form.get("player_name") or "").strip(),
                    max(0, min(12, _parse_loose_int(request.form.get("vip_level", profile.get("vip_level")), 0))),
                    _parse_town_hall_level(request.form.get("town_hall_level", profile.get("town_hall_level")), 30),
                    max(0, _parse_total_power(request.form.get("total_power", profile.get("total_power")), 0)),
                    max(0, _parse_loose_int(request.form.get("power_ac", profile.get("power_ac")), 0)),
                    str(request.form.get("infantry_troops", profile.get("infantry_troops") or "")),
                    str(request.form.get("cavalry_troops", profile.get("cavalry_troops") or "")),
                    str(request.form.get("archer_troops", profile.get("archer_troops") or "")), json.dumps(hero_progress),
                    json.dumps(roster_data), now, now, int(profile["id"]),
                ),
            )
            if roster_form and roster_form["id"]:
                connection.execute(
                    """
                    INSERT INTO alliance_roster_submissions
                        (alliance_id, roster_form_id, player_id, user_id, payload_json, submitted_at)
                    VALUES (?, ?, ?, ?, ?, ?)
                    ON CONFLICT(roster_form_id, player_id)
                    DO UPDATE SET user_id = excluded.user_id,
                                  payload_json = excluded.payload_json,
                                  submitted_at = excluded.submitted_at
                    """,
                    (
                        int(alliance["id"]), int(roster_form["id"]),
                        int(profile["id"]), int(profile["user_id"]),
                        json.dumps(submitted_values), now,
                    ),
                )
            if roster_data.get("notes"):
                connection.execute(
                    """
                    INSERT INTO alliance_roster_suggestions
                        (alliance_id, roster_form_id, player_id, user_id, note, submitted_at)
                    VALUES (?, ?, ?, ?, ?, ?)
                    """,
                    (
                        int(alliance["id"]), roster_form["id"] if roster_form else None,
                        int(profile["id"]), int(profile["user_id"]), roster_data["notes"], now,
                    ),
                )
        return redirect(url_for("public_roster_update", token=token, game_id=game_id, submitted=1))

    @app.get("/alliance/<tag>")
    def alliance_page_by_tag(tag: str) -> str:
        target_alliance = _get_alliance_by_key(tag)
        if not target_alliance:
            _set_error("That alliance was not found.")
            return redirect(url_for("alliance_page"))

        user = _get_current_user()
        user_alliance = _get_current_alliance_for_user(user) if user else None

        if user_alliance and int(user_alliance["id"]) == int(target_alliance["id"]):
            active_tab = str(request.args.get("tab", "player-list") or "player-list").strip().lower()
            valid_profile_tabs = {"my-profile"} | {f"my-profile-{number}" for number in range(2, 100)}
            if active_tab not in ({"player-list", "admin", "forms", "suggestions", "ac", "swordland", "kvk", "bear-calculator", "nap4", "stats"} | valid_profile_tabs):
                active_tab = "player-list"
            if active_tab == "player-list" and not user.get("is_admin"):
                active_tab = "my-profile"
            if active_tab == "ac" and not user.get("is_admin"):
                active_tab = "my-profile"
            if active_tab == "bear-calculator" and not _can_access_bear_calculator(user):
                active_tab = "player-list"
            if active_tab == "stats" and not _can_access_usage_stats(user):
                active_tab = "my-profile"
            swordland_slot = 2 if _parse_loose_int(request.args.get("swordland_slot"), 1) == 2 else 1
            selected_user_id = None
            selected_profile_id = _parse_loose_int(request.args.get("profile_id"), 0)
            if user and user.get("is_admin"):
                selected_user_id = _parse_loose_int(request.args.get("edit_user_id"), 0)
                if selected_user_id <= 0:
                    selected_user_id = None
            player_list_filters = {
                "sort_by": request.args.get("sort_by", "score"),
                "sort_dir": request.args.get("sort_dir", "desc"),
                "search": request.args.get("search", ""),
                "min_power": request.args.get("min_power", ""),
                "min_kills": request.args.get("min_kills", ""),
                "min_mystic": request.args.get("min_mystic", ""),
                "min_radiant_spire": request.args.get("min_radiant_spire", ""),
                "min_power_ac": request.args.get("min_power_ac", ""),
                "min_level": request.args.get("min_level", ""),
                "diff_window": request.args.get("diff_window", "7"),
            }
            dashboard = _build_alliance_dashboard_context(user, user_alliance, selected_user_id, player_list_filters, active_tab, swordland_slot, selected_profile_id)
            return render_template(
                "alliance.html",
                user=user,
                alliance=user_alliance,
                alliance_url_key=_alliance_url_key(user_alliance),
                is_portal_view=False,
                public_alliance=None,
                troop_level_options=TROOP_LEVEL_OPTIONS,
                vip_level_options=VIP_LEVEL_OPTIONS,
                town_hall_level_options=TOWN_HALL_LEVEL_OPTIONS,
                registered_alliances=_list_alliances_with_member_counts(),
                notice=session.pop("notice", None),
                error=session.pop("error", None),
                discord_username=session.get("discord_username"),
                discord_avatar=session.get("discord_avatar"),
                **dashboard,
            )

        with _get_db_connection() as connection:
            member_count_row = connection.execute(
                "SELECT COUNT(*) FROM alliance_users WHERE alliance_id = ?",
                (target_alliance["id"],),
            ).fetchone()
        target_alliance["member_count"] = member_count_row[0] if member_count_row else 0

        return render_template(
            "alliance.html",
            user=user,
            alliance=None,
            alliance_url_key="",
            is_portal_view=False,
            public_alliance=target_alliance,
            members=[],
            current_profile=None,
            heroes=[],
            troop_level_options=TROOP_LEVEL_OPTIONS,
            vip_level_options=VIP_LEVEL_OPTIONS,
            town_hall_level_options=TOWN_HALL_LEVEL_OPTIONS,
            pending_join_requests=[],
            accepted_join_requests=[],
            invite_link_registered_users=[],
            invite_link_url=None,
            jeabs_sync_enabled=False,
            jeabs_alliance_id="",
            requires_game_id_link=False,
            own_profile_game_id="",
            default_tab="player-list",
            registered_alliances=[],
            swordland={
                "left_side": None,
                "right_side": None,
                "comparison_rows": [],
                "report": None,
                "rival_id": "",
                "rival_name": "",
                "rival_message": "",
                "has_cache": False,
                "last_synced_at": "",
            },
            nap4={
                "entries": [
                    {"jeabs_id": ""},
                    {"jeabs_id": ""},
                    {"jeabs_id": ""},
                    {"jeabs_id": ""},
                ],
                "alliances": [],
                "general_rows": [],
                "message": "",
                "errors": [],
                "last_synced_at": "",
                "has_cache": False,
            },
            notice=session.pop("notice", None),
            error=session.pop("error", None),
            discord_username=session.get("discord_username"),
            discord_avatar=session.get("discord_avatar"),
        )

    @app.get("/alliance/invite/<token>")
    def alliance_invite_link(token: str) -> Any:
        with _get_db_connection() as connection:
            row = connection.execute(
                """
                SELECT alliance_invite_links.id, alliance_invite_links.alliance_id,
                       alliances.name, alliances.tag
                FROM alliance_invite_links
                JOIN alliances ON alliances.id = alliance_invite_links.alliance_id
                WHERE alliance_invite_links.token = ? AND alliance_invite_links.status = 'active'
                ORDER BY alliance_invite_links.id DESC
                LIMIT 1
                """,
                (str(token).strip(),),
            ).fetchone()
        if not row:
            _set_error("That invite link is invalid or expired.")
            return redirect(url_for("alliance_page"))
        continue_url = url_for(
            "alliance_join",
            alliance_id=int(row["alliance_id"]),
            invite_link_id=int(row["id"]),
        )
        invite_image_version = _alliance_invite_image_version()
        return render_template(
            "alliance_invite.html",
            alliance=dict(row),
            continue_url=continue_url,
            invite_url=f"{PUBLIC_SITE_URL}{request.path}",
            invite_image_url=_alliance_invite_image_url(),
        )

    @app.post("/alliance/invite-link/create")
    def alliance_invite_link_create() -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            _set_error("Only the alliance admin can generate invite links.")
            return _redirect_to_alliance_dashboard(user)

        alliance_id = int(user["alliance_id"])
        now = datetime.now(timezone.utc).isoformat()
        token = secrets.token_urlsafe(24)
        with _get_db_connection() as connection:
            connection.execute(
                "UPDATE alliance_invite_links SET status = 'revoked', revoked_at = ? WHERE alliance_id = ? AND status = 'active'",
                (now, alliance_id),
            )
            connection.execute(
                """
                INSERT INTO alliance_invite_links (alliance_id, created_by_user_id, token, status, created_at)
                VALUES (?, ?, ?, 'active', ?)
                """,
                (alliance_id, int(user["id"]), token, now),
            )

        _set_notice("Player invite URL generated.")
        return _redirect_to_alliance_dashboard(user)

    @app.post("/alliance/roster-form/create")
    def alliance_roster_form_create() -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            _set_error("Only the alliance admin can create roster forms.")
            return _redirect_to_alliance_dashboard(user)

        title = str(request.form.get("title") or "").strip()
        form_type = str(request.form.get("form_type") or "roster").strip()
        target_scope = str(request.form.get("target_scope") or "all").strip()
        target_list = [
            item.strip() for item in str(request.form.get("target_list") or "").split(",") if item.strip()
        ]
        if form_type not in {"roster", "transfer"}:
            form_type = "roster"
        if target_scope not in {"all", "custom"}:
            target_scope = "all"
        if not title or len(title) > 100:
            _set_error("The form title is required and must contain at most 100 characters.")
            return _redirect_to_alliance_dashboard(user)
        if target_scope == "custom" and not target_list:
            _set_error("Add at least one Game ID for a custom recipient list.")
            return _redirect_to_alliance_dashboard(user)
        if target_scope == "custom" and any(not game_id.isdigit() for game_id in target_list):
            _set_error("Custom recipient lists must contain only numeric Game IDs separated by commas.")
            return _redirect_to_alliance_dashboard(user)

        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            connection.execute(
                """
                INSERT INTO alliance_roster_forms
                    (alliance_id, created_by_user_id, token, title, schema_json, form_type,
                     target_scope, target_list_json, status, created_at, updated_at)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, 'draft', ?, ?)
                """,
                (int(user["alliance_id"]), int(user["id"]), secrets.token_urlsafe(24), title,
                 json.dumps(_transfer_application_schema() if form_type == "transfer" else _default_roster_form_schema()),
                 form_type, target_scope, json.dumps(target_list), now, now),
            )
            form_id = int(connection.execute("SELECT last_insert_rowid()").fetchone()[0])
        return redirect(url_for("alliance_roster_form_edit", form_id=form_id))

    @app.get("/alliance/roster-form/<int:form_id>/edit")
    def alliance_roster_form_edit(form_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            abort(403)
        with _get_db_connection() as connection:
            roster_form = connection.execute(
                "SELECT * FROM alliance_roster_forms WHERE id = ? AND alliance_id = ?",
                (form_id, int(user["alliance_id"])),
            ).fetchone()
        if roster_form is None:
            abort(404)
        try:
            schema = json.loads(roster_form["schema_json"] or "{}")
        except (TypeError, json.JSONDecodeError):
            schema = _default_roster_form_schema()
        if not schema.get("sections"):
            schema = _default_roster_form_schema()
        alliance = _get_current_alliance_for_user(user)
        return render_template(
            "roster_form_editor.html", roster_form=dict(roster_form), schema=schema,
            forms_url=url_for("alliance_page_by_tag", tag=_alliance_url_key(alliance), tab="forms"),
        )

    @app.post("/alliance/roster-form/<int:form_id>/edit")
    def alliance_roster_form_edit_save(form_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            abort(403)
        title = str(request.form.get("title") or "").strip()
        try:
            submitted_schema = json.loads(str(request.form.get("schema_json") or "{}"))
        except json.JSONDecodeError:
            submitted_schema = {}
        clean_sections: list[dict[str, Any]] = []
        allowed_types = {"text", "number", "textarea", "select", "radio", "checkbox", "multiselect", "timezone", "calculated"}
        for section_index, section in enumerate(submitted_schema.get("sections", []) if isinstance(submitted_schema, dict) else []):
            if not isinstance(section, dict):
                continue
            section_title = str(section.get("title") or "").strip()[:100]
            fields: list[dict[str, Any]] = []
            for field_index, field in enumerate(section.get("fields", [])):
                if not isinstance(field, dict):
                    continue
                label = str(field.get("label") or "").strip()[:150]
                field_type = str(field.get("type") or "text")
                if not label or field_type not in allowed_types:
                    continue
                options = [str(value).strip()[:100] for value in field.get("options", []) if str(value).strip()][:30]
                submitted_name = str(field.get("name") or "").strip()
                safe_name = submitted_name if re.fullmatch(r"[a-z][a-z0-9_]{0,79}", submitted_name) else f"custom_{secrets.token_hex(6)}"
                fields.append({
                    "name": safe_name, "label": label,
                    "type": field_type, "required": bool(field.get("required")), "options": options,
                })
            if section_title and fields:
                clean_sections.append({"title": section_title, "fields": fields})
        if not title or len(title) > 100:
            _set_error("The form title is required and must contain at most 100 characters.")
            return redirect(url_for("alliance_roster_form_edit", form_id=form_id))
        now = datetime.now(timezone.utc).isoformat()
        publish = str(request.form.get("publish") or "") == "1"
        with _get_db_connection() as connection:
            updated = connection.execute(
                "UPDATE alliance_roster_forms SET title = ?, schema_json = ?, status = CASE WHEN ? THEN 'active' ELSE status END, updated_at = ? WHERE id = ? AND alliance_id = ?",
                (title, json.dumps({"sections": clean_sections}), publish, now, form_id, int(user["alliance_id"])),
            ).rowcount
        if not updated:
            abort(404)
        if request.headers.get("X-Requested-With") == "XMLHttpRequest":
            return jsonify({"ok": True, "updated_at": now})
        _set_notice("Form published. Its sharing URL is now active." if publish else "Form draft saved.")
        return _redirect_to_alliance_dashboard(user, tab="forms") if publish else redirect(url_for("alliance_roster_form_edit", form_id=form_id))

    @app.post("/alliance/roster-form/<int:form_id>/publish")
    def alliance_roster_form_publish(form_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            abort(403)
        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            updated = connection.execute(
                "UPDATE alliance_roster_forms SET status = 'active', updated_at = ? WHERE id = ? AND alliance_id = ? AND status = 'draft'",
                (now, form_id, int(user["alliance_id"])),
            ).rowcount
        if not updated:
            abort(404)
        _set_notice("Form published. Its sharing URL is now active.")
        return _redirect_to_alliance_dashboard(user, tab="forms")

    @app.post("/alliance/roster-form/<int:form_id>/update")
    def alliance_roster_form_update(form_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            _set_error("Only the alliance admin can edit roster forms.")
            return _redirect_to_alliance_dashboard(user)

        target_scope = str(request.form.get("target_scope") or "all").strip()
        target_list = [
            item.strip() for item in str(request.form.get("target_list") or "").split(",") if item.strip()
        ]
        if target_scope not in {"all", "custom"}:
            target_scope = "all"
        if target_scope == "custom" and not target_list:
            _set_error("Add at least one Game ID for a custom recipient list.")
            return _redirect_to_alliance_dashboard(user)
        if target_scope == "custom" and any(not game_id.isdigit() for game_id in target_list):
            _set_error("Custom recipient lists must contain only numeric Game IDs separated by commas.")
            return _redirect_to_alliance_dashboard(user)

        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            updated = connection.execute(
                """
                UPDATE alliance_roster_forms
                SET target_scope = ?, target_list_json = ?, updated_at = ?
                WHERE id = ? AND alliance_id = ?
                """,
                (target_scope, json.dumps(target_list), now, form_id, int(user["alliance_id"])),
            ).rowcount
        _set_notice("Form recipients updated." if updated else "Roster form was not found.")
        return _redirect_to_alliance_dashboard(user, tab="forms")

    @app.post("/alliance/roster-form/<int:form_id>/status")
    def alliance_roster_form_status(form_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            _set_error("Only the alliance admin can manage roster forms.")
            return _redirect_to_alliance_dashboard(user)

        status = str(request.form.get("status") or "").strip()
        if status not in {"active", "closed"}:
            _set_error("Invalid roster form status.")
            return _redirect_to_alliance_dashboard(user, tab="forms")
        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            updated = connection.execute(
                "UPDATE alliance_roster_forms SET status = ?, updated_at = ? WHERE id = ? AND alliance_id = ?",
                (status, now, form_id, int(user["alliance_id"])),
            ).rowcount
        _set_notice("Roster form status updated." if updated else "Roster form was not found.")
        return _redirect_to_alliance_dashboard(user, tab="forms")

    @app.post("/alliance/roster-form/<int:form_id>/delete")
    def alliance_roster_form_delete(form_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            abort(403)
        alliance_id = int(user["alliance_id"])
        with _get_db_connection() as connection:
            roster_form = connection.execute(
                "SELECT id FROM alliance_roster_forms WHERE id = ? AND alliance_id = ?",
                (form_id, alliance_id),
            ).fetchone()
            if roster_form is None:
                abort(404)
            connection.execute("DELETE FROM alliance_roster_suggestions WHERE roster_form_id = ? AND alliance_id = ?", (form_id, alliance_id))
            connection.execute("DELETE FROM alliance_roster_submissions WHERE roster_form_id = ? AND alliance_id = ?", (form_id, alliance_id))
            connection.execute("DELETE FROM alliance_transfer_applications WHERE roster_form_id = ? AND alliance_id = ?", (form_id, alliance_id))
            connection.execute("DELETE FROM alliance_roster_forms WHERE id = ? AND alliance_id = ?", (form_id, alliance_id))
        _set_notice("Form and its responses deleted.")
        return _redirect_to_alliance_dashboard(user, tab="forms")

    @app.get("/alliance/roster-form/<int:form_id>/xlsx")
    def alliance_roster_form_xlsx(form_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            abort(403)
        with _get_db_connection() as connection:
            roster_form = connection.execute(
                "SELECT title, form_type, status, created_at FROM alliance_roster_forms WHERE id = ? AND alliance_id = ?",
                (form_id, int(user["alliance_id"])),
            ).fetchone()
            if roster_form is None:
                abort(404)
            if roster_form["form_type"] == "transfer":
                submissions = connection.execute(
                    """
                    SELECT submitted_at, game_id, player_name, payload_json
                    FROM alliance_transfer_applications
                    WHERE roster_form_id = ? AND alliance_id = ?
                    ORDER BY submitted_at, player_name COLLATE NOCASE
                    """,
                    (form_id, int(user["alliance_id"])),
                ).fetchall()
            else:
                submissions = connection.execute(
                    """
                    SELECT s.submitted_at, p.game_id, p.player_name, s.payload_json
                    FROM alliance_roster_submissions s JOIN alliance_players p ON p.id = s.player_id
                    WHERE s.roster_form_id = ? AND s.alliance_id = ?
                    ORDER BY s.submitted_at, p.player_name COLLATE NOCASE
                    """,
                    (form_id, int(user["alliance_id"])),
                ).fetchall()

        parsed_rows: list[tuple[Any, dict[str, Any]]] = []
        payload_fields: list[str] = []
        for submission in submissions:
            try:
                payload = json.loads(submission["payload_json"] or "{}")
            except (TypeError, json.JSONDecodeError):
                payload = {}
            payload = payload if isinstance(payload, dict) else {}
            parsed_rows.append((submission, payload))
            for key in payload:
                if key not in payload_fields and key not in {"csrf_token", "game_id"}:
                    payload_fields.append(key)

        workbook = Workbook()
        responses_sheet = workbook.active
        responses_sheet.title = "Responses"
        headers = ["Submitted at", "Player ID", "Player name", *payload_fields]
        responses_sheet.append(headers)
        for submission, payload in parsed_rows:
            responses_sheet.append([
                submission["submitted_at"], submission["game_id"], submission["player_name"],
                *[payload.get(key, "") for key in payload_fields],
            ])
        responses_sheet.freeze_panes = "A2"
        responses_sheet.auto_filter.ref = responses_sheet.dimensions
        for index, header in enumerate(headers, start=1):
            responses_sheet.column_dimensions[get_column_letter(index)].width = min(42, max(14, len(str(header)) + 2))

        summary_sheet = workbook.create_sheet("Summary")
        summary_sheet.append(["Form", roster_form["title"]])
        summary_sheet.append(["Status", roster_form["status"]])
        summary_sheet.append(["Created", roster_form["created_at"]])
        summary_sheet.append(["Responses", len(parsed_rows)])
        summary_sheet.column_dimensions["A"].width = 18
        summary_sheet.column_dimensions["B"].width = 40

        output = BytesIO()
        workbook.save(output)
        filename = re.sub(r"[^A-Za-z0-9_-]+", "-", str(roster_form["title"])).strip("-") or "roster-form"
        response = app.make_response(output.getvalue())
        response.headers["Content-Type"] = "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"
        response.headers["Content-Disposition"] = f'attachment; filename="{filename}.xlsx"'
        return response

    @app.get("/alliance/roster-form/<int:form_id>/csv")
    def alliance_roster_form_csv(form_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            abort(403)

        with _get_db_connection() as connection:
            roster_form = connection.execute(
                "SELECT title FROM alliance_roster_forms WHERE id = ? AND alliance_id = ?",
                (form_id, int(user["alliance_id"])),
            ).fetchone()
            if roster_form is None:
                abort(404)
            submissions = connection.execute(
                """
                SELECT s.submitted_at, p.game_id, p.player_name, s.payload_json
                FROM alliance_roster_submissions s
                JOIN alliance_players p ON p.id = s.player_id
                WHERE s.roster_form_id = ? AND s.alliance_id = ?
                ORDER BY s.submitted_at, p.player_name COLLATE NOCASE
                """,
                (form_id, int(user["alliance_id"])),
            ).fetchall()

        parsed_rows: list[tuple[Any, dict[str, str]]] = []
        payload_fields: list[str] = []
        for submission in submissions:
            try:
                payload = json.loads(submission["payload_json"] or "{}")
            except (TypeError, json.JSONDecodeError):
                payload = {}
            payload = payload if isinstance(payload, dict) else {}
            parsed_rows.append((submission, payload))
            for key in payload:
                if key not in payload_fields and key not in {"csrf_token", "game_id"}:
                    payload_fields.append(key)

        output = StringIO(newline="")
        fieldnames = ["submitted_at", "game_id", "display_name", *payload_fields]
        writer = csv.DictWriter(output, fieldnames=fieldnames)
        writer.writeheader()
        for submission, payload in parsed_rows:
            writer.writerow({
                "submitted_at": submission["submitted_at"],
                "game_id": submission["game_id"],
                "display_name": submission["player_name"],
                **{key: payload.get(key, "") for key in payload_fields},
            })

        filename = re.sub(r"[^A-Za-z0-9_-]+", "-", str(roster_form["title"])).strip("-") or "roster-form"
        response = app.make_response("\ufeff" + output.getvalue())
        response.headers["Content-Type"] = "text/csv; charset=utf-8"
        response.headers["Content-Disposition"] = f'attachment; filename="{filename}.csv"'
        return response

    @app.get("/alliance/roster-form/<int:form_id>/analysis")
    def alliance_roster_form_analysis(form_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            abort(403)

        with _get_db_connection() as connection:
            roster_form = connection.execute(
                "SELECT id, title, form_type, status, created_at FROM alliance_roster_forms WHERE id = ? AND alliance_id = ?",
                (form_id, int(user["alliance_id"])),
            ).fetchone()
            if roster_form is None:
                abort(404)
            if roster_form["form_type"] == "transfer":
                submissions = connection.execute(
                    """
                    SELECT submitted_at, game_id, player_name, payload_json
                    FROM alliance_transfer_applications
                    WHERE roster_form_id = ? AND alliance_id = ?
                    ORDER BY player_name COLLATE NOCASE
                    """,
                    (form_id, int(user["alliance_id"])),
                ).fetchall()
            else:
                submissions = connection.execute(
                    """
                    SELECT s.submitted_at, p.game_id, p.player_name, s.payload_json
                    FROM alliance_roster_submissions s
                    JOIN alliance_players p ON p.id = s.player_id
                    WHERE s.roster_form_id = ? AND s.alliance_id = ?
                    ORDER BY p.player_name COLLATE NOCASE
                    """,
                    (form_id, int(user["alliance_id"])),
                ).fetchall()

        def payload_value(payload: dict[str, Any], clean_key: str, legacy_text: str) -> str:
            direct = str(payload.get(clean_key) or "").strip()
            if direct:
                return direct
            legacy_text = legacy_text.casefold()
            for key, value in payload.items():
                if legacy_text in str(key).casefold():
                    return str(value or "").strip()
            return ""

        def numeric_value(raw: Any) -> int:
            digits = re.sub(r"[^0-9]", "", str(raw or ""))
            return int(digits) if digits else 0

        players: list[dict[str, Any]] = []
        tg_counts: dict[str, int] = {}
        vip_counts: dict[str, int] = {}
        activity_counts: dict[str, int] = {}
        kvk_counts: dict[str, int] = {}
        for submission in submissions:
            try:
                payload = json.loads(submission["payload_json"] or "{}")
            except (TypeError, json.JSONDecodeError):
                payload = {}
            payload = payload if isinstance(payload, dict) else {}
            total_power = numeric_value(payload_value(payload, "total_power", "current power"))
            town_hall = payload_value(payload, "town_hall_level", "city tg level") or "Unknown"
            vip = payload_value(payload, "vip_level", "vip level") or "Unknown"
            activity = payload_value(payload, "daily_activity", "daily activity level") or "Unknown"
            kvk = (
                payload_value(payload, "source_kingdom", "kingdom transferring from")
                if roster_form["form_type"] == "transfer"
                else payload_value(payload, "kvk_attendance", "kvk battle attendance")
            ) or "Unknown"
            for counts, value in ((tg_counts, town_hall), (vip_counts, vip), (activity_counts, activity), (kvk_counts, kvk)):
                counts[value] = counts.get(value, 0) + 1
            players.append({
                "name": str(submission["player_name"] or submission["game_id"]),
                "game_id": str(submission["game_id"] or ""),
                "power": total_power,
                "town_hall": town_hall,
                "vip": vip,
                "activity": activity,
                "kvk": kvk,
                "submitted_at": str(submission["submitted_at"] or ""),
            })
        players.sort(key=lambda player: int(player["power"]), reverse=True)
        powers = [int(player["power"]) for player in players if int(player["power"]) > 0]
        return render_template(
            "roster_form_analysis.html",
            roster_form=dict(roster_form), players=players,
            forms_url=url_for(
                "alliance_page_by_tag",
                tag=_alliance_url_key(_get_current_alliance_for_user(user)), tab="forms",
            ),
            total_power=sum(powers), average_power=round(sum(powers) / len(powers)) if powers else 0,
            chart_data={
                "power": {"labels": [player["name"] for player in players], "values": [player["power"] for player in players]},
                "townHall": tg_counts, "vip": vip_counts,
                "activity": activity_counts, "kvk": kvk_counts,
            },
            category_label="Kingdom of origin" if roster_form["form_type"] == "transfer" else "KVK attendance",
            category_description="Applicants grouped by their current kingdom." if roster_form["form_type"] == "transfer" else "Planned participation in the next KVK battle.",
        )

    @app.post("/alliance/create")
    def alliance_create() -> Any:
        user = _get_current_user()
        if not user:
            return redirect(url_for("alliance_page"))

        alliance_name = str(request.form.get("name", "")).strip()
        kingdom = str(request.form.get("kingdom", "")).strip()
        tag = _normalize_alliance_tag(request.form.get("tag", ""))
        description = str(request.form.get("description", "")).strip()
        avatar_url = str(request.form.get("avatar_url", "")).strip() or None
        if not alliance_name:
            _set_error("Alliance name is required.")
            return redirect(url_for("alliance_page"))
        if len(description) > 200:
            _set_error("Alliance description must be 200 characters or less.")
            return redirect(url_for("alliance_page"))

        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            if tag:
                duplicate = connection.execute(
                    "SELECT id FROM alliances WHERE LOWER(tag) = LOWER(?) LIMIT 1",
                    (tag,),
                ).fetchone()
                if duplicate:
                    _set_error("That tag is already in use by another alliance.")
                    return redirect(url_for("alliance_page"))

            cursor = connection.execute(
                """
                INSERT INTO alliances (name, tag, kingdom, description, avatar_url, created_by_user_id, created_at, updated_at)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                """,
                (alliance_name, tag or None, kingdom or None, description or None, avatar_url, user["id"], now, now),
            )
            alliance_id = cursor.lastrowid
            connection.execute(
                "UPDATE alliance_users SET alliance_id = ?, is_admin = 1, updated_at = ? WHERE id = ?",
                (alliance_id, now, user["id"]),
            )
        session["is_admin"] = True
        _set_notice("Alliance created successfully.")
        return _redirect_to_alliance_dashboard(_get_current_user())

    @app.post("/alliance/update")
    def alliance_update() -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            _set_error("Only the alliance admin can update alliance details.")
            return _redirect_to_alliance_dashboard(user, tab="player-list")

        alliance_name = str(request.form.get("name", "")).strip()
        tag = _normalize_alliance_tag(request.form.get("tag", ""))
        description = str(request.form.get("description", "")).strip()
        avatar_url = str(request.form.get("avatar_url", "")).strip() or None

        if not alliance_name:
            _set_error("Alliance name is required.")
            return _redirect_to_alliance_dashboard(user, tab="player-list")
        if len(description) > 200:
            _set_error("Alliance description must be 200 characters or less.")
            return _redirect_to_alliance_dashboard(user, tab="player-list")

        alliance_id = int(user["alliance_id"])
        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            if tag:
                duplicate = connection.execute(
                    "SELECT id FROM alliances WHERE LOWER(tag) = LOWER(?) AND id != ? LIMIT 1",
                    (tag, alliance_id),
                ).fetchone()
                if duplicate:
                    _set_error("That tag is already in use by another alliance.")
                    return _redirect_to_alliance_dashboard(user, tab="player-list")

            connection.execute(
                "UPDATE alliances SET name = ?, tag = ?, description = ?, avatar_url = ?, updated_at = ? WHERE id = ?",
                (alliance_name, tag or None, description or None, avatar_url, now, alliance_id),
            )

        _set_notice("Alliance details updated.")
        return _redirect_to_alliance_dashboard(_get_current_user(), tab="player-list")

    @app.post("/alliance/swordland/update")
    @app.post("/alliance/kvk/update")
    def alliance_swordland_update() -> Any:
        event_key = "kvk" if request.path.startswith("/alliance/kvk/") else "swordland"
        event_name = "KVK" if event_key == "kvk" else "Swordland"
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            _set_error(f"Only the alliance admin can configure {event_name}.")
            return _redirect_to_alliance_dashboard(user, tab=event_key)

        rival_input = str(request.form.get("rival_jeabs_id", "")).strip()
        if event_key == "kvk":
            rival_input = json.dumps([
                value
                for index in range(1, 5)
                if (value := str(request.form.get(f"rival_jeabs_id_{index}", "")).strip())
            ])
        rival_name = str(request.form.get("rival_name", "")).strip()
        slot = 2 if _parse_loose_int(request.form.get("slot"), 1) == 2 else 1
        rival_id_field, rival_name_field, cache_field, cache_updated_field = _swordland_storage_fields(slot, event_key)
        normalized = _normalize_jeabs_alliance_input(rival_input)
        rival_jeabs_id = rival_input if event_key == "kvk" else str(normalized.get("alliance_id") or "").strip()

        alliance_id = int(user["alliance_id"])
        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            connection.execute(
                f"UPDATE alliances SET {rival_id_field} = ?, {rival_name_field} = ?, {cache_field} = NULL, {cache_updated_field} = NULL, updated_at = ? WHERE id = ?",
                (rival_jeabs_id or None, rival_name or None, now, alliance_id),
            )

        _set_notice(f"{event_name} rival updated. Cached data cleared, click Refresh {event_name} Data to sync.")
        return _redirect_to_alliance_dashboard(_get_current_user(), tab=event_key, swordland_slot=slot)

    @app.post("/alliance/swordland/refresh")
    @app.post("/alliance/kvk/refresh")
    def alliance_swordland_refresh() -> Any:
        event_key = "kvk" if request.path.startswith("/alliance/kvk/") else "swordland"
        event_name = "KVK" if event_key == "kvk" else "Swordland"
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            _set_error(f"Only the alliance admin can refresh {event_name} data.")
            return _redirect_to_alliance_dashboard(user, tab=event_key)

        token = _get_jeabs_token(alliance)
        if not token:
            _set_error("A JeabsPlus API token is not configured for this alliance.")
            return _redirect_to_alliance_dashboard(user, tab=event_key)

        alliance = _get_current_alliance_for_user(user)
        if not alliance:
            _set_error("Alliance not found for this user.")
            return _redirect_to_alliance_dashboard(user, tab=event_key)

        slot = 2 if _parse_loose_int(request.form.get("slot"), 1) == 2 else 1
        rival_id_field, _, cache_field, cache_updated_field = _swordland_storage_fields(slot, event_key)
        rival_id = str(alliance.get(rival_id_field) or "").strip()
        if not rival_id:
            _set_error(f"Configure the rival JeabsPlus ID before refreshing {event_name} data.")
            return _redirect_to_alliance_dashboard(user, tab=event_key)

        members = _load_alliance_member_rows_for_swordland(int(alliance["id"]))
        snapshot = _build_swordland_live_snapshot(alliance, members, slot, event_key=event_key)
        now = datetime.now(timezone.utc).isoformat()
        payload = {
            "left_side": snapshot.get("left_side"),
            "right_side": snapshot.get("right_side"),
            "comparison_rows": snapshot.get("comparison_rows") or [],
            "report": snapshot.get("report"),
            "rival_message": snapshot.get("rival_message") or "",
            "cached_at": now,
        }

        with _get_db_connection() as connection:
            connection.execute(
                f"UPDATE alliances SET {cache_field} = ?, {cache_updated_field} = ?, updated_at = ? WHERE id = ?",
                (json.dumps(payload), now, now, int(alliance["id"])),
            )

        if snapshot.get("right_side"):
            _set_notice(f"{event_name} cache refreshed successfully.")
        else:
            _set_notice(f"{event_name} cache refreshed with errors. Review the {event_name} message panel.")
        return _redirect_to_alliance_dashboard(_get_current_user(), tab=event_key, swordland_slot=slot)

    @app.post("/alliance/swordland/refresh/start")
    @app.post("/alliance/kvk/refresh/start")
    def alliance_swordland_refresh_start() -> Any:
        event_key = "kvk" if request.path.startswith("/alliance/kvk/") else "swordland"
        event_name = "KVK" if event_key == "kvk" else "Swordland"
        user = _get_current_user()
        if not user:
            return jsonify({"ok": False, "requires_login": True, "message": "Session expired. Please log in again."}), 401
        if not user.get("alliance_id") or not user.get("is_admin"):
            return jsonify({"ok": False, "message": f"Only the alliance admin can refresh {event_name} data."}), 403
        alliance = _get_current_alliance_for_user(user)
        if not alliance:
            return jsonify({"ok": False, "message": "Alliance not found for this user."}), 404
        if not _get_jeabs_token(alliance):
            return jsonify({"ok": False, "message": "A JeabsPlus API token is not configured for this alliance."}), 400
        slot = 2 if _parse_loose_int(request.form.get("slot"), 1) == 2 else 1
        rival_id_field, _, _, _ = _swordland_storage_fields(slot, event_key)
        if not str(alliance.get(rival_id_field) or "").strip():
            return jsonify({"ok": False, "message": f"Configure the rival JeabsPlus ID before refreshing {event_name} data."}), 400

        job, error = _create_swordland_sync_job(int(alliance["id"]), slot, event_key)
        if not job:
            return jsonify({"ok": False, "message": error}), 409
        return jsonify({"ok": True, "job": job}), 202

    @app.post("/alliance/kvk/plan/save")
    def alliance_kvk_plan_save() -> Any:
        wants_json = request.headers.get("X-Requested-With") == "XMLHttpRequest"

        def kvk_error(message: str, status: int = 400) -> Any:
            if wants_json:
                return jsonify({"ok": False, "message": message}), status
            _set_error(message)
            return _redirect_to_alliance_dashboard(_get_current_user(), tab="kvk", swordland_view="plan")

        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            return kvk_error("Only the alliance admin can save a KVK plan.", 403)

        alliance = _get_current_alliance_for_user(user)
        if not alliance:
            return kvk_error("Alliance not found for this user.", 404)

        members = _load_alliance_member_rows_for_swordland(int(alliance["id"]))
        valid_ids = {str(member.get("game_id") or "").strip() for member in members}
        valid_ids.discard("")
        try:
            stored_plan = json.loads(str(alliance.get("kvk_plan_json") or "{}"))
        except (TypeError, ValueError):
            stored_plan = {}
        stored_turrets = stored_plan.get("turrets") if isinstance(stored_plan, dict) else {}
        plan: dict[str, Any] = {
            "castles": {},
            "turrets": stored_turrets if isinstance(stored_turrets, dict) else {},
        }
        assigned_ids: list[str] = []
        for castle in KVK_CASTLES:
            rows: dict[str, dict[str, str]] = {}
            for role in KVK_CASTLE_ROLES:
                player_id = str(request.form.get(f"{castle}_{role}_player") or "").strip()
                if player_id.startswith("manual:"):
                    manual_name = player_id[7:].strip()[:100]
                    player_id = f"manual:{manual_name}" if manual_name else ""
                attack_hero = str(request.form.get(f"{castle}_{role}_attack") or "").strip()
                garrison_hero = str(request.form.get(f"{castle}_{role}_garrison") or "").strip()
                if role != "captain" and (attack_hero not in (*KVK_HEROES, "") or garrison_hero not in (*KVK_HEROES, "")):
                    return kvk_error("Select a valid KVK hero.")
                rows[role] = {
                    "player_id": player_id,
                    "attack_hero": attack_hero[:80],
                    "garrison_hero": garrison_hero[:80],
                    "troops": {
                        action: {
                            troop: max(0, _parse_loose_int(
                                request.form.get(f"{castle}_{role}_{action}_{troop}"), 0
                            ))
                            for troop in KVK_TROOPS
                        }
                        for action in KVK_ACTIONS
                    },
                }
                if player_id:
                    assigned_ids.append(player_id)
            plan["castles"][castle] = {
                "attack_1_formation": str(request.form.get(f"{castle}_attack_1_formation") or "50/20/30").strip()[:40],
                "attack_2_formation": str(request.form.get(f"{castle}_attack_2_formation") or "50/0/50").strip()[:40],
                "defense_formation": str(request.form.get(f"{castle}_defense_formation") or "60/40/0").strip()[:40],
                "rows": rows,
            }

        if any(player_id not in valid_ids and not player_id.startswith("manual:") for player_id in assigned_ids):
            return kvk_error("The KVK plan contains a player who is no longer in your alliance roster.")
        if len(assigned_ids) != len({player_id.casefold() for player_id in assigned_ids}):
            return kvk_error("Each player can only be assigned once in the KVK plan.")

        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            connection.execute(
                "UPDATE alliances SET kvk_plan_json = ?, updated_at = ? WHERE id = ?",
                (json.dumps(plan), now, int(alliance["id"])),
            )
        if wants_json:
            return jsonify({"ok": True, "message": "KVK plan saved."})
        _set_notice("KVK plan saved.")
        return _redirect_to_alliance_dashboard(_get_current_user(), tab="kvk", swordland_view="plan")

    @app.post("/alliance/swordland/plan/save")
    def alliance_swordland_plan_save() -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            _set_error("Only the alliance admin can save a Swordland plan.")
            return _redirect_to_alliance_dashboard(user, tab="swordland")

        alliance = _get_current_alliance_for_user(user)
        if not alliance:
            _set_error("Alliance not found for this user.")
            return _redirect_to_alliance_dashboard(user, tab="swordland")

        slot = 2 if _parse_loose_int(request.form.get("slot"), 1) == 2 else 1
        members = _load_alliance_member_rows_for_swordland(int(alliance["id"]))
        valid_ids = {str(member.get("game_id") or "").strip() for member in members}
        valid_ids.discard("")
        plan = {"aggressor": str(request.form.get("aggressor") or "").strip(), "teams": {}}
        primary_assigned_ids = [plan["aggressor"]] if plan["aggressor"] else []
        loot_assigned_ids: list[str] = []
        for team in SWORDLAND_PLAN_TEAMS:
            plan["teams"][team] = {}
            reserve_roles = sorted(
                {
                    key[len(team) + 1 :]
                    for key in request.form
                    if key.startswith(f"{team}_") and re.fullmatch(r"reserve_\d+", key[len(team) + 1 :])
                },
                key=lambda role: int(role.split("_", 1)[1]),
            )
            for role in (*SWORDLAND_PLAN_ROLES, *(role for role in reserve_roles if role not in SWORDLAND_PLAN_ROLES)):
                player_id = str(request.form.get(f"{team}_{role}") or "").strip()
                plan["teams"][team][role] = player_id
                if player_id:
                    if team == "loot":
                        loot_assigned_ids.append(player_id)
                    else:
                        primary_assigned_ids.append(player_id)

        assigned_ids = [*primary_assigned_ids, *loot_assigned_ids]
        if any(player_id not in valid_ids for player_id in assigned_ids):
            _set_error("The plan contains a player who is no longer in your alliance roster.")
            return _redirect_to_alliance_dashboard(user, tab="swordland", swordland_slot=slot)
        if (
            len(primary_assigned_ids) != len(set(primary_assigned_ids))
            or len(loot_assigned_ids) != len(set(loot_assigned_ids))
        ):
            _set_error("Each player can only be assigned once within the primary teams and once within Loot Team.")
            return _redirect_to_alliance_dashboard(user, tab="swordland", swordland_slot=slot)

        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            connection.execute(
                f"UPDATE alliances SET {_swordland_plan_field(slot)} = ?, updated_at = ? WHERE id = ?",
                (json.dumps(plan), now, int(alliance["id"])),
            )
        _set_notice("Swordland plan saved.")
        return _redirect_to_alliance_dashboard(_get_current_user(), tab="swordland", swordland_slot=slot)

    @app.post("/alliance/ac/split")
    def alliance_ac_split() -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            return jsonify({"error": "Only alliance admins can use AC."}), 403

        payload = request.get_json(silent=True) or {}
        strategy = str(payload.get("strategy") or "two_strong")
        if strategy not in {"two_strong", "one_strong"}:
            return jsonify({"error": "Unknown AC build strategy."}), 400
        raw_registered_ids = payload.get("registered_ids") if isinstance(payload.get("registered_ids"), list) else []
        registered_ids = {int(value) for value in raw_registered_ids if str(value).isdigit()}
        with _get_db_connection() as connection:
            rows = connection.execute(
                """
                SELECT id, player_name, power_ac FROM alliance_players
                WHERE alliance_id = ?
                ORDER BY power_ac DESC, player_name COLLATE NOCASE ASC
                """,
                (int(user["alliance_id"]),),
            ).fetchall()
        roster = [
            {"id": int(row["id"]), "name": str(row["player_name"] or "Player"), "power": int(row["power_ac"] or 0)}
            for row in rows if int(row["id"]) in registered_ids
        ]
        return jsonify(split_roster(roster, strategy))

    @app.post("/alliance/ac/player/<int:player_id>/power")
    def alliance_ac_update_power(player_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            return jsonify({"ok": False, "message": "Only alliance admins can edit Power AC."}), 403

        payload = request.get_json(silent=True) or {}
        power_ac = max(0, _parse_loose_int(payload.get("power_ac"), 0))
        with _get_db_connection() as connection:
            cursor = connection.execute(
                """
                UPDATE alliance_players SET power_ac = ?, updated_at = ?
                WHERE id = ? AND alliance_id = ?
                """,
                (power_ac, datetime.now(timezone.utc).isoformat(), player_id, int(user["alliance_id"])),
            )
            if cursor.rowcount != 1:
                return jsonify({"ok": False, "message": "Player profile was not found."}), 404
        return jsonify({"ok": True, "power_ac": power_ac, "display_value": _format_whole_number(power_ac)})

    @app.post("/alliance/ac/simulate")
    def alliance_ac_simulate() -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            return jsonify({"error": "Only alliance admins can use AC."}), 403
        payload = request.get_json(silent=True) or {}
        try:
            loss_min_pct = payload.get("loss_min_pct", payload.get("loss_pct", 5))
            loss_max_pct = payload.get("loss_max_pct")
            return jsonify(simulate_lane(payload.get("mine", []), payload.get("theirs", []), loss_min_pct, loss_max_pct))
        except (TypeError, ValueError) as exc:
            return jsonify({"error": str(exc)}), 400

    @app.post("/alliance/ac/extract-rivals")
    def alliance_ac_extract_rivals() -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            return jsonify({"ok": False, "message": "Only alliance admins can use AC OCR."}), 403

        image_files = [image for image in request.files.getlist("images") if image and image.filename]
        if not image_files:
            return jsonify({"ok": False, "message": "Upload at least one screenshot."}), 400
        if len(image_files) > 10:
            return jsonify({"ok": False, "message": "Upload a maximum of 10 screenshots per lane."}), 400
        side = str(request.form.get("side") or "right").strip().lower()
        if side not in {"left", "right"}:
            return jsonify({"ok": False, "message": "Select whether the rival is on the left or right."}), 400

        from utils.ac_ocr import extract_ac_rivals, merge_ac_rivals

        extracted_groups: list[list[dict[str, Any]]] = []
        extraction_counts: list[int] = []
        paddle_paths: list[str] = []
        paddle_directory = tempfile.TemporaryDirectory()
        for image_file in image_files:
            if image_file.mimetype and not image_file.mimetype.startswith("image/"):
                return jsonify({"ok": False, "message": "Every uploaded file must be an image."}), 400
            image_bytes = image_file.read()
            if not image_bytes:
                continue
            if len(image_bytes) > 10 * 1024 * 1024:
                return jsonify({"ok": False, "message": "Each image must be 10 MB or smaller."}), 400
            image_path = Path(paddle_directory.name) / f"{len(paddle_paths)}.png"
            image_path.write_bytes(image_bytes)
            paddle_paths.append(str(image_path))

        try:
            worker = PROJECT_ROOT / "scripts" / "ac_paddleocr_worker.py"
            paddle_python = PROJECT_ROOT / "paddleocr-venv" / "bin" / "python"
            paddle_logs = []
            extracted_groups = []
            for start in range(0, len(paddle_paths), 3):
                completed = subprocess.run(
                    [str(paddle_python), str(worker), side, *paddle_paths[start:start + 3]],
                    check=True,
                    capture_output=True,
                    text=True,
                    timeout=180,
                    env={
                        **os.environ,
                        "PADDLE_PDX_DISABLE_MODEL_SOURCE_CHECK": "True",
                        "OMP_NUM_THREADS": "2",
                    },
                )
                extracted_groups.extend(json.loads(completed.stdout.strip().splitlines()[-1]))
                paddle_logs.append(completed.stderr)
            extraction_counts = [len(group) for group in extracted_groups]
            app.logger.warning("AC PaddleOCR details: %s", "\n".join(paddle_logs)[-16000:])
        except (OSError, subprocess.SubprocessError, json.JSONDecodeError) as exc:
            app.logger.warning("AC PaddleOCR failed, using Tesseract fallback: %s", exc)
            extracted_groups = []
            extraction_counts = []
            for image_path in paddle_paths:
                try:
                    extracted = extract_ac_rivals(Path(image_path).read_bytes(), side)
                    extracted_groups.append(extracted)
                    extraction_counts.append(len(extracted))
                except Exception as fallback_exc:
                    return jsonify({"ok": False, "message": f"Could not read screenshot: {fallback_exc}"}), 400
        finally:
            paddle_directory.cleanup()

        rivals = merge_ac_rivals(extracted_groups)
        app.logger.warning(
            "AC OCR summary side=%s per_image=%s merged=%s",
            side,
            extraction_counts,
            [(rival.get("position"), rival.get("name"), rival.get("power")) for rival in rivals],
        )
        if not rivals:
            return jsonify({"ok": False, "message": "No rival positions could be read. Use screenshots of the lane battle list."}), 400
        return jsonify({
            "ok": True,
            "rivals": rivals,
            "message": (
                f"Extracted {len(rivals)} rival players. "
                f"Per image: {', '.join(str(count) for count in extraction_counts)}. "
                "Review names and Power AC before simulating."
            ),
        })

    @app.post("/alliance/ac/save")
    def alliance_ac_save() -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            return jsonify({"error": "Only alliance admins can save AC lanes."}), 403
        payload = request.get_json(silent=True) or {}
        lock_token = str(payload.get("lock_token") or "").strip()
        if not lock_token:
            return jsonify({"error": "AC editing control is required before saving.", "lock_lost": True}), 409
        lanes = payload.get("lanes") if isinstance(payload.get("lanes"), dict) else {}
        raw_registered_ids = payload.get("registered_ids") if isinstance(payload.get("registered_ids"), list) else []
        registered_ids = [int(value) for value in raw_registered_ids if str(value).isdigit()]
        rivals = payload.get("rivals") if isinstance(payload.get("rivals"), dict) else {}
        loss_min_pct = min(40.0, max(0.0, float(payload.get("loss_min_pct", 5))))
        loss_max_pct = min(40.0, max(0.0, float(payload.get("loss_max_pct", 20))))
        loss_min_pct, loss_max_pct = sorted((loss_min_pct, loss_max_pct))
        normalized = {
            "lane_a": [],
            "lane_b": [],
            "lane_c": [],
            "registered_ids": registered_ids,
            "rivals": {
                lane: str(rivals.get(lane) or "")[:10000]
                for lane in ("lane_a", "lane_b", "lane_c")
            },
            "loss_min_pct": loss_min_pct,
            "loss_max_pct": loss_max_pct,
        }
        submitted_ids: list[int] = []
        for lane in ("lane_a", "lane_b", "lane_c"):
            values = lanes.get(lane, []) if isinstance(lanes.get(lane), list) else []
            normalized[lane] = [int(value) for value in values[:20] if str(value).isdigit()]
            submitted_ids.extend(normalized[lane])
        if len(submitted_ids) != len(set(submitted_ids)):
            return jsonify({"error": "A player can only be assigned to one AC lane."}), 400
        if len(registered_ids) != len(set(registered_ids)):
            return jsonify({"error": "The AC registration list contains duplicate players."}), 400
        if any(player_id not in set(registered_ids) for player_id in submitted_ids):
            return jsonify({"error": "Every assigned AC player must be registered for the event."}), 400

        with _get_db_connection() as connection:
            connection.execute("BEGIN IMMEDIATE")
            lock_row = connection.execute(
                "SELECT ac_lock_token, ac_lock_user_id, ac_lock_updated_at FROM alliances WHERE id = ?",
                (int(user["alliance_id"]),),
            ).fetchone()
            lock_updated_at = datetime.fromisoformat(str(lock_row["ac_lock_updated_at"] or "1970-01-01T00:00:00+00:00"))
            lock_expired = (datetime.now(timezone.utc) - lock_updated_at).total_seconds() > 120
            if (
                lock_expired
                or str(lock_row["ac_lock_token"] or "") != lock_token
                or int(lock_row["ac_lock_user_id"] or 0) != int(user["id"])
            ):
                return jsonify({"error": "Another administrator has taken control of AC.", "lock_lost": True}), 409
            valid_ids = {
                int(row["id"])
                for row in connection.execute(
                    "SELECT id FROM alliance_players WHERE alliance_id = ?",
                    (int(user["alliance_id"]),),
                ).fetchall()
            }
            if any(player_id not in valid_ids for player_id in [*registered_ids, *submitted_ids]):
                return jsonify({"error": "The AC plan contains a player outside your alliance."}), 400
            connection.execute(
                "UPDATE alliances SET ac_plan_json = ?, updated_at = ? WHERE id = ?",
                (json.dumps(normalized), datetime.now(timezone.utc).isoformat(), int(user["alliance_id"])),
            )
        return jsonify({"ok": True, "lanes": normalized})

    @app.post("/alliance/ac/lock")
    def alliance_ac_lock() -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            return jsonify({"error": "Only alliance admins can edit AC."}), 403
        payload = request.get_json(silent=True) or {}
        action = str(payload.get("action") or "acquire").strip().lower()
        lock_token = str(payload.get("lock_token") or "").strip()[:200]
        if action not in {"acquire", "heartbeat", "takeover"} or not lock_token:
            return jsonify({"error": "Invalid AC lock request."}), 400

        now = datetime.now(timezone.utc)
        alliance_id = int(user["alliance_id"])
        with _get_db_connection() as connection:
            connection.execute("BEGIN IMMEDIATE")
            row = connection.execute(
                """
                SELECT alliances.ac_lock_token, alliances.ac_lock_user_id, alliances.ac_lock_updated_at,
                       alliances.ac_plan_json, alliance_users.username AS lock_username
                FROM alliances
                LEFT JOIN alliance_users ON alliance_users.id = alliances.ac_lock_user_id
                WHERE alliances.id = ?
                """,
                (alliance_id,),
            ).fetchone()
            updated_at = datetime.fromisoformat(str(row["ac_lock_updated_at"] or "1970-01-01T00:00:00+00:00"))
            expired = (now - updated_at).total_seconds() > 120
            owns_lock = (
                str(row["ac_lock_token"] or "") == lock_token
                and int(row["ac_lock_user_id"] or 0) == int(user["id"])
            )
            available = expired or not row["ac_lock_token"] or owns_lock
            if action == "takeover" or (action in {"acquire", "heartbeat"} and available):
                connection.execute(
                    "UPDATE alliances SET ac_lock_token = ?, ac_lock_user_id = ?, ac_lock_updated_at = ? WHERE id = ?",
                    (lock_token, int(user["id"]), now.isoformat(), alliance_id),
                )
                return jsonify({
                    "ok": True,
                    "has_control": True,
                    "owner_name": str(user.get("username") or "Administrator"),
                    "plan": json.loads(str(row["ac_plan_json"] or "{}")),
                })

            return jsonify({
                "ok": True,
                "has_control": False,
                "owner_name": str(row["lock_username"] or "Another administrator"),
                "plan": json.loads(str(row["ac_plan_json"] or "{}")),
            })

    @app.post("/alliance/ac/optimize")
    def alliance_ac_optimize() -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            return jsonify({"error": "Only alliance admins can optimize AC lanes."}), 403
        payload = request.get_json(silent=True) or {}
        lanes = payload.get("lanes") if isinstance(payload.get("lanes"), dict) else {}
        rivals = payload.get("rivals") if isinstance(payload.get("rivals"), dict) else {}
        if any(not isinstance(lanes.get(lane), list) or not isinstance(rivals.get(lane), list) for lane in ("lane_a", "lane_b", "lane_c")):
            return jsonify({"error": "Complete all three rival lanes before optimizing."}), 400
        if not any(lanes.get(lane) for lane in ("lane_a", "lane_b", "lane_c")):
            return jsonify({"error": "Register players or build the AC lanes before optimizing."}), 400
        try:
            return jsonify(optimize_lanes(
                lanes,
                rivals,
                payload.get("loss_min_pct", 5),
                payload.get("loss_max_pct", 20),
            ))
        except (TypeError, ValueError) as exc:
            return jsonify({"error": str(exc)}), 400

    @app.post("/alliance/nap4/update")
    def alliance_nap4_update() -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            _set_error("Only the alliance admin can configure NAP4.")
            return _redirect_to_alliance_dashboard(user, tab="nap4")

        entries: list[dict[str, str]] = []
        for index in range(1, 5):
            raw_id = str(request.form.get(f"nap4_jeabs_id_{index}", "")).strip()
            normalized = _normalize_jeabs_alliance_input(raw_id)
            entries.append(
                {
                    "jeabs_id": str(normalized.get("alliance_id") or "").strip(),
                }
            )

        alliance_id = int(user["alliance_id"])
        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            connection.execute(
                "UPDATE alliances SET nap4_config_json = ?, nap4_cache_json = NULL, nap4_cache_updated_at = NULL, updated_at = ? WHERE id = ?",
                (json.dumps(entries), now, alliance_id),
            )

        _set_notice("NAP4 configuration updated. Cached data cleared, click Refresh NAP4 Data to sync.")
        return _redirect_to_alliance_dashboard(_get_current_user(), tab="nap4")

    @app.post("/alliance/nap4/refresh")
    def alliance_nap4_refresh() -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            _set_error("Only the alliance admin can refresh NAP4 data.")
            return _redirect_to_alliance_dashboard(user, tab="nap4")

        token = _get_jeabs_token(alliance_id)
        if not token:
            _set_error("A JeabsPlus API token is not configured for this alliance.")
            return _redirect_to_alliance_dashboard(user, tab="nap4")

        alliance = _get_current_alliance_for_user(user)
        if not alliance:
            _set_error("Alliance not found for this user.")
            return _redirect_to_alliance_dashboard(user, tab="nap4")

        entries = _parse_nap4_entries(alliance.get("nap4_config_json"), alliance)
        if not any(str(entry.get("jeabs_id") or "").strip() for entry in entries):
            _set_error("Configure at least one Jeabs ID before refreshing NAP4 data.")
            return _redirect_to_alliance_dashboard(user, tab="nap4")

        kingdom_id = str(alliance.get("kingdom") or "").strip()
        snapshot = _build_nap4_snapshot(entries, kingdom_id, token)

        now = datetime.now(timezone.utc).isoformat()
        payload = {
            "alliances": snapshot.get("alliances", []),
            "general_rows": snapshot.get("general_rows", []),
            "errors": snapshot.get("errors", []),
            "cached_at": now,
        }

        with _get_db_connection() as connection:
            connection.execute(
                "UPDATE alliances SET nap4_cache_json = ?, nap4_cache_updated_at = ?, updated_at = ? WHERE id = ?",
                (json.dumps(payload), now, now, int(alliance["id"])),
            )

        snapshot_errors = snapshot.get("errors") if isinstance(snapshot.get("errors"), list) else []
        if snapshot_errors:
            _set_notice("NAP4 cache refreshed with partial errors. Check the panel for details.")
        else:
            _set_notice("NAP4 cache refreshed successfully.")
        return _redirect_to_alliance_dashboard(_get_current_user(), tab="nap4")

    @app.post("/alliance/nap4/refresh/start")
    def alliance_nap4_refresh_start() -> Any:
        user = _get_current_user()
        if not user:
            return jsonify({"ok": False, "requires_login": True, "message": "Session expired. Please log in again."}), 401
        if not user.get("alliance_id") or not user.get("is_admin"):
            return jsonify({"ok": False, "message": "Only the alliance admin can refresh NAP4 data."}), 403
        alliance = _get_current_alliance_for_user(user)
        if not alliance:
            return jsonify({"ok": False, "message": "Alliance not found for this user."}), 404
        if not _get_jeabs_token(alliance):
            return jsonify({"ok": False, "message": "A JeabsPlus API token is not configured for this alliance."}), 400
        entries = _parse_nap4_entries(alliance.get("nap4_config_json"), alliance)
        if not any(str(entry.get("jeabs_id") or "").strip() for entry in entries):
            return jsonify({"ok": False, "message": "Configure at least one Jeabs ID before refreshing NAP4 data."}), 400

        job, error = _create_nap4_sync_job(int(alliance["id"]))
        if not job:
            return jsonify({"ok": False, "message": error}), 409
        return jsonify({"ok": True, "job": job}), 202

    @app.get("/alliance/join/<int:alliance_id>")
    def alliance_join(alliance_id: int) -> Any:
        alliance = _get_alliance_by_id(alliance_id)
        if not alliance:
            _set_error("That alliance no longer exists.")
            return redirect(url_for("home_page"))

        invite_link_id = _parse_loose_int(request.args.get("invite_link_id"), 0)
        if invite_link_id <= 0:
            invite_link_id = 0

        user = _get_current_user()
        if not user:
            session["pending_join_alliance_id"] = alliance_id
            if invite_link_id > 0:
                session["pending_join_invite_link_id"] = invite_link_id
            else:
                session.pop("pending_join_invite_link_id", None)
            return redirect(url_for("discord_login"))

        _process_join_request(
            user,
            alliance_id,
            invite_link_id=invite_link_id if invite_link_id > 0 else None,
        )
        return _redirect_to_alliance_dashboard(user, tab="admin")

    @app.post("/alliance/join-request/<int:request_id>/accept")
    def alliance_join_request_accept(request_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            _set_error("Only the alliance admin can approve join requests.")
            return _redirect_to_alliance_dashboard(user, tab="admin")

        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            join_request = connection.execute(
                "SELECT * FROM alliance_join_requests WHERE id = ? AND alliance_id = ? AND status = 'pending'",
                (request_id, int(user["alliance_id"])),
            ).fetchone()
            if not join_request:
                _set_error("That join request is no longer available.")
                return _redirect_to_alliance_dashboard(user, tab="admin")

            connection.execute(
                "UPDATE alliance_join_requests SET status = 'accepted', updated_at = ? WHERE id = ?",
                (now, join_request["id"]),
            )
            connection.execute(
                "UPDATE alliance_users SET alliance_id = ?, updated_at = ? WHERE id = ?",
                (int(user["alliance_id"]), now, join_request["user_id"]),
            )
        _set_notice("Join request approved.")
        return _redirect_to_alliance_dashboard(user, tab="admin")

    @app.post("/alliance/join-request/<int:request_id>/reject")
    def alliance_join_request_reject(request_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            _set_error("Only the alliance admin can reject join requests.")
            return _redirect_to_alliance_dashboard(user, tab="admin")

        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            updated = connection.execute(
                "UPDATE alliance_join_requests SET status = 'rejected', updated_at = ? WHERE id = ? AND alliance_id = ? AND status = 'pending'",
                (now, request_id, int(user["alliance_id"])),
            )
            if updated.rowcount == 0:
                _set_error("That join request is no longer available.")
                return _redirect_to_alliance_dashboard(user, tab="admin")
        _set_notice("Join request rejected.")
        return _redirect_to_alliance_dashboard(user, tab="admin")

    @app.post("/alliance/player/extract-details")
    def alliance_player_extract_details() -> Any:
        user = _get_current_user()
        if not user:
            return jsonify({"ok": False, "message": "Login required."}), 401

        alliance = _get_current_alliance_for_user(user)
        if not alliance:
            return jsonify({"ok": False, "message": "Create or join an alliance first."}), 400

        image_file = request.files.get("image")
        if not image_file or not image_file.filename:
            return jsonify({"ok": False, "message": "Upload an image first."}), 400

        image_bytes = image_file.read()
        if not image_bytes:
            return jsonify({"ok": False, "message": "Uploaded image is empty."}), 400
        if len(image_bytes) > 10 * 1024 * 1024:
            return jsonify({"ok": False, "message": "Image is too large. Max size is 10 MB."}), 400

        from utils.ocr_extractor import extract_battle_report_stats_with_retries

        extraction = extract_battle_report_stats_with_retries(image_bytes, max_attempts=3)
        if not extraction.get("success"):
            return jsonify({
                "ok": False,
                "message": extraction.get("error") or "Could not read the screenshot.",
            }), 400

        allied_stats = extraction.get("stats", {}).get("aliados", {})
        fields = {
            "infantry_attack_bonus": allied_stats.get("infanteria", {}).get("ataque", 0.0),
            "infantry_defense_bonus": allied_stats.get("infanteria", {}).get("defensa", 0.0),
            "infantry_lethality_bonus": allied_stats.get("infanteria", {}).get("letalidad", 0.0),
            "infantry_health_bonus": allied_stats.get("infanteria", {}).get("salud", 0.0),
            "cavalry_attack_bonus": allied_stats.get("caballeria", {}).get("ataque", 0.0),
            "cavalry_defense_bonus": allied_stats.get("caballeria", {}).get("defensa", 0.0),
            "cavalry_lethality_bonus": allied_stats.get("caballeria", {}).get("letalidad", 0.0),
            "cavalry_health_bonus": allied_stats.get("caballeria", {}).get("salud", 0.0),
            "archer_attack_bonus": allied_stats.get("arquero", {}).get("ataque", 0.0),
            "archer_defense_bonus": allied_stats.get("arquero", {}).get("defensa", 0.0),
            "archer_lethality_bonus": allied_stats.get("arquero", {}).get("letalidad", 0.0),
            "archer_health_bonus": allied_stats.get("arquero", {}).get("salud", 0.0),
        }

        has_detected_bonus = any(abs(_parse_loose_float(value, 0.0)) > 0 for value in fields.values())
        if not has_detected_bonus:
            return jsonify({
                "ok": False,
                "message": "The screenshot did not contain readable ally bonus percentages. Use the battle summary where Infantry, Cavalry and Archers stats are visible.",
            }), 400

        normalized_fields = {
            key: _normalize_ocr_combat_bonus(value)
            for key, value in fields.items()
        }
        invalid_fields = [
            field_name
            for field_name, value in normalized_fields.items()
            if value < 0 or value > MAX_OCR_COMBAT_BONUS
        ]
        if invalid_fields:
            return jsonify({
                "ok": False,
                "message": "The screenshot contains an implausible combat bonus. Review the image and enter the affected stat manually.",
            }), 400
        return jsonify({
            "ok": True,
            "fields": normalized_fields,
            "message": "Ally bonuses extracted. Review troop tiers manually before saving.",
        }), 200

    @app.post("/alliance/member/<int:member_user_id>/role")
    def alliance_member_role_update(member_user_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            _set_error("Only the alliance admin can update member roles.")
            return _redirect_to_alliance_dashboard(user, tab="admin")

        requested_role = str(request.form.get("role", "member")).strip().lower()
        if requested_role not in {"member", "admin"}:
            _set_error("Invalid role selected.")
            return _redirect_to_alliance_dashboard(user, tab="admin")

        alliance_id = int(user["alliance_id"])
        make_admin = requested_role == "admin"
        now = datetime.now(timezone.utc).isoformat()

        with _get_db_connection() as connection:
            target_row = connection.execute(
                "SELECT id, is_admin FROM alliance_users WHERE id = ? AND alliance_id = ?",
                (member_user_id, alliance_id),
            ).fetchone()
            if not target_row:
                _set_error("Member not found in your alliance.")
                return _redirect_to_alliance_dashboard(user, tab="admin")

            if not make_admin and bool(target_row["is_admin"]):
                admin_count_row = connection.execute(
                    "SELECT COUNT(*) AS total FROM alliance_users WHERE alliance_id = ? AND is_admin = 1",
                    (alliance_id,),
                ).fetchone()
                admin_count = int(admin_count_row["total"] if admin_count_row else 0)
                if admin_count <= 1:
                    _set_error("You cannot remove the last admin of the alliance.")
                    return _redirect_to_alliance_dashboard(user, tab="admin")

            connection.execute(
                "UPDATE alliance_users SET is_admin = ?, updated_at = ? WHERE id = ? AND alliance_id = ?",
                (1 if make_admin else 0, now, member_user_id, alliance_id),
            )

        if int(member_user_id) == int(user["id"]):
            session["is_admin"] = make_admin

        _set_notice("Member role updated.")
        return _redirect_to_alliance_dashboard(_get_current_user(), tab="admin")

    @app.post("/alliance/member/<int:member_user_id>/remove")
    def alliance_member_remove(member_user_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            _set_error("Only the alliance admin can remove members.")
            return _redirect_to_alliance_dashboard(user, tab="admin")
        if request.form.get("confirm_remove") != "REMOVE":
            _set_error("Member removal was not confirmed.")
            return _redirect_to_alliance_dashboard(user, tab="admin")
        if int(member_user_id) == int(user["id"]):
            _set_error("You cannot remove yourself from the alliance.")
            return _redirect_to_alliance_dashboard(user, tab="admin")

        alliance_id = int(user["alliance_id"])
        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            target_row = connection.execute(
                "SELECT id FROM alliance_users WHERE id = ? AND alliance_id = ?",
                (member_user_id, alliance_id),
            ).fetchone()
            if not target_row:
                _set_error("Member not found in your alliance.")
                return _redirect_to_alliance_dashboard(user, tab="admin")
            connection.execute(
                "UPDATE alliance_users SET alliance_id = NULL, is_admin = 0, updated_at = ? WHERE id = ? AND alliance_id = ?",
                (now, member_user_id, alliance_id),
            )

        _set_notice("Member removed from the alliance.")
        return _redirect_to_alliance_dashboard(_get_current_user(), tab="admin")

    @app.post("/alliance/sync/jeabsplus")
    def alliance_sync_jeabsplus() -> Any:
        user = _get_current_user()
        if not user:
            return jsonify({
                "ok": False,
                "requires_login": True,
                "message": "Session expired. Please log in again.",
            }), 401
        if not user.get("alliance_id") or not user.get("is_admin"):
            return jsonify({"ok": False, "message": "Only the alliance admin can run JeabsPlus sync."}), 403

        alliance_id = int(user["alliance_id"])

        with _get_db_connection() as connection:
            alliance_row = connection.execute(
                "SELECT id, jeabs_alliance_id FROM alliances WHERE id = ? LIMIT 1",
                (alliance_id,),
            ).fetchone()
            stored_jeabs_id = str((alliance_row["jeabs_alliance_id"] if alliance_row else "") or "").strip()
            final_jeabs_id = stored_jeabs_id

            if not final_jeabs_id:
                return jsonify({
                    "ok": False,
                    "message": "The alliance creator must configure the JeabsPlus alliance ID first.",
                }), 400

        token = _get_jeabs_token(alliance_id)
        if not token:
            return jsonify({
                "ok": False,
                "message": "A JeabsPlus API token is not configured for this alliance.",
            }), 400

        try:
            raw_members = _fetch_jeabs_members(final_jeabs_id, token)
            with _get_db_connection() as connection:
                kingdom_row = connection.execute(
                    """
                    SELECT COALESCE(NULLIF(alliances.kingdom, ''), MAX(alliance_players.kingdom_id)) AS kingdom_id
                    FROM alliances
                    LEFT JOIN alliance_players ON alliance_players.alliance_id = alliances.id
                    WHERE alliances.id = ?
                    """,
                    (alliance_id,),
                ).fetchone()
            kingdom_id = str((kingdom_row["kingdom_id"] if kingdom_row else "") or "").strip()
            try:
                radiant_scores = _fetch_jeabs_radiant_leaderboard(kingdom_id, token)
            except (ValueError, requests.RequestException):
                radiant_scores = {}
            if radiant_scores:
                raw_members = [
                    {
                        **member,
                        **(
                            {"radiant_spire": radiant_scores[player_id]}
                            if (player_id := str(
                                member.get("governor_id")
                                or member.get("governorId")
                                or member.get("player_id")
                                or member.get("playerId")
                                or member.get("id")
                                or ""
                            ).strip()) in radiant_scores
                            else {}
                        ),
                    }
                    for member in raw_members
                    if isinstance(member, dict)
                ]
            enriched_members, detail_stats = _enrich_jeabs_members_with_player_details(raw_members, token)
            sync_result = _sync_jeabs_members_into_alliance(alliance_id, enriched_members, reconcile_roster=True)
        except ValueError as exc:
            return jsonify({"ok": False, "message": str(exc)}), 400
        except requests.RequestException:
            return jsonify({"ok": False, "message": "JeabsPlus request failed. Try again in a moment."}), 502

        imported_count = int(sync_result["created_profiles"]) + int(sync_result["updated_profiles"])
        if not raw_members:
            message = "JeabsPlus sync completed, but no members were returned for that alliance ID."
        else:
            message = (
                "JeabsPlus sync completed. "
                f"Imported {imported_count} players "
                f"({sync_result['created_profiles']} new, {sync_result['updated_profiles']} updated, {sync_result['removed_profiles']} removed). "
                f"Scanned {detail_stats['scanned_ids']} IDs for details "
                f"({detail_stats['detail_hits']} with detail data)."
            )

        return jsonify({
            "ok": True,
            "message": message,
            "jeabs_alliance_id": final_jeabs_id,
            "result": sync_result,
            "fetched_members": len(raw_members),
            "detail_scan": detail_stats,
        }), 200

    @app.post("/alliance/sync/jeabsplus/start")
    def alliance_sync_jeabsplus_start() -> Any:
        user = _get_current_user()
        if not user:
            return jsonify({"ok": False, "requires_login": True, "message": "Session expired. Please log in again."}), 401
        if not user.get("alliance_id") or not user.get("is_admin"):
            return jsonify({"ok": False, "message": "Only the alliance admin can run JeabsPlus sync."}), 403

        alliance_id = int(user["alliance_id"])
        with _get_db_connection() as connection:
            alliance_row = connection.execute(
                "SELECT jeabs_alliance_id FROM alliances WHERE id = ? LIMIT 1",
                (alliance_id,),
            ).fetchone()
            stored_jeabs_id = str((alliance_row["jeabs_alliance_id"] if alliance_row else "") or "").strip()
            final_jeabs_id = stored_jeabs_id
            if not final_jeabs_id:
                return jsonify({"ok": False, "message": "The alliance creator must configure the JeabsPlus alliance ID first."}), 400

        token = _get_jeabs_token(alliance_id)
        if not token:
            return jsonify({"ok": False, "message": "A JeabsPlus API token is not configured for this alliance."}), 400
        job, error = _create_jeabs_sync_job(alliance_id, final_jeabs_id, token)
        if not job:
            return jsonify({"ok": False, "message": error}), 409
        return jsonify({"ok": True, "job": job, "jeabs_alliance_id": final_jeabs_id}), 202

    @app.post("/alliance/sync/jeabsplus/configure")
    def alliance_configure_jeabsplus() -> Any:
        user = _get_current_user()
        if not user:
            return jsonify({"ok": False, "requires_login": True, "message": "Session expired. Please log in again."}), 401
        if not user.get("alliance_id") or not user.get("is_admin"):
            return jsonify({"ok": False, "message": "Only the alliance creator can configure this ID."}), 403

        alliance_id = int(user["alliance_id"])
        provided_id = str(request.form.get("jeabs_alliance_id", "")).strip()
        normalized_id = str(_normalize_jeabs_alliance_input(provided_id).get("alliance_id") or "").strip()
        with _get_db_connection() as connection:
            alliance_row = connection.execute(
                "SELECT created_by_user_id FROM alliances WHERE id = ? LIMIT 1",
                (alliance_id,),
            ).fetchone()
            if not alliance_row or int(alliance_row["created_by_user_id"] or 0) != int(user["id"]):
                return jsonify({"ok": False, "message": "Only the alliance creator can configure this ID."}), 403
            if not normalized_id:
                return jsonify({"ok": False, "message": "A valid JeabsPlus alliance ID is required."}), 400
            connection.execute(
                "UPDATE alliances SET jeabs_alliance_id = ?, updated_at = ? WHERE id = ?",
                (normalized_id, datetime.now(timezone.utc).isoformat(), alliance_id),
            )
        return jsonify({"ok": True, "jeabs_alliance_id": normalized_id}), 200

    @app.post("/alliance/sync/jeabsplus/token")
    def alliance_configure_jeabsplus_token() -> Any:
        user = _get_current_user()
        if not user:
            return _redirect_to_alliance_dashboard(user, tab="player-list")
        if not user.get("alliance_id") or not user.get("is_admin"):
            _set_error("Only the alliance admin can configure the JeabsPlus API token.")
            return _redirect_to_alliance_dashboard(user, tab="player-list")

        token = str(request.form.get("jeabs_api_token") or "").strip()
        if len(token) > 500:
            _set_error("The JeabsPlus API token is too long.")
            return _redirect_to_alliance_dashboard(user, tab="player-list")

        with _get_db_connection() as connection:
            connection.execute(
                "UPDATE alliances SET jeabs_api_token = ?, updated_at = ? WHERE id = ?",
                (token or None, datetime.now(timezone.utc).isoformat(), int(user["alliance_id"])),
            )
        _set_notice("JeabsPlus API token updated for this alliance." if token else "JeabsPlus API token removed for this alliance.")
        return _redirect_to_alliance_dashboard(_get_current_user(), tab="player-list")

    @app.get("/alliance/sync/jeabsplus/status/<job_id>")
    def alliance_sync_jeabsplus_status(job_id: str) -> Any:
        user = _get_current_user()
        if not user:
            return jsonify({"ok": False, "requires_login": True, "message": "Session expired. Please log in again."}), 401
        if not user.get("alliance_id") or not user.get("is_admin"):
            return jsonify({"ok": False, "message": "Only the alliance admin can view synchronization progress."}), 403
        with JEABS_SYNC_JOBS_LOCK:
            job = dict(JEABS_SYNC_JOBS.get(str(job_id)) or {})
        if not job:
            return jsonify({"ok": False, "message": "Synchronization job was not found."}), 404
        if int(job.get("alliance_id") or 0) != int(user["alliance_id"]):
            return jsonify({"ok": False, "message": "Synchronization job belongs to another alliance."}), 403
        job.pop("alliance_id", None)
        return jsonify({"ok": True, "job": job}), 200

    def _refresh_single_player_from_jeabs_data(
        alliance_id: int,
        member_user_id: int,
        token: str,
    ) -> dict[str, Any]:
        with _get_db_connection() as connection:
            profile_row = connection.execute(
                """
                SELECT
                    alliance_players.*, alliance_users.username AS discord_username
                FROM alliance_players
                JOIN alliance_users ON alliance_users.id = alliance_players.user_id
                WHERE alliance_players.alliance_id = ? AND alliance_players.user_id = ?
                ORDER BY alliance_players.id DESC
                LIMIT 1
                """,
                (alliance_id, member_user_id),
            ).fetchone()
            alliance_row = connection.execute(
                "SELECT jeabs_alliance_id FROM alliances WHERE id = ? LIMIT 1",
                (alliance_id,),
            ).fetchone()

        if not profile_row:
            raise ValueError("That player has no profile to refresh yet.")

        game_id = str(profile_row["game_id"] or "").strip()
        if not game_id:
            raise ValueError("Player ID is missing. Save the profile first.")

        base_member = {
            "id": game_id,
            "player_id": game_id,
            "name": str(profile_row["player_name"] or profile_row["discord_username"] or f"Player {game_id}").strip(),
        }

        player_details, _template = _fetch_jeabs_player_details(game_id, token)
        if not player_details:
            raise ValueError("JeabsPlus did not return detail data for that player ID.")

        base_member.update(player_details)

        try:
            radiant_spire = _fetch_jeabs_radiant_spire(game_id, token)
        except (ValueError, requests.RequestException):
            radiant_spire = None
        if radiant_spire is not None:
            base_member["radiant_spire"] = radiant_spire

        # Some alliance-specific fields (like R1..R5 rank) are exposed in
        # the alliance roster endpoint, not in /players/{id}.
        jeabs_alliance_id = str((alliance_row["jeabs_alliance_id"] if alliance_row else "") or "").strip()
        if jeabs_alliance_id:
            try:
                roster_members = _fetch_jeabs_members(jeabs_alliance_id, token)
            except Exception:
                roster_members = []
            for roster_member in roster_members:
                if not isinstance(roster_member, dict):
                    continue
                roster_game_id = str(
                    roster_member.get("governor_id")
                    or roster_member.get("governorId")
                    or roster_member.get("player_id")
                    or roster_member.get("playerId")
                    or roster_member.get("id")
                    or ""
                ).strip()
                if roster_game_id == game_id:
                    base_member.update(roster_member)
                    break

        sync_result = _sync_jeabs_members_into_alliance(alliance_id, [base_member])
        return {
            "player_name": base_member.get("name") or str(profile_row["player_name"] or "Player"),
            "sync_result": sync_result,
            "game_id": game_id,
        }

    @app.post("/alliance/player/<int:member_user_id>/refresh-jeabs")
    def alliance_player_refresh_jeabs(member_user_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            _set_error("Only the alliance admin can refresh a player from JeabsPlus.")
            return _redirect_to_alliance_dashboard(user, tab="player-list")

        alliance_id = int(user["alliance_id"])
        return_to = _sanitize_post_login_next(request.form.get("return_to"))

        with _get_db_connection() as connection:
            profile_row = connection.execute(
                """
                SELECT
                    alliance_players.*, alliance_users.username AS discord_username
                FROM alliance_players
                JOIN alliance_users ON alliance_users.id = alliance_players.user_id
                WHERE alliance_players.alliance_id = ? AND alliance_players.user_id = ?
                ORDER BY alliance_players.id DESC
                LIMIT 1
                """,
                (alliance_id, member_user_id),
            ).fetchone()

        if not profile_row:
            _set_error("That player has no profile to refresh yet.")
            if return_to:
                return redirect(return_to)
            return _redirect_to_alliance_dashboard(user, tab="player-list")

        game_id = str(profile_row["game_id"] or "").strip()
        if not game_id:
            _set_error("Player ID is missing. Save the profile first.")
            if return_to:
                return redirect(return_to)
            return _redirect_to_alliance_dashboard(user, tab="player-list")

        token = _get_jeabs_token(alliance_id)
        if not token:
            _set_error("A JeabsPlus API token is not configured for this alliance.")
            if return_to:
                return redirect(return_to)
            return _redirect_to_alliance_dashboard(user, tab="player-list")

        try:
            refresh_result = _refresh_single_player_from_jeabs_data(alliance_id, member_user_id, token)
        except ValueError as exc:
            _set_error(str(exc))
            if return_to:
                return redirect(return_to)
            return _redirect_to_alliance_dashboard(user, tab="player-list")
        except requests.RequestException:
            _set_error("JeabsPlus request failed. Try again in a moment.")
            if return_to:
                return redirect(return_to)
            return _redirect_to_alliance_dashboard(user, tab="player-list")

        sync_result = refresh_result["sync_result"]
        if int(sync_result.get("updated_profiles", 0)) > 0:
            _set_notice("Player refreshed from JeabsPlus.")
        else:
            _set_notice("Player detail fetched, but no profile changes were needed.")

        if return_to:
            return redirect(return_to)
        return _redirect_to_alliance_dashboard(user, tab="player-list")

    @app.post("/alliance/player/<int:member_user_id>/refresh-jeabs-json")
    def alliance_player_refresh_jeabs_json(member_user_id: int) -> Any:
        user = _get_current_user()
        if not user:
            return jsonify({"ok": False, "requires_login": True, "message": "Session expired. Please log in again."}), 401
        if not user.get("alliance_id") or not user.get("is_admin"):
            return jsonify({"ok": False, "message": "Only the alliance admin can refresh a player from JeabsPlus."}), 403

        alliance_id = int(user["alliance_id"])
        token = _get_jeabs_token(alliance_id)
        if not token:
            return jsonify({"ok": False, "message": "A JeabsPlus API token is not configured for this alliance."}), 400

        try:
            refresh_result = _refresh_single_player_from_jeabs_data(alliance_id, member_user_id, token)
        except ValueError as exc:
            return jsonify({"ok": False, "message": str(exc)}), 400
        except requests.RequestException:
            return jsonify({"ok": False, "message": "JeabsPlus request failed. Try again in a moment."}), 502

        sync_result = refresh_result["sync_result"]
        updated_profiles = int(sync_result.get("updated_profiles", 0))
        return jsonify(
            {
                "ok": True,
                "member_user_id": member_user_id,
                "game_id": refresh_result["game_id"],
                "updated": updated_profiles > 0,
                "message": "Player refreshed from JeabsPlus." if updated_profiles > 0 else "No changes were needed.",
            }
        ), 200

    @app.get("/alliance/player/<int:member_user_id>/growth")
    def alliance_player_growth(member_user_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id"):
            return jsonify({"ok": False, "message": "Login required."}), 401

        alliance_id = int(user["alliance_id"])
        metric = str(request.args.get("metric", "power")).strip().lower()
        if metric not in {"power", "mystic", "score"}:
            metric = "power"
        range_param = str(request.args.get("range", "7")).strip().lower()
        if range_param not in {"7", "14", "30", "all"}:
            range_param = "7"

        with _get_db_connection() as connection:
            profile_row = connection.execute(
                """
                SELECT alliance_players.*, alliance_users.username AS discord_username
                FROM alliance_players
                JOIN alliance_users ON alliance_users.id = alliance_players.user_id
                WHERE alliance_players.alliance_id = ? AND alliance_players.user_id = ?
                ORDER BY alliance_players.id DESC
                LIMIT 1
                """,
                (alliance_id, member_user_id),
            ).fetchone()

            if not profile_row:
                return jsonify({"ok": False, "message": "That player has no profile yet."}), 404

            if range_param == "all":
                snapshot_rows = connection.execute(
                    "SELECT * FROM alliance_player_snapshots WHERE alliance_id = ? AND player_id = ? ORDER BY id ASC",
                    (alliance_id, int(profile_row["id"])),
                ).fetchall()
            else:
                cutoff = (datetime.now(timezone.utc) - timedelta(days=int(range_param))).isoformat()
                snapshot_rows = connection.execute(
                    """
                    SELECT * FROM alliance_player_snapshots
                    WHERE alliance_id = ? AND player_id = ? AND created_at >= ?
                    ORDER BY id ASC
                    """,
                    (alliance_id, int(profile_row["id"]), cutoff),
                ).fetchall()

        def _metric_value(row: Any) -> float:
            if metric == "power":
                return _as_float(row["total_power"])
            if metric == "mystic":
                return _as_float(row["mystic_score"])
            return sum(_as_float(row[field]) for field in PLAYER_COMBAT_STAT_FIELDS)

        points = [{"t": str(row["created_at"]), "v": _metric_value(row)} for row in snapshot_rows]
        points.append(
            {
                "t": str(profile_row["updated_at"] or datetime.now(timezone.utc).isoformat()),
                "v": _metric_value(profile_row),
            }
        )

        player_name = str(profile_row["player_name"] or profile_row["discord_username"] or "Player").strip()
        return jsonify(
            {
                "ok": True,
                "player_name": player_name,
                "metric": metric,
                "range": range_param,
                "points": points,
            }
        ), 200

    @app.get("/alliance/player/<int:member_user_id>/hero-gear")
    def alliance_player_hero_gear(member_user_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id"):
            return jsonify({"ok": False, "message": "Login required."}), 401

        with _get_db_connection() as connection:
            profile_row = connection.execute(
                """
                SELECT id, game_id, hero_gear_json, hero_gear_updated_at
                FROM alliance_players
                WHERE alliance_id = ? AND user_id = ?
                ORDER BY id DESC
                LIMIT 1
                """,
                (int(user["alliance_id"]), member_user_id),
            ).fetchone()
        if not profile_row:
            return jsonify({"ok": False, "message": "That player has no profile yet."}), 404

        cached_payload: dict[str, Any] = {}
        try:
            parsed_cache = json.loads(str(profile_row["hero_gear_json"] or "{}"))
            if isinstance(parsed_cache, dict):
                cached_payload = parsed_cache
        except (TypeError, ValueError):
            cached_payload = {}

        cache_updated_at = str(profile_row["hero_gear_updated_at"] or "").strip()
        cache_is_fresh = False
        if cached_payload and cache_updated_at:
            try:
                cache_time = datetime.fromisoformat(cache_updated_at.replace("Z", "+00:00"))
                if cache_time.tzinfo is None:
                    cache_time = cache_time.replace(tzinfo=timezone.utc)
                cache_is_fresh = datetime.now(timezone.utc) - cache_time <= timedelta(minutes=JEABSPLUS_HERO_GEAR_CACHE_MINUTES)
            except ValueError:
                cache_is_fresh = False

        if cache_is_fresh:
            return jsonify({"ok": True, "cached": True, "stale": False, "gear": cached_payload}), 200

        token = _get_jeabs_token(int(user["alliance_id"]))
        game_id = str(profile_row["game_id"] or "").strip()
        try:
            payload = _fetch_jeabs_hero_gear(game_id, token)
        except (ValueError, requests.RequestException) as exc:
            if cached_payload:
                return jsonify({
                    "ok": True,
                    "cached": True,
                    "stale": True,
                    "warning": "JeabsPlus is temporarily unavailable; showing cached Hero Gear.",
                    "gear": cached_payload,
                }), 200
            return jsonify({"ok": False, "message": str(exc) or "Could not load Hero Gear."}), 502

        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            connection.execute(
                "UPDATE alliance_players SET hero_gear_json = ?, hero_gear_updated_at = ? WHERE id = ?",
                (json.dumps(payload), now, int(profile_row["id"])),
            )
        return jsonify({"ok": True, "cached": False, "stale": bool(payload.get("stale")), "gear": payload}), 200

    @app.post("/alliance/player/<int:member_user_id>/inline-update")
    def alliance_player_inline_update(member_user_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id") or not user.get("is_admin"):
            return jsonify({"ok": False, "message": "Only the alliance admin can edit inline."}), 403

        field = str(request.form.get("field", "")).strip()
        raw_value = request.form.get("value", "")
        alliance_id = int(user["alliance_id"])

        editable_field_types: dict[str, str] = {
            "att_troops": "int",
            "power_ac": "int",
            "radiant_spire": "plain_int",
            "bt": "bt_choice",
            "bt_time": "seconds",
            "infantry_attack_bonus": "float",
            "infantry_defense_bonus": "float",
            "infantry_lethality_bonus": "float",
            "infantry_health_bonus": "float",
            "cavalry_attack_bonus": "float",
            "cavalry_defense_bonus": "float",
            "cavalry_lethality_bonus": "float",
            "cavalry_health_bonus": "float",
            "archer_attack_bonus": "float",
            "archer_defense_bonus": "float",
            "archer_lethality_bonus": "float",
            "archer_health_bonus": "float",
        }

        field_type = editable_field_types.get(field)
        if not field_type:
            return jsonify({"ok": False, "message": "This field cannot be edited inline."}), 400

        with _get_db_connection() as connection:
            profile_row = connection.execute(
                """
                SELECT id FROM alliance_players
                WHERE alliance_id = ? AND user_id = ?
                ORDER BY id DESC
                LIMIT 1
                """,
                (alliance_id, member_user_id),
            ).fetchone()

            if not profile_row:
                return jsonify({"ok": False, "message": "Player profile was not found."}), 404

            if field_type == "bt_choice":
                normalized_value = str(raw_value).strip()
                if normalized_value not in {"BT1", "BT2", "Both"}:
                    return jsonify({"ok": False, "message": "BT must be BT1, BT2, or Both."}), 400
                display_value = normalized_value
            elif field_type == "seconds":
                normalized_value = max(0, _parse_loose_int(raw_value, 0))
                display_value = f"{_format_whole_number(normalized_value)} s"
            elif field_type == "plain_int":
                normalized_value = max(0, _parse_loose_int(raw_value, 0))
                display_value = _format_whole_number(normalized_value)
            elif field_type == "int":
                normalized_value = max(0, int(_parse_total_power(raw_value, 0)))
                display_value = _format_whole_number(normalized_value)
            else:
                normalized_value = max(0.0, round(_parse_loose_float(raw_value, 0.0), 1))
                display_value = _format_stat_value(normalized_value)

            now = datetime.now(timezone.utc).isoformat()
            connection.execute(
                f"UPDATE alliance_players SET {field} = ?, updated_at = ? WHERE id = ?",
                (normalized_value, now, int(profile_row["id"])),
            )

        return jsonify(
            {
                "ok": True,
                "field": field,
                "value": normalized_value,
                "display_value": display_value,
                "message": "Player value updated.",
            }
        ), 200

    @app.post("/alliance/player/link-game-id")
    def alliance_player_link_game_id() -> Any:
        user = _get_current_user()
        if not user:
            return redirect(url_for("alliance_page"))

        alliance = _get_current_alliance_for_user(user)
        if not alliance:
            _set_error("Create or join an alliance first.")
            return _redirect_to_alliance_dashboard(user)

        game_id = str(request.form.get("game_id", "")).strip()
        player_name = str(request.form.get("player_name", "")).strip()
        if not game_id:
            _set_error("Game ID is required.")
            return _redirect_to_alliance_dashboard(user, tab="my-profile")

        try:
            result = _claim_or_create_profile_by_game_id(
                int(alliance["id"]),
                int(user["id"]),
                game_id,
                preferred_player_name=player_name or str(user.get("username") or ""),
            )
        except ValueError as exc:
            _set_error(str(exc))
            return _redirect_to_alliance_dashboard(user, tab="my-profile")

        mode = str(result.get("mode") or "")
        if mode == "claimed_existing":
            _set_notice("Existing player profile linked by Game ID. No duplicate created.")
        elif mode == "created_new":
            _set_notice("Game ID registered successfully.")
        else:
            _set_notice("Game ID updated successfully.")

        return _redirect_to_alliance_dashboard(user, tab="my-profile")

    @app.post("/alliance/player/add-secondary")
    def alliance_player_add_secondary() -> Any:
        user = _get_current_user()
        alliance = _get_current_alliance_for_user(user) if user else None
        if not user or not alliance:
            return redirect(url_for("alliance_page"))

        game_id = str(request.form.get("game_id", "")).strip()
        if not game_id:
            _set_error("Game ID is required to create a secondary profile.")
            return _redirect_to_alliance_dashboard(user, tab="my-profile")

        with _get_db_connection() as connection:
            profile_count = connection.execute(
                "SELECT COUNT(*) AS total FROM alliance_players WHERE alliance_id = ? AND user_id = ?",
                (int(alliance["id"]), int(user["id"])),
            ).fetchone()["total"]
            existing_game = connection.execute(
                "SELECT id FROM alliance_players WHERE alliance_id = ? AND game_id = ? LIMIT 1",
                (int(alliance["id"]), game_id),
            ).fetchone()
        if existing_game:
            _set_error("That Game ID already belongs to a player in this alliance.")
            return _redirect_to_alliance_dashboard(user, tab="my-profile")

        try:
            result = _claim_or_create_profile_by_game_id(
                int(alliance["id"]),
                int(user["id"]),
                game_id,
                preferred_player_name=str(user.get("username") or ""),
            )
        except (ValueError, sqlite3.IntegrityError) as exc:
            _set_error(str(exc) or "Could not create the secondary profile.")
            return _redirect_to_alliance_dashboard(user, tab="my-profile")

        profile_id = int(result["row"]["id"])
        return _redirect_to_alliance_dashboard(user, tab=f"my-profile-{int(profile_count or 0) + 1}", profile_id=profile_id)

    @app.post("/alliance/player/delete-last")
    def alliance_player_delete_last() -> Any:
        user = _get_current_user()
        alliance = _get_current_alliance_for_user(user) if user else None
        if not user or not alliance:
            return redirect(url_for("alliance_page"))
        with _get_db_connection() as connection:
            row = connection.execute(
                "SELECT id FROM alliance_players WHERE alliance_id = ? AND user_id = ? ORDER BY id DESC LIMIT 1",
                (int(alliance["id"]), int(user["id"])),
            ).fetchone()
            if row:
                connection.execute("DELETE FROM alliance_players WHERE id = ?", (int(row["id"]),))
        return _redirect_to_alliance_dashboard(user, tab="my-profile")

    @app.post("/alliance/player/<int:member_user_id>/bear-config")
    def alliance_player_bear_config(member_user_id: int) -> Any:
        user = _get_current_user()
        if not user or not user.get("alliance_id"):
            _set_error("Login required to configure Bear Trap calculations.")
            return _redirect_to_alliance_dashboard(user, tab="player-list")
        if int(member_user_id) != int(user["id"]) and not user.get("is_admin"):
            _set_error("You can only configure your own Bear Trap calculation.")
            return _redirect_to_alliance_dashboard(user, tab="bear-calculator")

        march_capacity_base = max(0, _parse_loose_int(request.form.get("march_capacity_base"), 0))
        valora_level = _clamp_int(request.form.get("valora_level"), 0, 10, 0)
        cassia_level = _clamp_int(request.form.get("cassia_level"), 0, 20, 0)
        bison_level = _clamp_int(request.form.get("bison_level"), 0, 10, 0)
        march_booster_percent = _parse_loose_int(request.form.get("march_booster_percent"), 0)
        attack_booster_percent = _parse_loose_int(request.form.get("attack_booster_percent"), 0)
        lethality_booster_percent = _parse_loose_int(request.form.get("lethality_booster_percent"), 0)
        percentages = {
            "infantry_pct": _clamp_int(request.form.get("infantry_pct"), 0, 100, 0),
            "cavalry_pct": _clamp_int(request.form.get("cavalry_pct"), 0, 100, 0),
            "archer_pct": _clamp_int(request.form.get("archer_pct"), 0, 100, 0),
        }
        allowed_bear_tiers = {
            "T10-TG5", "T10-TG6", "T10-TG7", "T10-TG8",
            "T11-TG5", "T11-TG6", "T11-TG7", "T11-TG8",
        }
        troop_tiers = {
            f"{troop_class}_troop_tier": str(request.form.get(f"{troop_class}_troop_tier") or "").strip().upper()
            for troop_class in ("infantry", "cavalry", "archer")
        }
        bear_stats = {
            "infantry_attack_bonus": max(0.0, _parse_loose_float(request.form.get("infantry_attack_bonus"), 0.0)),
            "infantry_lethality_bonus": max(0.0, _parse_loose_float(request.form.get("infantry_lethality_bonus"), 0.0)),
            "cavalry_attack_bonus": max(0.0, _parse_loose_float(request.form.get("cavalry_attack_bonus"), 0.0)),
            "cavalry_lethality_bonus": max(0.0, _parse_loose_float(request.form.get("cavalry_lethality_bonus"), 0.0)),
            "archer_attack_bonus": max(0.0, _parse_loose_float(request.form.get("archer_attack_bonus"), 0.0)),
            "archer_lethality_bonus": max(0.0, _parse_loose_float(request.form.get("archer_lethality_bonus"), 0.0)),
        }
        bear_attack_bonus = max(0.0, _parse_loose_float(request.form.get("bear_attack_bonus"), 0.0))
        lead_heroes = {
            "lead_infantry": str(request.form.get("lead_infantry") or "").strip(),
            "lead_cavalry": str(request.form.get("lead_cavalry") or "").strip(),
            "lead_archer": str(request.form.get("lead_archer") or "").strip(),
        }
        lead_widgets = {
            "lead_infantry_widget": _clamp_int(request.form.get("lead_infantry_widget"), 0, 10, 0),
            "lead_cavalry_widget": _clamp_int(request.form.get("lead_cavalry_widget"), 0, 10, 0),
            "lead_archer_widget": _clamp_int(request.form.get("lead_archer_widget"), 0, 10, 0),
        }
        lead_skills = {
            "lead_infantry_skill": _clamp_int(request.form.get("lead_infantry_skill"), 0, 5, 0),
            "lead_cavalry_skill": _clamp_int(request.form.get("lead_cavalry_skill"), 0, 5, 0),
            "lead_archer_skill": _clamp_int(request.form.get("lead_archer_skill"), 0, 5, 0),
        }
        allowed_joiners = set(BEAR_JOINER_EFFECTS)
        joiners = {f"joiner_{index}": str(request.form.get(f"joiner_{index}") or "").strip() for index in range(1, 5)}
        requested_action = str(request.form.get("action") or "calculate")
        optimize_composition = requested_action == "optimize"
        optimize_heroes = requested_action == "optimize_heroes"
        if march_capacity_base <= 0:
            _set_error("Base march capacity must be greater than zero.")
            return _redirect_to_alliance_dashboard(user, tab="bear-calculator")
        if march_booster_percent not in (0, 10, 20):
            _set_error("March capacity booster must be 0%, 10%, or 20%.")
            return _redirect_to_alliance_dashboard(user, tab="bear-calculator")
        if attack_booster_percent not in (0, 10, 20) or lethality_booster_percent not in (0, 10, 20):
            _set_error("Attack and Lethality boosters must be 0%, 10%, or 20%.")
            return _redirect_to_alliance_dashboard(user, tab="bear-calculator")
        if not optimize_composition and sum(percentages.values()) != 100:
            _set_error("Infantry, Cavalry, and Archery percentages must add up to 100%.")
            return _redirect_to_alliance_dashboard(user, tab="bear-calculator")
        if any(tier not in allowed_bear_tiers for tier in troop_tiers.values()):
            _set_error("Choose a supported troop tier for Infantry, Cavalry, and Archery.")
            return _redirect_to_alliance_dashboard(user, tab="bear-calculator")
        missing_stats = _get_bear_missing_stats(bear_stats)
        if missing_stats:
            _set_error(f"Complete the Bear march statistics: {', '.join(missing_stats)}.")
            return _redirect_to_alliance_dashboard(user, tab="bear-calculator")
        if not all(lead_heroes.values()) or len(set(lead_heroes.values())) != 3:
            _set_error("Choose three different main heroes for Infantry, Cavalry, and Archery.")
            return _redirect_to_alliance_dashboard(user, tab="bear-calculator")
        allowed_leaders = {
            "lead_infantry": {"amadeus", "helga", "zoe"},
            "lead_cavalry": {"petra", "hilde", "margot", "thrud"},
            "lead_archer": {"marlin", "rosa", "yang"},
        }
        if any(hero_id not in allowed_leaders[field] for field, hero_id in lead_heroes.items()):
            _set_error("Choose a supported Bear leader for each troop class.")
            return _redirect_to_alliance_dashboard(user, tab="bear-calculator")
        if any(hero_id not in allowed_joiners for hero_id in joiners.values()):
            _set_error("Choose all four joiners from Chenko, Amane, Yeonwoo, or Margot.")
            return _redirect_to_alliance_dashboard(user, tab="bear-calculator")

        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            profile = connection.execute(
                "SELECT * FROM alliance_players WHERE alliance_id = ? AND user_id = ? ORDER BY id DESC LIMIT 1",
                (int(user["alliance_id"]), member_user_id),
            ).fetchone()
            if not profile:
                _set_error("Player profile was not found.")
                return _redirect_to_alliance_dashboard(user, tab="player-list")
            profile_data = dict(profile)
            previous_config = _parse_bear_trap_config(profile_data.get("bear_trap_config_json"))
            saved_config = {
                "march_capacity_base": march_capacity_base,
                "valora_level": valora_level,
                "cassia_level": cassia_level,
                "bison_level": bison_level,
                "march_booster_percent": march_booster_percent,
                "attack_booster_percent": attack_booster_percent,
                "lethality_booster_percent": lethality_booster_percent,
                "bear_attack_bonus": round(bear_attack_bonus, 1),
                "stats_source": "TERROR_REPORT",
                "leader_stat_skills_in_report": previous_config["leader_stat_skills_in_report"],
                "attack_booster_in_report": False,
                "lethality_booster_in_report": False,
                "widget_stacking_strategy": previous_config["widget_stacking_strategy"],
                **percentages,
                **troop_tiers,
                **bear_stats,
                **lead_heroes,
                **lead_skills,
                **lead_widgets,
                **joiners,
                "best_composition_calculated": previous_config["best_composition_calculated"],
                "best_infantry_pct": previous_config["best_infantry_pct"],
                "best_cavalry_pct": previous_config["best_cavalry_pct"],
                "best_archer_pct": previous_config["best_archer_pct"],
            }
            if optimize_heroes:
                try:
                    best_leaders, best_widgets, best_hero_damage = _find_best_bear_leaders(profile_data, saved_config)
                except ValueError as exc:
                    _set_error(str(exc))
                    return _redirect_to_alliance_dashboard(user, tab="bear-calculator")
                profile_progress = _parse_hero_progress_data(profile_data.get("hero_data"))
                saved_config.update({
                    "lead_infantry": best_leaders[0],
                    "lead_cavalry": best_leaders[1],
                    "lead_archer": best_leaders[2],
                    "lead_infantry_skill": _clamp_int((profile_progress.get(best_leaders[0]) or {}).get("skill"), 0, 5, 0),
                    "lead_cavalry_skill": _clamp_int((profile_progress.get(best_leaders[1]) or {}).get("skill"), 0, 5, 0),
                    "lead_archer_skill": _clamp_int((profile_progress.get(best_leaders[2]) or {}).get("skill"), 0, 5, 0),
                    "lead_infantry_widget": best_widgets[0],
                    "lead_cavalry_widget": best_widgets[1],
                    "lead_archer_widget": best_widgets[2],
                })
            if optimize_composition:
                best_percentages, best_damage = _find_best_bear_composition(profile_data, saved_config)
                saved_config.update({
                    "infantry_pct": best_percentages[0],
                    "cavalry_pct": best_percentages[1],
                    "archer_pct": best_percentages[2],
                    "best_composition_calculated": True,
                    "best_infantry_pct": best_percentages[0],
                    "best_cavalry_pct": best_percentages[1],
                    "best_archer_pct": best_percentages[2],
                })
            connection.execute(
                "UPDATE alliance_players SET bear_trap_config_json = ?, updated_at = ? WHERE id = ?",
                (
                    json.dumps(saved_config),
                    now,
                    int(profile_data["id"]),
                ),
            )
        if optimize_heroes:
            _set_notice(
                f"Best leaders: {best_leaders[0].title()} / {best_leaders[1].title()} / "
                f"{best_leaders[2].title()} · Expected damage {best_hero_damage:,.0f}."
            )
        elif optimize_composition:
            _set_notice(
                f"Best composition: {best_percentages[0]}% Infantry / {best_percentages[1]}% Cavalry / "
                f"{best_percentages[2]}% Archery · Expected damage {best_damage:,.0f}."
            )
        else:
            _set_notice("Bear Trap calculation saved.")
        return _redirect_to_alliance_dashboard(_get_current_user(), tab="bear-calculator")

    @app.post("/alliance/player/save")
    def alliance_player_save() -> Any:
        user = _get_current_user()
        if not user:
            return redirect(url_for("alliance_page"))

        alliance = _get_current_alliance_for_user(user)
        if not alliance:
            _set_error("Create or join an alliance first.")
            return _redirect_to_alliance_dashboard(user)

        target_user_id = int(user["id"])
        requested_profile_id = _parse_loose_int(request.form.get("profile_id"), 0)
        if user.get("is_admin"):
            requested_target_user_id = _parse_loose_int(request.form.get("target_user_id"), int(user["id"]))
            with _get_db_connection() as connection:
                target_member = connection.execute(
                    "SELECT id FROM alliance_users WHERE id = ? AND alliance_id = ?",
                    (requested_target_user_id, alliance["id"]),
                ).fetchone()
            if target_member:
                target_user_id = int(target_member["id"])
            else:
                _set_error("You can only edit members from your own alliance.")
                return _redirect_to_alliance_dashboard(user)

        player_name = str(request.form.get("player_name", "")).strip()
        game_id = str(request.form.get("game_id", "")).strip()
        vip_level = str(request.form.get("vip_level", "0")).strip()
        town_hall_level = str(request.form.get("town_hall_level", "30")).strip()
        total_power_value = _parse_total_power(request.form.get("total_power"), 5000000)
        if total_power_value < 0:
            total_power_value = 0
        power_ac_value = _parse_loose_int(request.form.get("power_ac"), 0)
        if power_ac_value < 0:
            power_ac_value = 0
        att_troops_value = _parse_loose_float(request.form.get("att_troops"), 0.0)
        if att_troops_value < 0 or not att_troops_value.is_integer():
            _set_error("ATT Troops must be a whole number.")
            return _redirect_to_alliance_dashboard(user)
        att_troops_value = int(att_troops_value)
        kills_value = max(0, _parse_loose_int(request.form.get("kills"), 0))
        mystic_score_value = max(0, _parse_loose_int(request.form.get("mystic_score"), 0))
        radiant_spire_value = max(0, _parse_loose_int(request.form.get("radiant_spire"), 0))
        requested_bt_value = str(request.form.get("bt", "")).strip()
        bt_time_value = max(0, _parse_loose_int(request.form.get("bt_time"), 0))
        kingdom_id = str(request.form.get("kingdom_id", "")).strip()
        infantry_troops = str(request.form.get("infantry_troops", "TG4")).strip()
        cavalry_troops = str(request.form.get("cavalry_troops", "TG4")).strip()
        archer_troops = str(request.form.get("archer_troops", "TG4")).strip()
        infantry_attack_bonus = _parse_loose_float(request.form.get("infantry_attack_bonus"), 0.0)
        infantry_defense_bonus = _parse_loose_float(request.form.get("infantry_defense_bonus"), 0.0)
        infantry_lethality_bonus = _parse_loose_float(request.form.get("infantry_lethality_bonus"), 0.0)
        infantry_health_bonus = _parse_loose_float(request.form.get("infantry_health_bonus"), 0.0)
        cavalry_attack_bonus = _parse_loose_float(request.form.get("cavalry_attack_bonus"), 0.0)
        cavalry_defense_bonus = _parse_loose_float(request.form.get("cavalry_defense_bonus"), 0.0)
        cavalry_lethality_bonus = _parse_loose_float(request.form.get("cavalry_lethality_bonus"), 0.0)
        cavalry_health_bonus = _parse_loose_float(request.form.get("cavalry_health_bonus"), 0.0)
        archer_attack_bonus = _parse_loose_float(request.form.get("archer_attack_bonus"), 0.0)
        archer_defense_bonus = _parse_loose_float(request.form.get("archer_defense_bonus"), 0.0)
        archer_lethality_bonus = _parse_loose_float(request.form.get("archer_lethality_bonus"), 0.0)
        archer_health_bonus = _parse_loose_float(request.form.get("archer_health_bonus"), 0.0)
        formation_infantry_pct = _parse_loose_float(request.form.get("formation_infantry_pct"), 0.0)
        formation_cavalry_pct = _parse_loose_float(request.form.get("formation_cavalry_pct"), 0.0)
        formation_archer_pct = _parse_loose_float(request.form.get("formation_archer_pct"), 0.0)

        if not player_name or not game_id:
            _set_error("Player name and game ID are required.")
            return _redirect_to_alliance_dashboard(user)

        formation_values = (formation_infantry_pct, formation_cavalry_pct, formation_archer_pct)
        if any(value < 0 or value > 100 or not value.is_integer() for value in formation_values):
            _set_error("Formation percentages must be whole numbers between 0 and 100.")
            return _redirect_to_alliance_dashboard(user)
        if sum(formation_values) != 100:
            _set_error("Formation percentages must add up to exactly 100%.")
            return _redirect_to_alliance_dashboard(user)
        formation_infantry_pct = int(formation_infantry_pct)
        formation_cavalry_pct = int(formation_cavalry_pct)
        formation_archer_pct = int(formation_archer_pct)

        try:
            vip_value = int(vip_level or 0)
            if vip_value < 0:
                vip_value = 0
            if vip_value > 12:
                vip_value = 12
        except ValueError:
            vip_value = 0

        hero_progress = _build_hero_progress_from_form(request.form)
        now = datetime.now(timezone.utc).isoformat()
        with _get_db_connection() as connection:
            game_id_match = connection.execute(
                """
                SELECT * FROM alliance_players
                WHERE alliance_id = ? AND game_id = ?
                ORDER BY id DESC
                LIMIT 1
                """,
                (alliance["id"], game_id),
            ).fetchone()

            if game_id_match and int(game_id_match["user_id"] or 0) != int(target_user_id):
                previous_owner_user_id = int(game_id_match["user_id"] or 0)
                existing_for_target = connection.execute(
                    """
                    SELECT id FROM alliance_players
                    WHERE alliance_id = ? AND user_id = ?
                    ORDER BY id DESC
                    LIMIT 1
                    """,
                    (alliance["id"], target_user_id),
                ).fetchone()
                if existing_for_target and int(existing_for_target["id"]) != int(game_id_match["id"]):
                    connection.execute("DELETE FROM alliance_players WHERE id = ?", (int(existing_for_target["id"]),))

                connection.execute(
                    "UPDATE alliance_players SET user_id = ?, updated_at = ? WHERE id = ?",
                    (target_user_id, now, int(game_id_match["id"])),
                )
                if previous_owner_user_id:
                    _detach_orphan_synthetic_alliance_user(connection, previous_owner_user_id, now)
                _detach_shadow_synthetic_alliance_users(connection, int(alliance["id"]), game_id, target_user_id, now)

            if requested_profile_id and not user.get("is_admin"):
                existing = connection.execute(
                    "SELECT * FROM alliance_players WHERE id = ? AND alliance_id = ? AND user_id = ?",
                    (requested_profile_id, alliance["id"], target_user_id),
                ).fetchone()
            else:
                existing = connection.execute(
                    "SELECT * FROM alliance_players WHERE alliance_id = ? AND user_id = ? ORDER BY id ASC LIMIT 1",
                    (alliance["id"], target_user_id),
                ).fetchone()
            bt_value = requested_bt_value if user.get("is_admin") and requested_bt_value in {"BT1", "BT2", "Both"} else ""
            if existing and not user.get("is_admin"):
                bt_value = str(existing["bt"] or "").strip()
            if existing:
                _insert_player_snapshot_if_not_first_ever(connection, int(alliance["id"]), existing, now)
                connection.execute(
                    """
                    UPDATE alliance_players
                    SET player_name = ?, game_id = ?, vip_level = ?, town_hall_level = ?, total_power = ?, power_ac = ?, att_troops = ?, formation_infantry_pct = ?, formation_cavalry_pct = ?, formation_archer_pct = ?, kills = ?, mystic_score = ?, radiant_spire = ?, bt = ?, bt_time = ?,
                        kingdom_id = ?, infantry_troops = ?, cavalry_troops = ?, archer_troops = ?,
                        infantry_attack_bonus = ?, infantry_defense_bonus = ?, infantry_lethality_bonus = ?, infantry_health_bonus = ?,
                        cavalry_attack_bonus = ?, cavalry_defense_bonus = ?, cavalry_lethality_bonus = ?, cavalry_health_bonus = ?,
                        archer_attack_bonus = ?, archer_defense_bonus = ?, archer_lethality_bonus = ?, archer_health_bonus = ?,
                        hero_data = ?, updated_at = ?
                    WHERE id = ?
                    """,
                    (
                        player_name,
                        game_id or None,
                        vip_value,
                        _parse_town_hall_level(town_hall_level, 30),
                        total_power_value,
                        power_ac_value,
                        att_troops_value,
                        formation_infantry_pct,
                        formation_cavalry_pct,
                        formation_archer_pct,
                        kills_value,
                        mystic_score_value,
                        radiant_spire_value,
                        bt_value,
                        bt_time_value,
                        kingdom_id or None,
                        infantry_troops or "TG4",
                        cavalry_troops or "TG4",
                        archer_troops or "TG4",
                        infantry_attack_bonus,
                        infantry_defense_bonus,
                        infantry_lethality_bonus,
                        infantry_health_bonus,
                        cavalry_attack_bonus,
                        cavalry_defense_bonus,
                        cavalry_lethality_bonus,
                        cavalry_health_bonus,
                        archer_attack_bonus,
                        archer_defense_bonus,
                        archer_lethality_bonus,
                        archer_health_bonus,
                        json.dumps(hero_progress),
                        now,
                        existing["id"],
                    ),
                )
            else:
                connection.execute(
                    """
                    INSERT INTO alliance_players (
                        alliance_id, user_id, player_name, game_id, vip_level, town_hall_level, total_power, power_ac, att_troops, formation_infantry_pct, formation_cavalry_pct, formation_archer_pct, kills, mystic_score, radiant_spire, bt, bt_time,
                        kingdom_id, infantry_troops, cavalry_troops, archer_troops,
                        infantry_attack_bonus, infantry_defense_bonus, infantry_lethality_bonus, infantry_health_bonus,
                        cavalry_attack_bonus, cavalry_defense_bonus, cavalry_lethality_bonus, cavalry_health_bonus,
                        archer_attack_bonus, archer_defense_bonus, archer_lethality_bonus, archer_health_bonus,
                        hero_data, created_at, updated_at
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """,
                    (
                        alliance["id"],
                        target_user_id,
                        player_name,
                        game_id,
                        vip_value,
                        _parse_town_hall_level(town_hall_level, 30),
                        total_power_value,
                        power_ac_value,
                        att_troops_value,
                        formation_infantry_pct,
                        formation_cavalry_pct,
                        formation_archer_pct,
                        kills_value,
                        mystic_score_value,
                        radiant_spire_value,
                        bt_value,
                        bt_time_value,
                        kingdom_id or None,
                        infantry_troops or "TG4",
                        cavalry_troops or "TG4",
                        archer_troops or "TG4",
                        infantry_attack_bonus,
                        infantry_defense_bonus,
                        infantry_lethality_bonus,
                        infantry_health_bonus,
                        cavalry_attack_bonus,
                        cavalry_defense_bonus,
                        cavalry_lethality_bonus,
                        cavalry_health_bonus,
                        archer_attack_bonus,
                        archer_defense_bonus,
                        archer_lethality_bonus,
                        archer_health_bonus,
                        json.dumps(hero_progress),
                        now,
                        now,
                    ),
                )

        _set_notice("Player saved successfully.")
        if user.get("is_admin") and target_user_id != int(user["id"]):
            return _redirect_to_alliance_dashboard(user, edit_user_id=target_user_id, tab="my-profile")
        return _redirect_to_alliance_dashboard(user, tab="my-profile")

    @app.get("/simulator")
    def simulator_page() -> str:
        return render_template(
            "simulator.html",
            show_simulator_progress=_can_view_simulator_progress(),
            simulator_client_ip=_get_client_ip(),
        )

    @app.get("/coordinated-attack")
    def coordinated_attack_page() -> str:
        return render_template("coordinated_attack.html")

    @app.get("/privacy")
    def privacy_page() -> str:
        return render_template("privacy.html")

    @app.get("/terms")
    def terms_page() -> str:
        return render_template("terms.html")

    @app.get("/health")
    def health() -> tuple[dict[str, str], int]:
        return {"status": "ok"}, 200

    @app.get("/favicon.ico")
    @app.get("/favicon.webp")
    def favicon() -> Any:
        return send_from_directory(PROJECT_ROOT, "favicon.webp")

    @app.get("/assets/<path:filename>")
    def shared_assets(filename: str) -> Any:
        return send_from_directory(ASSETS_ROOT, filename)

    @app.get("/heroes")
    def heroes_page() -> str:
        q = str(request.args.get("q", "")).strip()
        generation = str(request.args.get("generation", "")).strip()
        rarity = str(request.args.get("rarity", "")).strip()
        troop_type = str(request.args.get("troop_type", "")).strip()
        sort_by = str(request.args.get("sort", "generation")).strip() or "generation"
        tier_category = str(request.args.get("tier_category", "")).strip()
        tier_rank = str(request.args.get("tier_rank", "")).strip().upper()

        # Build name→badges lookup from TIER_LIST_DATA
        name_to_badges: dict[str, list[dict]] = {}
        for cat_key, cat_data in TIER_LIST_DATA.items():
            for rank, names in cat_data["tiers"].items():
                for name in names:
                    key = name.lower()
                    if key not in name_to_badges:
                        name_to_badges[key] = []
                    name_to_badges[key].append({
                        "category_key": cat_key,
                        "category_label": cat_data["label"],
                        "short": cat_data["short"],
                        "tier": rank,
                    })

        # Attach tier_badges to every hero
        heroes_with_badges = [{**h, "tier_badges": name_to_badges.get(str(h.get("name", "")).lower(), [])} for h in heroes]

        filtered = _filter_heroes(heroes_with_badges, q=q, generation=generation, rarity=rarity, troop_type=troop_type)

        # Apply tier filter
        if tier_category:
            cat_data = TIER_LIST_DATA.get(tier_category)
            if cat_data:
                if tier_rank and tier_rank in cat_data["tiers"]:
                    tier_names = {n.lower() for n in cat_data["tiers"][tier_rank]}
                else:
                    tier_names = {n.lower() for names in cat_data["tiers"].values() for n in names}
                filtered = [h for h in filtered if str(h.get("name", "")).lower() in tier_names]

        filtered = _sort_heroes(filtered, sort_by=sort_by)

        # Build tier view data: {cat_key: {rank: [hero, ...]}}
        heroes_for_tier_view: dict[str, dict[str, list]] = {}
        for cat_key, cat_data in TIER_LIST_DATA.items():
            heroes_for_tier_view[cat_key] = {}
            for rank, names in cat_data["tiers"].items():
                tier_heroes = []
                for name in names:
                    match = next((h for h in heroes_with_badges if str(h.get("name", "")).lower() == name.lower()), None)
                    if match:
                        tier_heroes.append(match)
                heroes_for_tier_view[cat_key][rank] = tier_heroes

        generations = sorted({int(h.get("generation", 0)) for h in heroes if int(h.get("generation", 0)) > 0})
        rarities = sorted({str(h.get("rarity", "")) for h in heroes if str(h.get("rarity", "")).strip()})
        troop_types = sorted({str(h.get("troop_type", "")) for h in heroes if str(h.get("troop_type", "")).strip()})
        compare_options = sorted(
            heroes,
            key=lambda item: (
                -int(item.get("generation", 0) or 0),
                str(item.get("name", "")).lower(),
            ),
        )

        return render_template(
            "heroes_list.html",
            heroes=filtered,
            total=len(filtered),
            all_total=len(heroes),
            filters={
                "q": q,
                "generation": generation,
                "rarity": rarity,
                "troop_type": troop_type,
                "sort": sort_by,
                "tier_category": tier_category,
                "tier_rank": tier_rank,
            },
            generations=generations,
            rarities=rarities,
            troop_types=troop_types,
            compare_options=compare_options,
            tier_list_data=TIER_LIST_DATA,
            tier_rank_order=TIER_RANK_ORDER,
            heroes_for_tier_view=heroes_for_tier_view,
        )

    @app.get("/heroes/compare")
    def heroes_compare_page() -> str:
        rarity_rank = {"legendary": 0, "epic": 1, "rare": 2}
        troop_display = {"infantry": "Infantry", "cavalry": "Cavalry", "archer": "Archer", "archers": "Archer"}

        compare_options = sorted(
            [
                {
                    "slug": str(hero.get("slug", "")),
                    "name": str(hero.get("name", "")),
                    "troop_type": str(hero.get("troop_type", "")).strip().lower(),
                    "generation": int(hero.get("generation", 0) or 0),
                    "rarity": str(hero.get("rarity", "")).strip().lower(),
                }
                for hero in heroes
                if str(hero.get("slug", "")).strip()
            ],
            key=lambda item: (
                -int(item.get("generation", 0) or 0),
                rarity_rank.get(str(item.get("rarity", "")).lower(), 99),
                str(item.get("name", "")).lower(),
            ),
        )

        def _group_compare_options(options: list[dict[str, Any]]) -> list[dict[str, Any]]:
            grouped: dict[str, list[dict[str, Any]]] = {}
            ordered_keys: list[str] = []

            for option in options:
                generation = int(option.get("generation", 0) or 0)
                rarity = str(option.get("rarity", "")).strip().lower()
                troop_key = str(option.get("troop_type", "")).strip().lower()
                troop_text = troop_display.get(troop_key, troop_key.title() or "Hero")

                if generation == 1 and rarity:
                    key = f"Generation 1 ({rarity.title()})"
                else:
                    key = f"Generation {generation}" if generation > 0 else "Other"

                if key not in grouped:
                    grouped[key] = []
                    ordered_keys.append(key)

                grouped[key].append(
                    {
                        "slug": str(option.get("slug", "")),
                        "label": f"{option.get('name', '')} ({troop_text})",
                    }
                )

            return [{"label": key, "options": grouped[key]} for key in ordered_keys]

        left_slug = _normalize_slug(str(request.args.get("left", "")).strip())
        right_slug = _normalize_slug(str(request.args.get("right", "")).strip())

        # Preferred param: star points in range 1..30 (5 stars x 6 sub-levels)
        left_star_points_raw = request.args.get("left_star_points")
        right_star_points_raw = request.args.get("right_star_points")

        if left_star_points_raw is None:
            legacy_left_star = _clamp_int(request.args.get("left_star", 1), minimum=1, maximum=5, default=1)
            left_star_points = legacy_left_star * 6
        else:
            left_star_points = _clamp_int(left_star_points_raw, minimum=1, maximum=30, default=1)

        if right_star_points_raw is None:
            legacy_right_star = _clamp_int(request.args.get("right_star", 1), minimum=1, maximum=5, default=1)
            right_star_points = legacy_right_star * 6
        else:
            right_star_points = _clamp_int(right_star_points_raw, minimum=1, maximum=30, default=1)

        left_widget = _clamp_int(request.args.get("left_widget", 0), minimum=0, maximum=10, default=0)
        right_widget = _clamp_int(request.args.get("right_widget", 0), minimum=0, maximum=10, default=0)

        level_state = {
            "left_star_points": left_star_points,
            "right_star_points": right_star_points,
            "left_widget": left_widget,
            "right_widget": right_widget,
        }

        if not left_slug or not right_slug:
            return render_template(
                "heroes_compare.html",
                left_hero=None,
                right_hero=None,
                comparison=None,
                message="Please select two heroes to compare.",
                levels=level_state,
                left_option_groups=_group_compare_options(compare_options),
                right_option_groups=_group_compare_options(compare_options),
            )

        left_hero = heroes_by_slug.get(left_slug)
        right_hero = heroes_by_slug.get(right_slug)

        if not left_hero or not right_hero:
            return render_template(
                "heroes_compare.html",
                left_hero=left_hero,
                right_hero=right_hero,
                comparison=None,
                message="One or both selected heroes were not found.",
                levels=level_state,
                left_option_groups=_group_compare_options(compare_options),
                right_option_groups=_group_compare_options(compare_options),
            )

        if left_slug == right_slug:
            return render_template(
                "heroes_compare.html",
                left_hero=left_hero,
                right_hero=right_hero,
                comparison=None,
                message="Select two different heroes to compare.",
                levels=level_state,
                left_option_groups=_group_compare_options(compare_options),
                right_option_groups=_group_compare_options(compare_options),
            )

        left_troop = str(left_hero.get("troop_type", "")).strip().lower()
        right_compatible_options = [
            option
            for option in compare_options
            if option.get("troop_type") == left_troop and option.get("slug") != left_slug
        ]

        right_compatible_slugs = {str(option.get("slug", "")) for option in right_compatible_options}
        if right_compatible_options and right_slug not in right_compatible_slugs:
            right_slug = str(right_compatible_options[0].get("slug", right_slug))
            right_hero = heroes_by_slug.get(right_slug, right_hero)

        left_option_groups = _group_compare_options(compare_options)
        right_option_source = right_compatible_options if right_compatible_options else [
            option for option in compare_options if option.get("slug") != left_slug
        ]
        right_option_groups = _group_compare_options(right_option_source)

        comparison = _build_hero_comparison(
            left_hero,
            right_hero,
            left_star_points=left_star_points,
            left_widget_level=left_widget,
            right_star_points=right_star_points,
            right_widget_level=right_widget,
        )
        return render_template(
            "heroes_compare.html",
            left_hero=left_hero,
            right_hero=right_hero,
            comparison=comparison,
            message="",
            levels=level_state,
            left_option_groups=left_option_groups,
            right_option_groups=right_option_groups,
        )

    @app.get("/heroes/<slug>")
    def hero_detail_page(slug: str) -> str:
        hero = heroes_by_slug.get(_normalize_slug(slug))
        if not hero:
            abort(404)
        hero_name_lower = str(hero.get("name", "")).lower()
        tier_badges: list[dict] = []
        for cat_key, cat_data in TIER_LIST_DATA.items():
            for rank, names in cat_data["tiers"].items():
                if any(n.lower() == hero_name_lower for n in names):
                    tier_badges.append({
                        "category_key": cat_key,
                        "category_label": cat_data["label"],
                        "short": cat_data["short"],
                        "tier": rank,
                    })
        return render_template("hero_detail.html", hero=hero, tier_badges=tier_badges)

    @app.get("/api/heroes")
    def api_heroes() -> tuple[Any, int]:
        q = str(request.args.get("q", "")).strip()
        generation = str(request.args.get("generation", "")).strip()
        rarity = str(request.args.get("rarity", "")).strip()
        troop_type = str(request.args.get("troop_type", "")).strip()
        sort_by = str(request.args.get("sort", "generation")).strip() or "generation"
        filtered = _filter_heroes(heroes, q=q, generation=generation, rarity=rarity, troop_type=troop_type)
        filtered = _sort_heroes(filtered, sort_by=sort_by)
        return jsonify({"total": len(filtered), "heroes": filtered}), 200

    @app.get("/api/heroes/<slug>")
    def api_hero_detail(slug: str) -> tuple[Any, int]:
        hero = heroes_by_slug.get(_normalize_slug(slug))
        if not hero:
            return jsonify({"message": "Hero not found"}), 404
        return jsonify(hero), 200

    @app.post("/api/optimize")
    def api_optimize() -> tuple[Any, int]:
        payload = request.get_json(silent=True)
        ok, error = _validate_payload(payload if isinstance(payload, dict) else {})
        if not ok:
            return jsonify({"possible": False, "message": error}), 400

        try:
            result = optimizer.optimize(payload)
            return jsonify(result), 200
        except Exception as exc:
            return jsonify({"possible": False, "message": f"Fallo en optimizacion: {exc}"}), 500

    @app.post("/api/coordinated-attack/calculate")
    def api_coordinated_attack_calculate() -> tuple[Any, int]:
        payload = request.get_json(silent=True)
        ok, error, normalized = _validate_coordinated_attack_payload(payload if isinstance(payload, dict) else {})
        if not ok:
            return jsonify({"ok": False, "message": error}), 400

        try:
            result = _build_coordinated_attack_result(normalized)
        except ValueError as exc:
            return jsonify({"ok": False, "message": str(exc)}), 400

        return jsonify({"ok": True, "result": result}), 200

    @app.get("/api/coordinated-attack/presets")
    def api_coordinated_attack_list_presets() -> tuple[Any, int]:
        target = str(request.args.get("target", "")).strip().upper()
        selected_target = COORDINATED_ATTACK_TARGET_ALIASES.get(target, "")
        selected_target = selected_target if selected_target in COORDINATED_ATTACK_TARGETS else None

        presets = coordinated_storage.list_presets()
        summary = []
        for item in presets:
            canonical_target = COORDINATED_ATTACK_TARGET_ALIASES.get(str(item.get("target", "")).strip().upper(), "")
            if selected_target and canonical_target != selected_target:
                continue
            summary.append(
                {
                    "name": str(item.get("name", "")).strip(),
                    "target": canonical_target,
                    "updated_at": str(item.get("updated_at", "")).strip(),
                }
            )

        summary.sort(key=lambda value: (value["target"], value["name"].lower()))
        return jsonify({"ok": True, "presets": summary}), 200

    @app.get("/api/coordinated-attack/presets/<preset_name>")
    def api_coordinated_attack_get_preset(preset_name: str) -> tuple[Any, int]:
        target = str(request.args.get("target", "")).strip().upper()
        canonical_target = COORDINATED_ATTACK_TARGET_ALIASES.get(target, "")
        if canonical_target not in COORDINATED_ATTACK_TARGETS:
            return jsonify({"ok": False, "message": "Invalid target for preset loading."}), 400

        preset = None
        for item in coordinated_storage.list_presets():
            if not isinstance(item, dict):
                continue
            item_name = str(item.get("name", "")).strip().lower()
            item_target = COORDINATED_ATTACK_TARGET_ALIASES.get(str(item.get("target", "")).strip().upper(), "")
            if item_name == preset_name.strip().lower() and item_target == canonical_target:
                preset = item
                break

        if not preset:
            return jsonify({"ok": False, "message": "Preset not found."}), 404

        form = preset.get("form") if isinstance(preset.get("form"), dict) else {}
        if isinstance(form, dict):
            form["target"] = canonical_target

        return jsonify({"ok": True, "preset": preset}), 200

    @app.post("/api/coordinated-attack/presets")
    def api_coordinated_attack_save_preset() -> tuple[Any, int]:
        payload = request.get_json(silent=True)
        if not isinstance(payload, dict):
            return jsonify({"ok": False, "message": "Invalid payload."}), 400

        name = str(payload.get("name", "")).strip()
        if not name:
            return jsonify({"ok": False, "message": "Preset name is required."}), 400

        form_payload = payload.get("form")
        ok, error, normalized = _validate_coordinated_attack_payload(form_payload if isinstance(form_payload, dict) else {})
        if not ok:
            return jsonify({"ok": False, "message": error}), 400

        preset = {
            "name": name,
            "target": normalized["target"],
            "updated_at": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC"),
            "form": {
                "target": normalized["target"],
                "time_mode": normalized["time_mode"],
                "coordinated_time_utc": normalized["coordinated_time_utc"],
                "rally_minutes": normalized["rally_minutes"],
                "players": [
                    {
                        "nick": item["nick"],
                        "march_time": item["march_time"],
                    }
                    for item in normalized["players"]
                ],
                "attack_ratio": normalized["attack_ratio"],
                "defense_ratio": normalized["defense_ratio"],
                "attack_line": normalized["attack_line"],
                "defense_line": normalized["defense_line"],
            },
        }

        coordinated_storage.upsert_preset(preset)
        return jsonify({"ok": True, "preset": {"name": preset["name"], "target": preset["target"], "updated_at": preset["updated_at"]}}), 200

    @app.delete("/api/coordinated-attack/presets/<preset_name>")
    def api_coordinated_attack_delete_preset(preset_name: str) -> tuple[Any, int]:
        target = str(request.args.get("target", "")).strip().upper()
        canonical_target = COORDINATED_ATTACK_TARGET_ALIASES.get(target, "")
        if canonical_target not in COORDINATED_ATTACK_TARGETS:
            return jsonify({"ok": False, "message": "Invalid target for preset deletion."}), 400

        deleted = coordinated_storage.delete_preset(preset_name, canonical_target)
        if not deleted:
            return jsonify({"ok": False, "message": "Preset not found."}), 404

        return jsonify({"ok": True}), 200

    return app


def _next_weekly_sync_at(now: datetime | None = None) -> datetime:
    current = now or datetime.now(timezone.utc)
    if current.tzinfo is None:
        current = current.replace(tzinfo=timezone.utc)
    else:
        current = current.astimezone(timezone.utc)
    days_until_monday = (7 - current.weekday()) % 7
    candidate = (current + timedelta(days=days_until_monday)).replace(hour=0, minute=0, second=0, microsecond=0)
    if candidate <= current:
        candidate += timedelta(days=7)
    return candidate


def _run_scheduled_sync_job(alliance_id: int, job_type: str, runner: Any, *args: Any) -> dict[str, Any]:
    now = time.time()
    with JEABS_SYNC_JOBS_LOCK:
        for job in JEABS_SYNC_JOBS.values():
            if int(job.get("alliance_id") or 0) == alliance_id and job.get("state") in {"pending", "running"}:
                return {"state": "skipped", "message": "Another synchronization is already running."}
        job_id = f"weekly-{job_type}-{alliance_id}-{int(now)}"
        JEABS_SYNC_JOBS[job_id] = {
            "job_id": job_id,
            "alliance_id": alliance_id,
            "job_type": job_type,
            "state": "pending",
            "stage": f"Starting weekly {job_type} synchronization",
            "completed": 0,
            "total": 0,
            "percent": 0,
            "message": "",
            "created_at": now,
            "updated_at": now,
        }
    runner(job_id, alliance_id, *args)
    with JEABS_SYNC_JOBS_LOCK:
        return dict(JEABS_SYNC_JOBS.get(job_id) or {})


def _run_weekly_jeabs_sync_cycle() -> list[dict[str, Any]]:
    with _get_db_connection() as connection:
        alliances = [dict(row) for row in connection.execute("SELECT * FROM alliances ORDER BY id ASC").fetchall()]

    results: list[dict[str, Any]] = []
    for alliance in alliances:
        alliance_id = int(alliance["id"])
        token = _get_jeabs_token(alliance)
        if not token:
            continue
        jeabs_alliance_id = str(alliance.get("jeabs_alliance_id") or "").strip()
        if jeabs_alliance_id:
            result = _run_scheduled_sync_job(
                alliance_id,
                "players",
                _run_jeabs_sync_job,
                jeabs_alliance_id,
                token,
            )
            results.append({"alliance_id": alliance_id, "job_type": "players", **result})

        if alliance.get("nap4_config_json"):
            entries = _parse_nap4_entries(alliance.get("nap4_config_json"), alliance)
            if any(str(entry.get("jeabs_id") or "").strip() for entry in entries):
                result = _run_scheduled_sync_job(alliance_id, "nap4", _run_nap4_sync_job)
                results.append({"alliance_id": alliance_id, "job_type": "nap4", **result})

        for slot in (1, 2):
            rival_id_field, _, _, _ = _swordland_storage_fields(slot)
            if not str(alliance.get(rival_id_field) or "").strip():
                continue
            result = _run_scheduled_sync_job(
                alliance_id,
                f"swordland-{slot}",
                _run_swordland_sync_job,
                slot,
            )
            results.append({"alliance_id": alliance_id, "job_type": f"swordland-{slot}", **result})

    completed = sum(1 for result in results if result.get("state") == "complete")
    failed = sum(1 for result in results if result.get("state") == "error")
    skipped = sum(1 for result in results if result.get("state") == "skipped")
    print(
        f"Weekly JeabsPlus sync finished: {completed} complete, {failed} failed, {skipped} skipped.",
        flush=True,
    )
    return results


def _weekly_jeabs_sync_scheduler() -> None:
    while True:
        next_run = _next_weekly_sync_at()
        wait_seconds = max(1.0, (next_run - datetime.now(timezone.utc)).total_seconds())
        print(f"Next weekly JeabsPlus sync: {next_run.isoformat()}.", flush=True)
        time.sleep(wait_seconds)
        _run_weekly_jeabs_sync_cycle()


def _start_weekly_jeabs_sync_scheduler() -> threading.Thread:
    scheduler = threading.Thread(
        target=_weekly_jeabs_sync_scheduler,
        daemon=True,
        name="weekly-jeabs-sync",
    )
    scheduler.start()
    return scheduler


def main() -> None:
    app = create_app()
    _start_weekly_jeabs_sync_scheduler()
    app.run(host="0.0.0.0", port=8086, debug=False)


if __name__ == "__main__":
    main()