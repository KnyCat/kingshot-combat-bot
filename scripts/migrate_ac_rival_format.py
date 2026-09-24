from __future__ import annotations

import json
import re
import shutil
import sqlite3
from datetime import datetime, timezone
from pathlib import Path


DATABASE_PATH = Path("data/alliance_registry.sqlite3")
LANES = ("lane_a", "lane_b", "lane_c")


def convert_rivals(text: str) -> str:
    converted = []
    for index, line in enumerate(str(text or "").splitlines(), 1):
        stripped = line.strip()
        if not stripped:
            continue
        if re.match(r"^\d+\s*-\s*.+?\s*-\s*[\d.,]+$", stripped):
            converted.append(stripped)
            continue
        match = re.match(r"^(.*?)\s+([\d.,]+)$", stripped)
        converted.append(f"{index} - {match.group(1)} - {match.group(2)}" if match else stripped)
    return "\n".join(converted)


backup_path = DATABASE_PATH.with_name(
    f"{DATABASE_PATH.stem}.before-ac-format-{datetime.now(timezone.utc):%Y%m%d-%H%M%S}.sqlite3"
)
shutil.copy2(DATABASE_PATH, backup_path)

updated = []
with sqlite3.connect(DATABASE_PATH) as connection:
    rows = connection.execute(
        "SELECT id, name, ac_plan_json FROM alliances WHERE ac_plan_json IS NOT NULL"
    ).fetchall()
    for alliance_id, alliance_name, raw_plan in rows:
        try:
            plan = json.loads(raw_plan or "{}")
        except json.JSONDecodeError:
            continue
        rivals = plan.get("rivals")
        if not isinstance(rivals, dict):
            continue
        changed = False
        for lane in LANES:
            converted = convert_rivals(rivals.get(lane, ""))
            if converted != rivals.get(lane, ""):
                rivals[lane] = converted
                changed = True
        if changed:
            connection.execute(
                "UPDATE alliances SET ac_plan_json = ?, updated_at = ? WHERE id = ?",
                (json.dumps(plan), datetime.now(timezone.utc).isoformat(), alliance_id),
            )
            updated.append((alliance_id, alliance_name, {lane: len(rivals.get(lane, "").splitlines()) for lane in LANES}))

print(json.dumps({"backup": str(backup_path), "updated": updated}, ensure_ascii=True))