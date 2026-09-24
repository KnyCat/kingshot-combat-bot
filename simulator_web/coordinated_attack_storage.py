from __future__ import annotations

import json
import tempfile
from pathlib import Path
from typing import Any


class CoordinatedAttackStorage:
    """Simple JSON storage with atomic writes for coordinated attack presets."""

    def __init__(self, file_path: Path) -> None:
        self.file_path = file_path

    def _default_payload(self) -> dict[str, Any]:
        return {"presets": []}

    def load(self) -> dict[str, Any]:
        if not self.file_path.exists():
            return self._default_payload()

        try:
            with self.file_path.open("r", encoding="utf-8") as handle:
                payload = json.load(handle)
        except (json.JSONDecodeError, OSError):
            return self._default_payload()

        if not isinstance(payload, dict):
            return self._default_payload()

        presets = payload.get("presets", [])
        if not isinstance(presets, list):
            presets = []

        return {"presets": presets}

    def save(self, payload: dict[str, Any]) -> None:
        self.file_path.parent.mkdir(parents=True, exist_ok=True)

        data = {"presets": payload.get("presets", []) if isinstance(payload.get("presets"), list) else []}

        with tempfile.NamedTemporaryFile("w", encoding="utf-8", delete=False, dir=str(self.file_path.parent)) as tmp:
            json.dump(data, tmp, ensure_ascii=True, indent=2)
            temp_name = tmp.name

        Path(temp_name).replace(self.file_path)

    def list_presets(self, target: str | None = None) -> list[dict[str, Any]]:
        payload = self.load()
        presets = payload.get("presets", [])
        if not isinstance(presets, list):
            return []

        cleaned: list[dict[str, Any]] = []
        for item in presets:
            if not isinstance(item, dict):
                continue
            if target and str(item.get("target", "")).upper() != target.upper():
                continue
            cleaned.append(item)
        return cleaned

    def upsert_preset(self, preset: dict[str, Any]) -> dict[str, Any]:
        payload = self.load()
        presets = payload.get("presets", [])
        if not isinstance(presets, list):
            presets = []

        name = str(preset.get("name", "")).strip()
        target = str(preset.get("target", "")).strip().upper()

        replaced = False
        for idx, item in enumerate(presets):
            if not isinstance(item, dict):
                continue
            item_name = str(item.get("name", "")).strip()
            item_target = str(item.get("target", "")).strip().upper()
            if item_name.lower() == name.lower() and item_target == target:
                presets[idx] = preset
                replaced = True
                break

        if not replaced:
            presets.append(preset)

        payload["presets"] = presets
        self.save(payload)
        return preset

    def get_preset(self, name: str, target: str) -> dict[str, Any] | None:
        name_l = name.strip().lower()
        target_u = target.strip().upper()
        for item in self.list_presets(target=target_u):
            if str(item.get("name", "")).strip().lower() == name_l:
                return item
        return None

    def delete_preset(self, name: str, target: str) -> bool:
        payload = self.load()
        presets = payload.get("presets", [])
        if not isinstance(presets, list):
            return False

        name_l = name.strip().lower()
        target_u = target.strip().upper()

        filtered = []
        removed = False
        for item in presets:
            if not isinstance(item, dict):
                filtered.append(item)
                continue

            item_name = str(item.get("name", "")).strip().lower()
            item_target = str(item.get("target", "")).strip().upper()
            if item_name == name_l and item_target == target_u:
                removed = True
                continue

            filtered.append(item)

        if not removed:
            return False

        payload["presets"] = filtered
        self.save(payload)
        return True
