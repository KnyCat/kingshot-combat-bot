from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
import contextlib
import io
import json
from pathlib import Path
from typing import Any

from models.battle import BattleCalculator
from models.hero import BattleHeroes
from models.troop import TroopComposition, TroopStats
from models.troop_base_stats import get_troop_base_stats


@dataclass
class HeroChoice:
    name: str
    level: int
    damage_up: float
    defense_up: float
    opp_damage_down: float


@dataclass
class CandidateResult:
    infantry_pct: int
    cavalry_pct: int
    archers_pct: int
    heroes: list[HeroChoice]
    damage_boost: int
    defense_boost: int
    health_boost: int
    turns_to_win: int
    casualty_pct: float
    score: float


class BattleCompositionOptimizer:
    """Find winning compositions with minimum boost cost under constraints."""

    def __init__(self) -> None:
        self._joiner_catalog = self._load_joiner_catalog()

    def _load_joiner_catalog(self) -> dict[str, dict[str, float]]:
        data_path = Path("data/heroes.json")
        if not data_path.exists():
            return {}

        with data_path.open("r", encoding="utf-8") as handle:
            raw = json.load(handle)

        catalog: dict[str, dict[str, float]] = {}
        for item in raw.get("joiner_heroes", []):
            name = str(item.get("name", "")).strip().lower()
            if not name:
                continue
            catalog[name] = {
                "damage_up": float(item.get("damage_up", 0.0) or 0.0),
                "defense_up": float(item.get("defense_up", 0.0) or 0.0),
                "opp_damage_down": float(item.get("opp_damage_down", 0.0) or 0.0),
            }
        return catalog

    @staticmethod
    def _normalize_pct(value: int | float) -> int:
        return max(0, min(100, int(value)))

    def _parse_hero_inputs(self, items: list[dict[str, Any]]) -> list[HeroChoice]:
        parsed: list[HeroChoice] = []
        for entry in items:
            name = str(entry.get("name", "")).strip()
            if not name:
                continue
            key = name.lower()
            if key not in self._joiner_catalog:
                continue
            level = max(1, min(100, int(entry.get("level", 100) or 100)))
            scale = level / 100.0
            base = self._joiner_catalog[key]
            parsed.append(
                HeroChoice(
                    name=name,
                    level=level,
                    damage_up=float(base["damage_up"]) * scale,
                    defense_up=float(base["defense_up"]) * scale,
                    opp_damage_down=float(base["opp_damage_down"]) * scale,
                )
            )
        return parsed

    @staticmethod
    def _make_troop_stats(
        attack: float,
        lethality: float,
        defense: float,
        health: float,
        count: int,
        troop_type: str,
        base_attack: float,
        base_lethality: float,
        base_defense: float,
        base_health: float,
    ) -> TroopStats:
        # Backward compatibility for environments where TroopStats lacks base_* kwargs.
        try:
            return TroopStats(
                attack=attack,
                lethality=lethality,
                defense=defense,
                health=health,
                count=count,
                troop_type=troop_type,
                base_attack=base_attack,
                base_lethality=base_lethality,
                base_defense=base_defense,
                base_health=base_health,
            )
        except TypeError:
            return TroopStats(
                attack=attack,
                lethality=lethality,
                defense=defense,
                health=health,
                count=count,
                troop_type=troop_type,
            )

    @staticmethod
    def _build_compositions(step: int) -> list[tuple[int, int, int]]:
        out: list[tuple[int, int, int]] = []
        for inf in range(10, 81, step):
            for cav in range(10, 81, step):
                arc = 100 - inf - cav
                if arc < 10:
                    continue
                out.append((inf, cav, arc))
        return out

    @staticmethod
    def _build_hero_sets(heroes: list[HeroChoice], max_team_size: int = 4) -> list[list[HeroChoice]]:
        if not heroes:
            return [[]]

        limited = heroes[:8]
        all_sets: list[list[HeroChoice]] = [[]]
        max_size = min(max_team_size, len(limited))
        for size in range(1, max_size + 1):
            for combo in combinations(limited, size):
                all_sets.append(list(combo))
        return all_sets

    @staticmethod
    def _aggregate_hero_effects(heroes: list[HeroChoice]) -> dict[str, float]:
        agg = {"damage_up": 0.0, "defense_up": 0.0, "opp_damage_down": 0.0}
        for hero in heroes:
            agg["damage_up"] += hero.damage_up
            agg["defense_up"] += hero.defense_up
            agg["opp_damage_down"] += hero.opp_damage_down
        return agg

    def _build_troops(
        self,
        total_troops: int,
        comp: tuple[int, int, int],
        troop_level: str,
        damage_boost: int,
        defense_boost: int,
        health_boost: int,
        hero_effects: dict[str, float],
    ) -> TroopComposition:
        inf_pct, cav_pct, arc_pct = comp
        inf_count = max(1, int(total_troops * inf_pct / 100))
        cav_count = max(1, int(total_troops * cav_pct / 100))
        arc_count = max(1, total_troops - inf_count - cav_count)

        hero_damage_pct = hero_effects["damage_up"] * 100.0
        hero_defense_pct = hero_effects["defense_up"] * 100.0

        inf_base = get_troop_base_stats("infantry", troop_level)
        cav_base = get_troop_base_stats("cavalry", troop_level)
        arc_base = get_troop_base_stats("archers", troop_level)

        return TroopComposition(
            infantry=self._make_troop_stats(
                attack=damage_boost + hero_damage_pct,
                lethality=damage_boost + hero_damage_pct,
                defense=defense_boost + hero_defense_pct,
                health=health_boost + hero_defense_pct,
                count=inf_count,
                troop_type="infantry",
                base_attack=inf_base["attack"],
                base_lethality=inf_base["lethality"],
                base_defense=inf_base["defense"],
                base_health=inf_base["health"],
            ),
            cavalry=self._make_troop_stats(
                attack=damage_boost + hero_damage_pct,
                lethality=damage_boost + hero_damage_pct,
                defense=defense_boost + hero_defense_pct,
                health=health_boost + hero_defense_pct,
                count=cav_count,
                troop_type="cavalry",
                base_attack=cav_base["attack"],
                base_lethality=cav_base["lethality"],
                base_defense=cav_base["defense"],
                base_health=cav_base["health"],
            ),
            archers=self._make_troop_stats(
                attack=damage_boost + hero_damage_pct,
                lethality=damage_boost + hero_damage_pct,
                defense=defense_boost + hero_defense_pct,
                health=health_boost + hero_defense_pct,
                count=arc_count,
                troop_type="archers",
                base_attack=arc_base["attack"],
                base_lethality=arc_base["lethality"],
                base_defense=arc_base["defense"],
                base_health=arc_base["health"],
            ),
        )

    @staticmethod
    def _make_enemy_comp(payload: dict[str, Any]) -> TroopComposition:
        total = int(payload["total_troops"])
        inf = int(payload["infantry_pct"])
        cav = int(payload["cavalry_pct"])
        arc = int(payload["archers_pct"])

        inf_count = max(1, int(total * inf / 100))
        cav_count = max(1, int(total * cav / 100))
        arc_count = max(1, total - inf_count - cav_count)

        level = str(payload["troop_level"])
        inf_base = get_troop_base_stats("infantry", level)
        cav_base = get_troop_base_stats("cavalry", level)
        arc_base = get_troop_base_stats("archers", level)

        dmg = int(payload.get("damage_boost", 0) or 0)
        defense = int(payload.get("defense_boost", 0) or 0)
        health = int(payload.get("health_boost", 0) or 0)

        return TroopComposition(
            infantry=BattleCompositionOptimizer._make_troop_stats(
                attack=dmg,
                lethality=dmg,
                defense=defense,
                health=health,
                count=inf_count,
                troop_type="infantry",
                base_attack=inf_base["attack"],
                base_lethality=inf_base["lethality"],
                base_defense=inf_base["defense"],
                base_health=inf_base["health"],
            ),
            cavalry=BattleCompositionOptimizer._make_troop_stats(
                attack=dmg,
                lethality=dmg,
                defense=defense,
                health=health,
                count=cav_count,
                troop_type="cavalry",
                base_attack=cav_base["attack"],
                base_lethality=cav_base["lethality"],
                base_defense=cav_base["defense"],
                base_health=cav_base["health"],
            ),
            archers=BattleCompositionOptimizer._make_troop_stats(
                attack=dmg,
                lethality=dmg,
                defense=defense,
                health=health,
                count=arc_count,
                troop_type="archers",
                base_attack=arc_base["attack"],
                base_lethality=arc_base["lethality"],
                base_defense=arc_base["defense"],
                base_health=arc_base["health"],
            ),
        )

    @staticmethod
    def _boost_candidates(max_damage: int, max_defense: int, max_health: int, step: int = 5) -> list[tuple[int, int, int]]:
        candidates: list[tuple[int, int, int]] = []
        for dmg in range(0, max_damage + 1, step):
            for defense in range(0, max_defense + 1, step):
                for health in range(0, max_health + 1, step):
                    candidates.append((dmg, defense, health))

        candidates.sort(key=lambda x: (x[0] + x[1] + x[2], x[0], x[1], x[2]))
        return candidates

    @staticmethod
    def _score(win_turns: int, casualty_pct: float, dmg: int, defense: int, health: int) -> float:
        return (dmg + defense + health) * 1000.0 + win_turns * 10.0 + casualty_pct

    def optimize(self, payload: dict[str, Any]) -> dict[str, Any]:
        player = payload["player"]
        enemy = payload["enemy"]

        available_heroes = self._parse_hero_inputs(player.get("available_heroes", []))
        hero_sets = self._build_hero_sets(available_heroes)
        compositions = self._build_compositions(int(player.get("composition_step", 10) or 10))

        enemy_comp = self._make_enemy_comp(enemy)
        enemy_heroes = BattleHeroes()

        boost_space = self._boost_candidates(
            self._normalize_pct(player.get("max_damage_boost", 0)),
            self._normalize_pct(player.get("max_defense_boost", 0)),
            self._normalize_pct(player.get("max_health_boost", 0)),
            step=int(player.get("boost_step", 5) or 5),
        )

        total_troops = int(player["total_troops"])
        troop_level = str(player["troop_level"])

        winners: list[CandidateResult] = []
        simulated = 0

        for comp in compositions:
            for hero_set in hero_sets:
                hero_effects = self._aggregate_hero_effects(hero_set)

                for dmg, defense, health in boost_space:
                    candidate_player = self._build_troops(
                        total_troops=total_troops,
                        comp=comp,
                        troop_level=troop_level,
                        damage_boost=dmg,
                        defense_boost=defense,
                        health_boost=health,
                        hero_effects=hero_effects,
                    )

                    simulated += 1
                    with contextlib.redirect_stdout(io.StringIO()):
                        result = BattleCalculator.simulate_battle(
                            attacker=candidate_player,
                            attacker_heroes=BattleHeroes(),
                            defender=enemy_comp,
                            defender_heroes=enemy_heroes,
                            max_turns=int(payload.get("max_turns", 300) or 300),
                        )

                    if not result.attacker_wins:
                        continue

                    casualties = sum(result.attacker_casualties.values())
                    casualty_pct = 0.0
                    if candidate_player.total_troops > 0:
                        casualty_pct = (casualties / candidate_player.total_troops) * 100.0

                    candidate = CandidateResult(
                        infantry_pct=comp[0],
                        cavalry_pct=comp[1],
                        archers_pct=comp[2],
                        heroes=hero_set,
                        damage_boost=dmg,
                        defense_boost=defense,
                        health_boost=health,
                        turns_to_win=result.turns_to_win_attacker,
                        casualty_pct=round(casualty_pct, 2),
                        score=self._score(result.turns_to_win_attacker, casualty_pct, dmg, defense, health),
                    )
                    winners.append(candidate)
                    break

        winners.sort(key=lambda item: item.score)
        top3 = winners[:3]

        return {
            "possible": len(top3) > 0,
            "searched": {
                "compositions": len(compositions),
                "hero_sets": len(hero_sets),
                "boost_candidates": len(boost_space),
                "simulations": simulated,
            },
            "results": [
                {
                    "composition": {
                        "infantry_pct": item.infantry_pct,
                        "cavalry_pct": item.cavalry_pct,
                        "archers_pct": item.archers_pct,
                    },
                    "heroes": [{"name": h.name, "level": h.level} for h in item.heroes],
                    "boosts": {
                        "damage_boost": item.damage_boost,
                        "defense_boost": item.defense_boost,
                        "health_boost": item.health_boost,
                    },
                    "outcome": {
                        "turns_to_win": item.turns_to_win,
                        "casualty_pct": item.casualty_pct,
                    },
                    "explanation": (
                        f"Win in {item.turns_to_win} turns with {item.casualty_pct:.2f}% casualties. "
                        f"Total boost cost={item.damage_boost + item.defense_boost + item.health_boost}."
                    ),
                }
                for item in top3
            ],
            "message": "No se encontro composicion ganadora con los limites actuales de heroes/boosts." if not top3 else "",
        }
