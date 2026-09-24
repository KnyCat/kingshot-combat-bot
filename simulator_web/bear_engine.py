from __future__ import annotations

import hashlib
import json
import math
import random
import statistics
from typing import Any

from models.troop_base_stats import get_troop_base_stats

BEAR_DEFENSE = 4.43
BEAR_TROOPS = 5000
BEAR_ROUNDS = 10
BASE_LETHALITY = 10.0
TROOP_CLASSES = ("infantry", "cavalry", "archers")
TYPE_BONUSES = (1.0, 1.0, 1.10)
SUPPORTED_TIERS = {
    "T10", "T11",
    "T10-TG5", "T10-TG6", "T10-TG7", "T10-TG8",
    "T11-TG5", "T11-TG6", "T11-TG7", "T11-TG8",
}
TROOP_TIER_CONFIDENCE = {
    tier: ("HIGH_CONFIDENCE" if "-TG" in tier else "CONFIRMED")
    for tier in SUPPORTED_TIERS
}
LEADER_CLASSES = {
    "infantry": {"amadeus", "helga", "zoe"},
    "cavalry": {"petra", "hilde", "margot", "thrud"},
    "archers": {"marlin", "rosa", "yang"},
}
JOINER_EFFECTS = {
    "chenko": ("damage_up", 101, 25.0),
    "yeonwoo": ("damage_up", 101, 25.0),
    "amane": ("damage_up", 102, 25.0),
    "margot": ("damage_up", 102, 25.0),
}
STAT_JOINER_EFFECTS = {
    "chenko": ("LETHALITY_UP", 25.0, 101),
    "yeonwoo": ("LETHALITY_UP", 25.0, 101),
    "amane": ("ATK_UP", 25.0, 102),
    "margot": ("ATK_UP", 25.0, 102),
}
LEADER_STAT_EFFECT_NAMES = {
    "amadeus": {"attack_all": "Way of the Blade", "lethality_all": "Battle Ready"},
    "helga": {"attack_all": "Echoes of Valhalla", "lethality_all": "Nature's Balance"},
    "zoe": {"attack_all": "Charisma"},
    "hilde": {"attack_all": "Noble Path"},
    "margot": {"attack_all": "Warbringer"},
    "rosa": {"attack_archers": "Rosa Archer Attack"},
}
PROBABLE_EFFECT_OPS = {
    "generic_damage_up": 102,
    "rally_attack_up": 102,
    "rally_lethality_up": 101,
}
WIDGET_SPECS = {
    "amadeus": ("discernment", "rally_attack_up"),
    "helga": ("zeal", "rally_lethality_up"),
    "marlin": ("admiral_of_the_line", "rally_lethality_up"),
    "petra": ("cosmic_eye", "rally_attack_up"),
    "rosa": ("perihelion", "rally_lethality_up"),
    "thrud": ("wolf_kissed", "rally_lethality_up"),
    "yang": ("offensive_defense", "rally_lethality_up"),
    "ava": ("color_storm", "rally_lethality_up"),
}
WIDGET_SKILL_VALUES = (0.0, 5.0, 7.5, 10.0, 12.5, 15.0)
LEADER_SPECS: dict[str, dict[str, Any]] = {
    "amadeus": {"attack_all": 25.0, "lethality_all": 25.0, "events": [("amadeus_unrighteous_strike", "global", None, 0.40, "damage_up", "generic_damage_up", 50.0)]},
    "helga": {"attack_all": 25.0, "lethality_all": 25.0},
    "zoe": {"attack_all": 25.0, "events": [("zoe_infinite_arsenal", "squad", None, 0.50, "defense_down", 211, 50.0)]},
    "petra": {"events": [
        ("petra_evil_eye", "squad", None, 0.50, "defense_down", 211, 50.0),
        ("petra_the_favor", "squad", None, 0.50, "damage_up", "generic_damage_up", 50.0),
    ]},
    "hilde": {"attack_all": 15.0, "events": [("hilde_elixir", "squad", None, 0.25, "attack_total", None, 100.0)]},
    "margot": {"attack_all": 25.0, "events": [("margot_sleight_hand", "class", "cavalry", 0.25, "extra_attack", None, 200.0)]},
    "thrud": {
        "passive_damage": {"targets": ("infantry", "archers"), "value": 15.0, "operation": "generic_damage_up", "name": "thrud_battle_hunger"},
        "events": [("thrud_reckless_charge", "class", "cavalry", 0.20, "extra_damage", None, 100.0)],
    },
    "marlin": {"events": [
        ("marlin_wild_card", "global", None, 0.40, "damage_up", 101, 50.0),
        ("marlin_dynamo", "squad", None, 0.50, "damage_up", "generic_damage_up", 50.0),
    ]},
    "rosa": {"attack_archers": 30.0, "events": [("rosa_chaos", "global", None, 0.40, "damage_up", "generic_damage_up", 50.0)]},
    "yang": {"events": [
        ("yang_ice_zone", "class", "archers", 0.40, "extra_attack", None, 100.0),
        ("yang_ambush", "global", None, 0.40, "damage_up", "generic_damage_up", 50.0),
    ]},
}


def _resolve_operation(operation: int | str | None, overrides: dict[str, int]) -> int | None:
    if not isinstance(operation, str):
        return operation
    return overrides.get(operation, PROBABLE_EFFECT_OPS[operation])


def _resolve_events(events: list[tuple[Any, ...]], overrides: dict[str, int]) -> list[tuple[Any, ...]]:
    return [
        (name, scope, target, chance, family, _resolve_operation(operation, overrides), value)
        for name, scope, target, chance, family, operation, value in events
    ]


def _widget_value(physical_level: int) -> float:
    return WIDGET_SKILL_VALUES[max(0, min(10, physical_level)) // 2]


def _base_damage_ops(
    joiner_ops: dict[int, float],
    leaders: tuple[str, str, str],
    widget_levels: tuple[int, int, int],
    troop_class: str,
    overrides: dict[str, int],
    widget_stacking_strategy: str,
    leader_specs: list[dict[str, Any]],
) -> tuple[dict[int, float], list[dict[str, Any]], float]:
    buckets = dict(joiner_ops)
    applied = []
    independent_widget_multiplier = 1.0
    for hero_id, physical_level in zip(leaders, widget_levels):
        widget = WIDGET_SPECS.get(hero_id)
        value = _widget_value(physical_level)
        if not widget or value <= 0:
            continue
        effect_name, mapping = widget
        operation = _resolve_operation(mapping, overrides)
        if widget_stacking_strategy == "INDEPENDENT_MULTIPLICATIVE":
            independent_widget_multiplier *= 1.0 + value / 100.0
        else:
            buckets[operation] = buckets.get(operation, 0.0) + value
        applied.append({"hero": hero_id, "effect": effect_name, "value": value, "effect_op": operation, "confidence": "PROBABLE"})
    if "thrud" in leaders and troop_class in ("infantry", "archers"):
        passive = leader_specs[leaders.index("thrud")]["passive_damage"]
        operation = _resolve_operation(passive["operation"], overrides)
        buckets[operation] = buckets.get(operation, 0.0) + passive["value"]
        applied.append({"hero": "thrud", "effect": passive["name"], "value": passive["value"], "effect_op": operation, "confidence": "PROBABLE"})
    return buckets, applied, independent_widget_multiplier


def _stat_family_multiplier(effects: list[dict[str, Any]], stacking_strategy: str) -> float:
    return 1.0 + sum(effect["value"] for effect in effects) / 100.0


def _stat_factor_effects(
    joiners: list[str],
    leaders: tuple[str, str, str],
    widget_levels: tuple[int, int, int],
    leader_specs: list[dict[str, Any]],
    stats_source: str,
    stacking_strategy: str,
    include_leader_stats: bool,
    overrides: dict[str, int],
) -> tuple[tuple[float, float, float], tuple[float, float, float], list[dict[str, Any]], bool]:
    effects: list[dict[str, Any]] = []
    for hero_id in joiners:
        family, value, effect_op = STAT_JOINER_EFFECTS[hero_id]
        effects.append({"source": "joiner", "hero": hero_id, "effect": "first_expedition_skill", "family": family, "value": value, "effect_op": effect_op, "targets": TROOP_CLASSES})
    if include_leader_stats:
        for hero_id, spec in zip(leaders, leader_specs):
            for key, effect_name in LEADER_STAT_EFFECT_NAMES.get(hero_id, {}).items():
                value = spec.get(key, 0.0)
                if not value:
                    continue
                family = "LETHALITY_UP" if key.startswith("lethality") else "ATK_UP"
                targets = TROOP_CLASSES if key.endswith("all") else (key.removeprefix("attack_"),)
                effects.append({"source": "leader_skill", "hero": hero_id, "effect": effect_name, "family": family, "value": value, "effect_op": None, "targets": targets})
    widgets_suppressed = stats_source == "TERROR_REPORT"
    if not widgets_suppressed:
        for hero_id, physical_level in zip(leaders, widget_levels):
            widget = WIDGET_SPECS.get(hero_id)
            value = _widget_value(physical_level)
            if not widget or value <= 0:
                continue
            effect_name, mapping = widget
            family = "ATK_UP" if mapping == "rally_attack_up" else "LETHALITY_UP"
            effects.append({"source": "widget", "hero": hero_id, "effect": effect_name, "family": family, "value": value, "effect_op": _resolve_operation(mapping, overrides), "targets": TROOP_CLASSES})
    attack_multipliers = tuple(
        _stat_family_multiplier([effect for effect in effects if effect["family"] == "ATK_UP" and troop_class in effect["targets"]], stacking_strategy)
        for troop_class in TROOP_CLASSES
    )
    lethality_multipliers = tuple(
        _stat_family_multiplier([effect for effect in effects if effect["family"] == "LETHALITY_UP" and troop_class in effect["targets"]], stacking_strategy)
        for troop_class in TROOP_CLASSES
    )
    return (
        attack_multipliers,
        lethality_multipliers,
        effects,
        widgets_suppressed,
    )


def _round_events(events: list[tuple[Any, ...]], leaders: tuple[str, str, str], leader_specs: list[dict[str, Any]], round_number: int) -> list[tuple[Any, ...]]:
    active = list(events)
    if "thrud" in leaders and round_number in (4, 5, 8, 9):
        value = leader_specs[leaders.index("thrud")].get("ancestral_guidance")
        if value is not None:
            active.append(("thrud_ancestral_guidance", "global", None, 1.0, "damage_up", "generic_damage_up", value))
    return active


def _leader_spec(hero_id: str, level: int, resolved: dict[str, dict[str, Any]]) -> dict[str, Any]:
    if level <= 0:
        return {}
    return resolved.get(hero_id, {"pending": ["leader_skill_values_unresolved"]})


def _op_multiplier(buckets: dict[int, float]) -> float:
    return math.prod(1.0 + value / 100.0 for value in buckets.values())


def joiner_effects(hero_ids: list[str]) -> tuple[float, dict[int, float]]:
    if len(hero_ids) != 4 or any(hero_id not in JOINER_EFFECTS for hero_id in hero_ids):
        raise ValueError("Bear joiners must be four selections from Chenko, Yeonwoo, Amane, and Margot")
    buckets: dict[int, float] = {}
    for hero_id in hero_ids:
        _, operation, value = JOINER_EFFECTS[hero_id]
        buckets[operation] = buckets.get(operation, 0.0) + value
    return _op_multiplier(buckets), buckets


def _validate_leaders(leaders: tuple[str, str, str]) -> None:
    for troop_class, hero_id in zip(TROOP_CLASSES, leaders):
        if hero_id not in LEADER_CLASSES[troop_class]:
            raise ValueError(f"Unsupported {troop_class} Bear leader: {hero_id}")
    if len(set(leaders)) != 3:
        raise ValueError("Bear leaders must be distinct")


def _event_options(event: tuple[Any, ...], troop_class: str) -> list[tuple[float, tuple[Any, ...] | None]]:
    name, scope, target, chance, family, operation, value = event
    if scope == "class" and target != troop_class:
        return [(1.0, None)]
    return [(1.0 - chance, None), (chance, (name, family, operation, value))]


def _outcome_multiplier(
    events: list[tuple[Any, ...]],
    troop_class: str,
    base_damage_ops: dict[int, float] | None = None,
) -> float:
    attack_multiplier = 1.0
    extra_attack = 0.0
    damage_ops = dict(base_damage_ops or {})
    defense_ops: dict[int, float] = {}
    for _, family, operation, value in events:
        if family == "attack_total":
            attack_multiplier *= 1.0 + value / 100.0
        elif family in ("extra_attack", "extra_damage"):
            extra_attack += value / 100.0
        elif family == "damage_up":
            damage_ops[operation] = damage_ops.get(operation, 0.0) + value
        elif family == "defense_down":
            defense_ops[operation] = defense_ops.get(operation, 0.0) + value
    return attack_multiplier * (1.0 + extra_attack) * _op_multiplier(damage_ops) * _op_multiplier(defense_ops)


def _enumerate_multiplier(
    events: list[tuple[Any, ...]],
    troop_class: str,
    base_damage_ops: dict[int, float],
) -> float:
    states: list[tuple[float, list[tuple[Any, ...]]]] = [(1.0, [])]
    for event in events:
        states = [
            (probability * option_probability, active + ([effect] if effect else []))
            for probability, active in states
            for option_probability, effect in _event_options(event, troop_class)
        ]
    return sum(
        probability * _outcome_multiplier(active, troop_class, base_damage_ops)
        for probability, active in states
    )


def _sample_multiplier(events: list[tuple[Any, ...]], troop_class: str, rng: random.Random) -> float:
    active = []
    for event in events:
        options = _event_options(event, troop_class)
        if len(options) == 2 and rng.random() < options[1][0]:
            active.append(options[1][1])
    return _outcome_multiplier(active, troop_class)


def _histogram(values: list[int], bin_count: int = 20) -> list[dict[str, float]]:
    minimum, maximum = min(values), max(values)
    width = (maximum - minimum) / bin_count if maximum > minimum else 1.0
    counts = [0] * bin_count
    for value in values:
        counts[min(bin_count - 1, int((value - minimum) / width))] += 1
    return [{"from": minimum + index * width, "to": minimum + (index + 1) * width, "probability": count / len(values)} for index, count in enumerate(counts)]


def _semantic_event_debug(events: list[tuple[Any, ...]]) -> dict[str, list[dict[str, Any]]]:
    families = {
        "damage_up": "DAMAGE_UP",
        "defense_down": "ENEMY_DAMAGE_TAKEN_UP",
        "attack_total": "SKILL_DAMAGE",
        "extra_attack": "SKILL_DAMAGE",
        "extra_damage": "SKILL_DAMAGE",
    }
    debug = {
        "DAMAGE_UP": [],
        "ENEMY_DAMAGE_TAKEN_UP": [],
        "ENEMY_DEFENSE_DOWN": [],
        "SKILL_DAMAGE": [],
    }
    for name, scope, target, chance, family, effect_op, value in events:
        semantic_family = families.get(family)
        if semantic_family:
            debug[semantic_family].append({
                "effect": name,
                "scope": scope,
                "target": target,
                "chance": chance,
                "value": value,
                "effect_op": effect_op,
            })
    return debug


def calculate_bear_hunt(
    *,
    troop_counts: tuple[int, int, int],
    troop_tiers: tuple[str, str, str],
    attack_stats: tuple[float, float, float],
    lethality_stats: tuple[float, float, float],
    attack_booster_percent: float,
    lethality_booster_percent: float,
    leaders: tuple[str, str, str],
    joiners: list[str],
    widget_levels: tuple[int, int, int] = (0, 0, 0),
    leader_skill_levels: tuple[int, int, int] = (5, 5, 5),
    resolved_leader_specs: dict[str, dict[str, Any]] | None = None,
    widget_stacking_strategy: str = "GLOBAL_EFFECT_OP",
    stats_source: str = "MANUAL",
    leader_stat_skills_in_report: str = "UNKNOWN",
    attack_booster_in_report: bool = False,
    lethality_booster_in_report: bool = False,
    effect_op_overrides: dict[str, int] | None = None,
    pitfall_attack_points: float = 0.0,
    simulation_count: int = 0,
    seed_config: Any = None,
) -> dict[str, Any]:
    _validate_leaders(leaders)
    overrides = effect_op_overrides or {}
    if any(tier.upper() not in SUPPORTED_TIERS for tier in troop_tiers):
        raise ValueError("Bear engine currently supports only T10 and T11")
    if any(count <= 0 for count in troop_counts):
        raise ValueError("Each Bear troop class requires at least one troop")
    if sum(troop_counts) <= 0:
        raise ValueError("Bear march must contain troops")

    joiner_multiplier, joiner_ops = joiner_effects(joiners)
    resolved_specs = resolved_leader_specs or LEADER_SPECS
    levels = tuple(max(0, min(5, int(level))) for level in leader_skill_levels)
    specs = [_leader_spec(hero_id, level, resolved_specs) for hero_id, level in zip(leaders, levels)]
    terror_report = stats_source == "TERROR_REPORT"
    effective_attack_booster = 0.0 if terror_report and attack_booster_in_report else attack_booster_percent
    effective_lethality_booster = 0.0 if terror_report and lethality_booster_in_report else lethality_booster_percent
    attack_multipliers, lethality_multipliers, stat_effects, widgets_suppressed = _stat_factor_effects(
        joiners, leaders, widget_levels, specs, stats_source, "GLOBAL_EFFECT_OP", True, overrides
    )
    attack_points = [value * (1.0 + effective_attack_booster / 100.0) + pitfall_attack_points for value in attack_stats]
    lethality_points = [value * (1.0 + effective_lethality_booster / 100.0) for value in lethality_stats]

    normalized_tiers = tuple(tier.upper() for tier in troop_tiers)
    base_attacks = tuple(get_troop_base_stats(troop_class, tier[1:])["attack"] for troop_class, tier in zip(TROOP_CLASSES, normalized_tiers))
    attack_per_troop = tuple(
        base
        * (1.0 + attack / 100.0) * attack_multiplier
        * (BASE_LETHALITY * (1.0 + lethality / 100.0) * lethality_multiplier)
        / 100.0
        for base, attack, lethality, attack_multiplier, lethality_multiplier in zip(
            base_attacks, attack_points, lethality_points, attack_multipliers, lethality_multipliers
        )
    )
    army_min = min(sum(troop_counts), BEAR_TROOPS)
    base_round_damage = tuple(
        math.sqrt(count * army_min) * attack / BEAR_DEFENSE * type_bonus / 100.0
        for count, attack, type_bonus in zip(troop_counts, attack_per_troop, TYPE_BONUSES)
    )
    events = [event for spec in specs for event in spec.get("events", [])]
    applied_effects: list[dict[str, Any]] = []
    expected_by_class = [0.0, 0.0, 0.0]
    for round_number in range(1, BEAR_ROUNDS + 1):
        round_events = _resolve_events(_round_events(events, leaders, specs, round_number), overrides)
        for index, troop_class in enumerate(TROOP_CLASSES):
            periodic = 1.0
            if leaders[2] == "yang" and round_number in (4, 8):
                periodic += specs[2].get("avalanche_extra", 0.0) / 100.0
            base_damage_ops, class_effects, widget_multiplier = _base_damage_ops({}, leaders, (0, 0, 0), troop_class, overrides, "GLOBAL_EFFECT_OP", specs)
            applied_effects.extend(class_effects)
            expected_by_class[index] += (
                base_round_damage[index]
                * periodic
                * widget_multiplier
                * _enumerate_multiplier(round_events, troop_class, base_damage_ops)
                * (1.10 if troop_class == "archers" else 1.0)
            )
    expected_before_score_bonus = sum(expected_by_class)
    semantic_source_events = list(events)
    for round_number in range(1, BEAR_ROUNDS + 1):
        semantic_source_events.extend(_round_events([], leaders, specs, round_number))
    semantic_events = _semantic_event_debug(_resolve_events(list(dict.fromkeys(semantic_source_events)), overrides))
    for hero_id, spec in zip(leaders, specs):
        passive = spec.get("passive_damage")
        if passive:
            semantic_events["DAMAGE_UP"].append({
                "effect": passive["name"],
                "scope": "class",
                "target": passive["targets"],
                "chance": 1.0,
                "value": passive["value"],
                "effect_op": _resolve_operation(passive["operation"], overrides),
                "hero": hero_id,
            })

    def build_stat_scenario(include_leader_stats: bool) -> dict[str, Any]:
        attack_multipliers, lethality_multipliers, stat_effects, widgets_suppressed = _stat_factor_effects(
            joiners, leaders, widget_levels, specs, stats_source, widget_stacking_strategy, include_leader_stats, overrides
        )
        scenario_attack_points = tuple(value * (1.0 + effective_attack_booster / 100.0) + pitfall_attack_points for value in attack_stats)
        scenario_lethality_points = tuple(value * (1.0 + effective_lethality_booster / 100.0) for value in lethality_stats)
        scenario_attack_per_troop = tuple(
            base
            * (1.0 + attack / 100.0) * attack_multiplier
            * (BASE_LETHALITY * (1.0 + lethality / 100.0) * lethality_multiplier)
            / 100.0
            for base, attack, lethality, attack_multiplier, lethality_multiplier in zip(
                base_attacks, scenario_attack_points, scenario_lethality_points, attack_multipliers, lethality_multipliers
            )
        )
        scenario_base_round_damage = tuple(
            math.sqrt(count * army_min) * attack / BEAR_DEFENSE * type_bonus / 100.0
            for count, attack, type_bonus in zip(troop_counts, scenario_attack_per_troop, TYPE_BONUSES)
        )
        scenario_expected_by_class = [0.0, 0.0, 0.0]
        skill_mod_sums = [0.0, 0.0, 0.0]
        for round_number in range(1, BEAR_ROUNDS + 1):
            round_events = _resolve_events(_round_events(events, leaders, specs, round_number), overrides)
            for index, troop_class in enumerate(TROOP_CLASSES):
                periodic = 1.0
                if leaders[2] == "yang" and round_number in (4, 8):
                    periodic += specs[2].get("avalanche_extra", 0.0) / 100.0
                damage_ops, _, _ = _base_damage_ops({}, leaders, (0, 0, 0), troop_class, overrides, widget_stacking_strategy, specs)
                skill_mod = periodic * _enumerate_multiplier(round_events, troop_class, damage_ops)
                skill_mod_sums[index] += skill_mod
                volley_multiplier = 1.10 if troop_class == "archers" else 1.0
                scenario_expected_by_class[index] += scenario_base_round_damage[index] * skill_mod * volley_multiplier
        atk_effects = [effect for effect in stat_effects if effect["family"] == "ATK_UP"]
        let_effects = [effect for effect in stat_effects if effect["family"] == "LETHALITY_UP"]
        return {
            "damage_avg": sum(scenario_expected_by_class),
            "per_type_damage": tuple(scenario_expected_by_class),
            "include_leader_stat_skills": include_leader_stats,
            "raw_report_atk": attack_stats,
            "raw_report_let": lethality_stats,
            "stats_source": stats_source,
            "widget_already_included": terror_report,
            "leader_atk_let_skill_already_included": "YES" if include_leader_stats is False else "NO",
            "booster_already_included": {
                "attack": "YES" if terror_report and attack_booster_in_report else "NO",
                "lethality": "YES" if terror_report and lethality_booster_in_report else "NO",
            },
            "atk_up_factors": atk_effects,
            "let_up_factors": let_effects,
            "damage_up_buckets": semantic_events["DAMAGE_UP"],
            "enemy_damage_taken_buckets": semantic_events["ENEMY_DAMAGE_TAKEN_UP"],
            "enemy_defense_down_buckets": semantic_events["ENEMY_DEFENSE_DOWN"],
            "skill_damage_effects": semantic_events["SKILL_DAMAGE"],
            "final_attack_factor": tuple((1.0 + value / 100.0) * multiplier for value, multiplier in zip(scenario_attack_points, attack_multipliers)),
            "final_lethality_factor": tuple((1.0 + value / 100.0) * multiplier for value, multiplier in zip(scenario_lethality_points, lethality_multipliers)),
            "final_skill_mod": tuple(value / BEAR_ROUNDS for value in skill_mod_sums),
            "attack_per_troop": scenario_attack_per_troop,
            "base_round_damage": scenario_base_round_damage,
            "widgets_suppressed_by_stats_source": widgets_suppressed,
        }

    stat_scenarios = {
        "A_ALREADY_INCLUDED": build_stat_scenario(False),
        "B_APPLIED_AFTER_REPORT": build_stat_scenario(True),
    }
    selected_stat_scenario = {
        "YES": "A_ALREADY_INCLUDED",
        "NO": "B_APPLIED_AFTER_REPORT",
    }.get(leader_stat_skills_in_report)
    score_bonus = 0.0
    raw_expected = expected_before_score_bonus
    pending = [{"hero": hero_id, "effect": effect, "status": "PENDING", "applied": False} for hero_id, spec in zip(leaders, specs) for effect in spec.get("pending", [])]
    source_policy = {
        "TERROR_REPORT": "INCLUDED_IN_VISIBLE_STATS",
        "BEAST_REPORT": "NOT_INCLUDED_IN_VISIBLE_STATS",
        "MANUAL": "USER_DEFINED_UNKNOWN",
    }.get(stats_source, "USER_DEFINED_UNKNOWN")
    unique_widget_effects = list({
        (item["hero"], item["effect"], item["effect_op"]): item
        for item in applied_effects
    }.values())
    class_debug = {}
    for index, troop_class in enumerate(TROOP_CLASSES):
        attack_booster_delta = attack_stats[index] * attack_booster_percent / 100.0
        lethality_booster_delta = lethality_stats[index] * lethality_booster_percent / 100.0
        leader_attack_delta = attack_points[index] - attack_stats[index] - attack_booster_delta - pitfall_attack_points
        leader_lethality_delta = lethality_points[index] - lethality_stats[index] - lethality_booster_delta
        class_debug[troop_class] = {
            "base_attack": base_attacks[index],
            "visible_attack": attack_stats[index],
            "attack_layers": {
                "booster_delta": attack_booster_delta,
                "pitfall_points": pitfall_attack_points,
                "leader_skill_points": leader_attack_delta,
                "direct_exclusive_gear_points": 0.0,
                "final_attack_points": attack_points[index],
            },
            "visible_lethality": lethality_stats[index],
            "lethality_layers": {
                "booster_delta": lethality_booster_delta,
                "leader_skill_points": leader_lethality_delta,
                "direct_exclusive_gear_points": 0.0,
                "final_lethality_points": lethality_points[index],
            },
            "attack_per_troop": attack_per_troop[index],
            "base_round_damage": base_round_damage[index],
            "joiner_buckets": dict(joiner_ops),
            "leader_effects": specs,
            "widget_effects": unique_widget_effects,
            "extra_attack_events": [event for event in events if event[4] in ("extra_attack", "extra_damage")],
            "expected_round_damage_before_score_bonus": expected_by_class[index] / BEAR_ROUNDS,
            "expected_hunt_damage_before_score_bonus": expected_by_class[index],
            "bear_score_bonus_percent": score_bonus,
            "final_expected_hunt_damage": expected_by_class[index] * (1.0 + score_bonus / 100.0),
        }
    result: dict[str, Any] = {
        "damage_avg": raw_expected,
        "raw_expected_damage": raw_expected,
        "expected_game_score": None,
        "hunt_score": math.ceil(raw_expected),
        "per_type_damage": tuple(expected_by_class),
        "joiner_heroes": joiners,
        "joiner_damage_multiplier": joiner_multiplier,
        "joiner_attack_pct": 0.0,
        "joiner_lethality_pct": 0.0,
        "lead_damage_multiplier": 1.0,
        "lead_archer_multiplier": 1.0,
        "widget_attack_pct": 0.0,
        "widget_lethality_pct": 0.0,
        "debug": {
            "initial_stats": {
                "troop_tiers": normalized_tiers,
                "troop_tier_confidence": tuple(TROOP_TIER_CONFIDENCE[tier] for tier in normalized_tiers),
                "base_attack": base_attacks,
                "attack_report": attack_stats,
                "lethality_report": lethality_stats,
                "base_lethality": BASE_LETHALITY,
            },
            "leader_skills": {"levels": levels, "level_source": "MANUAL_CONFIG"},
            "stats_source": stats_source,
            "anti_double_count": {
                "direct_gear_stats_in_visible_report": source_policy,
                "direct_gear_stats_applied": False,
                "reason": "Direct Exclusive Gear stats are not added until their conversion is confirmed; Rally Skills remain independent.",
            },
            "direct_exclusive_gear_stats": {"applied": False, "visible_stats_policy": source_policy},
            "widget_rally_skills": {"levels": widget_levels, "stacking_strategy": "ADDITIVE_WITHIN_STAT_FAMILY", "confidence": "PROBABLE", "suppressed_by_stats_source": widgets_suppressed},
            "stat_factors": {
                "effects": stat_effects,
                "attack_multipliers": attack_multipliers,
                "lethality_multipliers": lethality_multipliers,
                "widgets_suppressed_by_stats_source": widgets_suppressed,
            },
            "boosters": {
                "attack": {"input": attack_booster_percent, "operation": "MULTIPLY_VISIBLE_ATTACK", "confidence": "PENDING"},
                "lethality": {"input": lethality_booster_percent, "operation": "MULTIPLY_VISIBLE_LETHALITY", "confidence": "PENDING"},
            },
            "squad_bonuses": {"pitfall_attack_points": pitfall_attack_points, "attack_booster_percent": attack_booster_percent, "lethality_booster_percent": lethality_booster_percent},
            "final_stats": {"attack_points": tuple(attack_points), "lethality_points": tuple(lethality_points), "attack_per_troop": attack_per_troop},
            "op_buckets": {"joiner_damage_up": joiner_ops},
            "applied_probable_effects": unique_widget_effects,
            "confidence": {
                "amadeus_unrighteous_strike": {"effect": "CONFIRMED", "effect_op": "PROBABLE"},
                "offensive_expedition_widgets": {"effect": "CONFIRMED", "effect_op": "PROBABLE"},
                "thrud_battle_hunger": {"effect": "CONFIRMED", "effect_op": "PROBABLE"},
                "thrud_reckless_charge": {"effect": "CONFIRMED", "counter_interaction": "HIGH_CONFIDENCE"},
                "thrud_ancestral_guidance": {"effect": "CONFIRMED", "timing": "HIGH_CONFIDENCE", "effect_op": "PROBABLE"},
            },
            "effect_op_mappings": {**PROBABLE_EFFECT_OPS, **overrides},
            "pending_effects": pending,
            "base_round_damage": base_round_damage,
            "damage_pipeline": {
                "base_attack": base_attacks,
                "visible_attack": attack_stats,
                "attack_layers": tuple(attack_points),
                "visible_lethality": lethality_stats,
                "lethality_layers": tuple(lethality_points),
                "attack_per_troop": attack_per_troop,
                "base_round_damage": base_round_damage,
                "joiner_buckets": joiner_ops,
                "leader_effects": specs,
                "widget_effects": list({(item["hero"], item["effect"], item["effect_op"]): item for item in applied_effects}.values()),
                "extra_attacks_events": events,
                "expected_final_damage_before_score_bonus": expected_before_score_bonus,
                "bear_score_bonus": {"source": None, "percent": score_bonus},
                "final_expected_damage": raw_expected,
                "classes": class_debug,
            },
        },
        "models": {
            "LEGACY_EFFECT_OP_MODEL": {
                "damage_avg": raw_expected,
                "per_type_damage": tuple(expected_by_class),
                "status": "PRODUCTION_BASELINE",
            },
            "STAT_FACTOR_MODEL": {
                "damage_avg": stat_scenarios[selected_stat_scenario]["damage_avg"] if selected_stat_scenario else None,
                "status": "EXPERIMENTAL",
                "calibration_multiplier": None,
                "stat_stacking_strategy": widget_stacking_strategy,
                "leader_stat_skills_in_report": leader_stat_skills_in_report,
                "selected_scenario": selected_stat_scenario,
                "scenarios": stat_scenarios,
                "archer_passives": {
                    "ranged_strike_multiplier": TYPE_BONUSES[2],
                    "volley": {
                        "chance": 0.10,
                        "expected_multiplier": 1.10,
                        "confidence": "HIGH_CONFIDENCE/PENDING_BEAR_VALIDATION",
                    },
                },
            },
        },
    }
    if simulation_count > 0:
        seed = int.from_bytes(hashlib.sha256(json.dumps(seed_config, sort_keys=True, default=str).encode()).digest()[:8], "big")
        rng = random.Random(seed)
        volley_rng = random.Random(seed ^ 0xA7C4E2)
        scores = []
        stat_scores = {scenario_name: [] for scenario_name in stat_scenarios}
        for _ in range(simulation_count):
            total = 0.0
            stat_totals = {scenario_name: 0.0 for scenario_name in stat_scenarios}
            for round_number in range(1, BEAR_ROUNDS + 1):
                round_events = _resolve_events(_round_events(events, leaders, specs, round_number), overrides)
                global_events = [event for event in round_events if event[1] == "global"]
                active_global = [event for event in global_events if rng.random() < event[3]]
                for index, troop_class in enumerate(TROOP_CLASSES):
                    periodic = 1.0
                    if leaders[2] == "yang" and round_number in (4, 8):
                        periodic += specs[2].get("avalanche_extra", 0.0) / 100.0
                    class_events = [event for event in round_events if event[1] != "global"]
                    sampled = []
                    for event in class_events:
                        options = _event_options(event, troop_class)
                        if len(options) == 2 and rng.random() < options[1][0]:
                            sampled.append(options[1][1])
                    global_effects = [(event[0], event[4], event[5], event[6]) for event in active_global]
                    base_damage_ops, _, widget_multiplier = _base_damage_ops({}, leaders, (0, 0, 0), troop_class, overrides, "GLOBAL_EFFECT_OP", specs)
                    multiplier = _outcome_multiplier(global_effects + sampled, troop_class, base_damage_ops)
                    volley_multiplier = 2.0 if troop_class == "archers" and volley_rng.random() < 0.10 else 1.0
                    total += base_round_damage[index] * periodic * widget_multiplier * multiplier * volley_multiplier
                    stat_damage_ops, _, _ = _base_damage_ops({}, leaders, (0, 0, 0), troop_class, overrides, widget_stacking_strategy, specs)
                    stat_multiplier = _outcome_multiplier(global_effects + sampled, troop_class, stat_damage_ops)
                    for scenario_name, scenario in stat_scenarios.items():
                        stat_totals[scenario_name] += scenario["base_round_damage"][index] * periodic * stat_multiplier * volley_multiplier
            scores.append(math.ceil(total * (1.0 + score_bonus / 100.0)))
            for scenario_name, total_damage in stat_totals.items():
                stat_scores[scenario_name].append(math.ceil(total_damage))
        scores.sort()
        percentile = lambda fraction: scores[min(len(scores) - 1, round((len(scores) - 1) * fraction))]
        mean = statistics.fmean(scores)
        result["simulation"] = {
            "runs": simulation_count,
            "mean": mean,
            "p10": percentile(0.10), "p25": percentile(0.25), "p50": percentile(0.50),
            "p75": percentile(0.75), "p90": percentile(0.90),
            "stddev": statistics.pstdev(scores), "minimum": scores[0], "maximum": scores[-1],
            "mean_position": ((mean - scores[0]) / (scores[-1] - scores[0]) * 100.0) if scores[-1] > scores[0] else 50.0,
            "histogram": _histogram(scores),
        }
        result["simulation"]["max_probability"] = max(item["probability"] for item in result["simulation"]["histogram"])
        for scenario_name, scenario_scores in stat_scores.items():
            scenario_scores.sort()
            stat_percentile = lambda fraction: scenario_scores[min(len(scenario_scores) - 1, round((len(scenario_scores) - 1) * fraction))]
            stat_mean = statistics.fmean(scenario_scores)
            result["models"]["STAT_FACTOR_MODEL"]["scenarios"][scenario_name]["simulation"] = {
                "runs": simulation_count,
                "mean": stat_mean,
                "p10": stat_percentile(0.10), "p25": stat_percentile(0.25), "p50": stat_percentile(0.50),
                "p75": stat_percentile(0.75), "p90": stat_percentile(0.90),
                "stddev": statistics.pstdev(scenario_scores), "minimum": scenario_scores[0], "maximum": scenario_scores[-1],
                "histogram": _histogram(scenario_scores),
            }
    return result
