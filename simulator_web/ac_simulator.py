from __future__ import annotations

import random
from dataclasses import dataclass
from itertools import permutations
from typing import Any, Sequence


MAX_WINS = 2
LANE_SIZE = 20


@dataclass(frozen=True)
class ACPlayer:
    id: int
    name: str
    power: float


def _players(items: Sequence[dict[str, Any]]) -> list[ACPlayer]:
    players: list[ACPlayer] = []
    for index, item in enumerate(items):
        try:
            power = max(0.0, float(item.get("power") or 0))
        except (TypeError, ValueError):
            power = 0.0
        players.append(
            ACPlayer(
                id=int(item.get("id") or index + 1),
                name=str(item.get("name") or "Player").strip()[:100],
                power=power,
            )
        )
    return players


def split_roster(
    items: Sequence[dict[str, Any]], strategy: str = "two_strong"
) -> dict[str, list[dict[str, Any]]]:
    players = sorted(_players(items), key=lambda player: (-player.power, player.name.casefold()))
    lanes: dict[str, list[ACPlayer]] = {"lane_a": [], "lane_b": [], "lane_c": []}
    player_count = min(len(players), LANE_SIZE * 3)
    base_size, extra = divmod(player_count, 3)
    capacities = {
        "lane_a": base_size + int(extra > 0),
        "lane_b": base_size + int(extra > 1),
        "lane_c": base_size,
    }

    def balance(selected: Sequence[ACPlayer], lane_keys: Sequence[str]) -> None:
        totals = {lane: 0.0 for lane in lane_keys}
        for player in selected:
            available = [lane for lane in lane_keys if len(lanes[lane]) < capacities[lane]]
            if not available:
                break
            target = min(available, key=lambda lane: (totals[lane], len(lanes[lane]), lane))
            lanes[target].append(player)
            totals[target] += player.power

    if strategy == "one_strong":
        strong_count = capacities["lane_a"]
        lanes["lane_a"] = players[:strong_count]
        balance(players[strong_count:player_count], ("lane_b", "lane_c"))
    else:
        strong_count = capacities["lane_a"] + capacities["lane_b"]
        balance(players[:strong_count], ("lane_a", "lane_b"))
        lanes["lane_c"] = players[strong_count:player_count]

    return {
        lane: [{"id": player.id, "name": player.name, "power": player.power} for player in players_in_lane]
        for lane, players_in_lane in lanes.items()
    }


def simulate_lane(
    mine: Sequence[dict[str, Any]],
    theirs: Sequence[dict[str, Any]],
    loss_min_pct: float = 5.0,
    loss_max_pct: float | None = None,
) -> dict[str, Any]:
    loss_min_pct = min(40.0, max(0.0, float(loss_min_pct)))
    loss_max_pct = loss_min_pct if loss_max_pct is None else min(40.0, max(0.0, float(loss_max_pct)))
    loss_min_pct, loss_max_pct = sorted((loss_min_pct, loss_max_pct))
    mine_queue = [{"player": player, "power": player.power, "wins": 0} for player in _players(mine)]
    their_queue = [{"player": player, "power": player.power, "wins": 0} for player in _players(theirs)]
    mine_index = their_index = 0
    my_kills = their_kills = 0
    battle_log: list[dict[str, Any]] = []

    while mine_index < len(mine_queue) and their_index < len(their_queue):
        mine_active = mine_queue[mine_index]
        their_active = their_queue[their_index]
        mine_wins = mine_active["power"] >= their_active["power"]
        stronger_power = max(mine_active["power"], their_active["power"])
        balance_ratio = min(mine_active["power"], their_active["power"]) / stronger_power if stronger_power else 0.0
        loss_pct = loss_min_pct + (loss_max_pct - loss_min_pct) * balance_ratio**2
        battle_log.append(
            {
                "winner": "mine" if mine_wins else "theirs",
                "mine_name": mine_active["player"].name,
                "mine_power": round(mine_active["power"]),
                "their_name": their_active["player"].name,
                "their_power": round(their_active["power"]),
                "loss_pct": round(loss_pct, 2),
            }
        )
        if mine_wins:
            my_kills += 1
            their_index += 1
            mine_active["wins"] += 1
            mine_active["power"] *= 1 - loss_pct / 100
            if mine_active["wins"] >= MAX_WINS:
                mine_index += 1
        else:
            their_kills += 1
            mine_index += 1
            their_active["wins"] += 1
            their_active["power"] *= 1 - loss_pct / 100
            if their_active["wins"] >= MAX_WINS:
                their_index += 1

    if their_index >= len(their_queue) and mine_index < len(mine_queue):
        result = "mine"
    elif mine_index >= len(mine_queue) and their_index < len(their_queue):
        result = "theirs"
    else:
        result = "mine" if my_kills > their_kills else "theirs" if their_kills > my_kills else "draw"

    return {
        "result": result,
        "my_kills": my_kills,
        "their_kills": their_kills,
        "mine_used": min(mine_index + 1, len(mine_queue)),
        "mine_total": len(mine_queue),
        "theirs_used": min(their_index + 1, len(their_queue)),
        "theirs_total": len(their_queue),
        "log": battle_log,
    }


def _probabilistic_lane_win(
    mine: Sequence[dict[str, Any]],
    theirs: Sequence[dict[str, Any]],
    loss_min_pct: float,
    loss_max_pct: float,
    rng: random.Random,
) -> bool:
    varied_mine = [dict(player, power=float(player.get("power") or 0) * rng.uniform(0.92, 1.08)) for player in mine]
    varied_theirs = [dict(player, power=float(player.get("power") or 0) * rng.uniform(0.92, 1.08)) for player in theirs]
    sampled_loss_max = rng.uniform(loss_min_pct, loss_max_pct)
    return simulate_lane(varied_mine, varied_theirs, loss_min_pct, sampled_loss_max)["result"] == "mine"


def optimize_lanes(
    lanes: dict[str, Sequence[dict[str, Any]]],
    rivals: dict[str, Sequence[dict[str, Any]]],
    loss_min_pct: float = 5.0,
    loss_max_pct: float = 20.0,
    samples: int = 80,
    attempts: int = 90,
    seed: int = 20260924,
) -> dict[str, Any]:
    lane_keys = ("lane_a", "lane_b", "lane_c")
    rival_orders = tuple(permutations(lane_keys))
    original = {lane: [dict(player) for player in lanes.get(lane, [])] for lane in lane_keys}
    players = sorted(
        (dict(player) for lane in lane_keys for player in original[lane]),
        key=lambda player: -float(player.get("power") or 0),
    )
    lane_sizes = {lane: len(original[lane]) for lane in lane_keys}
    rng = random.Random(seed)

    def evaluate(current: dict[str, list[dict[str, Any]]]) -> tuple[float, dict[str, float]]:
        wins = {lane: 0 for lane in lane_keys}
        match_wins = 0
        for order_index, rival_order in enumerate(rival_orders):
            for sample_index in range(samples):
                sample_rng = random.Random(seed + order_index * samples + sample_index)
                lane_results = []
                for lane_index, lane in enumerate(lane_keys):
                    won = _probabilistic_lane_win(
                        current[lane], rivals.get(rival_order[lane_index], []),
                        loss_min_pct, loss_max_pct, sample_rng,
                    )
                    wins[lane] += int(won)
                    lane_results.append(won)
                match_wins += int(sum(lane_results) >= 2)
        scenario_count = samples * len(rival_orders)
        probabilities = {lane: round(wins[lane] * 100 / scenario_count, 1) for lane in lane_keys}
        return match_wins * 100 / scenario_count, probabilities

    def distribute_balanced(
        selected: Sequence[dict[str, Any]], target_lanes: Sequence[str]
    ) -> dict[str, list[dict[str, Any]]]:
        result = {lane: [] for lane in target_lanes}
        totals = {lane: 0.0 for lane in target_lanes}
        for player in selected:
            available = [lane for lane in target_lanes if len(result[lane]) < lane_sizes[lane]]
            if not available:
                break
            target = min(available, key=lambda lane: (totals[lane], len(result[lane]), lane))
            result[target].append(player)
            totals[target] += float(player.get("power") or 0)
        return result

    candidates: list[tuple[str, dict[str, list[dict[str, Any]]]]] = [("Current lineup", original)]
    for discard_lane in lane_keys:
        strong_lanes = tuple(lane for lane in lane_keys if lane != discard_lane)
        strong_count = sum(lane_sizes[lane] for lane in strong_lanes)
        proposal = {lane: [] for lane in lane_keys}
        proposal.update(distribute_balanced(players[:strong_count], strong_lanes))
        proposal[discard_lane] = players[strong_count:strong_count + lane_sizes[discard_lane]]
        candidates.append((f"Two strong lanes; sacrifice {discard_lane.replace('_', ' ').upper()}", proposal))

    for strong_lane in lane_keys:
        medium_lanes = tuple(lane for lane in lane_keys if lane != strong_lane)
        strong_count = lane_sizes[strong_lane]
        proposal = {lane: [] for lane in lane_keys}
        proposal[strong_lane] = players[:strong_count]
        proposal.update(distribute_balanced(players[strong_count:], medium_lanes))
        candidates.append((f"One strong lane: {strong_lane.replace('_', ' ').upper()}; two balanced", proposal))

    strategy, best = candidates[0]
    best_score, best_probabilities = evaluate(best)
    for candidate_strategy, candidate in candidates[1:]:
        candidate_score, candidate_probabilities = evaluate(candidate)
        if candidate_score > best_score or (
            candidate_score == best_score
            and sum(candidate_probabilities.values()) > sum(best_probabilities.values())
        ):
            strategy = candidate_strategy
            best = {lane: list(candidate[lane]) for lane in lane_keys}
            best_score = candidate_score
            best_probabilities = candidate_probabilities

    candidate = {lane: list(best[lane]) for lane in lane_keys}
    for _ in range(attempts):
        left_lane, right_lane = rng.sample(lane_keys, 2)
        if not candidate[left_lane] or not candidate[right_lane]:
            continue
        proposal = {lane: list(players) for lane, players in candidate.items()}
        left_index = rng.randrange(len(proposal[left_lane]))
        right_index = rng.randrange(len(proposal[right_lane]))
        proposal[left_lane][left_index], proposal[right_lane][right_index] = (
            proposal[right_lane][right_index],
            proposal[left_lane][left_index],
        )
        proposal_score, proposal_probabilities = evaluate(proposal)
        if proposal_score > best_score or (
            proposal_score == best_score
            and sum(proposal_probabilities.values()) > sum(best_probabilities.values())
        ):
            candidate = proposal
            best = {lane: list(players) for lane, players in proposal.items()}
            best_score = proposal_score
            best_probabilities = proposal_probabilities

    order_results: list[dict[str, Any]] = []
    for order_index, rival_order in enumerate(rival_orders):
        order_wins = 0
        lane_wins = {lane: 0 for lane in lane_keys}
        for sample_index in range(samples):
            sample_rng = random.Random(seed + order_index * samples + sample_index)
            results = []
            for lane_index, lane in enumerate(lane_keys):
                won = _probabilistic_lane_win(
                    best[lane], rivals.get(rival_order[lane_index], []),
                    loss_min_pct, loss_max_pct, sample_rng,
                )
                lane_wins[lane] += int(won)
                results.append(won)
            order_wins += int(sum(results) >= 2)
        order_results.append({
            "order": [lane.rsplit("_", 1)[-1].upper() for lane in rival_order],
            "match_win_pct": round(order_wins * 100 / samples, 1),
            "lane_win_pct": {
                lane: round(lane_wins[lane] * 100 / samples, 1) for lane in lane_keys
            },
        })

    return {
        "lanes": best,
        "strategy": strategy,
        "match_win_pct": round(best_score, 1),
        "lane_win_pct": best_probabilities,
        "samples": samples,
        "rival_orders": len(rival_orders),
        "scenario_count": samples * len(rival_orders),
        "order_results": order_results,
    }