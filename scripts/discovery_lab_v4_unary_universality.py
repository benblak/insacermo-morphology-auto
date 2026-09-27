#!/usr/bin/env python3
"""
INSACERMO Discovery Lab V4
Unary-activation universality probe.

Question:
Can every monotone capability feasibility region be realized exactly by a
future-actionability cover system in which each primitive action is unlocked
by only one capability?

For an upward-closed U subset of P([n]), let L(U) be the maximal losing
coalitions. Create one future world w_L for each L in L(U). Capability i
unlocks one action a_i. Action a_i covers w_L iff i notin L.

Then the available actions indexed by C cover every future world iff
C belongs to U.

This script exhaustively checks every monotone Boolean function for n <= 5.
It also stress-tests random upward-closed regions for larger n.
"""

from __future__ import annotations

import json
import random
from typing import Iterable, List, Sequence, Tuple


def subset(a: int, b: int) -> bool:
    return (a & ~b) == 0


def antichains(n: int) -> Iterable[Tuple[int, ...]]:
    """Enumerate every antichain of P([n]) exactly once."""
    vertices = list(range(1 << n))

    # Put middle layers first: stronger pruning in the incomparability search.
    vertices.sort(key=lambda x: (abs(x.bit_count() - n / 2), x))

    def rec(cands: Tuple[int, ...], chosen: Tuple[int, ...]):
        if not cands:
            yield tuple(sorted(chosen))
            return
        v = cands[0]
        rest = cands[1:]

        # Exclude v.
        yield from rec(rest, chosen)

        # Include v; all comparable elements become unavailable.
        keep = tuple(
            u for u in rest
            if not subset(u, v) and not subset(v, u)
        )
        yield from rec(keep, chosen + (v,))

    yield from rec(tuple(vertices), tuple())


def upper_from_minimal(C: int, minimal_winners: Sequence[int]) -> bool:
    return any(subset(m, C) for m in minimal_winners)


def maximal_losers(n: int, minimal_winners: Sequence[int]) -> Tuple[int, ...]:
    losing = [
        C for C in range(1 << n)
        if not upper_from_minimal(C, minimal_winners)
    ]
    out = []
    for C in losing:
        if not any(C != D and subset(C, D) for D in losing):
            out.append(C)
    return tuple(sorted(out))


def unary_cover_feasible(C: int, max_losers: Sequence[int], n: int) -> bool:
    # World L is covered iff at least one available capability i lies outside L.
    for L in max_losers:
        if all(not ((C >> i) & 1) or ((L >> i) & 1) for i in range(n)):
            return False
    return True


def verify_region(n: int, minimal_winners: Sequence[int]) -> Tuple[bool, Tuple[int, ...]]:
    ml = maximal_losers(n, minimal_winners)
    for C in range(1 << n):
        expected = upper_from_minimal(C, minimal_winners)
        got = unary_cover_feasible(C, ml, n)
        if expected != got:
            return False, ml
    return True, ml


def exhaustive(n: int):
    count = 0
    max_worlds = -1
    max_world_examples: List[Tuple[int, ...]] = []
    world_hist = {}
    for A in antichains(n):
        ok, ml = verify_region(n, A)
        if not ok:
            raise AssertionError((n, A, ml))
        count += 1
        w = len(ml)
        world_hist[w] = world_hist.get(w, 0) + 1
        if w > max_worlds:
            max_worlds = w
            max_world_examples = [A]
        elif w == max_worlds and len(max_world_examples) < 5:
            max_world_examples.append(A)
    return {
        "n": n,
        "monotone_regions_verified": count,
        "max_required_worlds": max_worlds,
        "max_world_examples_minimal_winners": [list(x) for x in max_world_examples],
        "world_count_histogram": dict(sorted(world_hist.items())),
    }


def random_antichain(n: int, rng: random.Random) -> Tuple[int, ...]:
    pool = list(range(1 << n))
    rng.shuffle(pool)
    A: List[int] = []
    for x in pool:
        if any(subset(x, y) or subset(y, x) for y in A):
            continue
        if rng.random() < 0.18:
            A.append(x)
    return tuple(sorted(A))


def stress(n: int, trials: int, seed: int):
    rng = random.Random(seed)
    max_worlds = 0
    for _ in range(trials):
        A = random_antichain(n, rng)
        ok, ml = verify_region(n, A)
        if not ok:
            raise AssertionError((n, A, ml))
        max_worlds = max(max_worlds, len(ml))
    return {
        "n": n,
        "trials": trials,
        "seed": seed,
        "max_required_worlds_seen": max_worlds,
    }


def main():
    exact = [exhaustive(n) for n in range(1, 6)]
    # Known Dedekind numbers M(n) for n=1..5.
    expected_counts = {1: 3, 2: 6, 3: 20, 4: 168, 5: 7581}
    for row in exact:
        assert row["monotone_regions_verified"] == expected_counts[row["n"]]

    random_checks = [
        stress(6, 1000, 2026092801),
        stress(7, 1000, 2026092802),
        stress(8, 500, 2026092803),
    ]

    report = {
        "experiment": "INSACERMO Discovery Lab V4 — unary-activation universality",
        "claim_tested": (
            "Every upward-closed capability region on n primitive capabilities "
            "is exactly realizable as future-cover feasibility using only unary "
            "capability-activated actions."
        ),
        "construction": {
            "worlds": "one world for each maximal losing coalition L",
            "actions": "one action a_i unlocked only by capability i",
            "coverage": "a_i covers world L iff i is not in L",
            "equivalence": "C covers all worlds iff C is in the target upward-closed region",
        },
        "exhaustive": exact,
        "stress": random_checks,
        "status": "SUCCESS",
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
