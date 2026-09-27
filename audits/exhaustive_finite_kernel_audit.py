#!/usr/bin/env python3
"""
Independent exhaustive falsification audit for the finite deterministic
INSACERMO kernel.

No Lean theorem is called here. The script recomputes the relevant objects
from their finite operational semantics by brute force on small universes.

Audits:
  A. min safe partition = min action cover = min certified messages
     = min obstruction coloring.
  B. infeasible pointwise systems are rejected by every formulation.
  C. joint context/message feasibility, upward closure, Pareto antichain,
     one-summary-symbol degeneracy, and combined-alphabet equality.
  D. finite one-step tree replacement/congruence sanity audit for every
     encoder World=2, Message=2 on all depth<=1 trees.

Any counterexample aborts with a reproducible JSON witness.
"""

from __future__ import annotations

import itertools
import json
import os
import sys
from dataclasses import dataclass
from typing import Iterable, List, Optional, Sequence, Tuple


def powerset_indices(n: int) -> Iterable[Tuple[int, ...]]:
    for r in range(n + 1):
        yield from itertools.combinations(range(n), r)


def set_partitions(n: int) -> List[Tuple[Tuple[int, ...], ...]]:
    """All unlabeled set partitions of range(n), canonicalized."""
    if n == 0:
        return [tuple()]
    out = []
    # restricted-growth strings
    def rec(seq: List[int], mx: int) -> None:
        if len(seq) == n:
            blocks = [[] for _ in range(mx + 1)]
            for i, b in enumerate(seq):
                blocks[b].append(i)
            out.append(tuple(tuple(b) for b in blocks))
            return
        for b in range(mx + 2):
            seq.append(b)
            rec(seq, max(mx, b))
            seq.pop()
    rec([0], 0)
    return out


PARTITIONS = {w: set_partitions(w) for w in range(1, 5)}


@dataclass(frozen=True)
class FiniteSystem:
    worlds: int
    actions: int
    available_mask: int
    admissible_mask: int

    def available(self, a: int) -> bool:
        return bool((self.available_mask >> a) & 1)

    def admissible(self, x: int, a: int) -> bool:
        bit = x * self.actions + a
        return bool((self.admissible_mask >> bit) & 1)

    def common_action(self, block: Sequence[int]) -> bool:
        return any(
            self.available(a) and all(self.admissible(x, a) for x in block)
            for a in range(self.actions)
        )

    def pointwise_feasible(self) -> bool:
        return all(self.common_action((x,)) for x in range(self.worlds))


def min_safe_partition(sysm: FiniteSystem) -> Optional[int]:
    best = None
    for part in PARTITIONS[sysm.worlds]:
        if all(sysm.common_action(block) for block in part):
            k = len(part)
            best = k if best is None else min(best, k)
    return best


def min_action_cover(sysm: FiniteSystem) -> Optional[int]:
    acts = [a for a in range(sysm.actions) if sysm.available(a)]
    for r in range(len(acts) + 1):
        for subset in itertools.combinations(acts, r):
            if all(any(sysm.admissible(x, a) for a in subset)
                   for x in range(sysm.worlds)):
                return r
    return None


def min_certified_messages(sysm: FiniteSystem) -> Optional[int]:
    """Direct decoder semantics. Encoder existence is checked per world."""
    for n in range(1, sysm.worlds + 1):
        for decoder in itertools.product(range(sysm.actions), repeat=n):
            if not all(sysm.available(a) for a in decoder):
                continue
            if all(any(sysm.admissible(x, decoder[m]) for m in range(n))
                   for x in range(sysm.worlds)):
                return n
    return None


def minimal_obstructions(sysm: FiniteSystem) -> List[Tuple[int, ...]]:
    out = []
    worlds = range(sysm.worlds)
    for r in range(1, sysm.worlds + 1):
        for block in itertools.combinations(worlds, r):
            if sysm.common_action(block):
                continue
            minimal = True
            for j in range(len(block)):
                sub = block[:j] + block[j + 1:]
                if sub and not sysm.common_action(sub):
                    minimal = False
                    break
            if minimal:
                out.append(block)
    return out


def min_obstruction_coloring(sysm: FiniteSystem) -> Optional[int]:
    obs = minimal_obstructions(sysm)
    # Singleton obstruction means pointwise infeasible.
    if any(len(o) == 1 for o in obs):
        return None
    for n in range(1, sysm.worlds + 1):
        for coloring in itertools.product(range(n), repeat=sysm.worlds):
            good = True
            for obstruction in obs:
                c0 = coloring[obstruction[0]]
                if all(coloring[x] == c0 for x in obstruction[1:]):
                    good = False
                    break
            if good:
                return n
    return None


def audit_core_equivalences() -> dict:
    checked = 0
    feasible = 0
    infeasible = 0
    hist = {}
    for w in range(1, 5):
        for a in range(1, 4):
            for available_mask in range(1 << a):
                for admissible_mask in range(1 << (w * a)):
                    s = FiniteSystem(w, a, available_mask, admissible_mask)
                    checked += 1
                    vals = {
                        "safe_partition": min_safe_partition(s),
                        "action_cover": min_action_cover(s),
                        "certified_messages": min_certified_messages(s),
                        "obstruction_coloring": min_obstruction_coloring(s),
                    }
                    point = s.pointwise_feasible()
                    if point:
                        feasible += 1
                        if None in vals.values() or len(set(vals.values())) != 1:
                            raise AssertionError(json.dumps({
                                "audit": "core_equivalence",
                                "system": s.__dict__,
                                "pointwise_feasible": point,
                                "values": vals,
                                "minimal_obstructions": minimal_obstructions(s),
                            }, sort_keys=True))
                        k = vals["safe_partition"]
                        hist[str(k)] = hist.get(str(k), 0) + 1
                    else:
                        infeasible += 1
                        if any(v is not None for v in vals.values()):
                            raise AssertionError(json.dumps({
                                "audit": "core_infeasible_rejection",
                                "system": s.__dict__,
                                "pointwise_feasible": point,
                                "values": vals,
                            }, sort_keys=True))
    return {
        "systems_checked": checked,
        "pointwise_feasible": feasible,
        "pointwise_infeasible": infeasible,
        "minimum_histogram": hist,
        "ranges": {"worlds": [1, 4], "actions": [1, 3]},
    }


@dataclass(frozen=True)
class ContextSystem:
    contexts: int
    actions: int
    available_mask: int
    admissible_mask: int

    def available(self, a: int) -> bool:
        return bool((self.available_mask >> a) & 1)

    def admissible(self, k: int, a: int) -> bool:
        bit = k * self.actions + a
        return bool((self.admissible_mask >> bit) & 1)

    def pointwise_feasible(self) -> bool:
        return all(
            any(self.available(a) and self.admissible(k, a)
                for a in range(self.actions))
            for k in range(self.contexts)
        )


def context_message_budget_exists(s: ContextSystem, q: int, m: int) -> bool:
    if q <= 0 or m <= 0:
        return False
    # W = Unit in this exhaustive interface audit.
    for summary in itertools.product(range(q), repeat=s.contexts):
        for encode in itertools.product(range(m), repeat=s.contexts):
            used_pairs = {(summary[k], encode[k]) for k in range(s.contexts)}
            # Only decoder cells actually used by a context constrain feasibility.
            pair_options = []
            pairs = sorted(used_pairs)
            for qm in pairs:
                valid = [
                    a for a in range(s.actions)
                    if s.available(a)
                    and all(
                        s.admissible(k, a)
                        for k in range(s.contexts)
                        if (summary[k], encode[k]) == qm
                    )
                ]
                if not valid:
                    break
                pair_options.append(valid)
            else:
                # Unused decoder cells may take any available action.
                if all(pair_options) and (not pairs or any(s.available(a) for a in range(s.actions))):
                    return True
    return False


def global_min_messages_context(s: ContextSystem) -> Optional[int]:
    # Direct global certified protocol on K x Unit.
    fs = FiniteSystem(
        worlds=s.contexts,
        actions=s.actions,
        available_mask=s.available_mask,
        admissible_mask=s.admissible_mask,
    )
    return min_certified_messages(fs)


def pareto_minima(points: Sequence[Tuple[int, int]]) -> List[Tuple[int, int]]:
    pts = set(points)
    out = []
    for p in sorted(pts):
        dominated = any(
            r != p and r[0] <= p[0] and r[1] <= p[1]
            for r in pts
        )
        if not dominated:
            out.append(p)
    return out


def audit_context_message_frontiers() -> dict:
    checked = 0
    feasible_systems = 0
    total_frontier_points = 0
    max_frontier_size = 0
    examples_multi = []

    for k in range(1, 4):
        for a in range(1, 3):
            for available_mask in range(1 << a):
                for admissible_mask in range(1 << (k * a)):
                    s = ContextSystem(k, a, available_mask, admissible_mask)
                    checked += 1
                    rectangle = {}
                    points = []
                    for q in range(1, k + 1):
                        for m in range(1, a + 1):
                            ok = context_message_budget_exists(s, q, m)
                            rectangle[(q, m)] = ok
                            if ok:
                                points.append((q, m))

                    # Upward closure inside the exhaustive rectangle.
                    for (q, m), ok in rectangle.items():
                        if not ok:
                            continue
                        for q2 in range(q, k + 1):
                            for m2 in range(m, a + 1):
                                if not rectangle[(q2, m2)]:
                                    raise AssertionError(json.dumps({
                                        "audit": "context_message_upward_closure",
                                        "system": s.__dict__,
                                        "from": [q, m],
                                        "to": [q2, m2],
                                    }, sort_keys=True))

                    gmin = global_min_messages_context(s)
                    if s.pointwise_feasible():
                        feasible_systems += 1
                        # q=1 must be feasible at m=gmin.
                        if gmin is None or not rectangle.get((1, gmin), False):
                            raise AssertionError(json.dumps({
                                "audit": "one_summary_symbol",
                                "system": s.__dict__,
                                "global_min_messages": gmin,
                                "rectangle": {str(k0): v for k0, v in rectangle.items()},
                            }, sort_keys=True))
                        # Combined alphabet minimum q*m equals global minimum.
                        min_product = min(q * m for q, m in points)
                        if min_product != gmin:
                            raise AssertionError(json.dumps({
                                "audit": "combined_alphabet_equality",
                                "system": s.__dict__,
                                "global_min_messages": gmin,
                                "min_q_times_m": min_product,
                                "points": points,
                            }, sort_keys=True))
                    else:
                        if points:
                            raise AssertionError(json.dumps({
                                "audit": "context_infeasible_has_budget",
                                "system": s.__dict__,
                                "points": points,
                            }, sort_keys=True))

                    front = pareto_minima(points)
                    total_frontier_points += len(front)
                    max_frontier_size = max(max_frontier_size, len(front))
                    # Pareto minima must be pairwise incomparable.
                    for i, p in enumerate(front):
                        for r in front[i + 1:]:
                            if ((p[0] <= r[0] and p[1] <= r[1]) or
                                (r[0] <= p[0] and r[1] <= p[1])):
                                raise AssertionError(json.dumps({
                                    "audit": "pareto_antichain",
                                    "system": s.__dict__,
                                    "frontier": front,
                                }, sort_keys=True))
                    if len(front) > 1 and len(examples_multi) < 8:
                        examples_multi.append({
                            "system": s.__dict__,
                            "frontier": front,
                        })

    return {
        "systems_checked": checked,
        "pointwise_feasible": feasible_systems,
        "total_pareto_points": total_frontier_points,
        "max_frontier_size": max_frontier_size,
        "multi_minimum_examples": examples_multi,
        "ranges": {
            "contexts": [1, 3],
            "actions": [1, 2],
            "local_worlds": 1,
            "q": "1..contexts",
            "m": "1..actions",
        },
    }


# Tiny binary-tree audit -----------------------------------------------------

# Tree representation:
# ("L", world)
# ("B", world, left, right)

def trees_depth_le_one() -> List[tuple]:
    leaves = [("L", w) for w in (0, 1)]
    branches = [
        ("B", w, l, r)
        for w in (0, 1)
        for l in leaves
        for r in leaves
    ]
    return leaves + branches


TREES_D1 = trees_depth_le_one()


def child_interface(enc: Tuple[int, ...], tree: tuple) -> Tuple[int, ...]:
    if tree[0] == "L":
        return (0,)  # none
    return (1, tree_message(enc, tree[2]), tree_message(enc, tree[3]))


def enc_index(world: int, ci: Tuple[int, ...]) -> int:
    # Message alphabet M=2. Five child-interface cases per world:
    # none, (0,0), (0,1), (1,0), (1,1)
    if ci[0] == 0:
        local = 0
    else:
        local = 1 + 2 * ci[1] + ci[2]
    return world * 5 + local


def tree_message(enc: Tuple[int, ...], tree: tuple) -> int:
    if tree[0] == "L":
        w = tree[1]
        return enc[enc_index(w, (0,))]
    w, l, r = tree[1], tree[2], tree[3]
    ci = (1, tree_message(enc, l), tree_message(enc, r))
    return enc[enc_index(w, ci)]


def parent_wrap(world: int, side: int, subtree: tuple, sibling: tuple) -> tuple:
    if side == 0:
        return ("B", world, subtree, sibling)
    return ("B", world, sibling, subtree)


def audit_tree_congruence() -> dict:
    encoders_checked = 0
    same_message_pairs = 0
    parent_context_checks = 0
    for bits in range(1 << 10):
        enc = tuple((bits >> i) & 1 for i in range(10))
        encoders_checked += 1
        msgs = [tree_message(enc, t) for t in TREES_D1]
        for i, t1 in enumerate(TREES_D1):
            for j in range(i, len(TREES_D1)):
                t2 = TREES_D1[j]
                if msgs[i] != msgs[j]:
                    continue
                same_message_pairs += 1
                for world in (0, 1):
                    for side in (0, 1):
                        for sibling in TREES_D1:
                            parent_context_checks += 1
                            m1 = tree_message(enc, parent_wrap(world, side, t1, sibling))
                            m2 = tree_message(enc, parent_wrap(world, side, t2, sibling))
                            if m1 != m2:
                                raise AssertionError(json.dumps({
                                    "audit": "tree_parent_congruence",
                                    "encoder_bits": bits,
                                    "t1": t1,
                                    "t2": t2,
                                    "world": world,
                                    "side": side,
                                    "sibling": sibling,
                                    "m1": m1,
                                    "m2": m2,
                                }, sort_keys=True))
    return {
        "encoders_checked": encoders_checked,
        "trees": len(TREES_D1),
        "same_message_pairs": same_message_pairs,
        "parent_context_checks": parent_context_checks,
        "world_alphabet": 2,
        "message_alphabet": 2,
    }


def main() -> int:
    report = {
        "audit_name": "INSACERMO exhaustive finite kernel falsification v1",
        "method": "independent brute force; no Lean theorem invoked",
        "core": audit_core_equivalences(),
        "context_message": audit_context_message_frontiers(),
        "tree_congruence": audit_tree_congruence(),
        "status": "SUCCESS",
    }
    os.makedirs("artifacts", exist_ok=True)
    path = "artifacts/exhaustive_finite_audit.json"
    with open(path, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2, sort_keys=True)
        f.write("\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    print(f"\nWROTE {path}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print("FAILURE: counterexample found", file=sys.stderr)
        print(str(exc), file=sys.stderr)
        raise
