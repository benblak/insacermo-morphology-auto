#!/usr/bin/env python3
from __future__ import annotations

import itertools
import json
from collections import Counter
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from insacermo_actionability_engine_v1 import FiniteContract, audit_observation

HERE = Path(__file__).resolve().parent
N = 6
VERTICES = tuple(range(N))
EDGES = tuple((i, j) for i in range(N) for j in range(i + 1, N))
EDGE_INDEX = {e: k for k, e in enumerate(EDGES)}
N_GRAPHS = 1 << len(EDGES)


def edge_bit(a: int, b: int) -> int:
    if a > b:
        a, b = b, a
    return 1 << EDGE_INDEX[(a, b)]


def edge_orbit_masks(p):
    seen = set()
    masks = []
    for e in EDGES:
        if e in seen:
            continue
        cur = e
        orbit = set()
        while cur not in orbit:
            orbit.add(cur)
            a, b = cur
            pa, pb = p[a], p[b]
            cur = (pa, pb) if pa < pb else (pb, pa)
        seen.update(orbit)
        mask = 0
        for a, b in orbit:
            mask |= edge_bit(a, b)
        masks.append(mask)
    return masks


def invariant_graph_masks(p):
    orbit_masks = edge_orbit_masks(p)
    masks = [0]
    for om in orbit_masks:
        masks += [m | om for m in masks]
    return masks


def build_automorphism_memberships():
    perms = list(itertools.permutations(VERTICES))
    auts = [[] for _ in range(N_GRAPHS)]
    memberships = 0
    for pi, p in enumerate(perms):
        fixed = invariant_graph_masks(p)
        memberships += len(fixed)
        for mask in fixed:
            auts[mask].append(pi)
    return perms, auts, memberships


def residual_perm_ids(perms, aut_ids, anchors):
    anchors = tuple(anchors)
    return [
        pi for pi in aut_ids
        if all(perms[pi][a] == a for a in anchors)
    ]


def target_orbit(perms, perm_ids, target):
    return {perms[pi][target] for pi in perm_ids}


def engine_status(perms, perm_ids, target):
    worlds = tuple(range(len(perm_ids)))
    actions = VERTICES
    admissible = frozenset(
        (wi, perms[pi][target])
        for wi, pi in enumerate(perm_ids)
    )
    contract = FiniteContract(
        worlds=worlds,
        actions=actions,
        available=frozenset(actions),
        admissible_pairs=admissible,
    )
    obs = {w: 0 for w in worlds}
    return audit_observation(contract, obs).status


def minimum_grounding(perms, aut_ids, target):
    candidates = tuple(v for v in VERTICES if v != target)
    for r in range(len(candidates) + 1):
        for anchors in itertools.combinations(candidates, r):
            residual = residual_perm_ids(perms, aut_ids, anchors)
            orbit = target_orbit(perms, residual, target)
            invariant = len(orbit) == 1
            status = engine_status(perms, residual, target)
            expected = "ACT" if invariant else "REFUSE"
            if status != expected:
                raise RuntimeError(
                    f"Engine mismatch target={target} anchors={anchors}: "
                    f"{status} vs {expected}"
                )
            if invariant:
                return r, anchors, len(residual), len(orbit)
    raise RuntimeError("No grounding found")


def main():
    perms, auts_by_graph, memberships = build_automorphism_memberships()

    # Burnside sanity check: number of unlabeled simple graphs on 6 vertices is 156.
    burnside_unlabeled = memberships // len(perms)
    if burnside_unlabeled != 156 or memberships % len(perms) != 0:
        raise RuntimeError(
            f"Burnside sanity failed: memberships={memberships}, "
            f"unlabeled={burnside_unlabeled}"
        )

    grounding_hist = Counter()
    aut_size_hist = Counter()
    no_anchor_act = 0
    total_cases = 0
    residual_ambiguity_at_act = 0
    examples = {}

    for mask, aut_ids in enumerate(auts_by_graph):
        aut_size_hist[len(aut_ids)] += 1
        for target in VERTICES:
            total_cases += 1
            base_orbit = target_orbit(perms, aut_ids, target)
            base_status = engine_status(perms, aut_ids, target)
            base_expected = "ACT" if len(base_orbit) == 1 else "REFUSE"
            if base_status != base_expected:
                raise RuntimeError(
                    f"Base engine mismatch graph={mask} target={target}"
                )
            if base_status == "ACT":
                no_anchor_act += 1

            r, anchors, residual_count, orbit_size = minimum_grounding(
                perms, aut_ids, target
            )
            grounding_hist[r] += 1
            if residual_count > 1:
                residual_ambiguity_at_act += 1
                examples.setdefault(
                    "safe_with_residual_decoder_ambiguity",
                    {
                        "graph_mask": mask,
                        "target": target,
                        "minimum_anchors": r,
                        "anchors": list(anchors),
                        "remaining_decoder_worlds": residual_count,
                        "target_orbit_size": orbit_size,
                        "automorphism_count": len(aut_ids),
                    },
                )

    result = {
        "protocol": "INSACERMO Sigma0 exhaustive simple graphs n=6",
        "n_vertices": N,
        "labeled_graphs": N_GRAPHS,
        "targets_per_graph": N,
        "graph_target_cases": total_cases,
        "permutations": len(perms),
        "automorphism_memberships": memberships,
        "burnside_unlabeled_graphs": burnside_unlabeled,
        "no_anchor_ACT_cases": no_anchor_act,
        "no_anchor_REFUSE_cases": total_cases - no_anchor_act,
        "minimum_grounding_histogram": {
            str(k): grounding_hist[k] for k in sorted(grounding_hist)
        },
        "graphs_by_automorphism_group_size": {
            str(k): aut_size_hist[k] for k in sorted(aut_size_hist)
        },
        "ACT_with_residual_decoder_ambiguity_cases": residual_ambiguity_at_act,
        "example": examples,
        "engine_group_mismatches": 0,
        "pass": True,
    }

    (HERE / "exhaustive_n6_results.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    lines = [
        "# Sigma0 exhaustive audit — all simple labeled graphs on 6 vertices",
        "",
        f"- labeled graphs: **{N_GRAPHS}**",
        f"- graph-target cases: **{total_cases}**",
        f"- permutations checked structurally: **{len(perms)}**",
        f"- automorphism memberships generated: **{memberships}**",
        f"- Burnside unlabeled-graph sanity check: **{burnside_unlabeled}**",
        f"- engine/group mismatches: **0**",
        f"- no-anchor ACT cases: **{no_anchor_act}**",
        f"- no-anchor REFUSE cases: **{total_cases - no_anchor_act}**",
        f"- ACT cases retaining >1 decoder-world at minimum grounding: "
        f"**{residual_ambiguity_at_act}**",
        "",
        "## Minimum grounding histogram over graph-target cases",
        "",
    ]
    for k in sorted(grounding_hist):
        lines.append(f"- {k} anchors: {grounding_hist[k]}")
    lines += [
        "",
        "## Exact finite identity checked",
        "",
        "For every graph, target and anchor set visited by the increasing-cardinality search:",
        "",
        "ACT <=> the residual pointwise anchor stabilizer has a singleton orbit on the target.",
        "",
        "This does not require the residual automorphism group to be trivial. "
        "Semantic/action safety can therefore occur before unique decoding of the entire structure.",
        "",
    ]
    (HERE / "EXHAUSTIVE_N6_RESULTS.md").write_text(
        "\n".join(lines), encoding="utf-8"
    )

    print(json.dumps({
        "labeled_graphs": N_GRAPHS,
        "graph_target_cases": total_cases,
        "unlabeled_graphs_burnside": burnside_unlabeled,
        "no_anchor_ACT": no_anchor_act,
        "no_anchor_REFUSE": total_cases - no_anchor_act,
        "min_grounding_hist": dict(sorted(grounding_hist.items())),
        "act_with_residual_ambiguity": residual_ambiguity_at_act,
        "engine_group_mismatches": 0,
        "pass": True,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
