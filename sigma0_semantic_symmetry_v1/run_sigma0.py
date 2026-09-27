#!/usr/bin/env python3
from __future__ import annotations

import itertools
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from insacermo_actionability_engine_v1 import FiniteContract, audit_observation

HERE = Path(__file__).resolve().parent
SPEC = json.loads((HERE / "structures.json").read_text(encoding="utf-8"))
TARGET = SPEC["target"]


def canon_edge(a, b):
    return (a, b) if a < b else (b, a)


def automorphisms(n, edges):
    edge_set = {canon_edge(a, b) for a, b in edges}
    out = []
    for p in itertools.permutations(range(n)):
        ok = True
        for a in range(n):
            for b in range(a + 1, n):
                lhs = (a, b) in edge_set
                rhs = canon_edge(p[a], p[b]) in edge_set
                if lhs != rhs:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            out.append(p)
    return out


def worlds_for_anchors(auts, anchors):
    anchors = set(anchors)
    return [p for p in auts if all(p[a] == a for a in anchors)]


def engine_status(worlds, n, target):
    world_ids = tuple(range(len(worlds)))
    actions = tuple(range(n))
    pairs = frozenset(
        (i, worlds[i][target])
        for i in range(len(worlds))
    )
    contract = FiniteContract(
        worlds=world_ids,
        actions=actions,
        available=frozenset(actions),
        admissible_pairs=pairs,
    )
    observation = {i: "single-message" for i in world_ids}
    audit = audit_observation(contract, observation)
    common = audit.fibers[0].common_actions if audit.fibers else tuple()
    independent = len({p[target] for p in worlds}) == 1
    expected = "ACT" if independent else "REFUSE"
    if audit.status != expected:
        raise RuntimeError(
            f"Engine/group mismatch: engine={audit.status} expected={expected}"
        )
    return audit.status, list(common), sorted({p[target] for p in worlds})


def min_anchors(auts, n, target):
    candidates = tuple(v for v in range(n) if v != target)
    base_worlds = worlds_for_anchors(auts, ())
    base_status, base_common, base_orbit = engine_status(base_worlds, n, target)
    if base_status == "ACT":
        return {
            "min_anchor_count": 0,
            "anchors": [],
            "remaining_decoder_worlds": len(base_worlds),
            "status": base_status,
            "common_actions": base_common,
            "target_orbit": base_orbit,
        }

    for r in range(1, len(candidates) + 1):
        for anchors in itertools.combinations(candidates, r):
            ws = worlds_for_anchors(auts, anchors)
            status, common, orbit = engine_status(ws, n, target)
            if status == "ACT":
                return {
                    "min_anchor_count": r,
                    "anchors": list(anchors),
                    "remaining_decoder_worlds": len(ws),
                    "status": status,
                    "common_actions": common,
                    "target_orbit": orbit,
                }
    raise RuntimeError("No anchor set found; impossible under frozen finite model.")


def main():
    rows = []
    for s in SPEC["structures"]:
        name = s["name"]
        n = s["n"]
        auts = automorphisms(n, s["edges"])
        no_anchor_worlds = worlds_for_anchors(auts, ())
        no_status, no_common, no_orbit = engine_status(no_anchor_worlds, n, TARGET)
        best = min_anchors(auts, n, TARGET)
        rows.append({
            "name": name,
            "n": n,
            "automorphism_count": len(auts),
            "no_anchor": {
                "decoder_worlds": len(no_anchor_worlds),
                "status": no_status,
                "common_actions": no_common,
                "target_orbit": no_orbit,
            },
            "minimum_grounding": best,
        })

    result = {
        "protocol": "INSACERMO Sigma0 — Semantic Symmetry V1",
        "evidence_class": "finite exact application-level symmetry stress test",
        "target": TARGET,
        "rows": rows,
        "pass": True,
    }

    (HERE / "results.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    lines = [
        "# INSACERMO Sigma0 — Semantic Symmetry V1 — Results",
        "",
        "| Structure | |Aut| | No anchors | min anchors | witness | decoder worlds at minimum |",
        "|---|---:|---|---:|---|---:|",
    ]
    for r in rows:
        m = r["minimum_grounding"]
        lines.append(
            f"| {r['name']} | {r['automorphism_count']} | "
            f"{r['no_anchor']['status']} | {m['min_anchor_count']} | "
            f"{m['anchors']} | {m['remaining_decoder_worlds']} |"
        )
    lines += [
        "",
        "## Interpretation",
        "",
        "The exact finite result is about residual semantic symmetry, not universal language. "
        "A relational message needs no external grounding only when its remaining automorphisms "
        "already leave the contract-relevant target invariant. Otherwise grounding is needed "
        "until all surviving decoder-worlds agree on one concrete action.",
        "",
    ]
    (HERE / "RESULTS.md").write_text("\n".join(lines), encoding="utf-8")

    for r in rows:
        m = r["minimum_grounding"]
        print(
            f"{r['name']} aut={r['automorphism_count']} "
            f"no_anchor={r['no_anchor']['status']} "
            f"min_anchors={m['min_anchor_count']} witness={m['anchors']} "
            f"remaining={m['remaining_decoder_worlds']}"
        )
    print("PASS")


if __name__ == "__main__":
    main()
