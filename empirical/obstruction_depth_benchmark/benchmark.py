from __future__ import annotations

import argparse
import collections
import csv
import hashlib
import json
from pathlib import Path
from typing import Hashable, Iterable

import networkx as nx

DATASETS = {
    "zachary_karate": nx.karate_club_graph,
    "florentine_families": nx.florentine_families_graph,
    "davis_southern_women": nx.davis_southern_women_graph,
}


def canonical_edge_rows(G: nx.Graph) -> list[tuple[str, str]]:
    rows = []
    for u, v in G.edges():
        a, b = sorted((str(u), str(v)))
        rows.append((a, b))
    return sorted(rows)


def canonical_edge_text(G: nx.Graph) -> str:
    return "".join(f"{a},{b}\n" for a, b in canonical_edge_rows(G))


def canonical_cycle(cycle: Iterable[Hashable]) -> tuple[str, ...]:
    labs = [str(x) for x in cycle]
    n = len(labs)
    reps: list[tuple[str, ...]] = []
    for seq in (labs, list(reversed(labs))):
        for i in range(n):
            reps.append(tuple(seq[i:] + seq[:i]))
    return min(reps)


def odd_cycle_obstructions(G: nx.Graph):
    if nx.is_bipartite(G):
        return collections.Counter(), None, None, 0, 0

    counts: collections.Counter[int] = collections.Counter()
    min_len = None
    max_len = None
    min_witnesses: list[tuple[str, ...]] = []
    max_witnesses: list[tuple[str, ...]] = []
    total_cycles = 0
    odd_cycles = 0

    for cycle in nx.simple_cycles(G):
        if len(cycle) < 3:
            continue
        total_cycles += 1
        L = len(cycle)
        if L % 2 == 0:
            continue
        odd_cycles += 1
        counts[L] += 1
        c = canonical_cycle(cycle)
        if min_len is None or L < min_len:
            min_len, min_witnesses = L, [c]
        elif L == min_len:
            min_witnesses.append(c)
        if max_len is None or L > max_len:
            max_len, max_witnesses = L, [c]
        elif L == max_len:
            max_witnesses.append(c)

    min_witness = min(min_witnesses) if min_witnesses else None
    max_witness = min(max_witnesses) if max_witnesses else None
    return counts, min_witness, max_witness, total_cycles, odd_cycles


Literal = tuple[str, bool]
Clause = tuple[Literal, Literal]


def inequality_cnf(cycle: tuple[str, ...]) -> list[Clause]:
    clauses: list[Clause] = []
    for i, u in enumerate(cycle):
        v = cycle[(i + 1) % len(cycle)]
        clauses.append(((u, True), (v, True)))
        clauses.append(((u, False), (v, False)))
    return clauses


def negate(lit: Literal) -> Literal:
    return (lit[0], not lit[1])


def two_sat_is_sat(clauses: list[Clause]) -> bool:
    I = nx.DiGraph()
    variables: set[str] = set()
    for a, b in clauses:
        variables.add(a[0])
        variables.add(b[0])
        I.add_edge(negate(a), b)
        I.add_edge(negate(b), a)
    for v in variables:
        I.add_node((v, False))
        I.add_node((v, True))
    comp = {}
    for idx, component in enumerate(nx.strongly_connected_components(I)):
        for node in component:
            comp[node] = idx
    return all(comp[(v, False)] != comp[(v, True)] for v in variables)


def audit_mus(clauses: list[Clause]) -> dict:
    full_sat = two_sat_is_sat(clauses)
    deletion_sat = []
    for i in range(len(clauses)):
        deletion_sat.append(two_sat_is_sat(clauses[:i] + clauses[i + 1 :]))
    return {
        "full_sat": full_sat,
        "single_clause_deletions": len(clauses),
        "single_clause_deletions_sat": sum(deletion_sat),
        "is_mus": (not full_sat) and all(deletion_sat),
    }


def write_csv(path: Path, fieldnames: list[str], rows: list[dict]):
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames, lineterminator="\n")
        w.writeheader()
        w.writerows(rows)


def run(outdir: Path) -> dict:
    outdir.mkdir(parents=True, exist_ok=True)
    summary = {
        "benchmark": "INSACERMO Obstruction Depth Benchmark V0.1",
        "networkx_version": nx.__version__,
        "contract": "for every selected undirected edge {u,v}, require x_u != x_v",
        "datasets": {},
    }
    distribution_rows = []
    witness_rows = []

    for name, generator in DATASETS.items():
        G = generator()
        edge_text = canonical_edge_text(G)
        edge_hash = hashlib.sha256(edge_text.encode("utf-8")).hexdigest()
        (outdir / f"{name}_edges.csv").write_text("u,v\n" + edge_text, encoding="utf-8")

        counts, minw, maxw, total_cycles, odd_cycles = odd_cycle_obstructions(G)
        for L, count in sorted(counts.items()):
            distribution_rows.append({"dataset": name, "obstruction_size_edges": L, "count": count})

        record = {
            "nodes": G.number_of_nodes(),
            "edges": G.number_of_edges(),
            "canonical_edge_sha256": edge_hash,
            "bipartite": nx.is_bipartite(G),
            "total_simple_cycles_enumerated": total_cycles,
            "odd_cycle_obstructions": odd_cycles,
            "detection_depth_edges": min(counts) if counts else None,
            "certification_depth_edges": max(counts) if counts else None,
            "min_obstruction_witness": list(minw) if minw else None,
            "max_obstruction_witness": list(maxw) if maxw else None,
        }

        if maxw:
            clauses = inequality_cnf(maxw)
            audit = audit_mus(clauses)
            record["max_witness_cnf_clauses"] = len(clauses)
            record["max_witness_cnf_mus_audit"] = audit
            record["cnf_local_audit_blindspot_depth"] = len(clauses) - 1 if audit["is_mus"] else None
            for i, (a, b) in enumerate(clauses, start=1):
                witness_rows.append({
                    "dataset": name,
                    "witness_kind": "max_odd_cycle_cnf",
                    "clause_index": i,
                    "literal_1_var": a[0],
                    "literal_1_value": a[1],
                    "literal_2_var": b[0],
                    "literal_2_value": b[1],
                })
        else:
            record["max_witness_cnf_clauses"] = 0
            record["max_witness_cnf_mus_audit"] = None
            record["cnf_local_audit_blindspot_depth"] = None

        summary["datasets"][name] = record

    write_csv(
        outdir / "obstruction_distribution.csv",
        ["dataset", "obstruction_size_edges", "count"],
        distribution_rows,
    )
    write_csv(
        outdir / "max_witness_cnf_clauses.csv",
        ["dataset", "witness_kind", "clause_index", "literal_1_var", "literal_1_value", "literal_2_var", "literal_2_value"],
        witness_rows,
    )
    (outdir / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return summary


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--out", default="results")
    p.add_argument("--check", action="store_true")
    args = p.parse_args()
    outdir = Path(args.out)
    summary = run(outdir)

    expected = {
        "zachary_karate": (34, 78, 3, 19, 365521, 38),
        "florentine_families": (15, 20, 3, 9, 20, 18),
        "davis_southern_women": (32, 89, None, None, 0, 0),
    }
    if args.check:
        for name, exp in expected.items():
            r = summary["datasets"][name]
            got = (
                r["nodes"], r["edges"], r["detection_depth_edges"],
                r["certification_depth_edges"], r["odd_cycle_obstructions"],
                r["max_witness_cnf_clauses"],
            )
            if got != exp:
                raise SystemExit(f"benchmark drift for {name}: expected {exp}, got {got}")
            if r["max_witness_cnf_clauses"]:
                a = r["max_witness_cnf_mus_audit"]
                if not a["is_mus"]:
                    raise SystemExit(f"MUS audit failed for {name}")
        print("BENCHMARK CHECK PASSED")


if __name__ == "__main__":
    main()
