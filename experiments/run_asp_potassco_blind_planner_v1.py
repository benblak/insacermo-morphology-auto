#!/usr/bin/env python3
"""Execute the frozen INSACERMO ASP-POTASSCO planner preregistration.

IMPORTANT: the protocol lives in INSACERMO_ASP_POTASSCO_BLIND_PLANNER_PREREG_V1.json
and was committed before algorithm_runs.arff was opened. This executor must not
change the frozen action sets, probe list, costs, safety rule, or endpoints.
"""
from __future__ import annotations

import csv
import hashlib
import itertools
import json
import math
import re
import urllib.request
from collections import defaultdict
from pathlib import Path

import numpy as np
import pandas as pd

ROOT = Path(__file__).resolve().parent
PREREG = ROOT / "INSACERMO_ASP_POTASSCO_BLIND_PLANNER_PREREG_V1.json"
OUT = ROOT / "asp_potassco_blind_planner_v1_output"
OUT.mkdir(exist_ok=True)

RAW_BASE = "https://raw.githubusercontent.com/coseal/aslib_data/master/ASP-POTASSCO/"
ALG_URL = RAW_BASE + "algorithm_runs.arff"
FEAT_URL = RAW_BASE + "feature_values.arff"
DESC_URL = RAW_BASE + "description.txt"


def download(url: str, path: Path) -> None:
    with urllib.request.urlopen(url, timeout=120) as r:
        path.write_bytes(r.read())


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_arff(path: Path):
    """Small ARFF reader sufficient for ASlib flat numeric/string tables."""
    attrs = []
    rows = []
    in_data = False
    attr_re = re.compile(r"^@attribute\s+(?:'([^']+)'|\"([^\"]+)\"|(\S+))\s+(.+)$", re.I)
    with path.open("r", encoding="utf-8", errors="replace", newline="") as f:
        data_lines = []
        for raw in f:
            line = raw.strip()
            if not line or line.startswith("%"):
                continue
            if not in_data:
                if line.lower().startswith("@data"):
                    in_data = True
                    continue
                m = attr_re.match(line)
                if m:
                    name = next(x for x in m.groups()[:3] if x is not None)
                    attrs.append((name, m.group(4).strip()))
            else:
                data_lines.append(raw)
        rdr = csv.reader(data_lines)
        rows = [r for r in rdr if r]
    if not attrs:
        raise RuntimeError(f"No ARFF attributes parsed from {path}")
    if any(len(r) != len(attrs) for r in rows):
        bad = [(i, len(r), len(attrs)) for i, r in enumerate(rows) if len(r) != len(attrs)][:5]
        raise RuntimeError(f"ARFF row width mismatch {path}: {bad}")
    return attrs, rows


def to_str(v):
    return v.strip().strip("'").strip('"')


def entropy_from_sizes(sizes):
    n = sum(sizes)
    if n == 0:
        return 0.0
    return -sum((s/n) * math.log2(s/n) for s in sizes if s)


def main():
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    base_algs = prereg["actions"]["base_capabilities"]
    repair_alg = prereg["actions"]["repair_adds"]
    features = prereg["probe_library"]["features"]
    cutoff = float(prereg["dataset"]["cutoff_seconds"])

    alg_path = OUT / "algorithm_runs.arff"
    feat_path = OUT / "feature_values.arff"
    desc_path = OUT / "description.txt"
    download(ALG_URL, alg_path)
    download(FEAT_URL, feat_path)
    download(DESC_URL, desc_path)

    # Parse algorithm outcomes.
    alg_attrs, alg_rows = parse_arff(alg_path)
    alg_cols = [a[0] for a in alg_attrs]
    expected_alg_cols = ["instance_id", "repetition", "algorithm", "runtime", "runstatus"]
    if alg_cols != expected_alg_cols:
        raise RuntimeError(f"Unexpected algorithm schema: {alg_cols}")

    wanted = set(base_algs + [repair_alg])
    records = []
    for r in alg_rows:
        inst, rep, alg, runtime, status = map(to_str, r)
        if alg in wanted:
            records.append((inst, int(float(rep)), alg, float(runtime), status))

    # Frozen protocol assumes deterministic one-record outcomes. Abort rather than
    # inventing an aggregation after seeing outcomes if duplicates exist.
    pair_counts = defaultdict(int)
    for inst, rep, alg, runtime, status in records:
        pair_counts[(inst, alg)] += 1
    duplicate_pairs = [k for k, v in pair_counts.items() if v != 1]
    if duplicate_pairs:
        raise RuntimeError(
            "Protocol execution halted: multiple/missing repetitions for an observed "
            f"instance-algorithm pair require a pre-outcome amendment. Examples: {duplicate_pairs[:10]}"
        )

    # Good matrix.
    good = defaultdict(dict)
    runtimes = defaultdict(dict)
    statuses = defaultdict(dict)
    for inst, rep, alg, runtime, status in records:
        good[inst][alg] = (status == "ok" and runtime < cutoff)
        runtimes[inst][alg] = runtime
        statuses[inst][alg] = status

    all_instances = sorted({inst for inst, *_ in records})
    complete_instances = [i for i in all_instances if all(a in good[i] for a in wanted)]
    incomplete = sorted(set(all_instances) - set(complete_instances))
    if incomplete:
        raise RuntimeError(f"Missing frozen algorithm outcomes for {len(incomplete)} instances")

    cohort = [i for i in complete_instances if any(good[i][a] for a in base_algs)]
    if not cohort:
        raise RuntimeError("Frozen base-actionable cohort is empty")

    # Parse feature table.
    feat_attrs, feat_rows = parse_arff(feat_path)
    feat_cols = [a[0] for a in feat_attrs]
    missing_frozen = [f for f in features if f not in feat_cols]
    if missing_frozen:
        raise RuntimeError(f"Frozen feature(s) absent: {missing_frozen}")

    fi = {c: j for j, c in enumerate(feat_cols)}
    if "instance_id" not in fi:
        raise RuntimeError("feature_values.arff has no instance_id")
    feat_by_inst = {}
    for row in feat_rows:
        inst = to_str(row[fi["instance_id"]])
        feat_by_inst[inst] = {f: to_str(row[fi[f]]) for f in features}

    # Frozen rule: missing values explicit category. Missing entire rows likewise.
    raw_feat = pd.DataFrame(index=cohort, columns=features, dtype=object)
    for inst in cohort:
        vals = feat_by_inst.get(inst, {})
        for f in features:
            raw_feat.loc[inst, f] = vals.get(f, "?")

    # Label-free quartile coarsening for numeric features; categorical values retained.
    Q = pd.DataFrame(index=cohort)
    bin_meta = {}
    for f in features:
        s = raw_feat[f].astype(str)
        nonmiss = s != "?"
        num = pd.to_numeric(s.where(nonmiss), errors="coerce")
        numeric_fraction = float(num.notna().sum()) / max(1, int(nonmiss.sum()))
        if nonmiss.sum() > 0 and numeric_fraction == 1.0:
            q = num.dropna()
            # Quantile edges are feature-only, fixed cohort only; collapse duplicates.
            cuts = np.unique(np.quantile(q.to_numpy(float), [0.25, 0.50, 0.75]))
            edges = np.concatenate(([-np.inf], cuts, [np.inf]))
            b = pd.cut(num, bins=edges, labels=False, include_lowest=True)
            Q[f] = b.astype("Int64").astype(str)
            Q.loc[~nonmiss, f] = "MISSING"
            bin_meta[f] = {"kind": "numeric_quartile", "cuts": [float(x) for x in cuts]}
        else:
            Q[f] = s.where(nonmiss, "MISSING")
            bin_meta[f] = {"kind": "categorical", "levels": sorted(Q[f].unique().tolist())}

    # Encode Good masks for fast exhaustive grouping.
    bit_for = {base_algs[0]: 1, base_algs[1]: 2, repair_alg: 4}
    goodmask = {}
    for inst in cohort:
        mask = 0
        for a, bit in bit_for.items():
            if good[inst][a]:
                mask |= bit
        goodmask[inst] = mask

    base_capmask = bit_for[base_algs[0]] | bit_for[base_algs[1]]
    repaired_capmask = base_capmask | bit_for[repair_alg]

    def eval_subset(subset, capmask):
        subset = list(subset)
        groups = defaultdict(list)
        if not subset:
            groups[("ALL",)] = cohort
        else:
            for inst in cohort:
                groups[tuple(Q.loc[inst, f] for f in subset)].append(inst)
        safe = True
        bad_cells = []
        for key, ids in groups.items():
            common = capmask
            for inst in ids:
                common &= goodmask[inst]
            if common == 0:
                safe = False
                if len(bad_cells) < 20:
                    bad_cells.append({"cell": list(key), "n": len(ids), "examples": ids[:10]})
        sizes = [len(x) for x in groups.values()]
        return {
            "safe": safe,
            "cells": len(sizes),
            "entropy_bits": entropy_from_sizes(sizes),
            "max_cell": max(sizes),
            "bad_cells_sample": bad_cells,
        }

    results = []
    for repaired, capmask in [(False, base_capmask), (True, repaired_capmask)]:
        for k in range(len(features) + 1):
            for subset in itertools.combinations(features, k):
                ev = eval_subset(subset, capmask)
                results.append({
                    "repaired": repaired,
                    "n_probes": k,
                    "probes": list(subset),
                    "total_structural_cost": k + int(repaired),
                    **ev,
                })

    def min_probes(repaired):
        ks = [r["n_probes"] for r in results if r["repaired"] == repaired and r["safe"]]
        return min(ks) if ks else None

    base_min = min_probes(False)
    repaired_min = min_probes(True)
    safe_results = [r for r in results if r["safe"]]
    min_cost = min((r["total_structural_cost"] for r in safe_results), default=None)
    optimal = [r for r in safe_results if r["total_structural_cost"] == min_cost] if min_cost is not None else []

    # Frozen primary route predicates.
    start_base = eval_subset([], base_capmask)["safe"]
    repair_only = eval_subset([], repaired_capmask)["safe"]
    any_base_probe_safe = any(r["safe"] and not r["repaired"] and r["n_probes"] > 0 for r in results)
    any_repaired_probe_safe = any(r["safe"] and r["repaired"] and r["n_probes"] > 0 for r in results)
    strong_mixed = (not start_base) and (not any_base_probe_safe) and (not repair_only) and any_repaired_probe_safe
    frozen_mixed_literal = (not start_base) and (not repair_only) and any_repaired_probe_safe

    # Route kinds represented among optimal plans.
    route_kinds = set()
    for r in optimal:
        if r["repaired"] and r["n_probes"] > 0:
            route_kinds.update(["PROBE", "REPAIR"])
        elif r["repaired"]:
            route_kinds.add("REPAIR")
        elif r["n_probes"] > 0:
            route_kinds.add("PROBE")
        else:
            route_kinds.add("ACT")

    # PRESERVE deletion stress from all optimal terminal states.
    preserve_rows = []
    for r in optimal:
        capmask = repaired_capmask if r["repaired"] else base_capmask
        for f in r["probes"]:
            reduced = [x for x in r["probes"] if x != f]
            ev = eval_subset(reduced, capmask)
            preserve_rows.append({
                "repaired": r["repaired"],
                "terminal_probes": "+".join(r["probes"]),
                "forgotten_probe": f,
                "remaining_probes": "+".join(reduced),
                "safe_after_forgetting": ev["safe"],
            })
    preserve_rejected = sum(not r["safe_after_forgetting"] for r in preserve_rows)

    # Frozen verdict.
    if repaired_min is not None and (base_min is None or repaired_min < base_min):
        verdict = "STRONG_POSITIVE_STRUCTURAL_REPLICATION" if base_min is None else "POSITIVE_CAPABILITY_INFORMATION_REPLICATION"
    elif repaired_min == base_min:
        verdict = "NULL_NO_INFORMATION_REDUCTION"
    elif repaired_min is not None and base_min is not None and repaired_min > base_min:
        verdict = "NEGATIVE_REPAIR_INCREASES_INFORMATION_REQUIREMENT"
    else:
        verdict = "NO_SAFE_REPRESENTATION_IN_FROZEN_SEARCH_SPACE"

    # Compact endpoint table.
    endpoint_rows = []
    for repaired in [False, True]:
        rr = [r for r in results if r["repaired"] == repaired]
        mk = min((r["n_probes"] for r in rr if r["safe"]), default=None)
        mins = [r for r in rr if r["safe"] and r["n_probes"] == mk] if mk is not None else []
        endpoint_rows.append({
            "regime": "base" if not repaired else "base_plus_repair",
            "minimum_probes": mk,
            "n_min_probe_safe_states": len(mins),
            "best_entropy_at_min_probes": min((r["entropy_bits"] for r in mins), default=None),
            "fewest_cells_at_min_probes": min((r["cells"] for r in mins), default=None),
        })

    # Save all safe states, not all 2048 rows, plus optimal frontier and PRESERVE audit.
    pd.DataFrame([
        {**{k:v for k,v in r.items() if k != "bad_cells_sample"}, "probes": "+".join(r["probes"])}
        for r in safe_results
    ]).to_csv(OUT / "safe_states.csv", index=False)
    pd.DataFrame([
        {**{k:v for k,v in r.items() if k != "bad_cells_sample"}, "probes": "+".join(r["probes"])}
        for r in optimal
    ]).to_csv(OUT / "optimal_frontier.csv", index=False)
    pd.DataFrame(preserve_rows).to_csv(OUT / "preserve_forgetting_audit.csv", index=False)
    pd.DataFrame(endpoint_rows).to_csv(OUT / "primary_endpoints.csv", index=False)

    audit = {
        "name": "INSACERMO_ASP_POTASSCO_BLIND_PLANNER_AUDIT_V1",
        "protocol_status": "EXECUTED_AGAINST_FROZEN_PRE_OUTCOME_PREREGISTRATION",
        "verdict": verdict,
        "source": {
            "repository": "coseal/aslib_data",
            "scenario": "ASP-POTASSCO",
            "algorithm_runs_sha256": sha256(alg_path),
            "feature_values_sha256": sha256(feat_path),
            "description_sha256": sha256(desc_path),
            "algorithm_rows_total": len(alg_rows),
            "feature_rows_total": len(feat_rows),
        },
        "frozen_contract": prereg,
        "execution": {
            "instances_complete_for_frozen_algorithms": len(complete_instances),
            "fixed_base_actionable_cohort_n": len(cohort),
            "base_good_counts": {a: sum(good[i][a] for i in cohort) for a in base_algs},
            "repair_good_count": sum(good[i][repair_alg] for i in cohort),
            "feature_binning": bin_meta,
            "search_states_evaluated": len(results),
        },
        "primary": {
            "base_minimum_probes": base_min,
            "repaired_minimum_probes": repaired_min,
            "minimum_total_structural_cost": min_cost,
            "optimal_terminal_states_n": len(optimal),
            "optimal_first_move_route_kinds": sorted(route_kinds),
            "start_base_safe": start_base,
            "any_probe_only_safe_in_frozen_library": any_base_probe_safe,
            "repair_only_safe": repair_only,
            "any_repaired_plus_probe_safe": any_repaired_probe_safe,
            "mixed_route_strong_definition": strong_mixed,
            "mixed_route_literal_frozen_interpretation": frozen_mixed_literal,
            "strict_capability_information_reduction": repaired_min is not None and (base_min is None or repaired_min < base_min),
        },
        "secondary": {
            "primary_endpoint_table": endpoint_rows,
            "preserve_forgetting_edges_tested": len(preserve_rows),
            "preserve_forgetting_edges_rejected": preserve_rejected,
        },
        "scientific_boundary": "Pre-specified second-domain real-data structural test by the same analyst, not third-party replication. Deterministic finite empirical planner only; no causal, population, stochastic, continuous-state, or infinite-horizon claim."
    }
    audit_path = OUT / "INSACERMO_ASP_POTASSCO_BLIND_PLANNER_AUDIT_V1.json"
    audit_path.write_text(json.dumps(audit, indent=2, ensure_ascii=False), encoding="utf-8")

    # Human-readable report generated mechanically from frozen endpoints.
    def fmt(x):
        return "UNREACHABLE" if x is None else str(x)
    report = f"""# INSACERMO ASP-POTASSCO blind planner replication V1

**Protocol:** frozen before `algorithm_runs.arff` was opened.  
**Verdict under frozen rules:** **{verdict}**

## Primary endpoints

- Fixed base-actionable cohort: **{len(cohort)}** instances
- Frozen base algorithms: `{base_algs[0]}`, `{base_algs[1]}`
- Frozen REPAIR: add `{repair_alg}`
- Minimum frozen coarse probes under base: **{fmt(base_min)}**
- Minimum frozen coarse probes after REPAIR: **{fmt(repaired_min)}**
- Minimum total structural cost: **{fmt(min_cost)}**
- Optimal terminal states: **{len(optimal)}**
- Optimal first-move route kinds: **{', '.join(sorted(route_kinds)) if route_kinds else 'NONE'}**

Start/base/no-probe safe: **{start_base}**  
Any probe-only safe representation in the full frozen 10-probe library: **{any_base_probe_safe}**  
REPAIR-only/no-probe safe: **{repair_only}**  
Any REPAIR+PROBE safe representation: **{any_repaired_probe_safe}**

Strong mixed-route predicate (PROBE-only unreachable, REPAIR-only unsafe, combined safe): **{strong_mixed}**  
Literal frozen mixed predicate: **{frozen_mixed_literal}**

## PRESERVE

Single-probe forgetting edges tested from optimal terminals: **{len(preserve_rows)}**  
Rejected because safety is lost: **{preserve_rejected}**

## Scope

This is a **pre-specified second-domain real-data structural test**, not a
third-party independent replication. The protocol and frozen feature/action
choices were committed before the outcome matrix was opened. Results were not
used to revise the protocol.
"""
    (OUT / "REPORT.md").write_text(report, encoding="utf-8")

    # Copy preregistration and create checksums.
    (OUT / PREREG.name).write_bytes(PREREG.read_bytes())
    checksum_lines = []
    for p in sorted(OUT.iterdir()):
        if p.is_file() and p.name != "SHA256SUMS.txt":
            checksum_lines.append(f"{sha256(p)}  {p.name}")
    (OUT / "SHA256SUMS.txt").write_text("\n".join(checksum_lines) + "\n", encoding="utf-8")

    print(json.dumps({
        "verdict": verdict,
        "cohort_n": len(cohort),
        "base_minimum_probes": base_min,
        "repaired_minimum_probes": repaired_min,
        "minimum_total_structural_cost": min_cost,
        "optimal_terminal_states_n": len(optimal),
        "optimal_first_move_route_kinds": sorted(route_kinds),
        "strong_mixed_route": strong_mixed,
        "preserve_rejected": preserve_rejected,
        "preserve_tested": len(preserve_rows),
    }, indent=2))


if __name__ == "__main__":
    main()
