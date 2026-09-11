#!/usr/bin/env python3
import csv
import hashlib
import itertools
import json
import math
import os
import urllib.request
from collections import Counter, defaultdict
from datetime import datetime, timezone

STUDY_ID = "INSACERMO_BNSL2016_FIXED_COHORT_SURFACE_V1"
PROTOCOL_SHA256 = "88a8627fa325925a81b9be87865b05a41bc4ee71473b88cebdb0017749a32004"
ALG_URL = "https://raw.githubusercontent.com/coseal/aslib_data/master/BNSL-2016/algorithm_runs.arff"
CV_URL = "https://raw.githubusercontent.com/coseal/aslib_data/master/BNSL-2016/cv.arff"
ALG_GIT_BLOB = "33adc274ba3bd7d62875a5ee017d9b4b147e6ee8"
CV_GIT_BLOB = "b53e47f5d081cfa8901ff652daf40b9c5ecd0a87"
BASE = ("astar-ec", "astar-ed3")
CANDIDATES = ("astar-comp", "cpbayes", "ilp-141", "ilp-141-nc", "ilp-162", "ilp-162-nc")
ALL = BASE + CANDIDATES
BUDGETS = (60.0, 300.0, 900.0, 1800.0, 3600.0, 7200.0)
T_REF = 7200.0
OUTDIR = "analysis/results_bnsl_fixed_v1"


def download(url):
    with urllib.request.urlopen(url, timeout=60) as r:
        return r.read()


def parse_arff_data(raw):
    text = raw.decode("utf-8")
    in_data = False
    rows = []
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("%"):
            continue
        if not in_data:
            if line.lower() == "@data":
                in_data = True
            continue
        rows.append(next(csv.reader([line])))
    return rows


def entropy_contribution(c, n):
    if c <= 0 or n <= 0:
        return 0.0
    p = c / n
    return -p * math.log2(p)


def hmin_priority_dp(freq, m):
    """Exact minimum Shannon entropy over feasible deterministic assignments.

    For a fixed priority order of actions, assign each profile to its first
    admissible action. For any feasible assignment, ordering actions by decreasing
    assignment counts and greedifying majorizes that assignment's count vector;
    Shannon entropy is Schur-concave. Therefore an optimum occurs for a priority
    order. Dynamic programming over chosen-action subsets evaluates all priority
    orders exactly in O(m 2^m |profiles|).
    """
    n = sum(freq.values())
    if n == 0:
        return 0.0, [0] * m, list(range(m))
    full = (1 << m) - 1
    # precompute newly captured count c(S,a)
    captured = {}
    for S in range(1 << m):
        for a in range(m):
            if S & (1 << a):
                continue
            c = 0
            abit = 1 << a
            for mask, count in freq.items():
                if (mask & abit) and not (mask & S):
                    c += count
            captured[(S, a)] = c

    inf = float("inf")
    dp = [inf] * (1 << m)
    parent = [None] * (1 << m)
    dp[0] = 0.0
    for S in range(1 << m):
        if not math.isfinite(dp[S]):
            continue
        for a in range(m):
            bit = 1 << a
            if S & bit:
                continue
            c = captured[(S, a)]
            S2 = S | bit
            val = dp[S] + entropy_contribution(c, n)
            # deterministic tie-break: lexicographically smaller priority order
            if val < dp[S2] - 1e-15:
                dp[S2] = val
                parent[S2] = (S, a, c)
            elif abs(val - dp[S2]) <= 1e-15:
                # reconstructing full order for tie-break is unnecessary for metrics;
                # prefer lower action index at the last step for deterministic output.
                if parent[S2] is None or a < parent[S2][1]:
                    parent[S2] = (S, a, c)

    order_rev = []
    counts_rev = []
    S = full
    while S:
        prev, a, c = parent[S]
        order_rev.append(a)
        counts_rev.append(c)
        S = prev
    order = list(reversed(order_rev))
    counts_in_order = list(reversed(counts_rev))
    counts = [0] * m
    for a, c in zip(order, counts_in_order):
        counts[a] = c
    return dp[full], counts, order


def pair_conflicts(freq):
    items = list(freq.items())
    total = 0
    for i, (m1, c1) in enumerate(items):
        for m2, c2 in items[i+1:]:
            if (m1 & m2) == 0:
                total += c1 * c2
    return int(total)


def admissible_mask(inst, runtimes, actions, T):
    mask = 0
    for j, a in enumerate(actions):
        rec = runtimes.get(inst, {}).get(a)
        if rec is not None:
            runtime, status = rec
            if status == "ok" and runtime <= T:
                mask |= 1 << j
    return mask


def evaluate(reference, runtimes, added, T):
    actions = BASE + tuple(added)
    m = len(actions)
    refuse_idx = m
    freq_total = Counter()
    freq_actionable = Counter()
    n_actionable = 0
    for inst in reference:
        mask = admissible_mask(inst, runtimes, actions, T)
        if mask:
            n_actionable += 1
            freq_actionable[mask] += 1
            freq_total[mask] += 1
        else:
            freq_total[1 << refuse_idx] += 1

    H_total, counts_total, order_total = hmin_priority_dp(freq_total, m + 1)
    if n_actionable:
        H_act, counts_act, order_act = hmin_priority_dp(freq_actionable, m)
    else:
        H_act, counts_act, order_act = 0.0, [0] * m, list(range(m))

    labels_total = list(actions) + ["REFUSE"]
    return {
        "T_seconds": T,
        "added": list(added),
        "n_added": len(added),
        "n_total": len(reference),
        "n_actionable": n_actionable,
        "n_refuse": len(reference) - n_actionable,
        "coverage": n_actionable / len(reference),
        "H_total_bits": H_total,
        "pair_conflicts_total": pair_conflicts(freq_total),
        "H_actionable_bits": H_act,
        "pair_conflicts_actionable": pair_conflicts(freq_actionable),
        "optimal_counts_total": {labels_total[i]: counts_total[i] for i in range(m + 1)},
        "optimal_priority_total": [labels_total[i] for i in order_total],
        "optimal_counts_actionable": {actions[i]: counts_act[i] for i in range(m)},
        "optimal_priority_actionable": [actions[i] for i in order_act],
        "profile_count_total": len(freq_total),
        "profile_count_actionable": len(freq_actionable),
    }


def better_for_frontier(e):
    # maximize coverage first, then minimize information requirement, conflicts,
    # implementation count, then lexicographic portfolio for reproducibility.
    return (-e["coverage"], round(e["H_total_bits"], 15), e["pair_conflicts_total"], e["n_added"], tuple(e["added"]))


def main():
    os.makedirs(OUTDIR, exist_ok=True)
    alg_raw = download(ALG_URL)
    cv_raw = download(CV_URL)
    alg_rows = parse_arff_data(alg_raw)
    cv_rows = parse_arff_data(cv_raw)

    runtimes = defaultdict(dict)
    for row in alg_rows:
        inst, rep, alg, runtime, status = row
        if rep == "1" and alg in ALL:
            runtimes[inst][alg] = (float(runtime), status)

    fold_of = {}
    for row in cv_rows:
        inst, rep, fold = row
        if rep == "1":
            fold_of[inst] = int(float(fold))
    all_instances = sorted(set(runtimes) & set(fold_of))

    # Frozen reference population: base-actionable at the primary 7200-s contract.
    reference = []
    for inst in all_instances:
        if admissible_mask(inst, runtimes, BASE, T_REF):
            reference.append(inst)
    if len(reference) != 519:
        raise RuntimeError(f"Reference population mismatch: expected 519, got {len(reference)}")

    all_rows = []
    frontiers = []
    per_budget = []
    for T in BUDGETS:
        rows_T = []
        for k in range(len(CANDIDATES) + 1):
            for added in itertools.combinations(CANDIDATES, k):
                e = evaluate(reference, runtimes, added, T)
                rows_T.append(e)
                all_rows.append(e)
        frontier_T = []
        for K in range(len(CANDIDATES) + 1):
            eligible = [e for e in rows_T if e["n_added"] <= K]
            best = min(eligible, key=better_for_frontier)
            fr = dict(best)
            fr["max_added_K"] = K
            frontier_T.append(fr)
            frontiers.append(fr)
        base = next(e for e in rows_T if e["n_added"] == 0)
        best_any = min(rows_T, key=better_for_frontier)
        full = next(e for e in rows_T if e["n_added"] == len(CANDIDATES))
        min_k_full_coverage = None
        for K in range(len(CANDIDATES) + 1):
            candidate = frontier_T[K]
            if abs(candidate["coverage"] - 1.0) < 1e-15:
                min_k_full_coverage = K
                break
        per_budget.append({
            "T_seconds": T,
            "base": base,
            "best_any": best_any,
            "all_candidates": full,
            "min_K_for_full_coverage": min_k_full_coverage,
            "frontier": frontier_T,
        })

    # Structural checks on the fixed population.
    base_path = [b["base"] for b in per_budget]
    checks = {
        "reference_n_is_519": len(reference) == 519,
        "base_7200_coverage_is_1": abs(base_path[-1]["coverage"] - 1.0) < 1e-15,
        "base_7200_H_total_is_0": abs(base_path[-1]["H_total_bits"]) < 1e-15,
        "coverage_base_nondecreasing_in_T": all(base_path[i]["coverage"] <= base_path[i+1]["coverage"] + 1e-15 for i in range(len(base_path)-1)),
        "coverage_full_portfolio_nondecreasing_in_T": all(per_budget[i]["all_candidates"]["coverage"] <= per_budget[i+1]["all_candidates"]["coverage"] + 1e-15 for i in range(len(per_budget)-1)),
    }

    source = {
        "algorithm_runs_git_blob_sha": ALG_GIT_BLOB,
        "cv_git_blob_sha": CV_GIT_BLOB,
        "algorithm_runs_sha256": hashlib.sha256(alg_raw).hexdigest(),
        "cv_sha256": hashlib.sha256(cv_raw).hexdigest(),
        "algorithm_runs_bytes": len(alg_raw),
        "cv_bytes": len(cv_raw),
        "instances_with_runtime_and_fold_rep1": len(all_instances),
        "reference_population_n": len(reference),
    }

    audit = {
        "study_id": STUDY_ID,
        "executed_at_utc": datetime.now(timezone.utc).isoformat(),
        "protocol_sha256": PROTOCOL_SHA256,
        "status": "secondary frozen follow-up on already-inspected data; not an independent blind replication",
        "source": source,
        "contract": {
            "reference_population": "519 instances base-actionable at 7200s",
            "base_capabilities": list(BASE),
            "candidate_capabilities": list(CANDIDATES),
            "budgets_seconds": list(BUDGETS),
            "refuse_rule": "REFUSE iff no solver in current portfolio is admissible",
            "frontier_order": "maximize coverage; minimize H_total; minimize pair conflicts; fewer additions; lexicographic",
        },
        "structural_checks": checks,
        "per_budget": per_budget,
        "guardrail": "H_total is contract-relative and includes the exact ACT/REFUSE routing requirement on a fixed population. It is not generic instance information, prediction entropy, or runtime-regret information."
    }

    audit_path = os.path.join(OUTDIR, "INSACERMO_BNSL2016_FIXED_COHORT_SURFACE_V1.json")
    with open(audit_path, "w", encoding="utf-8") as f:
        json.dump(audit, f, indent=2, ensure_ascii=False)

    all_path = os.path.join(OUTDIR, "INSACERMO_BNSL2016_FIXED_COHORT_ALL_PORTFOLIOS_V1.csv")
    fields = ["T_seconds","n_added","added","n_total","n_actionable","n_refuse","coverage","H_total_bits","pair_conflicts_total","H_actionable_bits","pair_conflicts_actionable"]
    with open(all_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for e in all_rows:
            r = {k:e[k] for k in fields if k != "added"}
            r["added"] = ";".join(e["added"])
            w.writerow(r)

    frontier_path = os.path.join(OUTDIR, "INSACERMO_BNSL2016_FIXED_COHORT_FRONTIER_V1.csv")
    ffields = ["T_seconds","max_added_K","n_added","added","n_total","n_actionable","n_refuse","coverage","H_total_bits","pair_conflicts_total","H_actionable_bits","pair_conflicts_actionable"]
    with open(frontier_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=ffields)
        w.writeheader()
        for e in frontiers:
            r = {k:e[k] for k in ffields if k != "added"}
            r["added"] = ";".join(e["added"])
            w.writerow(r)

    summary = {
        "protocol_sha256": PROTOCOL_SHA256,
        "source": source,
        "structural_checks": checks,
        "base_fixed_population_path": [
            {k:e[k] for k in ("T_seconds","n_actionable","n_refuse","coverage","H_total_bits","pair_conflicts_total","H_actionable_bits","pair_conflicts_actionable")}
            for e in base_path
        ],
        "frontier_K1_path": [
            {k:b["frontier"][1][k] for k in ("T_seconds","n_added","added","n_actionable","n_refuse","coverage","H_total_bits","pair_conflicts_total","H_actionable_bits","pair_conflicts_actionable")}
            for b in per_budget
        ],
        "best_any_path": [
            {k:b["best_any"][k] for k in ("T_seconds","n_added","added","n_actionable","n_refuse","coverage","H_total_bits","pair_conflicts_total","H_actionable_bits","pair_conflicts_actionable")}
            for b in per_budget
        ],
        "min_K_for_full_coverage": {str(int(b["T_seconds"])): b["min_K_for_full_coverage"] for b in per_budget},
    }
    summary_path = os.path.join(OUTDIR, "SUMMARY.txt")
    with open(summary_path, "w", encoding="utf-8") as f:
        f.write("INSACERMO BNSL-2016 FIXED-COHORT SURFACE V1\n")
        f.write(json.dumps(summary, indent=2, ensure_ascii=False))
        f.write("\n")

    manifest = {}
    for p in (audit_path, all_path, frontier_path, summary_path):
        with open(p, "rb") as fh:
            manifest[os.path.basename(p)] = hashlib.sha256(fh.read()).hexdigest()
    sums_path = os.path.join(OUTDIR, "SHA256SUMS.json")
    with open(sums_path, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2)

    print(open(summary_path, encoding="utf-8").read())
    print("SHA256SUMS", json.dumps(manifest, indent=2))


if __name__ == "__main__":
    main()
