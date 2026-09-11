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

STUDY_ID = "INSACERMO_BNSL2016_BLIND_COST_AWARE_CAPABILITY_DESIGN_V1"
PREREG_SHA256 = "aeebf3d9f3217d82787787d74bee9447e2e5fd9f80670f8b5d160a25d4577c63"
REPO = "coseal/aslib_data"
ALG_URL = "https://raw.githubusercontent.com/coseal/aslib_data/master/BNSL-2016/algorithm_runs.arff"
CV_URL = "https://raw.githubusercontent.com/coseal/aslib_data/master/BNSL-2016/cv.arff"
ALG_GIT_BLOB = "33adc274ba3bd7d62875a5ee017d9b4b147e6ee8"
CV_GIT_BLOB = "b53e47f5d081cfa8901ff652daf40b9c5ecd0a87"
BASE = ("astar-ec", "astar-ed3")
CANDIDATES = ("astar-comp", "cpbayes", "ilp-141", "ilp-141-nc", "ilp-162", "ilp-162-nc")
ALL = BASE + CANDIDATES
PRIMARY_T = 7200.0
STRESS_T = (60.0, 300.0, 900.0, 1800.0, 3600.0, 7200.0)
OUTDIR = "analysis/results_bnsl_v1"


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


def entropy_from_counts(counts):
    n = sum(counts)
    if n == 0:
        return 0.0
    h = 0.0
    for c in counts:
        if c:
            p = c / n
            h -= p * math.log2(p)
    return h


def profiles_for(instances, runtimes, actions, T):
    """Return nonzero admissibility masks and per-instance masks for the supplied instances."""
    freq = Counter()
    masks = {}
    for inst in instances:
        mask = 0
        for j, a in enumerate(actions):
            rec = runtimes.get(inst, {}).get(a)
            if rec is not None:
                runtime, status = rec
                if status == "ok" and runtime <= T:
                    mask |= (1 << j)
        if mask:
            freq[mask] += 1
            masks[inst] = mask
    return freq, masks


def hmin_exact(freq, m):
    """Exact minimum assignment entropy by enumeration of action priority orders.

    Exactness: for any feasible assignment, sort actions by its assignment counts.
    Greedily assigning every state to its first admissible action in that order
    yields a count vector that majorizes the original count vector. Shannon entropy
    is Schur-concave. Therefore some priority order attains a global minimum.
    """
    n = sum(freq.values())
    if n == 0:
        return 0.0, [0] * m, tuple(range(m))
    best = None
    best_counts = None
    best_perm = None
    for perm in itertools.permutations(range(m)):
        counts = [0] * m
        for mask, c in freq.items():
            for j in perm:
                if mask & (1 << j):
                    counts[j] += c
                    break
        h = entropy_from_counts(counts)
        key = (round(h, 15), tuple(-x for x in sorted(counts, reverse=True)), perm)
        if best is None or key < best:
            best = key
            best_counts = counts
            best_perm = perm
    return float(best[0]), best_counts, best_perm


def pair_conflicts(freq):
    items = list(freq.items())
    total = 0
    for i, (m1, c1) in enumerate(items):
        for m2, c2 in items[i+1:]:
            if (m1 & m2) == 0:
                total += c1 * c2
    return int(total)


def evaluate(instances, runtimes, actions, T):
    freq, masks = profiles_for(instances, runtimes, actions, T)
    h, counts, perm = hmin_exact(freq, len(actions))
    return {
        "n_actionable": int(sum(freq.values())),
        "H_min_bits": h,
        "pair_conflicts": pair_conflicts(freq),
        "optimal_counts": counts,
        "optimal_priority": [actions[i] for i in perm],
        "profile_counts": {str(k): int(v) for k, v in sorted(freq.items())},
    }, masks


def base_cohort(instances, runtimes, T):
    out = []
    for inst in instances:
        ok = False
        for a in BASE:
            rec = runtimes.get(inst, {}).get(a)
            if rec and rec[1] == "ok" and rec[0] <= T:
                ok = True
                break
        if ok:
            out.append(inst)
    return out


def reduction(base, new):
    if base <= 0:
        return None
    return (base - new) / base


def eval_portfolio(cohort, runtimes, added, T):
    actions = BASE + tuple(added)
    e, _ = evaluate(cohort, runtimes, actions, T)
    e["actions"] = list(actions)
    e["added"] = list(added)
    return e


def choose_one_candidate(train_cohort, runtimes, T):
    rows = []
    for cand in CANDIDATES:
        e = eval_portfolio(train_cohort, runtimes, (cand,), T)
        rows.append((e["H_min_bits"], e["pair_conflicts"], cand, e))
    rows.sort(key=lambda x: (round(x[0], 12), x[1], x[2]))
    return rows[0][2], {r[2]: r[3] for r in rows}


def brute_force_hmin(masks, m):
    choices = []
    for mask in masks:
        opts = [j for j in range(m) if mask & (1 << j)]
        if not opts:
            return None
        choices.append(opts)
    best = float("inf")
    for assign in itertools.product(*choices):
        counts = [0] * m
        for j in assign:
            counts[j] += 1
        best = min(best, entropy_from_counts(counts))
    return best


def verify_priority_method(all_instances, runtimes):
    checks = []
    # Deterministic real-data checks, each with <=6 instances and 3 actions.
    for cand in CANDIDATES:
        actions = BASE + (cand,)
        cohort = base_cohort(all_instances, runtimes, PRIMARY_T)
        _, mask_map = profiles_for(cohort, runtimes, actions, PRIMARY_T)
        sample = list(mask_map)[:6]
        masks = [mask_map[x] for x in sample]
        freq = Counter(masks)
        exact_priority, _, _ = hmin_exact(freq, len(actions))
        exact_brute = brute_force_hmin(masks, len(actions))
        checks.append({
            "candidate": cand,
            "n": len(sample),
            "priority_H": exact_priority,
            "bruteforce_H": exact_brute,
            "abs_diff": abs(exact_priority - exact_brute),
            "pass": abs(exact_priority - exact_brute) < 1e-12,
        })
    return checks


def main():
    os.makedirs(OUTDIR, exist_ok=True)
    alg_raw = download(ALG_URL)
    cv_raw = download(CV_URL)
    alg_rows = parse_arff_data(alg_raw)
    cv_rows = parse_arff_data(cv_raw)

    runtimes = defaultdict(dict)
    repetitions = Counter()
    for row in alg_rows:
        inst, rep, alg, runtime, status = row
        repetitions[rep] += 1
        if rep == "1" and alg in ALL:
            runtimes[inst][alg] = (float(runtime), status)

    fold_of = {}
    for row in cv_rows:
        inst, rep, fold = row
        if rep == "1":
            fold_of[inst] = int(float(fold))

    all_instances = sorted(set(runtimes) & set(fold_of))
    folds = sorted(set(fold_of[i] for i in all_instances))

    source = {
        "algorithm_runs_git_blob_sha": ALG_GIT_BLOB,
        "cv_git_blob_sha": CV_GIT_BLOB,
        "algorithm_runs_sha256": hashlib.sha256(alg_raw).hexdigest(),
        "cv_sha256": hashlib.sha256(cv_raw).hexdigest(),
        "algorithm_runs_bytes": len(alg_raw),
        "cv_bytes": len(cv_raw),
        "instances_with_runtime_and_fold_rep1": len(all_instances),
        "folds_rep1": folds,
    }

    verification = verify_priority_method(all_instances, runtimes)
    if not all(x["pass"] for x in verification):
        raise RuntimeError("Priority-order exactness check failed")

    # Primary 7200-second blind 10-fold capability selection.
    fold_results = []
    for f in folds:
        train_all = [i for i in all_instances if fold_of[i] != f]
        hold_all = [i for i in all_instances if fold_of[i] == f]
        train = base_cohort(train_all, runtimes, PRIMARY_T)
        hold = base_cohort(hold_all, runtimes, PRIMARY_T)

        base_train = eval_portfolio(train, runtimes, (), PRIMARY_T)
        base_hold = eval_portfolio(hold, runtimes, (), PRIMARY_T)
        selected, train_candidates = choose_one_candidate(train, runtimes, PRIMARY_T)
        hold_candidates = {c: eval_portfolio(hold, runtimes, (c,), PRIMARY_T) for c in CANDIDATES}
        selected_hold = hold_candidates[selected]
        oracle = sorted(CANDIDATES, key=lambda c: (round(hold_candidates[c]["H_min_bits"],12), hold_candidates[c]["pair_conflicts"], c))[0]
        oracle_hold = hold_candidates[oracle]
        fold_results.append({
            "fold": f,
            "train_n": len(train),
            "holdout_n": len(hold),
            "selected_on_train": selected,
            "holdout_oracle": oracle,
            "base_train_H": base_train["H_min_bits"],
            "base_holdout_H": base_hold["H_min_bits"],
            "selected_holdout_H": selected_hold["H_min_bits"],
            "oracle_holdout_H": oracle_hold["H_min_bits"],
            "holdout_H_reduction_fraction": reduction(base_hold["H_min_bits"], selected_hold["H_min_bits"]),
            "base_holdout_conflicts": base_hold["pair_conflicts"],
            "selected_holdout_conflicts": selected_hold["pair_conflicts"],
            "holdout_conflict_reduction_fraction": reduction(base_hold["pair_conflicts"], selected_hold["pair_conflicts"]),
            "holdout_regret_bits": selected_hold["H_min_bits"] - oracle_hold["H_min_bits"],
            "train_candidate_H": {c: train_candidates[c]["H_min_bits"] for c in CANDIDATES},
            "holdout_candidate_H": {c: hold_candidates[c]["H_min_bits"] for c in CANDIDATES},
        })

    # Pooled out-of-fold policy: each instance is assigned the capability selected without its fold.
    # H_min for this heterogeneous policy is not a single common action-set entropy, so report
    # fold-weighted means and summed conflicts, not a misleading pooled global H.
    evaluable_h = [r for r in fold_results if r["base_holdout_H"] > 0]
    evaluable_c = [r for r in fold_results if r["base_holdout_conflicts"] > 0]
    primary_summary = {
        "n_folds": len(fold_results),
        "selection_counts": dict(Counter(r["selected_on_train"] for r in fold_results)),
        "folds_with_positive_H_reduction": sum((r["base_holdout_H"] - r["selected_holdout_H"]) > 1e-12 for r in fold_results),
        "folds_with_H_room_to_improve": len(evaluable_h),
        "positive_H_reduction_among_evaluable": sum((r["base_holdout_H"] - r["selected_holdout_H"]) > 1e-12 for r in evaluable_h),
        "folds_with_positive_conflict_reduction": sum((r["base_holdout_conflicts"] - r["selected_holdout_conflicts"]) > 0 for r in fold_results),
        "folds_with_conflict_room_to_improve": len(evaluable_c),
        "zero_regret_folds": sum(abs(r["holdout_regret_bits"]) < 1e-12 for r in fold_results),
        "mean_holdout_regret_bits": sum(r["holdout_regret_bits"] for r in fold_results) / max(1,len(fold_results)),
        "max_holdout_regret_bits": max((r["holdout_regret_bits"] for r in fold_results), default=0.0),
        "weighted_base_holdout_H": sum(r["base_holdout_H"] * r["holdout_n"] for r in fold_results) / max(1,sum(r["holdout_n"] for r in fold_results)),
        "weighted_selected_holdout_H": sum(r["selected_holdout_H"] * r["holdout_n"] for r in fold_results) / max(1,sum(r["holdout_n"] for r in fold_results)),
        "sum_base_holdout_conflicts_within_folds": sum(r["base_holdout_conflicts"] for r in fold_results),
        "sum_selected_holdout_conflicts_within_folds": sum(r["selected_holdout_conflicts"] for r in fold_results),
    }
    primary_summary["weighted_H_reduction_fraction"] = reduction(primary_summary["weighted_base_holdout_H"], primary_summary["weighted_selected_holdout_H"])
    primary_summary["within_fold_conflict_reduction_fraction"] = reduction(primary_summary["sum_base_holdout_conflicts_within_folds"], primary_summary["sum_selected_holdout_conflicts_within_folds"])

    # Full-dataset primary-contract candidate effects.
    full_primary_cohort = base_cohort(all_instances, runtimes, PRIMARY_T)
    full_base = eval_portfolio(full_primary_cohort, runtimes, (), PRIMARY_T)
    full_candidates = {}
    for c in CANDIDATES:
        e = eval_portfolio(full_primary_cohort, runtimes, (c,), PRIMARY_T)
        e["H_reduction_fraction"] = reduction(full_base["H_min_bits"], e["H_min_bits"])
        e["conflict_reduction_fraction"] = reduction(full_base["pair_conflicts"], e["pair_conflicts"])
        full_candidates[c] = e

    # Exact cardinality frontier and budget stress.
    budget_results = []
    frontier_rows = []
    for T in STRESS_T:
        cohort = base_cohort(all_instances, runtimes, T)
        base_eval = eval_portfolio(cohort, runtimes, (), T)
        per_k = []
        all_portfolios = []
        for k in range(0, len(CANDIDATES)+1):
            for added in itertools.combinations(CANDIDATES, k):
                e = eval_portfolio(cohort, runtimes, added, T)
                all_portfolios.append((k, added, e))
        for K in range(0, len(CANDIDATES)+1):
            eligible = [(k,a,e) for (k,a,e) in all_portfolios if k <= K]
            best = min(eligible, key=lambda x: (round(x[2]["H_min_bits"],12), x[2]["pair_conflicts"], x[0], x[1]))
            k, added, e = best
            row = {
                "T_seconds": T,
                "max_added_capabilities": K,
                "actual_added_capabilities": k,
                "cohort_n": len(cohort),
                "H_min_bits": e["H_min_bits"],
                "pair_conflicts": e["pair_conflicts"],
                "added_portfolio": list(added),
                "H_reduction_fraction_vs_base": reduction(base_eval["H_min_bits"], e["H_min_bits"]),
                "conflict_reduction_fraction_vs_base": reduction(base_eval["pair_conflicts"], e["pair_conflicts"]),
            }
            per_k.append(row)
            frontier_rows.append(row)
        best_one = min([(a,e) for k,a,e in all_portfolios if k == 1], key=lambda x: (round(x[1]["H_min_bits"],12), x[1]["pair_conflicts"], x[0])) if CANDIDATES else None
        budget_results.append({
            "T_seconds": T,
            "cohort_n": len(cohort),
            "base": base_eval,
            "frontier": per_k,
            "best_exactly_one_added": {"added": list(best_one[0]), **best_one[1]} if best_one else None,
        })

    audit = {
        "study_id": STUDY_ID,
        "executed_at_utc": datetime.now(timezone.utc).isoformat(),
        "preregistration_sha256": PREREG_SHA256,
        "source": source,
        "contract": {
            "base_capabilities": list(BASE),
            "candidate_capabilities": list(CANDIDATES),
            "primary_cutoff_seconds": PRIMARY_T,
            "stress_cutoffs_seconds": list(STRESS_T),
            "primary_selection": "min TRAIN H_min; tie fewest TRAIN conflicts; tie lexicographic",
            "cohort": "base-actionable within each subset at the same cutoff",
        },
        "method_verification": verification,
        "full_primary_cohort_n": len(full_primary_cohort),
        "full_primary_base": full_base,
        "full_primary_candidates": full_candidates,
        "blind_cv_folds": fold_results,
        "blind_cv_summary": primary_summary,
        "budget_frontiers": budget_results,
        "interpretation_guardrail": "All information requirements are contract-relative. H_min=0 means one common admissible algorithm suffices for the declared cohort and time budget; it does not erase the value of instance information for runtime optimization, other budgets, cost, robustness, or other contracts."
    }

    audit_path = os.path.join(OUTDIR, "INSACERMO_BNSL2016_BLIND_COST_AWARE_AUDIT_V1.json")
    with open(audit_path, "w", encoding="utf-8") as f:
        json.dump(audit, f, indent=2, ensure_ascii=False)

    folds_path = os.path.join(OUTDIR, "INSACERMO_BNSL2016_BLIND_CV_FOLDS_V1.csv")
    with open(folds_path, "w", newline="", encoding="utf-8") as f:
        fields = ["fold","train_n","holdout_n","selected_on_train","holdout_oracle","base_holdout_H","selected_holdout_H","oracle_holdout_H","holdout_H_reduction_fraction","base_holdout_conflicts","selected_holdout_conflicts","holdout_conflict_reduction_fraction","holdout_regret_bits"]
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for r in fold_results:
            w.writerow({k:r[k] for k in fields})

    frontier_path = os.path.join(OUTDIR, "INSACERMO_BNSL2016_CAPABILITY_INFORMATION_FRONTIER_V1.csv")
    with open(frontier_path, "w", newline="", encoding="utf-8") as f:
        fields = ["T_seconds","max_added_capabilities","actual_added_capabilities","cohort_n","H_min_bits","pair_conflicts","added_portfolio","H_reduction_fraction_vs_base","conflict_reduction_fraction_vs_base"]
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for r in frontier_rows:
            rr = dict(r)
            rr["added_portfolio"] = ";".join(rr["added_portfolio"])
            w.writerow({k:rr[k] for k in fields})

    # Human-readable summary for easy connector retrieval.
    summary_path = os.path.join(OUTDIR, "SUMMARY.txt")
    with open(summary_path, "w", encoding="utf-8") as f:
        f.write("INSACERMO BNSL-2016 BLIND COST-AWARE AUDIT V1\n")
        f.write(json.dumps({
            "preregistration_sha256": PREREG_SHA256,
            "source": source,
            "full_primary_cohort_n": len(full_primary_cohort),
            "full_primary_base": {"H_min_bits": full_base["H_min_bits"], "pair_conflicts": full_base["pair_conflicts"]},
            "full_primary_candidates": {c:{"H_min_bits":e["H_min_bits"],"pair_conflicts":e["pair_conflicts"],"H_reduction_fraction":e["H_reduction_fraction"]} for c,e in full_candidates.items()},
            "blind_cv_summary": primary_summary,
            "selected_by_fold": {str(r["fold"]):r["selected_on_train"] for r in fold_results},
            "oracle_by_fold": {str(r["fold"]):r["holdout_oracle"] for r in fold_results},
            "budget_frontier_compact": [
                {"T":b["T_seconds"], "n":b["cohort_n"], "base_H":b["base"]["H_min_bits"], "best1":b["best_exactly_one_added"], "frontier":[{"K":x["max_added_capabilities"],"k":x["actual_added_capabilities"],"H":x["H_min_bits"],"conf":x["pair_conflicts"],"added":x["added_portfolio"]} for x in b["frontier"]]} for b in budget_results
            ],
            "method_checks_pass": all(x["pass"] for x in verification),
        }, indent=2, ensure_ascii=False))
        f.write("\n")

    manifest = {}
    for p in (audit_path, folds_path, frontier_path, summary_path):
        with open(p, "rb") as fh:
            manifest[os.path.basename(p)] = hashlib.sha256(fh.read()).hexdigest()
    with open(os.path.join(OUTDIR, "SHA256SUMS.json"), "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2)

    print(open(summary_path, encoding="utf-8").read())
    print("SHA256SUMS", json.dumps(manifest, indent=2))


if __name__ == "__main__":
    main()
