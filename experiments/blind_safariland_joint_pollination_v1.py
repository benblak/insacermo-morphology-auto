import hashlib
import itertools
import os
from collections import Counter

import numpy as np
import pyreadr

# Fixed-before-result ecological cross-domain protocol.
# Dataset: Safariland plant-pollinator visitation matrix from the R bipartite
# package (9 plants x 27 pollinators; empirical field observations).
# Contract for plant p: after pollinator loss/repair, retained observed
# visitation service to p must be >= 50% of that plant's baseline total.
# Destruction candidates are pollinators whose single removal leaves ALL plant
# contracts satisfied. Candidates are ranked only by baseline shared support:
# number of plants visited, then summed normalized visitation contribution,
# then deterministic hash. Nested repairable losses use 4/8/12 candidates,
# truncated only if fewer eligible candidates exist. Recovery depth is the exact
# minimum number of deleted pollinators that must be restored for every plant in
# a requested bundle to satisfy its service contract simultaneously.
# This is an empirical interaction-network service proxy, not a population-
# dynamics, demographic, causal, conservation-policy, or ecosystem-viability claim.

DATA_PATH = os.environ.get("INSACERMO_SAFARILAND_RDA", "/tmp/Safariland.rda")
SERVICE_FRACTION = 0.50
MAX_BUNDLE = 3
DELETE_LEVELS = (4, 8, 12)
HASH_CONTROL = 8
PERMANENT_COUNT = 4
REPAIRABLE_AFTER_PERMANENT = 4
HORIZONS = (0, 1, 2, 3)
INF = 10**9


def load_matrix():
    objs = pyreadr.read_r(DATA_PATH)
    if not objs:
        raise RuntimeError("Safariland RDA contained no readable object")
    obj = objs.get("Safariland")
    if obj is None:
        obj = next(iter(objs.values()))
    arr = np.asarray(obj, dtype=float)
    if arr.ndim != 2:
        raise RuntimeError(f"Expected 2D matrix, got shape {arr.shape}")
    if arr.shape != (9, 27):
        raise RuntimeError(f"Unexpected Safariland shape {arr.shape}")
    if np.any(arr < 0):
        raise RuntimeError("Negative visitation counts")
    plant_names = [str(x) for x in getattr(obj, "index", range(arr.shape[0]))]
    poll_names = [str(x) for x in getattr(obj, "columns", range(arr.shape[1]))]
    if len(set(plant_names)) != arr.shape[0]:
        plant_names = [f"plant_{i+1}" for i in range(arr.shape[0])]
    if len(set(poll_names)) != arr.shape[1]:
        poll_names = [f"pollinator_{j+1}" for j in range(arr.shape[1])]
    return arr, plant_names, poll_names


def rank_candidates(W, poll_names):
    totals = W.sum(axis=1)
    if np.any(totals <= 0):
        raise RuntimeError("Plant with zero baseline visitation")
    threshold = SERVICE_FRACTION * totals
    eligible = []
    for j, name in enumerate(poll_names):
        retained = totals - W[:, j]
        if np.all(retained + 1e-12 >= threshold):
            shared = int(np.count_nonzero(W[:, j] > 0))
            norm = float(np.sum(W[:, j] / totals))
            digest = hashlib.sha256(("INSACERMO-SAFARILAND-20260917|" + name).encode()).hexdigest()
            eligible.append((name, j, shared, norm, digest))
    eligible.sort(key=lambda x: (-x[2], -x[3], x[4]))
    return eligible, totals, threshold


def scenario_map(eligible):
    names = [x[0] for x in eligible]
    n = len(names)
    if n < 4:
        raise RuntimeError(f"Only {n} individually-silent pollinator candidates; protocol requires >=4")
    levels = sorted(set(min(k, n) for k in DELETE_LEVELS))
    out = {"BASELINE": (set(), set())}
    for k in levels:
        out[f"SHARED_{k}_REPAIRABLE"] = (set(names[:k]), set())
    hashed = sorted(names, key=lambda s: hashlib.sha256(("INSACERMO-SAFARILAND-HASH-20260917|" + s).encode()).hexdigest())
    hk = min(HASH_CONTROL, n)
    out[f"HASHED_{hk}_REPAIRABLE"] = (set(hashed[:hk]), set())
    p = min(PERMANENT_COUNT, max(1, n // 2))
    r = min(REPAIRABLE_AFTER_PERMANENT, n - p)
    out[f"SHARED_{p}_PERMANENT_PLUS_{r}_REPAIRABLE"] = (set(names[p:p+r]), set(names[:p]))
    return out, levels


def repair_depth(W, plant_idx, poll_names, threshold, bundle, repairable, permanent):
    name_to_col = {name: j for j, name in enumerate(poll_names)}
    gone = set(repairable) | set(permanent)
    base = W.copy()
    for name in gone:
        base[:, name_to_col[name]] = 0.0
    service0 = base.sum(axis=1)
    bidx = [plant_idx[p] for p in bundle]
    if all(service0[i] + 1e-12 >= threshold[i] for i in bidx):
        return 0
    reps = sorted(repairable)
    contrib = {name: W[:, name_to_col[name]] for name in reps}
    for k in range(1, len(reps) + 1):
        for subset in itertools.combinations(reps, k):
            service = service0.copy()
            for name in subset:
                service += contrib[name]
            if all(service[i] + 1e-12 >= threshold[i] for i in bidx):
                return k
    return INF


def fmt(d):
    return "INF" if d >= INF else str(int(d))


def main():
    W, plants, pollinators = load_matrix()
    eligible, totals, threshold = rank_candidates(W, pollinators)
    scenarios, levels = scenario_map(eligible)
    pidx = {p: i for i, p in enumerate(plants)}

    print("INSACERMO_BLIND_SAFARILAND_JOINT_POLLINATION_V1")
    print("DATASET Safariland")
    print("PLANTS", len(plants), "POLLINATORS", len(pollinators), "TOTAL_VISITS", int(W.sum()))
    print("CONTRACT retained visitation service >= 50% of each plant baseline")
    print("DESTRUCTION_RULE individually-silent pollinators ranked by shared baseline support")
    print("ELIGIBLE", len(eligible))
    print("ELIGIBLE_RANK", " ".join(f"{name}:{shared}:{norm:.6g}" for name, _, shared, norm, _ in eligible[:20]))
    print("DELETE_LEVELS_USED", " ".join(map(str, levels)))
    print("MAX_BUNDLE", MAX_BUNDLE)
    print("CAVEAT empirical visitation-service proxy only; no population-dynamics, demographic, causal, conservation-policy, or ecosystem-viability claim")

    all_results = {}
    singletons_by_scenario = {}

    for sname, (repairable, permanent) in scenarios.items():
        print("SCENARIO", sname, "REPAIRABLE", len(repairable), "PERMANENT", len(permanent))
        singleton = {}
        for p in plants:
            singleton[p] = repair_depth(W, pidx, pollinators, threshold, (p,), repairable, permanent)
        singletons_by_scenario[sname] = singleton
        print("SINGLETONS", " ".join(f"{p}:{fmt(singleton[p])}" for p in plants))

        results = {}
        for size in range(1, MAX_BUNDLE + 1):
            vals = []
            for F in itertools.combinations(plants, size):
                d = repair_depth(W, pidx, pollinators, threshold, F, repairable, permanent)
                results[F] = d
                vals.append((F, d))
            finite = [(F, d) for F, d in vals if d < INF]
            infinite = [(F, d) for F, d in vals if d >= INF]
            hist = Counter(int(d) for _, d in finite)
            print("BUNDLE_SIZE", size, "TOTAL", len(vals), "FINITE", len(finite), "INFINITE", len(infinite))
            htxt = " ".join(f"D{k}:{hist[k]}" for k in sorted(hist))
            if infinite:
                htxt += (" " if htxt else "") + f"INF:{len(infinite)}"
            print("DEPTH_HIST", htxt)

            positive = []
            hidden_inf = []
            for F, d in vals:
                indiv = tuple(singleton[p] for p in F)
                if d >= INF:
                    if all(x < INF for x in indiv):
                        hidden_inf.append((F, indiv))
                    continue
                if all(x < INF for x in indiv):
                    gap = int(d - max(indiv))
                    if gap < 0:
                        raise AssertionError((sname, F, d, indiv))
                    if gap > 0:
                        positive.append((gap, F, d, indiv))
            print("POSITIVE_INTERACTION_GAP", len(positive))
            print("INFINITE_WITH_ALL_SINGLETONS_FINITE", len(hidden_inf))
            if positive:
                positive.sort(key=lambda x: (-x[0], x[1]))
                gap, F, d, indiv = positive[0]
                print("MAX_INTERACTION_GAP", gap, "BUNDLE", ",".join(F), "JOINT", fmt(d), "SINGLETONS", ",".join(map(fmt, indiv)))
            else:
                print("MAX_INTERACTION_GAP NA BUNDLE NA")
            if finite:
                F, d = max(finite, key=lambda x: (x[1], x[0]))
                print("MAX_FINITE_DEPTH", d, "BUNDLE", ",".join(F))
            else:
                print("MAX_FINITE_DEPTH NA BUNDLE NA")

        all_results[sname] = results

        print("MINIMAL_RANK3_OBSTRUCTIONS")
        for H in HORIZONS:
            witnesses = []
            for F in itertools.combinations(plants, 3):
                dF = results[F]
                if dF <= H:
                    continue
                proper = []
                for r in (1, 2):
                    for G in itertools.combinations(F, r):
                        proper.append(results[tuple(G)])
                if all(d <= H for d in proper):
                    witnesses.append((F, dF))
            print("H", H, "COUNT", len(witnesses))
            for F, dF in witnesses[:5]:
                print("RANK3_WITNESS", "H", H, "BUNDLE", ",".join(F), "DEPTH", fmt(dF))

    chain = ["BASELINE"] + [f"SHARED_{k}_REPAIRABLE" for k in levels]
    print("NESTED_DAMAGE_CHAIN")
    for a, b in zip(chain, chain[1:]):
        ra, rb = all_results[a], all_results[b]
        delayed = irreversible = unchanged = finite_added = 0
        for F in ra:
            da, db = ra[F], rb[F]
            if da >= INF and db >= INF:
                unchanged += 1
            elif da < INF and db >= INF:
                irreversible += 1
            elif da < INF and db < INF and db > da:
                delayed += 1
                finite_added += int(db - da)
            elif db == da:
                unchanged += 1
            else:
                raise AssertionError(("destruction made recovery easier", a, b, F, da, db))
        print("TRANSFORM", a, "TO", b, "DELAYED", delayed, "NEW_IRREVERSIBLE", irreversible, "UNCHANGED", unchanged, "TOTAL_ADDED_FINITE_DEPTH", finite_added)


if __name__ == "__main__":
    main()
