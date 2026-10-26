import hashlib
import heapq
import itertools
import math
from collections import Counter, defaultdict

import numpy as np
import pandas as pd
import pypsa

# Fixed-before-result protocol.
# Dataset: PyPSA SciGRID-DE example (grid from SciGRID / OpenStreetMap;
# load/generation layers documented by PyPSA). This is a historical/open
# model-derived network, not a real-time operator state estimator.
DATASET = "PyPSA SciGRID-DE"
N_TARGETS = 12
MAX_BUNDLE = 3
THRESHOLDS = (0, 1, 2, 3)
ROOT = "__INSACERMO_SOURCE_ROOT__"
INF = 10**9


def load_network():
    n = pypsa.examples.scigrid_de()
    return n


def aggregate_loads(n):
    # Prefer mean time-series load when present; otherwise static p_set.
    by_load = pd.Series(0.0, index=n.loads.index, dtype=float)
    try:
        ts = n.loads_t.p_set
        if ts is not None and not ts.empty:
            by_load = ts.mean(axis=0).reindex(n.loads.index).fillna(0.0).astype(float)
    except Exception:
        pass
    static = n.loads.get("p_set", pd.Series(0.0, index=n.loads.index)).fillna(0.0).astype(float)
    by_load = by_load.where(by_load.abs() > 1e-12, static)
    frame = pd.DataFrame({"bus": n.loads.bus.astype(str), "p": by_load})
    return frame.groupby("bus")["p"].sum().sort_values(ascending=False)


def source_buses(n):
    gens = n.generators.copy()
    if "p_nom" in gens:
        gens = gens[gens.p_nom.fillna(0.0).astype(float) > 0]
    if "active" in gens:
        gens = gens[gens.active.fillna(True).astype(bool)]
    return sorted(set(gens.bus.astype(str)))


def physical_edges(n):
    edges = []
    for kind, table in (("line", n.lines), ("trafo", n.transformers)):
        if table is None or len(table) == 0:
            continue
        for name, row in table.iterrows():
            b0 = str(row["bus0"])
            b1 = str(row["bus1"])
            uid = f"{kind}:{name}"
            edges.append((uid, b0, b1))
    return edges


def edge_rankings(n, edges):
    coords = n.buses[["x", "y"]].astype(float)
    x0 = float(coords.x.median())
    y0 = float(coords.y.median())
    sx = float(coords.x.std()) or 1.0
    sy = float(coords.y.std()) or 1.0

    central = []
    hashed = []
    for uid, b0, b1 in edges:
        if b0 not in coords.index or b1 not in coords.index:
            central_score = float("inf")
        else:
            mx = 0.5 * (float(coords.loc[b0, "x"]) + float(coords.loc[b1, "x"]))
            my = 0.5 * (float(coords.loc[b0, "y"]) + float(coords.loc[b1, "y"]))
            central_score = ((mx - x0) / sx) ** 2 + ((my - y0) / sy) ** 2
        central.append((central_score, uid))
        digest = hashlib.sha256(("INSACERMO-SCIGRID-20260917|" + uid).encode()).hexdigest()
        hashed.append((digest, uid))
    central_ids = [uid for _, uid in sorted(central)]
    hashed_ids = [uid for _, uid in sorted(hashed)]
    return central_ids, hashed_ids


def scenarios(n, edges):
    central, hashed = edge_rankings(n, edges)
    # Nested geographic stress footprints plus a deterministic hash control.
    # Permanent scenario separates delayed recovery from irreversibility.
    return {
        "BASELINE": (set(), set()),
        "CENTRAL_40_REPAIRABLE": (set(central[:40]), set()),
        "CENTRAL_80_REPAIRABLE": (set(central[:80]), set()),
        "CENTRAL_120_REPAIRABLE": (set(central[:120]), set()),
        "HASHED_80_REPAIRABLE": (set(hashed[:80]), set()),
        "CENTRAL_60_PERMANENT_PLUS_60_REPAIRABLE": (set(central[60:120]), set(central[:60])),
    }


def build_weighted_graph(bus_names, sources, edges, repairable, permanent):
    nodes = list(bus_names) + [ROOT]
    idx = {b: i for i, b in enumerate(nodes)}
    adj = [[] for _ in nodes]
    for uid, b0, b1 in edges:
        if uid in permanent:
            continue
        w = 1 if uid in repairable else 0
        if b0 not in idx or b1 not in idx:
            continue
        u, v = idx[b0], idx[b1]
        adj[u].append((v, w))
        adj[v].append((u, w))
    r = idx[ROOT]
    for b in sources:
        if b in idx:
            u = idx[b]
            adj[r].append((u, 0))
            adj[u].append((r, 0))
    return nodes, idx, adj


def dijkstra_from(adj, src):
    n = len(adj)
    d = [INF] * n
    d[src] = 0
    pq = [(0, src)]
    while pq:
        du, u = heapq.heappop(pq)
        if du != d[u]:
            continue
        for v, w in adj[u]:
            nd = du + w
            if nd < d[v]:
                d[v] = nd
                heapq.heappush(pq, (nd, v))
    return d


def closure(adj, initial):
    d = list(initial)
    pq = [(dv, i) for i, dv in enumerate(d) if dv < INF]
    heapq.heapify(pq)
    while pq:
        du, u = heapq.heappop(pq)
        if du != d[u]:
            continue
        for v, w in adj[u]:
            nd = du + w
            if nd < d[v]:
                d[v] = nd
                heapq.heappush(pq, (nd, v))
    return d


def steiner_depth(adj, terminal_nodes, singleton_dist_cache):
    # Exact Dreyfus-Wagner dynamic programming for small terminal sets.
    # terminal_nodes includes ROOT and 1..3 target buses.
    k = len(terminal_nodes)
    full = (1 << k) - 1
    dp = {}
    for i, t in enumerate(terminal_nodes):
        dp[1 << i] = singleton_dist_cache[t]

    for mask in range(1, full + 1):
        if mask in dp:
            continue
        best = [INF] * len(adj)
        sub = (mask - 1) & mask
        while sub:
            other = mask ^ sub
            if other and sub < other and sub in dp and other in dp:
                a = dp[sub]
                b = dp[other]
                for v in range(len(best)):
                    val = a[v] + b[v]
                    if val < best[v]:
                        best[v] = val
            sub = (sub - 1) & mask
        dp[mask] = closure(adj, best)
    root = terminal_nodes[0]
    return dp[full][root]


def fmt_depth(d):
    return "INF" if d >= INF else str(int(d))


def main():
    n = load_network()
    loads = aggregate_loads(n)
    sources = source_buses(n)
    edges = physical_edges(n)
    buses = list(map(str, n.buses.index))

    targets = [b for b in loads.index if loads.loc[b] > 0][:N_TARGETS]
    assert len(targets) == N_TARGETS, (len(targets), targets)
    assert len(sources) > 0
    assert len(edges) > 0

    print("INSACERMO_BLIND_SCIGRID_JOINT_RECOVERY_V1")
    print("DATASET", DATASET)
    print("BUSES", len(buses), "PHYSICAL_EDGES", len(edges), "SOURCE_BUSES", len(sources), "LOADS", len(n.loads))
    print("TARGET_RULE top_mean_load_buses")
    print("TARGETS", " ".join(f"{b}:{loads.loc[b]:.6g}" for b in targets))
    print("MAX_BUNDLE", MAX_BUNDLE)
    print("THRESHOLDS", ",".join(map(str, THRESHOLDS)))
    print("SEMANTICS one repairable branch restored per step; repairs accumulate; permanent branches never return")
    print("CAVEAT topological restoration only; no AC/DC power-flow, thermal-limit, voltage, stability, protection, or dispatch feasibility claim")

    scen = scenarios(n, edges)
    all_results = {}

    for sname, (repairable, permanent) in scen.items():
        nodes, idx, adj = build_weighted_graph(buses, sources, edges, repairable, permanent)
        relevant = [idx[ROOT]] + [idx[b] for b in targets]
        dist_cache = {t: dijkstra_from(adj, t) for t in relevant}

        singleton_depth = {}
        root_idx = idx[ROOT]
        for b in targets:
            d = dist_cache[idx[b]][root_idx]
            singleton_depth[b] = d

        results = {}
        print("SCENARIO", sname, "REPAIRABLE", len(repairable), "PERMANENT", len(permanent))
        print("SINGLETONS", " ".join(f"{b}:{fmt_depth(singleton_depth[b])}" for b in targets))

        for size in range(1, MAX_BUNDLE + 1):
            bundles = list(itertools.combinations(targets, size))
            vals = []
            for bundle in bundles:
                terms = [root_idx] + [idx[b] for b in bundle]
                d = steiner_depth(adj, terms, dist_cache)
                results[bundle] = d
                vals.append((bundle, d))

            finite = [(b, d) for b, d in vals if d < INF]
            infinite = [(b, d) for b, d in vals if d >= INF]
            hist = Counter(int(d) for _, d in finite)
            if infinite:
                hist["INF"] = len(infinite)

            print("BUNDLE_SIZE", size)
            print("TOTAL", len(vals), "FINITE", len(finite), "INFINITE", len(infinite))
            print("DEPTH_HIST", " ".join(f"D{k}:{hist[k]}" if k != "INF" else f"INF:{hist[k]}" for k in sorted([x for x in hist if x != "INF"])) + ((" INF:" + str(hist["INF"])) if "INF" in hist else ""))

            for H in THRESHOLDS:
                safe = sum(1 for _, d in vals if d <= H)
                indiv_safe_joint_unsafe = 0
                for b, d in vals:
                    if all(singleton_depth[q] <= H for q in b) and d > H:
                        indiv_safe_joint_unsafe += 1
                print("H", H, "SAFE", safe, "INDIVIDUAL_SAFE_JOINT_UNSAFE", indiv_safe_joint_unsafe)

            positive_gap = []
            infinite_all_singletons_finite = []
            for b, d in vals:
                indiv = [singleton_depth[q] for q in b]
                if d >= INF:
                    if all(x < INF for x in indiv):
                        infinite_all_singletons_finite.append(b)
                    continue
                if all(x < INF for x in indiv):
                    gap = int(d - max(indiv))
                    if gap > 0:
                        positive_gap.append((gap, b, d, tuple(indiv)))
                    assert d >= max(indiv), (sname, b, d, indiv)

            print("POSITIVE_INTERACTION_GAP", len(positive_gap))
            print("INFINITE_WITH_ALL_SINGLETONS_FINITE", len(infinite_all_singletons_finite))
            if positive_gap:
                positive_gap.sort(key=lambda x: (-x[0], x[1]))
                gap, b, d, indiv = positive_gap[0]
                print("MAX_INTERACTION_GAP", gap, "BUNDLE", ",".join(b), "JOINT", fmt_depth(d), "SINGLETONS", ",".join(map(fmt_depth, indiv)))
            else:
                print("MAX_INTERACTION_GAP", "NA", "BUNDLE", "NA")
            if finite:
                b, d = max(finite, key=lambda x: (x[1], x[0]))
                print("MAX_FINITE_DEPTH", int(d), "BUNDLE", ",".join(b))
            else:
                print("MAX_FINITE_DEPTH", "NA", "BUNDLE", "NA")

            witnesses = []
            for H in (1, 2, 3):
                for b, d in vals:
                    if all(singleton_depth[q] <= H for q in b) and d > H:
                        witnesses.append((H, b, d, tuple(singleton_depth[q] for q in b)))
                        if len(witnesses) >= 5:
                            break
                if len(witnesses) >= 5:
                    break
            print("FIRST_JOINT_UNSAFE_WITNESSES")
            for H, b, d, indiv in witnesses:
                print("WITNESS_H", H, "BUNDLE", ",".join(b), "JOINT", fmt_depth(d), "SINGLETONS", ",".join(map(fmt_depth, indiv)))

        all_results[sname] = results

    # Nested destruction comparison: count exact bundle-depth changes.
    chain = ["BASELINE", "CENTRAL_40_REPAIRABLE", "CENTRAL_80_REPAIRABLE", "CENTRAL_120_REPAIRABLE"]
    print("NESTED_DAMAGE_CHAIN")
    for a, b in zip(chain, chain[1:]):
        ra, rb = all_results[a], all_results[b]
        delayed = irreversible = unchanged = 0
        finite_added = 0
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
                # Nested destruction should not make recovery easier.
                raise AssertionError((a, b, F, da, db))
        print("TRANSFORM", a, "TO", b, "DELAYED", delayed, "NEW_IRREVERSIBLE", irreversible, "UNCHANGED", unchanged, "TOTAL_ADDED_FINITE_DEPTH", finite_added)


if __name__ == "__main__":
    main()
