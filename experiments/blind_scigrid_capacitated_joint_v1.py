import hashlib
import itertools
import math
from collections import Counter, defaultdict

import networkx as nx
import numpy as np
import pandas as pd
import pypsa
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

# Fixed-before-result cross-domain protocol.
# Dataset: PyPSA SciGRID-DE example.
# Semantics: static capacitated transport/dispatch envelope using observed/model
# branch ratings and mean available generator capacities. A failed repairable
# branch may be restored at unit cost; permanent branches never return.
# This is intentionally stronger than pure connectivity, but it is NOT an AC/DC
# power-flow, voltage, stability, protection, unit-commitment, N-1, or market model.

DATASET = "PyPSA SciGRID-DE"
N_TARGETS = 10
MAX_BUNDLE = 3
INF = 10**9
ROOT = "__INSACERMO_SUPPLY_ROOT__"
CUT_LEVELS = (6, 12, 18)
HASH_CONTROL = 12
PERMANENT_COUNT = 6
REPAIRABLE_AFTER_PERMANENT = 6


def load_network():
    return pypsa.examples.scigrid_de()


def mean_load_by_bus(n):
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


def mean_generation_capacity_by_bus(n):
    gens = n.generators.copy()
    p_nom = gens.get("p_nom", pd.Series(0.0, index=gens.index)).fillna(0.0).astype(float)
    static = gens.get("p_max_pu", pd.Series(1.0, index=gens.index)).fillna(1.0).astype(float)
    avail = static.copy()
    try:
        ts = n.generators_t.p_max_pu
        if ts is not None and not ts.empty:
            avail = ts.mean(axis=0).reindex(gens.index).fillna(static).astype(float)
    except Exception:
        pass
    cap = (p_nom * avail.clip(lower=0.0)).clip(lower=0.0)
    frame = pd.DataFrame({"bus": gens.bus.astype(str), "cap": cap})
    out = frame.groupby("bus")["cap"].sum()
    return out[out > 1e-9].sort_values(ascending=False)


def physical_edges(n):
    edges = []
    for kind, table in (("line", n.lines), ("trafo", n.transformers)):
        if table is None or len(table) == 0:
            continue
        for name, row in table.iterrows():
            b0 = str(row["bus0"])
            b1 = str(row["bus1"])
            s_nom = float(row.get("s_nom", 0.0) or 0.0)
            s_max_pu = float(row.get("s_max_pu", 1.0) or 1.0)
            cap = s_nom * max(0.0, s_max_pu)
            if not math.isfinite(cap) or cap <= 1e-9:
                continue
            uid = f"{kind}:{name}"
            edges.append((uid, b0, b1, cap))
    return edges


def target_buses(loads, gen_cap):
    # Highest mean-load buses with no local available generation, fixed before result.
    targets = []
    for b in loads.index:
        if loads.loc[b] <= 1e-9:
            continue
        if float(gen_cap.get(b, 0.0)) > 1e-9:
            continue
        targets.append(str(b))
        if len(targets) == N_TARGETS:
            break
    return targets


def aggregate_capacity_graph(buses, edges, gen_cap):
    G = nx.DiGraph()
    G.add_nodes_from(map(str, buses))
    G.add_node(ROOT)
    pair_cap = defaultdict(float)
    for _, b0, b1, cap in edges:
        pair_cap[(b0, b1)] += cap
        pair_cap[(b1, b0)] += cap
    for (u, v), cap in pair_cap.items():
        if G.has_edge(u, v):
            G[u][v]["capacity"] += cap
        else:
            G.add_edge(u, v, capacity=cap)
    for b, cap in gen_cap.items():
        if b in G and cap > 0:
            G.add_edge(ROOT, str(b), capacity=float(cap))
    return G


def cut_ranked_edges(buses, edges, gen_cap, targets):
    G = aggregate_capacity_graph(buses, edges, gen_cap)
    score = Counter()
    cut_values = {}
    for t in targets:
        try:
            cut_value, (S, T) = nx.minimum_cut(G, ROOT, t, capacity="capacity")
        except (nx.NetworkXError, nx.NetworkXUnbounded):
            cut_values[t] = 0.0
            continue
        cut_values[t] = float(cut_value)
        S, T = set(S), set(T)
        for uid, b0, b1, _ in edges:
            if (b0 in S and b1 in T) or (b1 in S and b0 in T):
                score[uid] += 1

    def key(item):
        uid, _, _, cap = item
        digest = hashlib.sha256(("INSACERMO-SCIGRID-CAP-20260917|" + uid).encode()).hexdigest()
        return (-score[uid], cap, digest)

    ranked = [uid for uid, _, _, _ in sorted(edges, key=key)]
    return ranked, score, cut_values


def hashed_rank(edges):
    return [uid for _, uid in sorted(
        (hashlib.sha256(("INSACERMO-SCIGRID-HASH-CAP-20260917|" + uid).encode()).hexdigest(), uid)
        for uid, _, _, _ in edges
    )]


def scenario_map(ranked, hashed):
    out = {"BASELINE": (set(), set())}
    for k in CUT_LEVELS:
        out[f"MINCUT_{k}_REPAIRABLE"] = (set(ranked[:k]), set())
    out[f"HASHED_{HASH_CONTROL}_REPAIRABLE"] = (set(hashed[:HASH_CONTROL]), set())
    out[f"MINCUT_{PERMANENT_COUNT}_PERMANENT_PLUS_{REPAIRABLE_AFTER_PERMANENT}_REPAIRABLE"] = (
        set(ranked[PERMANENT_COUNT:PERMANENT_COUNT + REPAIRABLE_AFTER_PERMANENT]),
        set(ranked[:PERMANENT_COUNT]),
    )
    return out


def solve_depth(buses, edges, gen_cap, demand_by_bus, repairable, permanent):
    bus_list = list(map(str, buses))
    bidx = {b: i for i, b in enumerate(bus_list)}
    E = len(edges)
    gen_items = [(str(b), float(c)) for b, c in gen_cap.items() if str(b) in bidx and c > 1e-9]
    G = len(gen_items)
    repair_list = sorted(repairable)
    ridx = {uid: i for i, uid in enumerate(repair_list)}
    R = len(repair_list)

    nvar = E + G + R
    c = np.zeros(nvar, dtype=float)
    if R:
        c[E + G:] = 1.0

    lb = np.full(nvar, -np.inf)
    ub = np.full(nvar, np.inf)

    # Branch flow variables.
    for i, (uid, _, _, cap) in enumerate(edges):
        if uid in permanent:
            lb[i] = ub[i] = 0.0
        else:
            lb[i] = -cap
            ub[i] = cap

    # Generation variables.
    for j, (_, cap) in enumerate(gen_items):
        lb[E + j] = 0.0
        ub[E + j] = cap

    # Repair binaries.
    for j in range(R):
        lb[E + G + j] = 0.0
        ub[E + G + j] = 1.0

    constraints = []

    # Nodal balance: generation + inflow - outflow = demand.
    Aeq = lil_matrix((len(bus_list), nvar), dtype=float)
    beq = np.zeros(len(bus_list), dtype=float)
    for i, (_, b0, b1, _) in enumerate(edges):
        if b0 in bidx and b1 in bidx:
            Aeq[bidx[b0], i] -= 1.0
            Aeq[bidx[b1], i] += 1.0
    for j, (b, _) in enumerate(gen_items):
        Aeq[bidx[b], E + j] += 1.0
    for b, d in demand_by_bus.items():
        if b not in bidx:
            return INF
        beq[bidx[b]] += float(d)
    constraints.append(LinearConstraint(Aeq.tocsr(), beq, beq))

    # Repairable branch may carry flow only when its binary is on.
    if R:
        Aub = lil_matrix((2 * R, nvar), dtype=float)
        upper = np.zeros(2 * R, dtype=float)
        row = 0
        edge_pos = {uid: i for i, (uid, _, _, _) in enumerate(edges)}
        edge_cap = {uid: cap for uid, _, _, cap in edges}
        for uid in repair_list:
            i = edge_pos[uid]
            y = E + G + ridx[uid]
            cap = edge_cap[uid]
            Aub[row, i] = 1.0
            Aub[row, y] = -cap
            row += 1
            Aub[row, i] = -1.0
            Aub[row, y] = -cap
            row += 1
        constraints.append(LinearConstraint(Aub.tocsr(), -np.inf, upper))

    integrality = np.zeros(nvar, dtype=int)
    if R:
        integrality[E + G:] = 1

    res = milp(
        c=c,
        integrality=integrality,
        bounds=Bounds(lb, ub),
        constraints=constraints,
        options={"time_limit": 20.0, "mip_rel_gap": 0.0},
    )
    if not res.success or res.fun is None:
        # status 2 is infeasible; any other non-success is a protocol failure.
        if getattr(res, "status", None) == 2:
            return INF
        raise RuntimeError(f"MILP failure status={getattr(res, 'status', None)} message={getattr(res, 'message', None)}")
    return int(round(float(res.fun)))


def fmt(d):
    return "INF" if d >= INF else str(int(d))


def main():
    n = load_network()
    loads = mean_load_by_bus(n)
    gen_cap = mean_generation_capacity_by_bus(n)
    buses = list(map(str, n.buses.index))
    edges = physical_edges(n)
    targets = target_buses(loads, gen_cap)

    assert len(targets) == N_TARGETS, (len(targets), targets)
    assert len(edges) > 0
    assert gen_cap.sum() > 0

    ranked, cut_score, cut_values = cut_ranked_edges(buses, edges, gen_cap, targets)
    hashed = hashed_rank(edges)
    scenarios = scenario_map(ranked, hashed)

    print("INSACERMO_BLIND_SCIGRID_CAPACITATED_JOINT_V1")
    print("DATASET", DATASET)
    print("BUSES", len(buses), "CAPACITATED_EDGES", len(edges), "GEN_BUSES", len(gen_cap), "MEAN_AVAILABLE_GEN_MW", f"{gen_cap.sum():.6f}")
    print("SEMANTICS static capacitated transport/dispatch envelope; one failed repairable branch restored per unit depth; permanent branches never return")
    print("CAVEAT no Kirchhoff-angle/DC-OPF, AC power-flow, voltage, reactive power, stability, protection, unit commitment, contingency security, or market feasibility claim")
    print("TARGET_RULE top_mean_load_buses_without_local_generation")
    print("TARGETS", " ".join(f"{b}:{loads.loc[b]:.6f}" for b in targets))
    print("TARGET_MINCUTS", " ".join(f"{b}:{cut_values.get(b, float('nan')):.6f}" for b in targets))
    print("RANKED_FAILED_EDGES", " ".join(f"{uid}:{cut_score[uid]}" for uid in ranked[:24]))
    print("MAX_BUNDLE", MAX_BUNDLE)

    all_results = {}
    all_singletons = {}

    for sname, (repairable, permanent) in scenarios.items():
        print("SCENARIO", sname, "REPAIRABLE", len(repairable), "PERMANENT", len(permanent))
        singleton = {}
        for q in targets:
            singleton[q] = solve_depth(buses, edges, gen_cap, {q: float(loads.loc[q])}, repairable, permanent)
        all_singletons[sname] = singleton
        print("SINGLETONS", " ".join(f"{q}:{fmt(singleton[q])}" for q in targets))

        results = {}
        for size in range(1, MAX_BUNDLE + 1):
            vals = []
            for F in itertools.combinations(targets, size):
                demand = {q: float(loads.loc[q]) for q in F}
                d = solve_depth(buses, edges, gen_cap, demand, repairable, permanent)
                results[F] = d
                vals.append((F, d))

            finite = [(F, d) for F, d in vals if d < INF]
            infinite = [(F, d) for F, d in vals if d >= INF]
            hist = Counter(int(d) for _, d in finite)
            print("BUNDLE_SIZE", size, "TOTAL", len(vals), "FINITE", len(finite), "INFINITE", len(infinite))
            hist_text = " ".join(f"D{k}:{hist[k]}" for k in sorted(hist))
            if infinite:
                hist_text += (" " if hist_text else "") + f"INF:{len(infinite)}"
            print("DEPTH_HIST", hist_text)

            positive = []
            finite_singletons_joint_inf = []
            for F, d in vals:
                indiv = [singleton[q] for q in F]
                if d >= INF:
                    if all(x < INF for x in indiv):
                        finite_singletons_joint_inf.append((F, tuple(indiv)))
                    continue
                if all(x < INF for x in indiv):
                    gap = int(d - max(indiv))
                    assert gap >= 0, (sname, F, d, indiv)
                    if gap > 0:
                        positive.append((gap, F, d, tuple(indiv)))

            print("POSITIVE_INTERACTION_GAP", len(positive))
            print("INFINITE_WITH_ALL_SINGLETONS_FINITE", len(finite_singletons_joint_inf))
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

            print("FIRST_JOINT_WITNESSES")
            shown = 0
            for gap, F, d, indiv in sorted(positive, key=lambda x: (-x[0], x[1])):
                print("WITNESS BUNDLE", ",".join(F), "JOINT", fmt(d), "SINGLETONS", ",".join(map(fmt, indiv)), "GAP", gap)
                shown += 1
                if shown == 5:
                    break
            if shown < 5:
                for F, indiv in finite_singletons_joint_inf[:5-shown]:
                    print("WITNESS BUNDLE", ",".join(F), "JOINT INF SINGLETONS", ",".join(map(fmt, indiv)), "GAP INF")

        all_results[sname] = results

    chain = ["BASELINE"] + [f"MINCUT_{k}_REPAIRABLE" for k in CUT_LEVELS]
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
            elif da >= INF and db < INF:
                raise AssertionError(("destruction made impossible future finite", a, b, F, da, db))
            else:
                raise AssertionError(("destruction made recovery easier", a, b, F, da, db))
        print("TRANSFORM", a, "TO", b, "DELAYED", delayed, "NEW_IRREVERSIBLE", irreversible, "UNCHANGED", unchanged, "TOTAL_ADDED_FINITE_DEPTH", finite_added)


if __name__ == "__main__":
    main()
