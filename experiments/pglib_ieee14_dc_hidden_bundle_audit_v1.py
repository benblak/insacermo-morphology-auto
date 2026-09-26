# INSACERMO — PGLib IEEE-14 DC power-flow hidden bundle audit V1
#
# Purpose
# -------
# Stress-test INSACERMO on a third system class: global physical flow constraints.
# This is NOT reachability and NOT finite-resource Petri semantics.
#
# Dataset
# -------
# IEEE PES Power Grid Library (PGLib-OPF), heavily loaded active-power-increase
# variant of IEEE-14:
#   api/pglib_opf_case14_ieee__api.m
#
# Model
# -----
# Linear DC power-flow feasibility with:
#   - nodal active-power balance,
#   - generator Pmin/Pmax,
#   - branch reactance / transformer tap,
#   - thermal rateA limits,
#   - branch angle-difference limits,
#   - one reference angle.
#
# We use the 8 largest positive-Pd load buses as future-capability goals.
# A bundle F means: fully serve exactly the loads in F; unselected candidate
# loads and all other loads are switched off for this capability test.
#
# Destruction = outage of exactly one in-service branch.
# Loss = bundle feasible before outage and infeasible after.
# Minimal loss = every proper subbundle remains feasible after outage.
#
# IMPORTANT LIMITATION
# --------------------
# This is a DC linear approximation, not full AC-OPF. Therefore any witness is
# an exploratory structural-physics result, not a claim of AC grid security.

from __future__ import annotations

import hashlib
import itertools
import math
import re
import urllib.request
from functools import lru_cache

try:
    import numpy as np
    from scipy.optimize import linprog
except Exception as e:
    raise RuntimeError("This experiment requires numpy and scipy") from e

URL = "https://raw.githubusercontent.com/power-grid-lib/pglib-opf/master/api/pglib_opf_case14_ieee__api.m"
TOP_LOAD_GOALS = 8


def download(url: str) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": "INSACERMO/1.0"})
    with urllib.request.urlopen(req, timeout=120) as r:
        return r.read()


def parse_matrix(text: str, name: str):
    m = re.search(rf"mpc\.{re.escape(name)}\s*=\s*\[(.*?)\];", text, re.S)
    if not m:
        raise RuntimeError(f"missing matrix {name}")
    rows = []
    for raw in m.group(1).splitlines():
        raw = raw.split("%", 1)[0].strip()
        if not raw:
            continue
        raw = raw.rstrip(";").strip()
        if not raw:
            continue
        rows.append([float(x) for x in raw.split()])
    return rows


def parse_scalar(text: str, name: str):
    m = re.search(rf"mpc\.{re.escape(name)}\s*=\s*([0-9eE+\-.]+)\s*;", text)
    if not m:
        raise RuntimeError(f"missing scalar {name}")
    return float(m.group(1))


class Grid:
    def __init__(self, baseMVA, bus, gen, branch):
        self.base = baseMVA
        self.bus = bus
        self.gen = gen
        self.branch = branch
        self.bus_ids = [int(r[0]) for r in bus]
        self.pos = {b:i for i,b in enumerate(self.bus_ids)}
        self.n = len(bus)

        # Only active generators with positive active capacity.
        self.active_gens = []
        for gi, g in enumerate(gen):
            bus_id = int(g[0])
            status = int(g[7])
            pmax, pmin = g[8], g[9]
            if status == 1 and pmax > pmin + 1e-12:
                self.active_gens.append((gi, bus_id, pmin, pmax))

        self.load = {int(r[0]): max(0.0, r[2]) for r in bus if r[2] > 1e-12}
        self.ref_bus = next(int(r[0]) for r in bus if int(r[1]) == 3)


def dc_feasible(grid: Grid, served_buses: frozenset[int], outage_idx: int | None):
    """
    Feasibility LP.
    Variables: theta[0:n], Pg[0:ng].
    """
    n = grid.n
    gens = grid.active_gens
    ng = len(gens)
    nv = n + ng

    c = np.zeros(nv)

    # Variable bounds. Angles are globally loose; branch constraints carry local limits.
    bounds = [(-10.0, 10.0)] * n
    bounds[grid.pos[grid.ref_bus]] = (0.0, 0.0)
    for _, _, pmin, pmax in gens:
        bounds.append((pmin, pmax))

    Aeq = np.zeros((n, nv))
    beq = np.zeros(n)

    # Generation coefficients.
    for gj, (_, bus_id, _, _) in enumerate(gens):
        Aeq[grid.pos[bus_id], n + gj] += 1.0

    # Demand: serve exactly chosen goal loads, switch all other loads off.
    for bus_id in served_buses:
        beq[grid.pos[bus_id]] += grid.load[bus_id]

    Aub = []
    bub = []

    # Branch DC flows and nodal balance.
    for li, br in enumerate(grid.branch):
        if li == outage_idx:
            continue
        fbus, tbus = int(br[0]), int(br[1])
        x = br[3]
        rateA = br[5]
        tap = br[8] if abs(br[8]) > 1e-12 else 1.0
        shift_deg = br[9]
        status = int(br[10])
        angmin, angmax = br[11], br[12]
        if status != 1:
            continue
        if abs(x) < 1e-12:
            continue

        i, j = grid.pos[fbus], grid.pos[tbus]
        bmw = grid.base / (x * tap)
        shift = math.radians(shift_deg)

        # f_ij = bmw * (theta_i - theta_j - shift)
        # Nodal balance: Pg - Pd = sum outgoing flows.
        Aeq[i, i] -= bmw
        Aeq[i, j] += bmw
        beq[i] -= bmw * shift

        Aeq[j, i] += bmw
        Aeq[j, j] -= bmw
        beq[j] += bmw * shift

        if rateA > 0:
            row = np.zeros(nv)
            row[i] = bmw
            row[j] = -bmw
            # bmw*(theta_i-theta_j-shift) <= rateA
            Aub.append(row)
            bub.append(rateA + bmw * shift)
            Aub.append(-row)
            bub.append(rateA - bmw * shift)

        # MATPOWER angle bounds are degrees; 0/0 can mean unconstrained in some files.
        if angmax > angmin and angmax < 360:
            row = np.zeros(nv)
            row[i] = 1.0
            row[j] = -1.0
            Aub.append(row)
            bub.append(math.radians(angmax))
            Aub.append(-row)
            bub.append(-math.radians(angmin))

    res = linprog(
        c,
        A_ub=np.array(Aub) if Aub else None,
        b_ub=np.array(bub) if bub else None,
        A_eq=Aeq,
        b_eq=beq,
        bounds=bounds,
        method="highs",
        options={"presolve": True},
    )
    return bool(res.success)


def main():
    raw = download(URL)
    sha = hashlib.sha256(raw).hexdigest()
    text = raw.decode("utf-8", errors="replace")
    baseMVA = parse_scalar(text, "baseMVA")
    bus = parse_matrix(text, "bus")
    gen = parse_matrix(text, "gen")
    branch = parse_matrix(text, "branch")
    grid = Grid(baseMVA, bus, gen, branch)

    goal_buses = [
        b for b, pd in sorted(grid.load.items(), key=lambda kv: (-kv[1], kv[0]))
    ][:TOP_LOAD_GOALS]
    goal_pd = {b: grid.load[b] for b in goal_buses}

    masks = list(range(1, 1 << len(goal_buses)))

    def mask_to_set(mask):
        return frozenset(goal_buses[i] for i in range(len(goal_buses)) if mask & (1 << i))

    # Baseline feasibility for every bundle.
    baseline = {}
    for mask in masks:
        baseline[mask] = dc_feasible(grid, mask_to_set(mask), None)

    outage_results = []
    all_minimal = []

    for oi, br in enumerate(branch):
        if int(br[10]) != 1:
            continue

        after = {}
        for mask in masks:
            after[mask] = dc_feasible(grid, mask_to_set(mask), oi)

        minimal_losses = []
        for mask in masks:
            if not baseline[mask] or after[mask]:
                continue
            # Strong minimality: every non-empty proper subbundle after outage feasible.
            proper_ok = True
            sub = (mask - 1) & mask
            while sub:
                if not after[sub]:
                    proper_ok = False
                    break
                sub = (sub - 1) & mask
            if proper_ok:
                minimal_losses.append(mask)
                all_minimal.append((oi, mask))

        if minimal_losses:
            outage_results.append((oi, minimal_losses))

    print("INSACERMO_PGLIB_DC_HIDDEN_BUNDLE_AUDIT_V1")
    print("STATUS EXPLORATORY_DC_PHYSICAL_FLOW_AUDIT")
    print("SOURCE_URL", URL)
    print("SOURCE_SHA256", sha)
    print("MODEL DC_LINEARIZED_POWER_FLOW")
    print("FULL_AC_OPF_CLAIM 0")
    print("BUSES", len(bus))
    print("BRANCHES", len(branch))
    print("ACTIVE_GENERATORS", len(grid.active_gens))
    print("GOAL_LOAD_BUSES", " ".join(map(str, goal_buses)))
    print("GOAL_LOAD_MW", " ".join(f"{b}:{goal_pd[b]:.2f}" for b in goal_buses))
    print("CATALOGUE_NONEMPTY_BUNDLES", len(masks))
    print("BASELINE_FEASIBLE_BUNDLES", sum(baseline.values()))
    print("OUTAGES_WITH_MINIMAL_LOSS", len(outage_results))
    print("TOTAL_MINIMAL_LOSSES", len(all_minimal))

    if not all_minimal:
        print("RESULT NO_MINIMAL_HIDDEN_BUNDLE_LOSS_FOUND")
        return

    # Prefer highest-order witness, then smallest branch index.
    all_minimal.sort(key=lambda x: (-int(x[1]).bit_count(), x[0], x[1]))
    oi, mask = all_minimal[0]
    F = mask_to_set(mask)
    k = len(F)
    br = branch[oi]
    print("MAX_OBSERVED_MINIMAL_LOSS_ORDER", k)
    print("WITNESS_OUTAGE_BRANCH_INDEX", oi)
    print("WITNESS_OUTAGE_BRANCH", int(br[0]), int(br[1]))
    print("WITNESS_BUNDLE_BUSES", " ".join(map(str, sorted(F))))
    print("WITNESS_BUNDLE_TOTAL_MW", f"{sum(goal_pd[b] for b in F):.6f}")
    print("FULL_BUNDLE_FEASIBLE_BEFORE", int(baseline[mask]))
    print("FULL_BUNDLE_FEASIBLE_AFTER", int(dc_feasible(grid, F, oi)))

    proper_total = 0
    proper_feasible = 0
    for sub in masks:
        if sub != mask and (sub & mask) == sub:
            proper_total += 1
            if dc_feasible(grid, mask_to_set(sub), oi):
                proper_feasible += 1

    print("PROPER_SUBBUNDLES_TOTAL", proper_total)
    print("PROPER_SUBBUNDLES_FEASIBLE_AFTER", proper_feasible)
    print("ALL_PROPER_SUBBUNDLES_FEASIBLE_AFTER", int(proper_total == proper_feasible))
    print("REPAIR_RESTORE_OUTAGED_BRANCH_FEASIBLE", int(dc_feasible(grid, F, None)))
    print("MECHANISM GLOBAL_DC_FLOW_AND_CAPACITY_CONSTRAINTS")
    print("LIMITATION DC_approximation_not_AC_security_assessment")
    print("RESULT COMPLETE")


if __name__ == "__main__":
    main()
