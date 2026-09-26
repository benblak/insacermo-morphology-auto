# INSACERMO — PGLib IEEE-14 DC cut-certificate audit V2
#
# Purpose
# -------
# Explain the V1 DC hidden-bundle obstructions with explicit network-cut
# certificates whenever possible, and measure where simple cuts cease to be
# complete and a stronger LP/Farkas certificate is needed.
#
# Necessary cut inequality for any served bundle F and bus subset S:
#
#   demand_F(S) <= Pmax_generation(S) + thermal_boundary_capacity(S).
#
# A strict violation is a mathematical infeasibility certificate for the DC
# model (indeed for any active-power flow respecting those generator and line
# capacities).  It does not depend on LP solver non-convergence.
#
# This script reuses the exact V1 PGLib parser and DC feasibility semantics.

from __future__ import annotations

import itertools
import math

import pglib_ieee14_dc_hidden_bundle_audit_v1 as base

TOP_LOAD_GOALS = 8


def thermal_cut_certificate(grid, served_buses, outage_idx):
    n = grid.n
    all_bits = (1 << n) - 1
    best = None

    # Generator active Pmax available inside each side.
    gen_pmax = {}
    for _, bus_id, _pmin, pmax in grid.active_gens:
        gen_pmax[bus_id] = gen_pmax.get(bus_id, 0.0) + pmax

    for bits in range(1, all_bits):
        if bits == all_bits:
            continue
        S = {
            grid.bus_ids[i]
            for i in range(n)
            if bits & (1 << i)
        }

        demand = sum(grid.load.get(b, 0.0) for b in served_buses if b in S)
        local_gen = sum(gen_pmax.get(b, 0.0) for b in S)

        boundary = []
        boundary_cap = 0.0
        valid = True
        for li, br in enumerate(grid.branch):
            if li == outage_idx:
                continue
            status = int(br[10])
            if status != 1:
                continue
            fbus, tbus = int(br[0]), int(br[1])
            if (fbus in S) == (tbus in S):
                continue
            rateA = float(br[5])
            if rateA <= 0:
                # No finite thermal rate -> this simple finite-capacity cut
                # cannot certify the cut.
                valid = False
                break
            boundary_cap += rateA
            boundary.append((li, fbus, tbus, rateA))

        if not valid:
            continue

        capacity = local_gen + boundary_cap
        margin = demand - capacity
        if margin > 1e-9:
            rec = {
                "margin": margin,
                "S": S,
                "demand": demand,
                "local_gen": local_gen,
                "boundary_cap": boundary_cap,
                "capacity": capacity,
                "boundary": boundary,
            }
            if best is None or rec["margin"] > best["margin"]:
                best = rec

    return best


def main():
    raw = base.download(base.URL)
    text = raw.decode("utf-8", errors="replace")
    baseMVA = base.parse_scalar(text, "baseMVA")
    bus = base.parse_matrix(text, "bus")
    gen = base.parse_matrix(text, "gen")
    branch = base.parse_matrix(text, "branch")
    grid = base.Grid(baseMVA, bus, gen, branch)

    goal_buses = [
        b for b, pd in sorted(grid.load.items(), key=lambda kv: (-kv[1], kv[0]))
    ][:TOP_LOAD_GOALS]
    masks = list(range(1, 1 << len(goal_buses)))

    def mask_to_set(mask):
        return frozenset(
            goal_buses[i]
            for i in range(len(goal_buses))
            if mask & (1 << i)
        )

    # Reproduce V1 minimal losses exactly.
    baseline = {
        mask: base.dc_feasible(grid, mask_to_set(mask), None)
        for mask in masks
    }

    minimal = []
    for oi, br in enumerate(branch):
        if int(br[10]) != 1:
            continue
        after = {
            mask: base.dc_feasible(grid, mask_to_set(mask), oi)
            for mask in masks
        }
        for mask in masks:
            if not baseline[mask] or after[mask]:
                continue
            proper_ok = True
            sub = (mask - 1) & mask
            while sub:
                if not after[sub]:
                    proper_ok = False
                    break
                sub = (sub - 1) & mask
            if proper_ok:
                minimal.append((oi, mask))

    covered = []
    uncovered = []
    for oi, mask in minimal:
        F = mask_to_set(mask)
        cert = thermal_cut_certificate(grid, F, oi)
        if cert is None:
            uncovered.append((oi, mask))
        else:
            covered.append((oi, mask, cert))

    print("INSACERMO_PGLIB_DC_CUT_CERTIFICATE_V2")
    print("STATUS EXACT_THERMAL_CUT_CERTIFICATE_AUDIT")
    print("MODEL SAME_DC_CAPABILITY_MODEL_AS_V1")
    print("GOAL_LOAD_BUSES", " ".join(map(str, goal_buses)))
    print("TOTAL_MINIMAL_LOSSES", len(minimal))
    print("CUT_CERTIFIED_MINIMAL_LOSSES", len(covered))
    print("CUT_UNEXPLAINED_MINIMAL_LOSSES", len(uncovered))

    # Pin the original highest-order witness: outage branch index 0.
    target = None
    for oi, mask, cert in covered:
        if oi == 0 and mask.bit_count() == 7:
            target = (oi, mask, cert)
            break

    if target is None:
        print("RESULT ORIGINAL_ORDER7_WITNESS_NOT_CUT_CERTIFIED")
        return

    oi, mask, cert = target
    F = mask_to_set(mask)
    br = branch[oi]
    smallest = min(grid.load[b] for b in F)

    print("WITNESS_OUTAGE_BRANCH_INDEX", oi)
    print("WITNESS_OUTAGE_BRANCH", int(br[0]), int(br[1]))
    print("WITNESS_ORDER", len(F))
    print("WITNESS_BUNDLE_BUSES", " ".join(map(str, sorted(F))))
    print("CUT_SIDE_BUSES", " ".join(map(str, sorted(cert["S"]))))
    print("CUT_LOCAL_GENERATION_PMAX_MW", f"{cert['local_gen']:.6f}")
    print("CUT_BOUNDARY_CAPACITY_MW", f"{cert['boundary_cap']:.6f}")
    print("CUT_TOTAL_CAPACITY_MW", f"{cert['capacity']:.6f}")
    print("FULL_BUNDLE_DEMAND_MW", f"{cert['demand']:.6f}")
    print("CUT_VIOLATION_MARGIN_MW", f"{cert['margin']:.6f}")
    print("SMALLEST_GOAL_LOAD_MW", f"{smallest:.6f}")
    print("FULL_MINUS_SMALLEST_MW", f"{cert['demand'] - smallest:.6f}")

    for li, fbus, tbus, rate in cert["boundary"]:
        print("CUT_BOUNDARY_BRANCH", li, fbus, tbus, f"{rate:.6f}")

    # Integer-centi-MW arithmetic: avoids floating-point ambiguity in the
    # certificate statement for this benchmark.
    C100 = round(cert["capacity"] * 100)
    W100 = round(cert["demand"] * 100)
    d100 = round(smallest * 100)
    print("EXACT_CENTI_MW_CAPACITY", C100)
    print("EXACT_CENTI_MW_FULL_DEMAND", W100)
    print("EXACT_CENTI_MW_MIN_GOAL", d100)
    print("EXACT_FULL_VIOLATES_CUT", int(C100 < W100))
    print("EXACT_REMOVE_MIN_FITS_CUT", int(W100 - d100 <= C100))

    # The V1 LP audit already establishes actual feasibility of every proper
    # subbundle. Recheck it here to bind the cut certificate to minimality.
    proper_total = 0
    proper_feasible = 0
    for sub in masks:
        if sub != mask and (sub & mask) == sub:
            proper_total += 1
            if base.dc_feasible(grid, mask_to_set(sub), oi):
                proper_feasible += 1
    print("PROPER_SUBBUNDLES_TOTAL", proper_total)
    print("PROPER_SUBBUNDLES_DC_FEASIBLE", proper_feasible)
    print("CUT_PLUS_PROPER_FEASIBILITY_CERTIFIES_MINIMALITY",
          int(proper_total == proper_feasible and C100 < W100))

    # Scope boundary: list the minimal losses simple thermal cuts do not explain.
    for oi, mask in uncovered:
        F = mask_to_set(mask)
        print(
            "UNCOVERED_MINIMAL_LOSS",
            "OUTAGE", oi,
            "ORDER", len(F),
            "BUSES", " ".join(map(str, sorted(F)))
        )

    print("INTERPRETATION simple_thermal_cuts_are_sound_but_not_complete_for_DC_model")
    print("NEXT_CERTIFICATE LP_FARKAS_DUAL_FOR_UNCOVERED_CASES")
    print("RESULT COMPLETE")


if __name__ == "__main__":
    main()
