# INSACERMO — PGLib IEEE-14 exact certificate-only depth closure V4
#
# Goal
# ----
# Close the gap between exact pre-audit upper bound and actual minimal-loss
# depth without calling the primal feasibility oracle and without enumerating
# future bundles.
#
# We use the exact extreme-ray machinery of V3.  For one order-7 witness F:
#   1. every exact baseline ray accepts F          -> feasible before outage;
#   2. one exact outage ray rejects F              -> infeasible after outage;
#   3. every exact outage ray accepts every proper subbundle G subset F
#                                                -> genuine minimality.
#
# We deliberately check ALL proper subbundles of the single witness instead of
# assuming downward closure.  This is still not a catalogue-wide feasibility
# audit: no primal solver is called, and only the proper subsets of one dual-
# derived witness are evaluated against the already-enumerated exact rays.
#
# No base.dc_feasible() call appears in this file.

from __future__ import annotations

import itertools
import sympy as sp

import pglib_ieee14_dc_hidden_bundle_audit_v1 as base
import pglib_ieee14_dc_exact_preaudit_depth_v3 as v3

Q = sp.Rational
TOP_LOAD_GOALS = 8


def prepare_scenario(grid, goal_buses, outage):
    A = v3.exact_A(grid, outage)
    rows, hs, labels, redundant = v3.exact_reduced_inequalities(grid, outage)
    (
        A, rows, hs, labels, row_index,
        dropped_eq, dropped_vars, dropped_ineq,
    ) = v3.prune_trivial_zero_factors(
        grid, goal_buses, A, rows, hs, labels
    )
    cols = v3.projected_columns(A, rows)
    rankB, rays = v3.enumerate_exact_extreme_rays(cols)
    y_parts = v3.prepare_y_solver(A, rows)
    return {
        "A": A,
        "rows": rows,
        "hs": hs,
        "labels": labels,
        "row_index": row_index,
        "rays": rays,
        "rankB": rankB,
        "redundant": redundant,
        "dropped_eq": dropped_eq,
        "dropped_vars": dropped_vars,
        "dropped_ineq": dropped_ineq,
        "y_parts": y_parts,
    }


def all_ray_data(grid, goal_buses, sc):
    out = []
    for support, zvals in sc["rays"]:
        beta, weights = v3.ray_data(
            grid, goal_buses,
            sc["A"], sc["rows"], sc["hs"],
            support, zvals, sc["y_parts"], sc["row_index"],
        )
        out.append((support, beta, weights))
    return out


def value(beta, weights, F):
    return sp.factor(beta + sum(weights[b] for b in F))


def main():
    raw = base.download(base.URL)
    text = raw.decode("utf-8", errors="replace")
    grid = base.Grid(
        base.parse_scalar(text, "baseMVA"),
        base.parse_matrix(text, "bus"),
        base.parse_matrix(text, "gen"),
        base.parse_matrix(text, "branch"),
    )
    goal_buses = [
        b for b, pd in sorted(grid.load.items(), key=lambda kv: (-kv[1], kv[0]))
    ][:TOP_LOAD_GOALS]

    print("INSACERMO_PGLIB_DC_EXACT_CERTIFICATE_ONLY_DEPTH_V4")
    print("STATUS EXACT_DUAL_ONLY_MINIMAL_LOSS_CLOSURE")
    print("PRIMAL_FEASIBILITY_CALLS", 0)
    print("FULL_CATALOGUE_BUNDLE_ENUMERATION_USED", 0)
    print("GOAL_LOAD_BUSES", " ".join(map(str, goal_buses)))

    # Re-derive a candidate order-7 witness from exact outage rays only.
    witness = None
    global_order8 = 0
    total_outage_rays = 0

    for outage, br in enumerate(grid.branch):
        if int(br[10]) != 1:
            continue
        sc = prepare_scenario(grid, goal_buses, outage)
        raydata = all_ray_data(grid, goal_buses, sc)
        total_outage_rays += len(raydata)

        for support, beta, weights in raydata:
            ok8, _ = v3.compatible_minimality(beta, weights, tuple(goal_buses))
            if ok8:
                global_order8 += 1

            if witness is None:
                for F in itertools.combinations(goal_buses, 7):
                    ok7, rec = v3.compatible_minimality(beta, weights, F)
                    if ok7:
                        witness = {
                            "outage": outage,
                            "branch": (int(br[0]), int(br[1])),
                            "F": tuple(F),
                            "support": support,
                            "beta": beta,
                            "weights": weights,
                            "rec": rec,
                        }
                        break

    if global_order8 != 0:
        raise RuntimeError(
            f"exact order-8 compatible rays found: {global_order8}"
        )
    if witness is None:
        raise RuntimeError("no exact order-7 candidate witness found")

    oi = witness["outage"]
    F = witness["F"]

    # Exact post-outage certificate family.
    post = prepare_scenario(grid, goal_buses, oi)
    post_rays = all_ray_data(grid, goal_buses, post)

    full_negative = [
        (support, value(beta, weights, F))
        for support, beta, weights in post_rays
        if value(beta, weights, F) < 0
    ]
    if not full_negative:
        raise RuntimeError("order-7 full witness is not dual-certified infeasible")

    # Strong cross-certificate closure: EVERY proper subbundle is accepted
    # by EVERY post-outage exact ray.
    proper_checked = 0
    proper_bad = []
    deletion_min = {}
    deletion_bad_counts = {}

    for k in range(0, len(F)):
        for G in itertools.combinations(F, k):
            vals = [value(beta, weights, G) for _, beta, weights in post_rays]
            proper_checked += 1
            bad = sum(1 for x in vals if x < 0)
            if bad:
                proper_bad.append((G, bad, min(vals)))
            if k == len(F) - 1:
                removed = next(q for q in F if q not in G)
                deletion_min[removed] = min(vals)
                deletion_bad_counts[removed] = bad

    if proper_bad:
        G, bad, vmin = proper_bad[0]
        raise RuntimeError(
            "candidate is not cross-certified on a proper subbundle: "
            f"G={G}, negative_rays={bad}, min={vmin}"
        )

    # Exact baseline certificate family: no outage.
    pre = prepare_scenario(grid, goal_buses, None)
    pre_rays = all_ray_data(grid, goal_buses, pre)
    pre_vals = [value(beta, weights, F) for _, beta, weights in pre_rays]
    pre_bad = sum(1 for x in pre_vals if x < 0)
    if pre_bad != 0:
        raise RuntimeError(
            f"order-7 witness is not baseline feasible by exact dual family: {pre_bad}"
        )

    full_worst_support, full_worst_value = min(
        full_negative, key=lambda x: x[1]
    )

    print("TOTAL_EXACT_OUTAGE_RAYS", total_outage_rays)
    print("EXACT_ORDER8_COMPATIBLE_RAYS", global_order8)
    print("WITNESS_OUTAGE", oi)
    print("WITNESS_BRANCH", *witness["branch"])
    print("WITNESS_BUSES", ",".join(map(str, F)))
    print("WITNESS_DISCOVERY_SUPPORT", ",".join(map(str, witness["support"])))
    print("POST_OUTAGE_EXACT_RAYS", len(post_rays))
    print("FULL_BUNDLE_NEGATIVE_RAYS", len(full_negative))
    print("FULL_BUNDLE_MOST_NEGATIVE_SUPPORT",
          ",".join(map(str, full_worst_support)))
    print("FULL_BUNDLE_MOST_NEGATIVE_VALUE", v3.compact_rat(full_worst_value))

    for q in F:
        print(
            "DELETION",
            q,
            "NEGATIVE_RAYS", deletion_bad_counts[q],
            "MIN_EXACT_VALUE", v3.compact_rat(deletion_min[q]),
        )

    print("WITNESS_PROPER_SUBBUNDLES_CHECKED", proper_checked)
    print("WITNESS_PROPER_SUBBUNDLES_WITH_NEGATIVE_RAY", len(proper_bad))
    print("ALL_PROPER_SUBBUNDLES_ACCEPTED_BY_ALL_POST_OUTAGE_RAYS", 1)
    print("CROSS_CERTIFIED_MINIMAL", 1)
    print("BASELINE_EXACT_RAYS", len(pre_rays))
    print("BASELINE_NEGATIVE_RAYS_FOR_WITNESS", pre_bad)
    print("BASELINE_WITNESS_ACCEPTED_BY_ALL_RAYS", 1)
    print("EXACT_PREAUDIT_UPPER_BOUND", 7)
    print("EXACT_DUAL_ONLY_ACTUAL_LOWER_WITNESS", 7)
    print("EXACT_CERTIFICATE_ONLY_DEPTH", 7)
    print("LIMITATION encoded_DC_LP_fixed_8_goal_catalogue_not_full_AC_security")
    print("RESULT COMPLETE")


if __name__ == "__main__":
    main()
