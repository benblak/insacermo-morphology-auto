# INSACERMO — PGLib IEEE-14 DC tight pre-audit depth from Farkas rays V2
#
# Purpose
# -------
# Tighten V1's coarse beta/delta cardinality bound without querying bundle
# feasibility. For every extreme Farkas ray, use the exact one-deletion
# minimality condition induced by that ray.
#
# A fixed ray gives a necessary feasibility inequality
#     phi(F) = beta + sum_{i in F} w_i >= 0.
#
# If that ray certifies an inclusion-minimal failed bundle F, then:
#   * phi(F) < 0;
#   * phi(F \ {j}) >= 0 for every j in F.
#
# Therefore every included w_j is negative. With p_j = -w_j > 0 and
# S_F = sum p_j:
#     S_F > beta
#     S_F - p_j <= beta for all j in F
# equivalently
#     S_F - min_{j in F} p_j <= beta < S_F.
#
# We compute the largest cardinality compatible with that condition from the
# ray weights alone. No dc_feasible() call and no bundle-feasibility audit is
# used to derive r.
#
# This remains a numerical pre-audit bound until the worst rays are rechecked
# with exact arithmetic.

from __future__ import annotations

import itertools
import math
import numpy as np

import pglib_ieee14_dc_hidden_bundle_audit_v1 as base
import pglib_ieee14_dc_farkas_certificate_v3 as fv3
import pglib_ieee14_dc_extreme_ray_depth_v1 as rayv1

TOP_LOAD_GOALS = 8
POS_TOL = 1e-10
REL_TOL = 1e-9


def conservative_le(a: float, b: float) -> bool:
    tol = REL_TOL * max(1.0, abs(a), abs(b))
    return a <= b + tol


def conservative_gt(a: float, b: float) -> bool:
    # For an upper bound on possible minimal-failure size, treat numerically
    # borderline strict inequalities as potentially satisfiable.
    tol = REL_TOL * max(1.0, abs(a), abs(b))
    return a > b - tol


def tight_bound_from_ray(beta: float, weights: dict[int, float]):
    burdens = [(bus, -w) for bus, w in weights.items() if w < -POS_TOL]
    if not burdens:
        return {
            "bound": 0,
            "witness_buses": (),
            "beta": beta,
            "sum": 0.0,
            "min_p": 0.0,
        }

    best = 0
    best_rec = None
    n = len(burdens)

    # This enumerates subsets of at most eight CERTIFICATE WEIGHTS. It never
    # asks whether the corresponding bundle is feasible.
    for mask in range(1, 1 << n):
        chosen = [burdens[i] for i in range(n) if mask & (1 << i)]
        ps = [p for _, p in chosen]
        S = float(sum(ps))
        pmin = float(min(ps))

        # Necessary conditions for a minimal failure certified by this ray.
        if conservative_gt(S, beta) and conservative_le(S - pmin, beta):
            m = len(chosen)
            if m > best:
                best = m
                best_rec = {
                    "bound": m,
                    "witness_buses": tuple(sorted(bus for bus, _ in chosen)),
                    "beta": beta,
                    "sum": S,
                    "min_p": pmin,
                    "slack_full": S - beta,
                    "slack_delete_min": beta - (S - pmin),
                }

    if best_rec is None:
        return {
            "bound": 0,
            "witness_buses": (),
            "beta": beta,
            "sum": 0.0,
            "min_p": 0.0,
        }
    return best_rec


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

    print("INSACERMO_PGLIB_DC_TIGHT_EXTREME_RAY_DEPTH_V2")
    print("STATUS NUMERICAL_TIGHT_PREAUDIT_BOUND")
    print("GOAL_LOAD_BUSES", " ".join(map(str, goal_buses)))
    print("BUNDLE_FEASIBILITY_CALLS_TO_DERIVE_R", 0)
    print("DERIVATION_USES_CERTIFICATE_WEIGHT_SUBSETS_ONLY", 1)

    global_r = 0
    total_rays = 0
    global_worst = []

    for outage, br in enumerate(grid.branch):
        if int(br[10]) != 1:
            continue

        # Empty bundle only: defines the affine certificate constant beta.
        A, b0, G, h = fv3.build_dc_system(grid, frozenset(), outage)
        ext = rayv1.enumerate_extreme_rays(A, G)
        scenario_r = 0
        scenario_worst = []

        for Ssupport, z in ext["rays"]:
            y, resid = rayv1.solve_y(A, G, z)
            if y is None:
                continue

            beta = float(b0 @ y + h @ z)
            # Empty contract is known feasible in this encoded model, so a
            # materially negative beta would signal a numerical/problem issue.
            if beta < -1e-7:
                continue

            weights = {
                bus: float(grid.load[bus] * y[grid.pos[bus]])
                for bus in goal_buses
            }
            rec = tight_bound_from_ray(beta, weights)
            r = rec["bound"]

            if r > scenario_r:
                scenario_r = r
                scenario_worst = [(Ssupport, resid, rec, weights)]
            elif r == scenario_r and r > 0:
                scenario_worst.append((Ssupport, resid, rec, weights))

        total_rays += len(ext["rays"])
        global_r = max(global_r, scenario_r)

        print(
            "SCENARIO",
            "OUTAGE", outage,
            "BRANCH", int(br[0]), int(br[1]),
            "EXTREME_RAYS", len(ext["rays"]),
            "TIGHT_PREAUDIT_R", scenario_r,
        )

        # Keep compact: print at most three scenario-maximizing rays.
        for Ssupport, resid, rec, weights in scenario_worst[:3]:
            print(
                "  TIGHT_WORST_RAY",
                "SUPPORT_SIZE", len(Ssupport),
                "SUPPORT", ",".join(map(str, Ssupport)),
                "BOUND", rec["bound"],
                "BUSES", ",".join(map(str, rec["witness_buses"])),
                "BETA", f"{rec['beta']:.12g}",
                "S", f"{rec['sum']:.12g}",
                "PMIN", f"{rec['min_p']:.12g}",
                "FULL_MARGIN", f"{rec.get('slack_full', 0.0):.12g}",
                "DELETE_MIN_SLACK", f"{rec.get('slack_delete_min', 0.0):.12g}",
                "STATIONARITY_INF", f"{resid:.3e}",
            )

        if scenario_r == global_r and scenario_r > 0:
            global_worst.extend(
                (outage, Ssupport, resid, rec, weights)
                for Ssupport, resid, rec, weights in scenario_worst
                if rec["bound"] == scenario_r
            )

    print("TOTAL_EXTREME_RAYS", total_rays)
    print("GLOBAL_TIGHT_PREAUDIT_R", global_r)
    print("GLOBAL_TIGHT_PREAUDIT_R_CAPPED_BY_GOALS", min(global_r, len(goal_buses)))
    print("COARSE_V1_BOUND_WAS", 8)
    print("BUNDLE_ENUMERATION_USED_TO_DERIVE_R", 0)
    print("CERTIFICATE_CLASS EXTREME_FARKAS_RAYS_WITH_ONE_DELETION_MINIMALITY")
    print("LIMITATION V2_depth_is_numerical_until_worst_rays_are_exactly_verified")
    print("RESULT COMPLETE")


if __name__ == "__main__":
    main()
