# INSACERMO — PGLib IEEE-14 DC pre-audit depth from extreme Farkas rays V1
#
# Goal
# ----
# Derive an audit-depth bound r BEFORE enumerating future bundles.
#
# For a fixed outage, every Farkas certificate has
#   A^T y + G^T z = 0, z >= 0.
# Let N span ker(A). Then stationarity is equivalent to
#   (N^T G^T) z = 0.
# Extreme rays of this nonnegative kernel have inclusion-minimal positive
# supports, of size at most rank(N^T G^T)+1.
#
# Each extreme ray induces, for bundle F,
#   phi(F) = beta + sum_{i in F} w_i >= 0
# as a necessary condition for feasibility.
#
# If F is an inclusion-minimal infeasible bundle certified by this ray, every
# included w_i must be negative; writing p_i=-w_i>0 and
# delta=min positive p_i, feasibility of every one-element deletion gives
#   (|F|-1) delta <= beta,
# hence
#   |F| <= 1 + floor(beta/delta).
#
# Taking the maximum over all extreme rays gives a pre-audit cardinality bound
# for this finite goal catalogue. This script discovers rays from the LP
# structure; it does NOT enumerate bundles to derive r.
#
# V1 uses floating linear algebra to discover/measure rays. The resulting r is
# therefore reported as NUMERICAL_PREAUDIT_BOUND until an exact rational/pi
# checker is added.

from __future__ import annotations

import itertools
import math
import numpy as np

import pglib_ieee14_dc_hidden_bundle_audit_v1 as base
import pglib_ieee14_dc_farkas_certificate_v3 as fv3

TOP_LOAD_GOALS = 8
SVD_TOL = 1e-9
SVD_ABS_TOL = 1e-10
POS_TOL = 1e-9
RES_TOL = 1e-7
BOUND_EPS = 1e-8


def nullspace(M, tol=SVD_TOL, abs_tol=SVD_ABS_TOL):
    """Numerical nullspace with an absolute floor.

    The absolute floor is essential here: structurally zero projected columns
    can appear as ~1e-14 after floating elimination. A purely relative SVD
    threshold would call a 1-column ~zero matrix full-rank because its largest
    singular value is itself tiny, thereby deleting genuine singleton extreme
    rays.
    """
    u, s, vh = np.linalg.svd(M, full_matrices=True)
    scale = s[0] if len(s) else 0.0
    threshold = max(abs_tol, tol * max(M.shape) * scale)
    rank = int(np.sum(s > threshold))
    return vh[rank:].T, rank


def positive_kernel_ray(BS):
    """Return a strictly-positive 1D kernel vector for B[:,S], else None."""
    ns, rank = nullspace(BS)
    if ns.shape[1] != 1:
        return None
    v = ns[:, 0]
    if np.all(v > POS_TOL):
        pass
    elif np.all(v < -POS_TOL):
        v = -v
    else:
        return None
    v = v / np.sum(v)
    if np.max(np.abs(BS @ v)) > RES_TOL:
        return None
    return v


def enumerate_extreme_rays(A, G):
    """Enumerate minimal positive supports of {z>=0 | N^T G^T z=0}."""
    N, rankA = nullspace(A)
    # N columns span ker(A).  v lies in row(A^T) iff N^T v = 0.
    B = N.T @ G.T
    rankB = np.linalg.matrix_rank(B, tol=SVD_TOL)
    max_support = min(G.shape[0], rankB + 1)

    rays = []
    for k in range(1, max_support + 1):
        for S in itertools.combinations(range(G.shape[0]), k):
            BS = B[:, S]
            v = positive_kernel_ray(BS)
            if v is None:
                continue
            # 1D positive kernel with all entries nonzero implies support
            # minimality when every proper subset has trivial kernel. Verify.
            minimal = True
            if k > 1:
                for j in range(k):
                    T = S[:j] + S[j+1:]
                    if not T:
                        continue
                    nsT, _ = nullspace(B[:, T])
                    if nsT.shape[1] > 0:
                        # A proper supported kernel exists. It may not be
                        # positive; test explicitly.
                        pv = positive_kernel_ray(B[:, T])
                        if pv is not None:
                            minimal = False
                            break
            if not minimal:
                continue
            z = np.zeros(G.shape[0])
            z[list(S)] = v
            rays.append((S, z))

    return {
        "rankA": rankA,
        "nullityA": A.shape[1] - rankA,
        "rankB": rankB,
        "max_support": max_support,
        "rays": rays,
    }


def solve_y(A, G, z):
    rhs = -(G.T @ z)
    y, residuals, rank, s = np.linalg.lstsq(A.T, rhs, rcond=None)
    resid = np.max(np.abs(A.T @ y + G.T @ z))
    if resid > RES_TOL:
        return None, resid
    return y, resid


def ray_cardinality_bound(grid, outage, goal_buses, A, b0, G, h, z):
    y, resid = solve_y(A, G, z)
    if y is None:
        return None

    beta = float(b0 @ y + h @ z)
    weights = {
        bus: float(grid.load[bus] * y[grid.pos[bus]])
        for bus in goal_buses
    }
    burdens = [-w for w in weights.values() if w < -POS_TOL]

    # If beta < 0, even empty would violate this necessary inequality. That
    # should not occur because empty bundle is feasible in the benchmark.
    if beta < -BOUND_EPS:
        return {
            "status": "EMPTY_CONTRACT_VIOLATION",
            "beta": beta,
            "resid": resid,
        }

    if not burdens:
        return {
            "status": "NO_NEGATIVE_GOAL_TERMS",
            "beta": beta,
            "resid": resid,
            "bound": 0,
            "weights": weights,
        }

    delta = min(burdens)
    # Conservative numerical upward rounding: never understate due to a value
    # sitting close to an integer boundary.
    ratio = max(0.0, beta) / delta
    bound = 1 + math.floor(ratio + BOUND_EPS)
    bound = min(bound, len(burdens), len(goal_buses))

    return {
        "status": "BOUND",
        "beta": beta,
        "delta": delta,
        "ratio": ratio,
        "bound": bound,
        "resid": resid,
        "weights": weights,
        "negative_goals": [b for b, w in weights.items() if w < -POS_TOL],
    }


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

    print("INSACERMO_PGLIB_DC_EXTREME_RAY_DEPTH_V1")
    print("STATUS NUMERICAL_PREAUDIT_BOUND")
    print("GOAL_LOAD_BUSES", " ".join(map(str, goal_buses)))
    print("BUNDLE_ENUMERATION_USED_TO_DERIVE_R 0")

    global_r = 0
    total_rays = 0
    bad_empty = 0
    scenario_bounds = []

    for outage, br in enumerate(grid.branch):
        if int(br[10]) != 1:
            continue

        A, b0, G, h = fv3.build_dc_system(grid, frozenset(), outage)
        ext = enumerate_extreme_rays(A, G)

        ray_bounds = []
        for S, z in ext["rays"]:
            rec = ray_cardinality_bound(
                grid, outage, goal_buses, A, b0, G, h, z
            )
            if rec is None:
                continue
            if rec["status"] == "EMPTY_CONTRACT_VIOLATION":
                bad_empty += 1
                continue
            if rec["status"] == "BOUND":
                ray_bounds.append((rec["bound"], S, rec))

        r = max((x[0] for x in ray_bounds), default=0)
        global_r = max(global_r, r)
        total_rays += len(ext["rays"])
        scenario_bounds.append((outage, r, len(ext["rays"])))

        print(
            "SCENARIO",
            "OUTAGE", outage,
            "BRANCH", int(br[0]), int(br[1]),
            "RANK_A", ext["rankA"],
            "NULLITY_A", ext["nullityA"],
            "RANK_PROJECTED_CONE", ext["rankB"],
            "MAX_EXTREME_SUPPORT", ext["max_support"],
            "EXTREME_RAYS", len(ext["rays"]),
            "PREAUDIT_R", r,
        )

        # Print all rays attaining the scenario maximum; these explain r.
        for bound, S, rec in ray_bounds:
            if bound != r:
                continue
            print(
                "  WORST_RAY",
                "SUPPORT_SIZE", len(S),
                "SUPPORT", ",".join(map(str, S)),
                "BETA", f"{rec['beta']:.12g}",
                "DELTA", f"{rec['delta']:.12g}",
                "RATIO", f"{rec['ratio']:.12g}",
                "BOUND", bound,
                "NEG_GOALS", ",".join(map(str, rec["negative_goals"])),
                "STATIONARITY_INF", f"{rec['resid']:.3e}",
            )

    print("TOTAL_EXTREME_RAYS", total_rays)
    print("EMPTY_CONTRACT_VIOLATING_RAYS", bad_empty)
    print("GLOBAL_PREAUDIT_R", global_r)
    print("GLOBAL_PREAUDIT_R_CAPPED_BY_GOALS", min(global_r, len(goal_buses)))
    print("CERTIFICATE_CLASS EXTREME_FARKAS_RAYS")
    print("COMPLETENESS_LOGIC",
          "any_negative_dual_combination_has_a_negative_extreme_ray")
    print("LIMITATION",
          "V1_depth_is_numerical_until_exact_ray_and_ratio_verification")
    print("RESULT COMPLETE")


if __name__ == "__main__":
    main()
