# INSACERMO — PGLib IEEE-14 exact pre-audit depth V3
#
# Purpose
# -------
# Replace V2's floating/SVD pre-audit depth by an exact rational certificate
# computation for the same encoded DC feasibility problem.
#
# Key reduction:
# every active branch in this PGLib case has a thermal flow bound that implies
# the +/-30 degree branch-angle bound.  Indeed, with zero phase shifts,
#     |theta_i-theta_j| <= rateA / bmw
# and the script checks exactly that rateA/bmw <= 1/2 < pi/6.
# Hence the angle-difference inequalities are redundant and may be removed
# without changing the primal feasible set.  The remaining A,G,h data are
# rational after finite-decimal rationalization.
#
# For A x = b_F, G x <= h, Farkas stationarity is
#     A^T y + G^T z = 0, z >= 0.
# Projecting through an exact basis N of ker(A) gives B z = 0, z>=0.
# In this case dim ker(A)=2, so every extreme ray has support <=3.
# We enumerate all singleton/pair/triple positive circuits exactly over Q.
#
# Each extreme ray induces
#     phi(F) = beta + sum_{i in F} w_i >= 0.
# If it certifies an inclusion-minimal failure F, every w_i in F is negative
# and, with p_i=-w_i,
#     sum p_i > beta
#     sum p_i - min p_i <= beta.
#
# The catalogue has exactly 8 goals.  Therefore:
#   * proving that NO exact extreme ray is compatible with order 8 gives r<=7;
#   * exhibiting one exact ray compatible with order 7 gives r>=7.
# No bundle-feasibility query is used to derive r.

from __future__ import annotations

import itertools
import sympy as sp

import pglib_ieee14_dc_hidden_bundle_audit_v1 as base

Q = sp.Rational
TOP_LOAD_GOALS = 8


def q(x):
    return Q(str(float(x)))


def exact_A(grid, outage_idx):
    n = grid.n
    ng = len(grid.active_gens)
    A = sp.zeros(n, n + ng)

    for gj, (_, bus_id, _, _) in enumerate(grid.active_gens):
        A[grid.pos[bus_id], n + gj] += 1

    for li, br in enumerate(grid.branch):
        if li == outage_idx:
            continue
        if int(br[10]) != 1:
            continue
        fbus, tbus = int(br[0]), int(br[1])
        x = q(br[3])
        if x == 0:
            continue
        tap = q(br[8]) if abs(br[8]) > 1e-12 else Q(1)
        shift = q(br[9])
        if shift != 0:
            raise RuntimeError("V3 exact reduction assumes zero phase shifts")

        bmw = q(grid.base) / (x * tap)
        i, j = grid.pos[fbus], grid.pos[tbus]
        A[i, i] -= bmw
        A[i, j] += bmw
        A[j, i] += bmw
        A[j, j] -= bmw

    return A


def exact_reduced_inequalities(grid, outage_idx):
    n = grid.n
    ng = len(grid.active_gens)
    nv = n + ng

    rows = []
    hs = []
    labels = []
    redundant_angle_rows = 0

    for li, br in enumerate(grid.branch):
        if li == outage_idx:
            continue
        if int(br[10]) != 1:
            continue

        fbus, tbus = int(br[0]), int(br[1])
        x = q(br[3])
        if x == 0:
            continue
        tap = q(br[8]) if abs(br[8]) > 1e-12 else Q(1)
        shift = q(br[9])
        if shift != 0:
            raise RuntimeError("V3 exact reduction assumes zero phase shifts")

        bmw = q(grid.base) / (x * tap)
        rate = q(br[5])
        i, j = grid.pos[fbus], grid.pos[tbus]

        if rate <= 0:
            raise RuntimeError("angle-redundancy proof requires positive rateA")

        row = sp.zeros(1, nv)
        row[0, i] = bmw
        row[0, j] = -bmw
        rows.append(row)
        hs.append(rate)
        labels.append(("thermal+", li))
        rows.append(-row)
        hs.append(rate)
        labels.append(("thermal-", li))

        angmin, angmax = q(br[11]), q(br[12])
        if angmax > angmin and angmax < 360:
            if not (angmin == -30 and angmax == 30):
                raise RuntimeError(
                    f"unexpected angle bounds on branch {li}: {angmin},{angmax}"
                )
            # Thermal bound implies |theta_i-theta_j| <= rate/bmw.
            # Check the stronger rational statement rate/bmw <= 1/2.
            # Since pi>3, 1/2 < pi/6 = 30 degrees in radians.
            theta_delta = sp.factor(rate / bmw)
            if theta_delta > Q(1, 2):
                raise RuntimeError(
                    f"thermal bound does not imply angle bound on branch {li}"
                )
            redundant_angle_rows += 2

    bounds = [(Q(-10), Q(10)) for _ in range(n)]
    bounds[grid.pos[grid.ref_bus]] = (Q(0), Q(0))
    for _, _, pmin, pmax in grid.active_gens:
        bounds.append((q(pmin), q(pmax)))

    eye = sp.eye(nv)
    for j, (lo, hi) in enumerate(bounds):
        rows.append(eye[j, :])
        hs.append(hi)
        labels.append(("bound+", j))
        rows.append(-eye[j, :])
        hs.append(-lo)
        labels.append(("bound-", j))

    return rows, hs, labels, redundant_angle_rows


def det2(a, b):
    return sp.factor(a[0] * b[1] - a[1] * b[0])


def projected_columns(A, rows):
    basis = A.nullspace()
    if len(basis) != 2:
        raise RuntimeError(
            f"expected dim ker(A)=2, got {len(basis)} (rank={A.rank()})"
        )
    cols = []
    for row in rows:
        cols.append(tuple(sp.factor((v.T * row.T)[0]) for v in basis))
    return cols


def projected_rank(cols):
    nonzero = [c for c in cols if c != (0, 0)]
    if not nonzero:
        return 0
    a = nonzero[0]
    for b in nonzero[1:]:
        if det2(a, b) != 0:
            return 2
    return 1


def enumerate_exact_extreme_rays(cols):
    m = len(cols)
    rankB = projected_rank(cols)
    rays = []

    # Singleton circuits: projected column exactly zero.
    for i, c in enumerate(cols):
        if c == (0, 0):
            rays.append(((i,), (Q(1),)))

    # Pair circuits: nonzero opposite collinear columns.
    for i in range(m):
        a = cols[i]
        if a == (0, 0):
            continue
        for j in range(i + 1, m):
            b = cols[j]
            if b == (0, 0) or det2(a, b) != 0:
                continue
            k = 0 if a[0] != 0 else 1
            zi = sp.factor(-b[k] / a[k])
            zj = Q(1)
            if zi > 0:
                rays.append(((i, j), (zi, zj)))

    # Triple circuits: for rank 2, the cofactor kernel vector is exact.
    if rankB == 2:
        for i in range(m):
            a = cols[i]
            if a == (0, 0):
                continue
            for j in range(i + 1, m):
                b = cols[j]
                if b == (0, 0):
                    continue
                dij = det2(a, b)
                for k in range(j + 1, m):
                    c = cols[k]
                    if c == (0, 0):
                        continue
                    z = (det2(b, c), det2(c, a), dij)
                    if all(v > 0 for v in z):
                        rays.append(((i, j, k), tuple(sp.factor(v) for v in z)))
                    elif all(v < 0 for v in z):
                        rays.append(((i, j, k), tuple(sp.factor(-v) for v in z)))

    return rankB, rays


def prepare_y_solver(A, rows):
    pivots = tuple(A.rref()[1])
    if len(pivots) != A.rows:
        raise RuntimeError(
            f"A is not full row rank: rank={len(pivots)} rows={A.rows}"
        )
    square = A.extract(range(A.rows), pivots).T
    inv = square.inv()

    # Candidate y contribution for each inequality, obtained from the pivot
    # equations.  A true projected circuit makes the remaining equations match.
    y_parts = []
    for row in rows:
        rhs = sp.Matrix([-row[0, j] for j in pivots])
        y_parts.append(inv * rhs)
    return y_parts


def ray_data(grid, goal_buses, A, rows, hs, support, zvals, y_parts):
    y = sp.zeros(A.rows, 1)
    for idx, zz in zip(support, zvals):
        y += zz * y_parts[idx]

    stationarity = A.T * y
    for idx, zz in zip(support, zvals):
        stationarity += zz * rows[idx].T
    if stationarity != sp.zeros(A.cols, 1):
        raise RuntimeError(f"nonzero exact stationarity for support {support}")

    beta = sp.factor(sum(hs[idx] * zz for idx, zz in zip(support, zvals)))
    weights = {
        bus: sp.factor(q(grid.load[bus]) * y[grid.pos[bus], 0])
        for bus in goal_buses
    }
    return beta, weights


def compatible_minimality(beta, weights, buses):
    ps = []
    for bus in buses:
        w = weights[bus]
        if not (w < 0):
            return False, None
        ps.append(-w)

    S = sp.factor(sum(ps))
    pmin = min(ps)
    ok = (S > beta) and (S - pmin <= beta)
    if not ok:
        return False, None

    return True, {
        "S": S,
        "pmin": pmin,
        "full_margin": sp.factor(S - beta),
        "delete_min_slack": sp.factor(beta - (S - pmin)),
    }


def compact_rat(x):
    x = sp.factor(x)
    if getattr(x, "q", None) is not None:
        return f"{sp.numer(x)}/{sp.denom(x)}"
    return str(x)


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
    if len(goal_buses) != 8:
        raise RuntimeError("this exact closure expects an 8-goal catalogue")

    print("INSACERMO_PGLIB_DC_EXACT_PREAUDIT_DEPTH_V3")
    print("STATUS EXACT_RATIONAL_PREAUDIT_DEPTH")
    print("MODEL EQUIVALENT_DC_LP_WITH_PROVEN_REDUNDANT_ANGLE_ROWS_REMOVED")
    print("ARITHMETIC EXACT_Q_RATIONALIZED_FINITE_DECIMAL_PGLIB_DATA")
    print("GOAL_LOAD_BUSES", " ".join(map(str, goal_buses)))
    print("BUNDLE_FEASIBILITY_CALLS_TO_DERIVE_R", 0)
    print("BUNDLE_ENUMERATION_USED_TO_DERIVE_R", 0)
    print("CERTIFICATE_WEIGHT_SUBSETS_ONLY", 1)

    total_rays = 0
    total_redundant_angle_rows = 0
    order8_compatible = []
    order7_compatible = []

    for outage, br in enumerate(grid.branch):
        if int(br[10]) != 1:
            continue

        A = exact_A(grid, outage)
        rows, hs, labels, redundant = exact_reduced_inequalities(grid, outage)
        cols = projected_columns(A, rows)
        rankB, rays = enumerate_exact_extreme_rays(cols)
        y_parts = prepare_y_solver(A, rows)

        scenario_8 = 0
        scenario_7 = 0
        total_rays += len(rays)
        total_redundant_angle_rows += redundant

        for support, zvals in rays:
            beta, weights = ray_data(
                grid, goal_buses, A, rows, hs, support, zvals, y_parts
            )

            ok8, rec8 = compatible_minimality(beta, weights, tuple(goal_buses))
            if ok8:
                scenario_8 += 1
                order8_compatible.append(
                    (outage, support, zvals, beta, weights, tuple(goal_buses), rec8)
                )

            for buses7 in itertools.combinations(goal_buses, 7):
                ok7, rec7 = compatible_minimality(beta, weights, buses7)
                if ok7:
                    scenario_7 += 1
                    if len(order7_compatible) < 20:
                        order7_compatible.append(
                            (outage, support, zvals, beta, weights, buses7, rec7)
                        )
                    break

        print(
            "SCENARIO",
            "OUTAGE", outage,
            "BRANCH", int(br[0]), int(br[1]),
            "RANK_A", A.rank(),
            "NULLITY_A", A.cols - A.rank(),
            "RANK_PROJECTED_CONE", rankB,
            "EXACT_EXTREME_RAYS", len(rays),
            "ORDER8_COMPATIBLE_RAYS", scenario_8,
            "ORDER7_COMPATIBLE_RAYS", scenario_7,
            "REDUNDANT_ANGLE_ROWS_REMOVED", redundant,
        )

    if order8_compatible:
        oi, support, zvals, beta, weights, buses, rec = order8_compatible[0]
        raise RuntimeError(
            "exact order-8 compatible extreme ray exists: "
            f"outage={oi}, support={support}"
        )

    if not order7_compatible:
        raise RuntimeError("no exact order-7 compatible extreme ray found")

    oi, support, zvals, beta, weights, buses7, rec = order7_compatible[0]

    print("TOTAL_EXACT_EXTREME_RAYS", total_rays)
    print("TOTAL_REDUNDANT_ANGLE_ROWS_REMOVED", total_redundant_angle_rows)
    print("EXACT_ORDER8_COMPATIBLE_RAYS", len(order8_compatible))
    print("EXACT_ORDER7_WITNESS_FOUND", 1)
    print("EXACT_ORDER7_WITNESS_OUTAGE", oi)
    print("EXACT_ORDER7_WITNESS_SUPPORT", ",".join(map(str, support)))
    print("EXACT_ORDER7_WITNESS_BUSES", ",".join(map(str, buses7)))
    print("EXACT_ORDER7_BETA", compact_rat(beta))
    print("EXACT_ORDER7_S", compact_rat(rec["S"]))
    print("EXACT_ORDER7_PMIN", compact_rat(rec["pmin"]))
    print("EXACT_ORDER7_FULL_MARGIN", compact_rat(rec["full_margin"]))
    print("EXACT_ORDER7_DELETE_MIN_SLACK", compact_rat(rec["delete_min_slack"]))
    print("EXACT_PREAUDIT_UPPER_BOUND", 7)
    print("EXACT_PREAUDIT_LOWER_WITNESS", 7)
    print("EXACT_PREAUDIT_DEPTH", 7)
    print("GLOBAL_TIGHT_PREAUDIT_R", 7)
    print("CERTIFICATE_CLASS EXACT_EXTREME_FARKAS_RAYS_WITH_ONE_DELETION_MINIMALITY")
    print("LIMITATION exact_for_encoded_DC_LP_not_full_AC_security")
    print("RESULT COMPLETE")


if __name__ == "__main__":
    main()
