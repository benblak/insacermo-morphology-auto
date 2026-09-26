# INSACERMO — PGLib IEEE-14 exact rational Farkas certificates V4
#
# This stage turns the numerical support patterns found by V3 into exact
# rational Farkas certificates for the 10 minimal DC losses not certified by
# simple thermal cuts.
#
# Key fact for this benchmark: the selected certificates use only thermal-line
# inequalities and, for some outages, the lower bound Pg(bus 2) >= 0. No angle
# inequality is used. Since PGLib loads, reactances, taps, thermal limits and
# generator bounds are finite decimals, these certificate equations can be
# checked exactly over Q after decimal rationalization.
#
# For A x = b and G x <= h, a certificate satisfies exactly:
#     A^T y + G^T z = 0, z >= 0, b^T y + h^T z < 0.
#
# The numerical V3 is used only to discover sparse support. V4 independently
# verifies the resulting rays in exact SymPy rational arithmetic.

from __future__ import annotations

from fractions import Fraction
import sympy as sp

import pglib_ieee14_dc_hidden_bundle_audit_v1 as base
import pglib_ieee14_dc_cut_certificate_v2 as cutv2

Q = sp.Rational
TOP_LOAD_GOALS = 8

# Sparse supports discovered by V3 and frozen for exact verification.
# ('thermal+', branch_index) is the +flow thermal inequality.
# ('pg2_lower', None) is -Pg(bus2) <= 0.
SUPPORT = {
    1:  [('thermal+', 2)],
    3:  [('thermal+', 1), ('thermal+', 2)],
    6:  [('thermal+', 2), ('pg2_lower', None)],
    7:  [('thermal+', 8), ('pg2_lower', None)],
    9:  [('thermal+', 8)],
    14: [('thermal+', 8), ('pg2_lower', None)],
}


def q(x):
    # Python str preserves the finite decimal source values used by the V1
    # parser for this benchmark, e.g. 0.19797, 0.978, 185.17.
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
        fbus, tbus = int(br[0]), int(br[1])
        x = q(br[3])
        tap = q(br[8]) if abs(br[8]) > 1e-12 else Q(1)
        status = int(br[10])
        shift = q(br[9])
        if status != 1 or x == 0:
            continue
        if shift != 0:
            raise RuntimeError("V4 exact certificate assumes zero phase shifts")
        bmw = q(grid.base) / (x * tap)
        i, j = grid.pos[fbus], grid.pos[tbus]
        A[i, i] -= bmw
        A[i, j] += bmw
        A[j, i] += bmw
        A[j, j] -= bmw

    return A


def exact_b(grid, served_buses):
    b = sp.zeros(grid.n, 1)
    for bus in served_buses:
        b[grid.pos[bus], 0] += q(grid.load[bus])
    return b


def support_row(grid, item):
    kind, idx = item
    nv = grid.n + len(grid.active_gens)
    row = sp.zeros(1, nv)

    if kind == 'thermal+':
        br = grid.branch[idx]
        fbus, tbus = int(br[0]), int(br[1])
        x = q(br[3])
        tap = q(br[8]) if abs(br[8]) > 1e-12 else Q(1)
        shift = q(br[9])
        if shift != 0:
            raise RuntimeError("V4 support assumes zero phase shifts")
        bmw = q(grid.base) / (x * tap)
        row[0, grid.pos[fbus]] = bmw
        row[0, grid.pos[tbus]] = -bmw
        return row, q(br[5])

    if kind == 'pg2_lower':
        # V1 active generators are buses 1 and 2, in that order.
        gj = next(
            j for j, (_, bus_id, _, _) in enumerate(grid.active_gens)
            if bus_id == 2
        )
        row[0, grid.n + gj] = -1
        return row, Q(0)

    raise RuntimeError(f"unknown support item {item}")


def exact_ray(grid, outage_idx):
    A = exact_A(grid, outage_idx)
    rows = []
    hs = []
    for item in SUPPORT[outage_idx]:
        row, rhs = support_row(grid, item)
        rows.append(row)
        hs.append(rhs)

    # Unknown vector is [y ; z_support].
    M = A.T.row_join(sp.Matrix.hstack(*[r.T for r in rows]))
    basis = M.nullspace()
    if len(basis) != 1:
        raise RuntimeError(
            f"expected one-dimensional exact ray for outage {outage_idx}, "
            f"got {len(basis)}"
        )

    v = basis[0]
    y = sp.Matrix(v[:grid.n, 0])
    z = [sp.factor(v[grid.n + j, 0]) for j in range(len(rows))]

    if all(zz <= 0 for zz in z) and any(zz < 0 for zz in z):
        y = -y
        z = [-zz for zz in z]

    if any(zz < 0 for zz in z):
        raise RuntimeError(f"mixed-sign z in exact ray for outage {outage_idx}")

    # Exact stationarity.
    stationarity = A.T * y
    for zz, row in zip(z, rows):
        stationarity += row.T * zz
    if stationarity != sp.zeros(A.cols, 1):
        raise RuntimeError(f"nonzero exact stationarity for outage {outage_idx}")

    return y, z, hs


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
    masks = list(range(1, 1 << len(goal_buses)))

    def mask_to_set(mask):
        return frozenset(
            goal_buses[i]
            for i in range(len(goal_buses))
            if mask & (1 << i)
        )

    baseline = {
        mask: base.dc_feasible(grid, mask_to_set(mask), None)
        for mask in masks
    }

    minimal = []
    for oi, br in enumerate(grid.branch):
        if int(br[10]) != 1:
            continue
        after = {
            mask: base.dc_feasible(grid, mask_to_set(mask), oi)
            for mask in masks
        }
        for mask in masks:
            if not baseline[mask] or after[mask]:
                continue
            sub = (mask - 1) & mask
            proper_ok = True
            while sub:
                if not after[sub]:
                    proper_ok = False
                    break
                sub = (sub - 1) & mask
            if proper_ok:
                minimal.append((oi, mask))

    residual = []
    for oi, mask in minimal:
        if cutv2.thermal_cut_certificate(grid, mask_to_set(mask), oi) is None:
            residual.append((oi, mask))

    print("INSACERMO_PGLIB_DC_EXACT_FARKAS_V4")
    print("STATUS EXACT_RATIONAL_FARKAS_CERTIFICATE_AUDIT")
    print("ARITHMETIC SYMPY_Q_RATIONALIZED_FINITE_DECIMAL_PGLIB_DATA")
    print("TOTAL_MINIMAL_LOSSES", len(minimal))
    print("CUT_UNEXPLAINED_TARGETS", len(residual))

    exact_ok = 0
    used_outages = set()

    for oi, mask in residual:
        if oi not in SUPPORT:
            raise RuntimeError(f"no frozen exact support for residual outage {oi}")
        F = mask_to_set(mask)
        y, z, hs = exact_ray(grid, oi)
        b = exact_b(grid, F)
        value = (b.T * y)[0] + sum(hh * zz for hh, zz in zip(hs, z))

        if not value < 0:
            raise RuntimeError(
                f"exact Farkas scalar is not negative for outage {oi}, F={sorted(F)}"
            )

        exact_ok += 1
        used_outages.add(oi)

        print(
            "EXACT_CASE",
            "OUTAGE", oi,
            "ORDER", len(F),
            "BUSES", " ".join(map(str, sorted(F))),
            "NEGATIVE", 1,
            "VALUE_NUM", sp.numer(value),
            "VALUE_DEN", sp.denom(value),
            "VALUE_DECIMAL", f"{float(value):.12f}",
        )
        print(
            "  SUPPORT",
            " | ".join(
                f"{kind}:{idx if idx is not None else 'Pg2'}"
                for kind, idx in SUPPORT[oi]
            ),
        )
        print(
            "  Z_NONNEGATIVE", int(all(zz >= 0 for zz in z)),
            "EXACT_STATIONARITY", 1,
        )

    print("EXACT_FARKAS_CERTIFIED_RESIDUAL", exact_ok)
    print("EXACT_FARKAS_UNCERTIFIED_RESIDUAL", len(residual) - exact_ok)
    print("CUT_PLUS_EXACT_FARKAS_CERTIFIED_TOTAL",
          (len(minimal) - len(residual)) + exact_ok)
    print("ALL_21_MINIMAL_LOSSES_CERTIFIED",
          int((len(minimal) - len(residual)) + exact_ok == len(minimal)))
    print("EXACT_RAYS_NEEDED_FOR_OUTAGES", " ".join(map(str, sorted(used_outages))))
    print("LIMITATION exact_for_encoded_DC_LP_not_full_AC_security")
    print("RESULT COMPLETE")


if __name__ == "__main__":
    main()
