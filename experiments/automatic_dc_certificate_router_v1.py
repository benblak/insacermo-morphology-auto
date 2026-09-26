# INSACERMO — Automatic DC certificate router V1
#
# For each minimal capability loss in the IEEE-14 DC benchmark, route the
# obstruction through increasingly general certificates WITHOUT knowing in
# advance which certificate will succeed:
#
#   1. SIMPLE_THERMAL_CUT
#   2. LP_FARKAS_DUAL
#   3. exact rational reconstruction of the sparse Farkas support when all
#      selected rows belong to the finite-decimal/rational part of the model.
#
# The router reports its own certificate class and decision-facing status.
# It does not hard-code the known 11/10 split.
#
# Scope: encoded DC LP only; not an AC-security theorem.

from __future__ import annotations

import math
import numpy as np
import sympy as sp

import pglib_ieee14_dc_hidden_bundle_audit_v1 as base
import pglib_ieee14_dc_cut_certificate_v2 as cutv2
import pglib_ieee14_dc_farkas_certificate_v3 as farkasv3

TOP_LOAD_GOALS = 8
SUPPORT_TOL = 1e-8
NEG_TOL = 1e-8
STAT_TOL = 1e-7


def q(x):
    return sp.Rational(str(float(x)))


def exact_equalities(grid, served_buses, outage_idx):
    n = grid.n
    ng = len(grid.active_gens)
    nv = n + ng
    A = sp.zeros(n, nv)
    b = sp.zeros(n, 1)

    for gj, (_, bus_id, _, _) in enumerate(grid.active_gens):
        A[grid.pos[bus_id], n + gj] += 1

    for bus_id in served_buses:
        b[grid.pos[bus_id], 0] += q(grid.load[bus_id])

    for li, br in enumerate(grid.branch):
        if li == outage_idx:
            continue
        status = int(br[10])
        x = q(br[3])
        if status != 1 or x == 0:
            continue
        fbus, tbus = int(br[0]), int(br[1])
        tap = q(br[8]) if abs(br[8]) > 1e-12 else sp.Integer(1)
        # PGLib case used here has zero phase shifts. Keep this explicit.
        shift_deg = q(br[9])
        if shift_deg != 0:
            return None
        bmw = q(grid.base) / (x * tap)
        i, j = grid.pos[fbus], grid.pos[tbus]
        A[i, i] -= bmw
        A[i, j] += bmw
        A[j, i] += bmw
        A[j, j] -= bmw
    return A, b


def exact_inequality_rows(grid, outage_idx):
    """Rebuild V3 G,h order with row metadata.

    A row is marked exact-rational only when both coefficients and RHS are
    finite-decimal rationals in this benchmark. Angle bounds contain pi/180 in
    their RHS and are intentionally left non-rational for this exactifier.
    """
    n = grid.n
    gens = grid.active_gens
    ng = len(gens)
    nv = n + ng
    rows = []

    for li, br in enumerate(grid.branch):
        if li == outage_idx:
            continue
        fbus, tbus = int(br[0]), int(br[1])
        x = q(br[3])
        rateA = q(br[5])
        tap = q(br[8]) if abs(br[8]) > 1e-12 else sp.Integer(1)
        shift_deg = q(br[9])
        status = int(br[10])
        angmin, angmax = br[11], br[12]
        if status != 1 or x == 0:
            continue

        i, j = grid.pos[fbus], grid.pos[tbus]
        bmw = q(grid.base) / (x * tap)

        if rateA > 0:
            if shift_deg != 0:
                return None
            rp = sp.zeros(1, nv)
            rp[0, i] = bmw
            rp[0, j] = -bmw
            rows.append((rp, rateA, f"thermal+:{li}", True))

            rm = -rp
            rows.append((rm, rateA, f"thermal-:{li}", True))

        if angmax > angmin and angmax < 360:
            # Same row order as V3, but mark angle RHS as not rational-exact
            # because radians introduce pi.
            rp = sp.zeros(1, nv)
            rp[0, i] = 1
            rp[0, j] = -1
            rows.append((rp, sp.pi * q(angmax) / 180, f"angle+:{li}", False))
            rows.append((-rp, -sp.pi * q(angmin) / 180, f"angle-:{li}", False))

    # Same finite bounds as V3.
    bounds = [(-10.0, 10.0)] * n
    bounds[grid.pos[grid.ref_bus]] = (0.0, 0.0)
    for _, _, pmin, pmax in gens:
        bounds.append((pmin, pmax))

    for j, (lo, hi) in enumerate(bounds):
        if hi is not None and np.isfinite(hi):
            r = sp.zeros(1, nv)
            r[0, j] = 1
            rows.append((r, q(hi), f"bound_hi:{j}", True))
        if lo is not None and np.isfinite(lo):
            r = sp.zeros(1, nv)
            r[0, j] = -1
            rows.append((r, q(-lo), f"bound_lo:{j}", True))
    return rows


def automatic_exactify(grid, served_buses, outage_idx, numerical_cert):
    znum = numerical_cert["z"]
    support_idx = [i for i, zz in enumerate(znum) if zz > SUPPORT_TOL]
    if not support_idx:
        return None

    eq = exact_equalities(grid, served_buses, outage_idx)
    rows = exact_inequality_rows(grid, outage_idx)
    if eq is None or rows is None:
        return None
    A, b = eq

    selected = [rows[i] for i in support_idx]
    # Require rational-exact rows for V1 exact certification.
    if not all(rec[3] for rec in selected):
        return {
            "status": "UNSUPPORTED_IRRATIONAL_ROW",
            "support": [rec[2] for rec in selected],
        }

    M = A.T.row_join(sp.Matrix.hstack(*[rec[0].T for rec in selected]))
    null = M.nullspace()
    if len(null) != 1:
        return {
            "status": f"NULLSPACE_DIM_{len(null)}",
            "support": [rec[2] for rec in selected],
        }

    v = null[0]
    y = sp.Matrix(v[:grid.n, 0])
    z = [sp.factor(v[grid.n + j, 0]) for j in range(len(selected))]

    # Orient so z is nonnegative.
    if all(zz <= 0 for zz in z) and any(zz < 0 for zz in z):
        y = -y
        z = [-zz for zz in z]
    if any(zz < 0 for zz in z):
        return {
            "status": "MIXED_SIGN_Z",
            "support": [rec[2] for rec in selected],
        }

    stationarity = A.T * y
    for zz, rec in zip(z, selected):
        stationarity += rec[0].T * zz
    exact_stationarity = stationarity == sp.zeros(A.cols, 1)
    if not exact_stationarity:
        return {
            "status": "NONZERO_STATIONARITY",
            "support": [rec[2] for rec in selected],
        }

    value = (b.T * y)[0] + sum(rec[1] * zz for zz, rec in zip(z, selected))
    # All selected rows are rational, so value is rational.
    negative = bool(value < 0)
    return {
        "status": "EXACT_RATIONAL_FARKAS" if negative else "NONNEGATIVE_EXACT_RAY",
        "support": [rec[2] for rec in selected],
        "value": value,
        "negative": negative,
        "z_nonnegative": all(zz >= 0 for zz in z),
        "stationarity": exact_stationarity,
    }


def route_certificate(grid, served_buses, outage_idx):
    # Tier 1: simple physical cut.
    cut = cutv2.thermal_cut_certificate(grid, served_buses, outage_idx)
    if cut is not None:
        return {
            "route": "CUT",
            "strength": "EXACT_STRUCTURAL",
            "proof": {
                "demand": cut["demand"],
                "capacity": cut["capacity"],
                "margin": cut["margin"],
                "side": sorted(cut["S"]),
            },
        }

    # Tier 2: generic LP dual/Farkas.
    A, b, G, h = farkasv3.build_dc_system(grid, served_buses, outage_idx)
    fc = farkasv3.find_normalized_farkas(A, b, G, h)
    if fc is None:
        return {"route": "NONE", "strength": "UNCERTIFIED", "proof": {}}

    num_ok = (
        fc["value"] < -NEG_TOL
        and fc["stationarity_inf"] <= STAT_TOL
        and fc["z_min"] >= -1e-10
    )
    if not num_ok:
        return {
            "route": "FARKAS",
            "strength": "NUMERICAL_FAILED_VERIFICATION",
            "proof": fc,
        }

    exact = automatic_exactify(grid, served_buses, outage_idx, fc)
    if exact and exact.get("status") == "EXACT_RATIONAL_FARKAS":
        return {
            "route": "FARKAS",
            "strength": "EXACT_RATIONAL",
            "proof": exact,
        }

    return {
        "route": "FARKAS",
        "strength": "VERIFIED_NUMERICAL_ONLY",
        "proof": {"numerical": fc, "exactification": exact},
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

    counts = {}
    exact_count = 0
    uncertified = 0

    print("INSACERMO_AUTOMATIC_DC_CERTIFICATE_ROUTER_V1")
    print("STATUS AUTOMATIC_CERTIFICATE_SELECTION")
    print("ROUTING_ORDER CUT_THEN_FARKAS_THEN_EXACTIFY")
    print("TOTAL_MINIMAL_LOSSES", len(minimal))

    for oi, mask in minimal:
        F = mask_to_set(mask)
        out = route_certificate(grid, F, oi)
        key = (out["route"], out["strength"])
        counts[key] = counts.get(key, 0) + 1

        is_exact = out["strength"] in ("EXACT_STRUCTURAL", "EXACT_RATIONAL")
        exact_count += int(is_exact)
        uncertified += int(out["strength"] == "UNCERTIFIED")

        print(
            "ROUTED_CASE",
            "OUTAGE", oi,
            "ORDER", len(F),
            "BUSES", " ".join(map(str, sorted(F))),
            "ROUTE", out["route"],
            "STRENGTH", out["strength"],
        )

        if out["route"] == "CUT":
            p = out["proof"]
            print(
                "  CUT_DEMAND", f"{p['demand']:.6f}",
                "CUT_CAPACITY", f"{p['capacity']:.6f}",
                "CUT_MARGIN", f"{p['margin']:.6f}",
            )
        elif out["strength"] == "EXACT_RATIONAL":
            p = out["proof"]
            print(
                "  FARKAS_SUPPORT", " | ".join(p["support"]),
                "VALUE_NUM", sp.numer(p["value"]),
                "VALUE_DEN", sp.denom(p["value"]),
                "EXACT_STATIONARITY", int(p["stationarity"]),
                "Z_NONNEGATIVE", int(p["z_nonnegative"]),
            )

    for (route, strength), count in sorted(counts.items()):
        print("ROUTER_COUNT", route, strength, count)

    print("EXACTLY_CERTIFIED", exact_count)
    print("UNCERTIFIED", uncertified)
    print("ALL_MINIMAL_LOSSES_EXACTLY_CERTIFIED", int(exact_count == len(minimal)))
    print("DECISION_INTERFACE",
          "EXACT_CERTIFICATE=>REFUSE_DESTRUCTIVE_TRANSFORMATION_UNDER_CONTRACT")
    print("PROBE_INTERFACE",
          "UNCERTIFIED_OR_NUMERICAL_ONLY=>PROBE_OR_ESCALATE_CERTIFICATE")
    print("LIMITATION encoded_DC_LP_only_not_AC_security")
    print("RESULT COMPLETE")


if __name__ == "__main__":
    main()
