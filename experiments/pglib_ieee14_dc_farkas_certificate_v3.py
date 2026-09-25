# INSACERMO — PGLib IEEE-14 DC Farkas certificate audit V3
#
# Goal
# ----
# For every minimal DC loss not explained by the simple thermal-cut certificate
# of V2, construct a direct Farkas certificate for the exact linear feasibility
# model used in V1.
#
# Feasibility system:
#     A x = b_F
#     G x <= h
# where variable bounds are explicitly folded into G x <= h.
#
# Farkas certificate:
#     A^T y + G^T z = 0,  z >= 0,
#     b_F^T y + h^T z < 0.
#
# Such a certificate is a mathematical proof of infeasibility for the encoded
# DC LP, up to the printed floating-point verification tolerances.

from __future__ import annotations

import math
import numpy as np
from scipy.optimize import linprog

import pglib_ieee14_dc_hidden_bundle_audit_v1 as base
import pglib_ieee14_dc_cut_certificate_v2 as cutv2

TOP_LOAD_GOALS = 8
TOL_NEG = 1e-8
TOL_STATIONARITY = 1e-7
TOL_Z = 1e-10


def build_dc_system(grid, served_buses, outage_idx):
    n = grid.n
    gens = grid.active_gens
    ng = len(gens)
    nv = n + ng

    # Same variable bounds as V1.
    bounds = [(-10.0, 10.0)] * n
    bounds[grid.pos[grid.ref_bus]] = (0.0, 0.0)
    for _, _, pmin, pmax in gens:
        bounds.append((pmin, pmax))

    Aeq = np.zeros((n, nv))
    beq = np.zeros(n)

    for gj, (_, bus_id, _, _) in enumerate(gens):
        Aeq[grid.pos[bus_id], n + gj] += 1.0

    for bus_id in served_buses:
        beq[grid.pos[bus_id]] += grid.load[bus_id]

    Aub = []
    bub = []

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
        if status != 1 or abs(x) < 1e-12:
            continue

        i, j = grid.pos[fbus], grid.pos[tbus]
        bmw = grid.base / (x * tap)
        shift = math.radians(shift_deg)

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
            Aub.append(row)
            bub.append(rateA + bmw * shift)
            Aub.append(-row)
            bub.append(rateA - bmw * shift)

        if angmax > angmin and angmax < 360:
            row = np.zeros(nv)
            row[i] = 1.0
            row[j] = -1.0
            Aub.append(row)
            bub.append(math.radians(angmax))
            Aub.append(-row)
            bub.append(-math.radians(angmin))

    # Fold finite variable bounds into inequalities, so Farkas covers the exact
    # same feasible set as V1.
    eye = np.eye(nv)
    for j, (lo, hi) in enumerate(bounds):
        if hi is not None and np.isfinite(hi):
            Aub.append(eye[j].copy())
            bub.append(float(hi))
        if lo is not None and np.isfinite(lo):
            Aub.append(-eye[j].copy())
            bub.append(float(-lo))

    G = np.asarray(Aub, dtype=float)
    h = np.asarray(bub, dtype=float)
    return Aeq, beq, G, h


def find_normalized_farkas(A, b, G, h):
    """
    Search a bounded L1-normalized Farkas ray.
    y = yp - ym, yp,ym >=0; z>=0.
    Minimize b^T y + h^T z subject to
        A^T y + G^T z = 0
        sum(yp+ym+z) <= 1.
    A strictly negative optimum yields a certificate.
    """
    meq, nv = A.shape
    mineq = G.shape[0]

    c = np.concatenate([b, -b, h])

    # Stationarity equations.
    M = np.hstack([A.T, -A.T, G.T])
    rhs = np.zeros(nv)

    norm_row = np.ones(2 * meq + mineq)

    res = linprog(
        c,
        A_ub=np.asarray([norm_row]),
        b_ub=np.asarray([1.0]),
        A_eq=M,
        b_eq=rhs,
        bounds=[(0.0, None)] * (2 * meq + mineq),
        method="highs",
        options={"presolve": True},
    )
    if not res.success:
        return None

    yp = res.x[:meq]
    ym = res.x[meq:2 * meq]
    z = res.x[2 * meq:]
    y = yp - ym

    value = float(b @ y + h @ z)
    stationarity = A.T @ y + G.T @ z
    return {
        "y": y,
        "z": z,
        "value": value,
        "stationarity_inf": float(np.max(np.abs(stationarity))) if len(stationarity) else 0.0,
        "z_min": float(np.min(z)) if len(z) else 0.0,
        "l1": float(np.sum(np.abs(y)) + np.sum(z)),
        "solver_fun": float(res.fun),
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
            goal_buses[i] for i in range(len(goal_buses))
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

    cut_covered = []
    residual = []
    for oi, mask in minimal:
        F = mask_to_set(mask)
        cert = cutv2.thermal_cut_certificate(grid, F, oi)
        if cert is None:
            residual.append((oi, mask))
        else:
            cut_covered.append((oi, mask))

    farkas_ok = []
    farkas_fail = []

    print("INSACERMO_PGLIB_DC_FARKAS_CERTIFICATE_V3")
    print("STATUS DIRECT_FARKAS_CERTIFICATE_AUDIT")
    print("MODEL SAME_DC_LINEAR_FEASIBILITY_MODEL_AS_V1")
    print("TOTAL_MINIMAL_LOSSES", len(minimal))
    print("SIMPLE_CUT_CERTIFIED", len(cut_covered))
    print("FARKAS_TARGET_RESIDUAL", len(residual))

    for oi, mask in residual:
        F = mask_to_set(mask)
        A, b, G, h = build_dc_system(grid, F, oi)
        cert = find_normalized_farkas(A, b, G, h)
        ok = (
            cert is not None
            and cert["value"] < -TOL_NEG
            and cert["stationarity_inf"] <= TOL_STATIONARITY
            and cert["z_min"] >= -TOL_Z
        )
        if ok:
            farkas_ok.append((oi, mask, cert))
        else:
            farkas_fail.append((oi, mask, cert))

        print(
            "RESIDUAL_CASE",
            "OUTAGE", oi,
            "ORDER", len(F),
            "BUSES", " ".join(map(str, sorted(F))),
            "CERTIFIED", int(ok),
            "FARKAS_VALUE", f"{cert['value']:.12e}" if cert else "NA",
            "STATIONARITY_INF", f"{cert['stationarity_inf']:.12e}" if cert else "NA",
            "Z_MIN", f"{cert['z_min']:.12e}" if cert else "NA",
            "L1", f"{cert['l1']:.12e}" if cert else "NA",
        )

        if ok:
            # Decompose the Farkas scalar into a bundle-independent constant
            # and per-goal load contributions. This reveals whether the dual
            # certificate itself induces an additive capacity-like threshold.
            y = cert["y"]
            # b0: same outage with no served goal loads.
            _, b0, _, _ = build_dc_system(grid, frozenset(), oi)
            constant = float(b0 @ y + h @ cert["z"])
            weights = {}
            for bus in goal_buses:
                contribution = float(grid.load[bus] * y[grid.pos[bus]])
                weights[bus] = contribution
            reconstructed = constant + sum(weights[b] for b in F)
            print("  DUAL_CONSTANT", f"{constant:.12e}")
            print("  DUAL_GOAL_TERMS", " ".join(f"{b}:{weights[b]:+.12e}" for b in sorted(F)))
            print("  DUAL_RECONSTRUCTED_VALUE", f"{reconstructed:.12e}")

    print("FARKAS_CERTIFIED_RESIDUAL", len(farkas_ok))
    print("FARKAS_UNCERTIFIED_RESIDUAL", len(farkas_fail))
    print("CUT_PLUS_FARKAS_CERTIFIED_TOTAL", len(cut_covered) + len(farkas_ok))
    print("ALL_MINIMAL_LOSSES_CERTIFIED", int(len(cut_covered) + len(farkas_ok) == len(minimal)))

    # Re-check proper-subset feasibility for every Farkas-certified residual.
    proper_checked = 0
    proper_all_feasible = 0
    for oi, mask, cert in farkas_ok:
        total = 0
        good = 0
        for sub in masks:
            if sub != mask and (sub & mask) == sub:
                total += 1
                if base.dc_feasible(grid, mask_to_set(sub), oi):
                    good += 1
        proper_checked += 1
        if total == good:
            proper_all_feasible += 1
        print(
            "MINIMALITY_RECHECK",
            "OUTAGE", oi,
            "ORDER", int(mask).bit_count(),
            "PROPER_TOTAL", total,
            "PROPER_FEASIBLE", good,
            "ALL", int(total == good),
        )

    print("FARKAS_CASES_WITH_ALL_PROPER_SUBBUNDLES_FEASIBLE", proper_all_feasible)
    print("LIMITATION certificates_are_for_the_encoded_DC_LP_not_full_AC_security")
    print("RESULT COMPLETE")


if __name__ == "__main__":
    main()
