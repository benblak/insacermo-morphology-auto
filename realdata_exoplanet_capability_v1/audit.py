from __future__ import annotations

import hashlib
import io
import itertools
import json
import math
import urllib.parse
import urllib.request
from pathlib import Path

import numpy as np
import pandas as pd

VERSION = "INSACERMO_REALDATA_EXOPLANET_CAPABILITY_VS_INFORMATION_V1"
SOURCE = "NASA Exoplanet Archive / PSCompPars"
METHODS = ("transit", "rv", "imaging", "microlensing")
FLAGS = {
    "transit": "tran_flag",
    "rv": "rv_flag",
    "imaging": "ima_flag",
    "microlensing": "micro_flag",
}
FEATURES = (
    "pl_orbper",
    "pl_rade",
    "pl_bmasse",
    "pl_orbsmax",
    "pl_eqt",
    "st_teff",
    "sy_dist",
)
QUANTILES = (2, 3, 4)
MAX_PROBES = 3

QUERY = """select pl_name,tran_flag,rv_flag,ima_flag,micro_flag,
pl_orbper,pl_rade,pl_bmasse,pl_orbsmax,pl_eqt,st_teff,sy_dist
from pscomppars order by pl_name"""


def fetch_snapshot() -> tuple[pd.DataFrame, bytes, str]:
    url = (
        "https://exoplanetarchive.ipac.caltech.edu/TAP/sync?query="
        + urllib.parse.quote_plus(" ".join(QUERY.split()))
        + "&format=csv"
    )
    with urllib.request.urlopen(url, timeout=180) as resp:
        raw = resp.read()
    digest = hashlib.sha256(raw).hexdigest()
    Path("realdata_exoplanet_capability_v1").mkdir(exist_ok=True)
    Path("realdata_exoplanet_capability_v1/nasa_pscomppars_snapshot.csv").write_bytes(raw)
    df = pd.read_csv(io.BytesIO(raw))
    return df, raw, digest


def clean_flags(df: pd.DataFrame) -> pd.DataFrame:
    out = df.copy()
    for col in FLAGS.values():
        out[col] = pd.to_numeric(out[col], errors="coerce").fillna(0).astype(int).clip(0, 1)
    return out


def make_probe_labels(series: pd.Series, q: int) -> np.ndarray:
    x = pd.to_numeric(series, errors="coerce")
    labels = np.full(len(x), -1, dtype=np.int16)
    mask = x.notna().to_numpy()
    if mask.sum() == 0:
        return labels
    vals = x[mask]
    try:
        bins = pd.qcut(vals, q=q, labels=False, duplicates="drop")
        labels[mask] = np.asarray(bins, dtype=np.int16)
    except ValueError:
        labels[mask] = 0
    return labels


def build_probe_family(df: pd.DataFrame):
    probes = []
    for feat in FEATURES:
        for q in QUANTILES:
            probes.append({
                "name": f"{feat}:q{q}",
                "feature": feat,
                "q": q,
                "labels": make_probe_labels(df[feat], q),
            })
    return probes


def repair_price(labels: np.ndarray, avail: np.ndarray) -> int:
    # Exact minimum unit edge-addition repair:
    # in each observation fiber choose the action already feasible in the
    # largest number of worlds; repair the remaining worlds in that fiber.
    _, inverse = np.unique(labels, axis=0, return_inverse=True)
    total = 0
    for f in range(int(inverse.max()) + 1):
        idx = inverse == f
        n = int(idx.sum())
        counts = avail[idx].sum(axis=0)
        total += n - int(counts.max())
    return int(total)


def labels_for_combo(probes, combo, row_idx):
    if not combo:
        return np.zeros((len(row_idx), 1), dtype=np.int16)
    return np.column_stack([probes[j]["labels"][row_idx] for j in combo])


def best_frontier(probes, row_idx, avail):
    frontier = []
    for k in range(MAX_PROBES + 1):
        best = None
        combos = [()] if k == 0 else itertools.combinations(range(len(probes)), k)
        for combo in combos:
            labels = labels_for_combo(probes, combo, row_idx)
            price = repair_price(labels, avail)
            names = tuple(probes[j]["name"] for j in combo)
            candidate = (price, names)
            if best is None or candidate < best:
                best = candidate
        frontier.append({
            "k": k,
            "repair_price": int(best[0]),
            "witness": list(best[1]),
        })
    return frontier


def scenario(df, probes, base_methods, added_method):
    base_methods = tuple(base_methods)
    expanded_methods = base_methods + (added_method,)

    base_cols = [FLAGS[m] for m in base_methods]
    exp_cols = [FLAGS[m] for m in expanded_methods]

    cohort_mask = df[base_cols].max(axis=1).to_numpy() == 1
    row_idx = np.flatnonzero(cohort_mask)

    base_avail = df.loc[cohort_mask, base_cols].to_numpy(dtype=np.int8)
    exp_avail = df.loc[cohort_mask, exp_cols].to_numpy(dtype=np.int8)

    one = np.zeros((len(row_idx), 1), dtype=np.int16)
    base_zero = repair_price(one, base_avail)
    expanded_zero = repair_price(one, exp_avail)
    frontier = best_frontier(probes, row_idx, base_avail)

    match_k = None
    for point in frontier:
        if point["repair_price"] <= expanded_zero:
            match_k = point["k"]
            break

    return {
        "base_methods": list(base_methods),
        "added_method": added_method,
        "cohort_n": int(len(row_idx)),
        "base_zero_probe_repair": int(base_zero),
        "expanded_zero_probe_repair": int(expanded_zero),
        "absolute_repair_reduction": int(base_zero - expanded_zero),
        "fractional_repair_reduction": (
            0.0 if base_zero == 0 else float((base_zero - expanded_zero) / base_zero)
        ),
        "base_probe_frontier": frontier,
        "probes_needed_to_match_added_capability": (
            match_k if match_k is not None else f">{MAX_PROBES}"
        ),
    }


def main():
    df, raw, digest = fetch_snapshot()
    df = clean_flags(df)
    probes = build_probe_family(df)

    scenarios = []

    # Fully predeclared exhaustive capability additions:
    # every 2-method base + one of the remaining methods,
    # and every 3-method base + the remaining method.
    for base_size in (2, 3):
        for base in itertools.combinations(METHODS, base_size):
            for added in METHODS:
                if added not in base:
                    scenarios.append(scenario(df, probes, base, added))

    scenarios.sort(
        key=lambda s: (
            -s["absolute_repair_reduction"],
            -s["fractional_repair_reduction"],
            tuple(s["base_methods"]),
            s["added_method"],
        )
    )

    report = {
        "version": VERSION,
        "source": SOURCE,
        "query": " ".join(QUERY.split()),
        "snapshot_sha256": digest,
        "rows": int(len(df)),
        "probe_family_size": int(len(probes)),
        "max_probes_exhaustive": MAX_PROBES,
        "scenario_count": len(scenarios),
        "scenarios": scenarios,
    }
    Path("realdata_exoplanet_capability_v1/report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True), encoding="utf-8"
    )

    print(VERSION)
    print("snapshot_sha256", digest)
    print("rows", len(df))
    print("probe_family_size", len(probes))
    print("scenario_count", len(scenarios))
    print("TOP_SCENARIOS")
    for s in scenarios[:8]:
        print(json.dumps(s, sort_keys=True))

    top = scenarios[0]
    print("TOP_BASE", "+".join(top["base_methods"]))
    print("TOP_ADDED", top["added_method"])
    print("TOP_COHORT_N", top["cohort_n"])
    print("TOP_BASE_ZERO", top["base_zero_probe_repair"])
    print("TOP_EXPANDED_ZERO", top["expanded_zero_probe_repair"])
    print("TOP_ABS_REDUCTION", top["absolute_repair_reduction"])
    print("TOP_FRAC_REDUCTION", f'{top["fractional_repair_reduction"]:.12f}')
    print("TOP_FRONTIER", [x["repair_price"] for x in top["base_probe_frontier"]])
    print("TOP_MATCH_K", top["probes_needed_to_match_added_capability"])

    # Structural sanity checks only; scientific endpoints are not pre-filled.
    assert len(probes) == len(FEATURES) * len(QUANTILES) == 21
    assert len(scenarios) == 16
    assert len(df) > 1000
    assert all(s["expanded_zero_probe_repair"] <= s["base_zero_probe_repair"] for s in scenarios)
    print("AUDIT_PASS")


if __name__ == "__main__":
    main()
