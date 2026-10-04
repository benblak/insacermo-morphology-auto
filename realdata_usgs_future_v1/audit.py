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

VERSION = "INSACERMO_REALDATA_USGS_FUTURE_NEARBY_EVENT_V1"
SOURCE = "USGS Earthquake Catalog"
START = "2020-01-01"
END = "2025-01-01"
MINMAG = 5.0
HORIZON_DAYS = 7
RADIUS_KM = 250.0

FEATURES = ("mag", "depth", "latitude", "longitude", "gap", "dmin", "rms", "nst")
QUANTILES = (2, 3, 4)
MAX_PROBES = 3

DISCOVERY_END = pd.Timestamp("2023-01-01T00:00:00Z")


def fetch_snapshot():
    params = {
        "format": "csv",
        "starttime": START,
        "endtime": END,
        "minmagnitude": str(MINMAG),
        "orderby": "time-asc",
        "limit": "20000",
    }
    url = "https://earthquake.usgs.gov/fdsnws/event/1/query?" + urllib.parse.urlencode(params)
    with urllib.request.urlopen(url, timeout=180) as resp:
        raw = resp.read()
    digest = hashlib.sha256(raw).hexdigest()
    Path("realdata_usgs_future_v1").mkdir(exist_ok=True)
    Path("realdata_usgs_future_v1/usgs_snapshot.csv").write_bytes(raw)
    df = pd.read_csv(io.BytesIO(raw))
    if len(df) >= 20000:
        raise RuntimeError("USGS_LIMIT_REACHED")
    return df, digest, url


def haversine_km(lat1, lon1, lat2, lon2):
    r = 6371.0088
    p1 = np.radians(lat1)
    p2 = np.radians(lat2)
    dp = p2 - p1
    dl = np.radians(lon2 - lon1)
    a = np.sin(dp / 2) ** 2 + np.cos(p1) * np.cos(p2) * np.sin(dl / 2) ** 2
    return 2 * r * np.arcsin(np.sqrt(a))


def future_nearby_labels(df):
    d = df.copy()
    d["time"] = pd.to_datetime(d["time"], utc=True)
    d = d.sort_values("time").reset_index(drop=True)
    ts = d["time"].astype("int64").to_numpy() / 1e9
    lat = d["latitude"].to_numpy(float)
    lon = d["longitude"].to_numpy(float)

    horizon = HORIZON_DAYS * 86400.0
    y = np.zeros(len(d), dtype=np.int8)
    j = 1
    for i in range(len(d)):
        if j < i + 1:
            j = i + 1
        while j < len(d) and ts[j] <= ts[i]:
            j += 1
        k = j
        while k < len(d) and ts[k] <= ts[i] + horizon:
            k += 1
        if j < k:
            dist = haversine_km(lat[i], lon[i], lat[j:k], lon[j:k])
            if np.any(dist <= RADIUS_KM):
                y[i] = 1
    return d, y


def fit_edges(series, q):
    x = pd.to_numeric(series, errors="coerce").dropna()
    if x.empty:
        return None
    _, edges = pd.qcut(x, q=q, retbins=True, duplicates="drop")
    edges = np.asarray(edges, dtype=float)
    if len(edges) < 2:
        return None
    edges[0] = -np.inf
    edges[-1] = np.inf
    return edges


def apply_edges(series, edges):
    x = pd.to_numeric(series, errors="coerce")
    out = np.full(len(x), -1, dtype=np.int16)
    if edges is None:
        return out
    mask = x.notna().to_numpy()
    if mask.any():
        vals = x[mask].to_numpy(float)
        out[mask] = np.digitize(vals, edges[1:-1], right=True).astype(np.int16)
    return out


def build_frozen_probes(discovery, holdout):
    probes = []
    for feat in FEATURES:
        for q in QUANTILES:
            edges = fit_edges(discovery[feat], q)
            probes.append({
                "name": f"{feat}:q{q}",
                "feature": feat,
                "q": q,
                "edges": None if edges is None else edges.tolist(),
                "disc": apply_edges(discovery[feat], edges),
                "hold": apply_edges(holdout[feat], edges),
            })
    return probes


def repair_price(labels, y):
    if labels.ndim == 1:
        labels = labels[:, None]
    _, inv = np.unique(labels, axis=0, return_inverse=True)
    total = 0
    pure_worlds = 0
    fiber_count = int(inv.max()) + 1
    for f in range(fiber_count):
        idx = inv == f
        ys = y[idx]
        n1 = int(ys.sum())
        n0 = int(len(ys) - n1)
        total += min(n0, n1)
        if n0 == 0 or n1 == 0:
            pure_worlds += len(ys)
    return int(total), int(pure_worlds), fiber_count


def combo_labels(probes, split_key, combo, n):
    if not combo:
        return np.zeros((n, 1), dtype=np.int16)
    return np.column_stack([probes[j][split_key] for j in combo])


def search_frontier(probes, y_disc):
    result = []
    for k in range(MAX_PROBES + 1):
        combos = [()] if k == 0 else itertools.combinations(range(len(probes)), k)
        best = None
        for combo in combos:
            labels = combo_labels(probes, "disc", combo, len(y_disc))
            price, pure, fibers = repair_price(labels, y_disc)
            names = tuple(probes[j]["name"] for j in combo)
            candidate = (price, -pure, fibers, names)
            if best is None or candidate < best[0]:
                best = (candidate, combo)
        cand, combo = best
        price, negpure, fibers, names = cand
        result.append({
            "k": k,
            "repair_price_discovery": int(price),
            "pure_worlds_discovery": int(-negpure),
            "fibers_discovery": int(fibers),
            "witness": list(names),
            "combo_indices": list(combo),
        })
    return result


def evaluate_holdout(frontier, probes, y_hold):
    out = []
    for point in frontier:
        combo = tuple(point["combo_indices"])
        labels = combo_labels(probes, "hold", combo, len(y_hold))
        price, pure, fibers = repair_price(labels, y_hold)
        out.append({
            "k": point["k"],
            "witness": point["witness"],
            "repair_price_discovery": point["repair_price_discovery"],
            "repair_price_holdout": int(price),
            "pure_worlds_discovery": point["pure_worlds_discovery"],
            "pure_worlds_holdout": int(pure),
            "fibers_discovery": point["fibers_discovery"],
            "fibers_holdout": int(fibers),
        })
    return out


def main():
    raw, digest, url = fetch_snapshot()
    df, y = future_nearby_labels(raw)

    disc_mask = (df["time"] < DISCOVERY_END).to_numpy()
    # Exclude the last horizon from holdout so every label is fully observable inside snapshot.
    hold_end = pd.Timestamp(END) - pd.Timedelta(days=HORIZON_DAYS)
    hold_mask = ((df["time"] >= DISCOVERY_END) & (df["time"] < hold_end)).to_numpy()

    discovery = df.loc[disc_mask].reset_index(drop=True)
    holdout = df.loc[hold_mask].reset_index(drop=True)
    y_disc = y[disc_mask]
    y_hold = y[hold_mask]

    probes = build_frozen_probes(discovery, holdout)
    frontier = search_frontier(probes, y_disc)
    evaluated = evaluate_holdout(frontier, probes, y_hold)

    report = {
        "version": VERSION,
        "source": SOURCE,
        "source_url": url,
        "snapshot_sha256": digest,
        "rows_total": int(len(df)),
        "discovery_n": int(len(discovery)),
        "holdout_n": int(len(holdout)),
        "future_contract": {
            "event_threshold_magnitude": MINMAG,
            "horizon_days": HORIZON_DAYS,
            "radius_km": RADIUS_KM,
        },
        "discovery_positive": int(y_disc.sum()),
        "holdout_positive": int(y_hold.sum()),
        "probe_family_size": len(probes),
        "frontier": evaluated,
    }
    Path("realdata_usgs_future_v1/report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True), encoding="utf-8"
    )

    print(VERSION)
    print("snapshot_sha256", digest)
    print("rows_total", len(df))
    print("discovery_n", len(discovery), "positive", int(y_disc.sum()))
    print("holdout_n", len(holdout), "positive", int(y_hold.sum()))
    print("probe_family_size", len(probes))
    for p in evaluated:
        print(
            "k", p["k"],
            "witness", p["witness"],
            "disc_repair", p["repair_price_discovery"],
            "hold_repair", p["repair_price_holdout"],
            "disc_pure", p["pure_worlds_discovery"],
            "hold_pure", p["pure_worlds_holdout"],
            "disc_fibers", p["fibers_discovery"],
            "hold_fibers", p["fibers_holdout"],
        )

    # Structural protocol checks only. Scientific endpoints are not prefilled.
    assert len(probes) == len(FEATURES) * len(QUANTILES) == 24
    assert len(frontier) == MAX_PROBES + 1 == 4
    assert len(discovery) > 1000 and len(holdout) > 500
    assert 0 < int(y_disc.sum()) < len(y_disc)
    assert 0 < int(y_hold.sum()) < len(y_hold)

    print("AUDIT_PASS")


if __name__ == "__main__":
    main()
