from __future__ import annotations

import hashlib
import itertools
import math
from collections import Counter, defaultdict

import numpy as np
import pandas as pd
import statsmodels.api as sm
import statsmodels.datasets.modechoice.data as modechoice_data
import inspect
import os

DATA_SHA256 = "d2d72c1db440f8ffce01f58ed39fc1145569ec1703970dac1636c154fc01fd8e"

BASE_ACTIONS = (2, 3, 4)       # train, bus, car
EXPANDED_ACTIONS = (1, 2, 3, 4)  # + air
FEATURES = ("gc", "total_time", "invc", "invt", "ttme")
QUANTILES = (2, 3, 4)


def load_data():
    path = os.path.join(os.path.dirname(inspect.getfile(modechoice_data)), "modechoice.csv")
    raw = open(path, "rb").read()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != DATA_SHA256:
        raise RuntimeError(f"DATA_SHA256_MISMATCH:{digest}")
    df = sm.datasets.modechoice.load_pandas().data.copy()
    df["total_time"] = df["ttme"] + df["invt"]
    return df, digest


def pareto_profiles(df: pd.DataFrame):
    profiles = {}
    for ind, g in df.groupby("individual"):
        admissible = []
        rows = g.sort_values("mode")
        for _, r in rows.iterrows():
            dominated = False
            for _, s in rows.iterrows():
                if s["mode"] == r["mode"]:
                    continue
                if (
                    s["gc"] <= r["gc"]
                    and s["total_time"] <= r["total_time"]
                    and (
                        s["gc"] < r["gc"]
                        or s["total_time"] < r["total_time"]
                    )
                ):
                    dominated = True
                    break
            if not dominated:
                admissible.append(int(r["mode"]))
        profiles[int(ind)] = tuple(sorted(admissible))
    return profiles


def repair_price(labels, profiles, individuals, actions):
    by_fiber = defaultdict(list)
    for i in individuals:
        by_fiber[labels[i]].append(i)

    total = 0
    detail = {}
    for fiber, members in by_fiber.items():
        counts = {a: sum(a in profiles[i] for i in members) for a in actions}
        best_action = max(actions, key=lambda a: (counts[a], -a))
        missing = [i for i in members if best_action not in profiles[i]]
        total += len(missing)
        detail[fiber] = {
            "members": members,
            "best_action": best_action,
            "repair_worlds": missing,
            "counts": counts,
        }
    return total, detail


def entropy(labels, individuals):
    c = Counter(labels[i] for i in individuals)
    n = len(individuals)
    return -sum((v / n) * math.log2(v / n) for v in c.values())


def build_probe_family(df, individuals):
    per_individual = {
        int(i): g.set_index("mode")
        for i, g in df[df["individual"].isin(individuals)].groupby("individual")
    }
    probes = []
    for mode in BASE_ACTIONS:
        for feat in FEATURES:
            vals = pd.Series(
                {i: float(per_individual[i].loc[float(mode), feat]) for i in individuals}
            )
            for q in QUANTILES:
                cats = pd.qcut(vals, q, duplicates="drop")
                labels = {i: str(cats.loc[i]) for i in individuals}
                probes.append(((mode, feat, q), labels))
    return probes


def joint_labels(probes, indices, individuals):
    if not indices:
        return {i: 0 for i in individuals}
    return {
        i: tuple(probes[j][1][i] for j in indices)
        for i in individuals
    }


def exhaustive_best_k(probes, profiles, individuals, k):
    if k == 0:
        labels = {i: 0 for i in individuals}
        price, detail = repair_price(labels, profiles, individuals, BASE_ACTIONS)
        return {
            "k": 0,
            "repair_price": price,
            "entropy_bits": 0.0,
            "fibers": 1,
            "probes": [],
            "detail": detail,
        }

    best = None
    for idxs in itertools.combinations(range(len(probes)), k):
        labels = joint_labels(probes, idxs, individuals)
        price, detail = repair_price(labels, profiles, individuals, BASE_ACTIONS)
        candidate = (
            price,
            entropy(labels, individuals),
            len(set(labels.values())),
            tuple(probes[j][0] for j in idxs),
            detail,
        )
        if best is None or candidate[:4] < best[:4]:
            best = candidate

    price, h, fibers, names, detail = best
    return {
        "k": k,
        "repair_price": price,
        "entropy_bits": h,
        "fibers": fibers,
        "probes": [list(x) for x in names],
        "detail": detail,
    }


def main():
    df, digest = load_data()
    profiles = pareto_profiles(df)

    # Frozen cohort: every traveler must already be actionable under train/bus/car.
    cohort = sorted(
        i for i, p in profiles.items()
        if any(a in p for a in BASE_ACTIONS)
    )

    base_labels = {i: 0 for i in cohort}
    base_price, _ = repair_price(base_labels, profiles, cohort, BASE_ACTIONS)
    expanded_price, expanded_detail = repair_price(
        base_labels, profiles, cohort, EXPANDED_ACTIONS
    )

    probes = build_probe_family(df, cohort)
    best = [exhaustive_best_k(probes, profiles, cohort, k) for k in range(5)]

    print("INSACERMO_REALDATA_CAPABILITY_VS_PROBES_V1")
    print("dataset_sha256", digest)
    print("rows", len(df))
    print("individuals", df["individual"].nunique())
    print("cohort_n", len(cohort))
    print("probe_family_size", len(probes))
    print("base_zero_probe_repair_price", base_price)
    print("expanded_zero_probe_repair_price", expanded_price)

    for r in best:
        print(
            "best_k",
            r["k"],
            "repair_price",
            r["repair_price"],
            "entropy_bits",
            f'{r["entropy_bits"]:.12f}',
            "fibers",
            r["fibers"],
            "probes",
            r["probes"],
        )

    expanded_repair_worlds = []
    for d in expanded_detail.values():
        expanded_repair_worlds.extend(d["repair_worlds"])
    print("expanded_zero_probe_repair_worlds", sorted(expanded_repair_worlds))

    assert len(df) == 840
    assert df["individual"].nunique() == 210
    assert len(cohort) == 147
    assert len(probes) == 45

    # Primary frozen endpoints.
    assert base_price == 21
    assert expanded_price == 2
    assert [r["repair_price"] for r in best] == [21, 21, 11, 5, 2]
    assert best[4]["probes"] == [
        [2, "total_time", 4],
        [2, "invc", 3],
        [3, "gc", 4],
        [4, "invc", 4],
    ]
    assert sorted(expanded_repair_worlds) == [175, 191]

    # Main empirical comparison:
    # one added real capability with zero probe reaches the same repair price
    # as the best four-probe plan in the declared exhaustive probe family.
    assert expanded_price == best[4]["repair_price"]
    assert expanded_price < best[3]["repair_price"]

    print("VERDICT CAPABILITY_ZERO_PROBE_EQUALS_BEST_FOUR_PROBE_REPAIR_PRICE")
    print("PASS")


if __name__ == "__main__":
    main()
