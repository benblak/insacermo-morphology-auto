import hashlib
import itertools
import os
import re

import numpy as np

MODEL_PATH = os.environ.get("INSACERMO_TCELL_BNET", "/tmp/tcell_diff.bnet")
EXPECTED_SHA256 = "a3cd91f9d85d2ffbd73001ab5deb6094c40aa29927143836d8e84d9d3c91b2c1"

PHENOTYPES = {
    "Th0": {"Tbet": False, "GATA3": False, "IFNg": False, "IL4": False},
    "Th1": {"Tbet": True, "GATA3": False, "IFNg": True},
    "Th2": {"GATA3": True, "Tbet": False, "IL4": True},
}
PRECURSOR_MARKERS = {"Tbet": False, "GATA3": False, "IFNg": False, "IL4": False}
EXPECTED_RULED = {
    "IL4","IL18R","GATA3","IRAK","IL10R","IFNgR","STAT1","IFNbR","IL10",
    "SOCS1","STAT3","Tbet","IL12R","STAT6","IL4R","JAK1","IFNg","NFAT","STAT4"
}
EXPECTED_INPUTS = {"IFNb","IL12","IL18","TCR"}


def parse_bnet(path):
    raw = open(path, "rb").read()
    sha = hashlib.sha256(raw).hexdigest()
    if sha != EXPECTED_SHA256:
        raise RuntimeError(f"Unexpected model SHA256 {sha}")
    rules = {}
    for raw_line in raw.decode("utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        lhs, rhs = line.split(",", 1)
        rules[lhs.strip()] = rhs.strip()
    names = set(rules)
    for rhs in rules.values():
        names.update(re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", rhs))
    inputs = names - set(rules)
    if set(rules) != EXPECTED_RULED or inputs != EXPECTED_INPUTS:
        raise RuntimeError("Pinned model structure differs from expected 19-rule/4-input network")
    return sha, rules, sorted(rules), sorted(inputs)


def env_assignments(inputs):
    for bits in itertools.product((False, True), repeat=len(inputs)):
        yield dict(zip(inputs, bits))


def phenotype_mask(values, phenotype):
    mask = np.ones(values[next(iter(values))].shape, dtype=bool)
    for node, val in phenotype.items():
        mask &= (values[node] == val)
    return mask


def precursor_mask(values):
    return phenotype_mask(values, PRECURSOR_MARKERS)


def evaluate_rules(states, ruled, env):
    idx = {n: i for i, n in enumerate(ruled)}
    def b(n):
        if n in idx:
            return ((states >> np.uint32(idx[n])) & np.uint32(1)).astype(bool)
        return np.full(states.shape, bool(env[n]), dtype=bool)

    # Exact vectorized transcription of the pinned tcell_diff.bnet rules.
    v = {}
    v["IL4"]   = b("GATA3") & ~b("STAT1")
    v["IL18R"] = b("IL18") & ~b("STAT6")
    v["GATA3"] = (b("GATA3") & ~b("Tbet")) | (b("STAT6") & ~b("Tbet"))
    v["IRAK"]  = b("IL18R")
    v["IL10R"] = b("IL10")
    v["IFNgR"] = b("IFNg")
    v["STAT1"] = b("JAK1") | b("IFNbR")
    v["IFNbR"] = b("IFNb")
    v["IL10"]  = b("GATA3")
    v["SOCS1"] = b("Tbet") | b("STAT1")
    v["STAT3"] = b("IL10R")
    v["Tbet"]  = (b("Tbet") & ~b("GATA3")) | (b("STAT1") & ~b("GATA3"))
    v["IL12R"] = b("IL12")
    v["STAT6"] = b("IL4R")
    v["IL4R"]  = b("IL4") & ~b("SOCS1")
    v["JAK1"]  = b("IFNgR") & ~b("SOCS1")
    v["IFNg"]  = (b("IRAK") & ~b("STAT3")) | (b("NFAT") & ~b("STAT3")) | (b("STAT4") & ~b("STAT3")) | (b("Tbet") & ~b("STAT3"))
    v["NFAT"]  = b("TCR")
    v["STAT4"] = b("IL12R") & ~b("GATA3")
    return v


def fixed_mask(states, ruled, values):
    out = np.ones(states.shape, dtype=bool)
    for i, n in enumerate(ruled):
        bit = ((states >> np.uint32(i)) & np.uint32(1)).astype(bool)
        out &= (bit == values[n])
    return out


def backward_distances(states, ruled, values, target_mask):
    # Exact shortest reverse reachability under fully asynchronous one-node updates.
    n = len(states)
    dist = np.full(n, -1, dtype=np.int16)
    frontier = target_mask.copy()
    dist[frontier] = 0
    level = 0
    indices = np.arange(n, dtype=np.uint32)

    while frontier.any():
        nxt = np.zeros(n, dtype=bool)
        for i, node in enumerate(ruled):
            bitmask = np.uint32(1 << i)
            current_bit = ((states >> np.uint32(i)) & np.uint32(1)).astype(bool)
            enabled = values[node] != current_bit
            successor = indices ^ bitmask
            # y is a predecessor of x iff updating node i in y flips to x.
            pred = enabled & frontier[successor]
            nxt |= pred
        nxt &= (dist < 0)
        if not nxt.any():
            break
        level += 1
        if level >= np.iinfo(np.int16).max:
            raise RuntimeError("Distance overflow")
        dist[nxt] = level
        frontier = nxt
    return dist


def fmt_env(env):
    return ",".join(f"{k}={int(env[k])}" for k in sorted(env))


sha, rules, ruled, inputs = parse_bnet(MODEL_PATH)
N = 1 << len(ruled)
states = np.arange(N, dtype=np.uint32)

print("INSACERMO_EXACT_TCELL_UNBOUNDED_COMMON_BRANCHING_V1")
print("MODEL_SHA256", sha)
print("RULED_NODES", len(ruled), "STATE_COUNT_PER_ENV", N, "ENVIRONMENTS", 1 << len(inputs))
print("SEMANTICS same fixed environment and same precursor state for all fates in a bundle; separate fully-asynchronous branches; endpoint must be a phenotype-compatible fixed point")
print("PRECURSOR_CONSTRAINT", ",".join(f"{k}={int(v)}" for k,v in PRECURSOR_MARKERS.items()))
print("STATUS exploratory exact unbounded audit; no cutoff horizon")

global_best = {}
for size in (1, 2, 3):
    for bundle in itertools.combinations(tuple(PHENOTYPES), size):
        global_best[bundle] = None

for env in env_assignments(inputs):
    values = evaluate_rules(states, ruled, env)
    fixed = fixed_mask(states, ruled, values)
    pre = precursor_mask(values)

    dists = {}
    target_counts = {}
    for fate, markers in PHENOTYPES.items():
        targets = fixed & phenotype_mask(values, markers)
        target_counts[fate] = int(targets.sum())
        dists[fate] = backward_distances(states, ruled, values, targets)

    print("ENV", fmt_env(env), "FIXED_POINTS", int(fixed.sum()),
          "TARGET_FIXED", " ".join(f"{p}:{target_counts[p]}" for p in PHENOTYPES))

    for size in (1, 2, 3):
        for bundle in itertools.combinations(tuple(PHENOTYPES), size):
            feasible = pre.copy()
            for fate in bundle:
                feasible &= (dists[fate] >= 0)
            count = int(feasible.sum())
            if count == 0:
                continue
            maxd = np.zeros(N, dtype=np.int16)
            for fate in bundle:
                maxd = np.maximum(maxd, dists[fate])
            vals = maxd.copy()
            vals[~feasible] = np.iinfo(np.int16).max
            best_h = int(vals.min())
            best_state = int(vals.argmin())
            rec = global_best[bundle]
            key = (best_h, fmt_env(env), best_state)
            if rec is None or key < rec[0]:
                global_best[bundle] = (key, count, env.copy(), best_state,
                                       tuple(int(dists[f][best_state]) for f in bundle))

print("EXACT_UNBOUNDED_SUMMARY")
for size in (1, 2, 3):
    for bundle in itertools.combinations(tuple(PHENOTYPES), size):
        rec = global_best[bundle]
        label = ",".join(bundle)
        if rec is None:
            print("BUNDLE", label, "UNBOUNDED_FEASIBLE", 0, "MIN_COMMON_HORIZON", "INF")
        else:
            key, count, env, state, ds = rec
            print("BUNDLE", label, "UNBOUNDED_FEASIBLE", 1,
                  "MIN_COMMON_HORIZON", key[0],
                  "ENV", fmt_env(env),
                  "PRECURSOR_STATE", state,
                  "BRANCH_DEPTHS", ",".join(map(str, ds)),
                  "FEASIBLE_PRECURSORS_IN_BEST_ENV", count)

# Critical exact audit against the earlier bounded-H=6 observation.
for bundle in (("Th1","Th2"), ("Th0","Th1","Th2")):
    rec = global_best[bundle]
    if rec is None:
        print("CRITICAL", ",".join(bundle), "EXACT_RESULT", "TRUE_UNBOUNDED_OBSTRUCTION")
    else:
        print("CRITICAL", ",".join(bundle), "EXACT_RESULT", "FINITE",
              "MIN_COMMON_HORIZON", rec[0][0])
