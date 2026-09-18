import hashlib
import itertools
import math
import urllib.request

SOURCE_COMMIT = "f46a8102e0ae93c98969e919c0b68897a202e0f3"
SOURCE_URL = f"https://raw.githubusercontent.com/linsea423/Intel_Lab_Data/{SOURCE_COMMIT}/mote_locs.txt"
EXPECTED_SHA256 = "3865c0263110c24c40e3377690cecaa552e0575cf56cdb9f5f8bd17130b6bf04"

COVERAGE_RADIUS = 8.0
OUTAGE_RADIUS = 7.0
MAX_BUNDLE = 3
BUDGET = 1

raw = urllib.request.urlopen(SOURCE_URL, timeout=60).read()
sha = hashlib.sha256(raw).hexdigest()
assert sha == EXPECTED_SHA256, (sha, EXPECTED_SHA256)

coords = {}
for line in raw.decode("utf-8").splitlines():
    if not line.strip():
        continue
    i, x, y = line.split()
    coords[int(i)] = (float(x), float(y))

assert len(coords) == 54, len(coords)

xmin = min(x for x, _ in coords.values())
xmax = max(x for x, _ in coords.values())
ymin = min(y for _, y in coords.values())
ymax = max(y for _, y in coords.values())

# Fixed spatial future obligations: 12 anchors derived only from the observed
# lab bounding box, not from downstream feasibility outcomes.
ANCHOR_FX = [0.10, 0.37, 0.63, 0.90]
ANCHOR_FY = [0.20, 0.50, 0.80]
anchors = []
for fx in ANCHOR_FX:
    for fy in ANCHOR_FY:
        anchors.append((
            xmin + fx * (xmax - xmin),
            ymin + fy * (ymax - ymin),
        ))
assert len(anchors) == 12

coverage = {
    a: {
        mote for mote, p in coords.items()
        if math.dist(p, anchors[a]) <= COVERAGE_RADIUS
    }
    for a in range(len(anchors))
}
assert all(coverage[a] for a in coverage)

# Structural outage classes: radius-7 neighborhoods around three sensor centers.
# Center 1 maximizes outage neighborhood size. Center 2 minimizes overlap with
# center 1, then maximizes its own neighborhood. Center 3 minimizes its worst
# overlap with the first two, then maximizes its own neighborhood.
outage_set = {
    i: {
        j for j, p in coords.items()
        if math.dist(p, coords[i]) <= OUTAGE_RADIUS
    }
    for i in coords
}

c1 = min(coords, key=lambda i: (-len(outage_set[i]), i))
remaining = [i for i in coords if i != c1]
c2 = min(
    remaining,
    key=lambda i: (
        len(outage_set[i] & outage_set[c1]),
        -len(outage_set[i]),
        i,
    ),
)
remaining = [i for i in remaining if i != c2]
c3 = min(
    remaining,
    key=lambda i: (
        max(
            len(outage_set[i] & outage_set[c1]),
            len(outage_set[i] & outage_set[c2]),
        ),
        -len(outage_set[i]),
        i,
    ),
)
CENTERS = [c1, c2, c3]
OUTAGES = {c: outage_set[c] for c in CENTERS}

# Contracts are bundles of 1, 2 or 3 distinct spatial obligations.
bundles = []
for k in range(1, MAX_BUNDLE + 1):
    bundles.extend(itertools.combinations(range(len(anchors)), k))
assert len(bundles) == 298

def feasible(bundle, active):
    # A bundle is feasible iff its obligations can be assigned injectively to
    # distinct active sensors that cover the corresponding anchors.
    ordered = sorted(bundle, key=lambda a: len(coverage[a] & active))
    used = set()

    def dfs(k):
        if k == len(ordered):
            return True
        a = ordered[k]
        for mote in sorted(coverage[a] & active):
            if mote in used:
                continue
            used.add(mote)
            if dfs(k + 1):
                return True
            used.remove(mote)
        return False

    return dfs(0)

all_active = set(coords)
Gamma = [b for b in bundles if feasible(b, all_active)]
assert Gamma, "empty intact future family"

restoration_subsets = []
for r in range(len(CENTERS) + 1):
    for s in itertools.combinations(CENTERS, r):
        restoration_subsets.append(frozenset(s))

def active_after(restored):
    removed = set().union(*(OUTAGES[c] for c in CENTERS))
    restored_motes = set().union(*(OUTAGES[c] for c in restored)) if restored else set()
    return all_active - (removed - restored_motes)

success = {}
for s in restoration_subsets:
    active = active_after(s)
    success[s] = {b for b in Gamma if feasible(b, active)}

def minimal_obstructions(success_set):
    obs = []
    for b in Gamma:
        if b in success_set:
            continue
        proper = []
        for r in range(1, len(b)):
            proper.extend(itertools.combinations(b, r))
        if all(p in success_set for p in proper):
            obs.append(b)
    return obs

repair_price = {}
for b in Gamma:
    opts = [len(s) for s in restoration_subsets if b in success[s]]
    assert opts, b
    repair_price[b] = min(opts)

hist = {k: 0 for k in range(len(CENTERS) + 1)}
for v in repair_price.values():
    hist[v] += 1

one_actions = [frozenset([c]) for c in CENTERS]
action_stats = []
for a in one_actions:
    safe = len(success[a])
    residual = []
    for b in Gamma:
        opts = [
            len(s - a)
            for s in restoration_subsets
            if a.issubset(s) and b in success[s]
        ]
        residual.append(min(opts))
    action_stats.append((
        next(iter(a)),
        safe,
        len(Gamma) - safe,
        sum(residual) / len(residual),
        max(residual),
    ))

best = min(action_stats, key=lambda x: (x[2], x[3], x[0]))

print("INSACERMO_POSTFREEZE_INTEL_SENSOR_COVERAGE_V1")
print("STATUS EXPLORATORY_POSTFREEZE_EXTERNAL_VALIDATION")
print("SOURCE_COMMIT", SOURCE_COMMIT)
print("SOURCE_SHA256", sha)
print("SENSORS", len(coords))
print("ANCHORS", len(anchors))
print("CATALOGUE_BUNDLES", len(bundles))
print("INTACT_FEASIBLE_GAMMA", len(Gamma))
print("COVERAGE_RADIUS", COVERAGE_RADIUS)
print("OUTAGE_RADIUS", OUTAGE_RADIUS)
print("MAX_BUNDLE", MAX_BUNDLE)
print("BUDGET", BUDGET)
print("SEMANTICS bundle feasibility requires an injective assignment of distinct active sensors to all spatial obligations")

for a in range(len(anchors)):
    print(
        "ANCHOR", a + 1,
        "X", f"{anchors[a][0]:.3f}",
        "Y", f"{anchors[a][1]:.3f}",
        "COVERING_SENSORS", len(coverage[a]),
    )

for i, c in enumerate(CENTERS, 1):
    print(
        "OUTAGE_CLASS", i,
        "CENTER_MOTE", c,
        "SIZE", len(OUTAGES[c]),
        "MOTES", ",".join(map(str, sorted(OUTAGES[c]))),
    )

for s in sorted(restoration_subsets, key=lambda x: (len(x), tuple(sorted(x)))):
    active = active_after(s)
    safe = len(success[s])
    obs = minimal_obstructions(success[s])
    label = "NONE" if not s else "+".join(f"M{c}" for c in sorted(s))
    print(
        "RESTORED", label,
        "COST", len(s),
        "ACTIVE_SENSORS", len(active),
        "SAFE", safe,
        "FAILED", len(Gamma) - safe,
        "SURVIVAL_MASS", f"{safe/len(Gamma):.12f}",
        "MINIMAL_OBSTRUCTIONS", len(obs),
        "MIN_OBS_SIZE1", sum(len(b) == 1 for b in obs),
        "MIN_OBS_SIZE2", sum(len(b) == 2 for b in obs),
        "MIN_OBS_SIZE3", sum(len(b) == 3 for b in obs),
    )

print("REPAIR_PRICE_HIST", " ".join(f"C{k}:{hist[k]}" for k in sorted(hist)))
for center, safe, failed, mean_resid, max_resid in action_stats:
    print(
        "ACTION", f"RESTORE_M{center}",
        "COST 1",
        "SAFE_NOW", safe,
        "FAILED_NOW", failed,
        "FAILURE_RISK", f"{failed/len(Gamma):.12f}",
        "MEAN_RESIDUAL_REPAIR_PRICE", f"{mean_resid:.12f}",
        "MAX_RESIDUAL_REPAIR_PRICE", max_resid,
    )
print("BUDGET1_DECISION_MIN_FAILURE_RISK", f"RESTORE_M{best[0]}")
print("RESULT COMPLETE")
