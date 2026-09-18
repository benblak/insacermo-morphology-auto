import hashlib
import itertools
import urllib.request

SOURCE_COMMIT = "c447f0fea703fcd0fff57de5000947b5ca81286b"
SOURCE_URL = (
    "https://raw.githubusercontent.com/PantheonPlusSH0ES/DataRelease/"
    + SOURCE_COMMIT
    + "/Pantheon+_Data/4_DISTANCES_AND_COVAR/Pantheon+SH0ES.dat"
)

# Static/null-dynamics falsification protocol.
# No transition, no acquisition, no repair, no planner action is permitted.
# Therefore every future contract must have depth exactly 0 or INF.
HORIZONS = [0, 1, 2, 3, 5, 10]
MAX_BUNDLE = 3

raw = urllib.request.urlopen(SOURCE_URL, timeout=120).read()
sha = hashlib.sha256(raw).hexdigest()
text = raw.decode("utf-8")
lines = [ln for ln in text.splitlines() if ln.strip()]
header = lines[0].split()
rows = [ln.split() for ln in lines[1:]]

assert len(rows) > 1000, len(rows)
assert all(len(r) == len(header) for r in rows[:100]), "row/header width mismatch"

columns = set(header)

# Fixed cosmology-observable obligations chosen before inspecting any outcome.
# Each obligation is an exact recoverability requirement on one or two released columns.
OBLIGATIONS = {
    "redshift_cmb": frozenset(["zCMB"]),
    "redshift_helio": frozenset(["zHEL"]),
    "corrected_magnitude": frozenset(["m_b_corr"]),
    "distance_modulus": frozenset(["MU_SH0ES"]),
    "stretch": frozenset(["x1"]),
    "color": frozenset(["c"]),
    "host_mass": frozenset(["HOST_LOGMASS"]),
    "sky_position": frozenset(["RA", "DEC"]),
}
for name, req in OBLIGATIONS.items():
    assert req <= columns, (name, req - columns)

# Fixed representations. They differ only in what columns are retained.
# No later transition is allowed between them.
REPRESENTATIONS = {
    "FULL_RELEASE": frozenset(header),
    "DISTANCE_ONLY": frozenset(["zCMB", "zHEL", "m_b_corr", "MU_SH0ES"]),
    "LIGHTCURVE_ONLY": frozenset(["x1", "c", "mB", "mBERR", "x0", "x0ERR"]),
    "HOST_ONLY": frozenset(["HOST_LOGMASS", "HOST_LOGMASS_ERR", "HOST_RA", "HOST_DEC"]),
    "POSITION_ONLY": frozenset(["RA", "DEC", "HOST_RA", "HOST_DEC"]),
}

obligation_names = list(OBLIGATIONS)
bundles = []
for k in range(1, MAX_BUNDLE + 1):
    bundles.extend(itertools.combinations(obligation_names, k))

def required_columns(bundle):
    req = set()
    for q in bundle:
        req.update(OBLIGATIONS[q])
    return frozenset(req)

def depth_value(retained, bundle):
    # Step = empty relation. Exact recoverability can only be immediate.
    return 0 if required_columns(bundle) <= retained else None

def at_most(depth, H):
    return depth is not None and depth <= H

results = {}
for rep, retained in REPRESENTATIONS.items():
    depths = {b: depth_value(retained, b) for b in bundles}

    # Core falsification: no positive finite depth may appear.
    positive_finite = [b for b, d in depths.items() if d not in (0, None)]
    assert not positive_finite, positive_finite

    # Every temporal sublevel complex must equal H=0.
    baseline = {b for b, d in depths.items() if at_most(d, 0)}
    for H in HORIZONS:
        current = {b for b, d in depths.items() if at_most(d, H)}
        assert current == baseline, (rep, H, len(current), len(baseline))

    immediate = sum(d == 0 for d in depths.values())
    irreversible = sum(d is None for d in depths.values())

    # Deadline risk must equal irreversible risk for every finite horizon.
    for H in HORIZONS:
        deadline_miss = sum(not at_most(d, H) for d in depths.values())
        assert deadline_miss == irreversible, (rep, H, deadline_miss, irreversible)

    results[rep] = {
        "immediate": immediate,
        "irreversible": irreversible,
        "depths": depths,
    }

print("INSACERMO_POSTFREEZE_COSMOLOGY_NULL_DYNAMICS_V1")
print("STATUS BLIND_CONFIRMATORY_NULL_DYNAMICS_FALSIFICATION")
print("SOURCE_COMMIT", SOURCE_COMMIT)
print("SOURCE_SHA256", sha)
print("ROWS", len(rows))
print("COLUMNS", len(header))
print("OBLIGATIONS", len(OBLIGATIONS))
print("CATALOGUE_BUNDLES", len(bundles))
print("HORIZONS", " ".join(map(str, HORIZONS)))
print("STEP_RELATION EMPTY")
print("REPAIR_ACTIONS NONE")
print("ACQUISITIONS NONE")

for rep, retained in REPRESENTATIONS.items():
    r = results[rep]
    print(
        "REPRESENTATION", rep,
        "RETAINED_COLUMNS", len(retained),
        "IMMEDIATE", r["immediate"],
        "IRREVERSIBLE", r["irreversible"],
        "IRREVERSIBLE_RISK", f"{r['irreversible']/len(bundles):.12f}",
    )
    for H in HORIZONS:
        safe = sum(at_most(d, H) for d in r["depths"].values())
        miss = len(bundles) - safe
        print(
            "HORIZON", H,
            "REP", rep,
            "SAFE", safe,
            "DEADLINE_MISS", miss,
            "DEADLINE_RISK", f"{miss/len(bundles):.12f}",
        )

print("ASSERTION NO_POSITIVE_FINITE_DEPTH PASSED")
print("ASSERTION ALL_TEMPORAL_COMPLEXES_EQUAL_H0 PASSED")
print("ASSERTION DEADLINE_RISK_EQUALS_IRREVERSIBLE_RISK_ALL_H PASSED")
print("RESULT COMPLETE")
