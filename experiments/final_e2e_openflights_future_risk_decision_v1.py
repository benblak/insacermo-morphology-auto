import csv
import hashlib
import io
import itertools
import urllib.request
from collections import defaultdict, deque

SOURCE_COMMIT = "5d623a6969a1adee7961cf1c9a8a212c4a784713"
SOURCE_SHA256 = "bd373706238134f619c624c606dccc74c05c2582a977c489c81de501735f2390"
URL = f"https://raw.githubusercontent.com/jpatokal/openflights/{SOURCE_COMMIT}/data/routes.dat"

START = "KEF"
REQUIRED = [
    "LHR","CDG","FRA","AMS","MAD","FCO","ATH","IST","DXB","DOH",
    "JFK","YYZ","MEX","GRU","EZE","CPT","JNB","DEL","SIN","HKG",
    "NRT","SYD","AKL","LAX","SFO"
]
DEADLINE = 3
MAX_BUNDLE = 3

# Decision problem:
# degraded base = FI routes removed AND LHR isolated;
# one unit of budget restores one repair class.
ACTIONS = {
    "NONE": {"restore_fi": False, "restore_lhr": False, "cost": 0},
    "RESTORE_FI": {"restore_fi": True, "restore_lhr": False, "cost": 1},
    "RESTORE_LHR": {"restore_fi": False, "restore_lhr": True, "cost": 1},
    "RESTORE_BOTH": {"restore_fi": True, "restore_lhr": True, "cost": 2},
}
BUDGET = 1

raw = urllib.request.urlopen(URL, timeout=60).read()
sha = hashlib.sha256(raw).hexdigest()
assert sha == SOURCE_SHA256, (sha, SOURCE_SHA256)
rows = list(csv.reader(io.StringIO(raw.decode("utf-8"))))


def valid_row(r):
    return len(r) >= 5 and r[2] not in ("", "\\N") and r[4] not in ("", "\\N")


def keep(r, action):
    airline, src, dst = r[0], r[2], r[4]
    a = ACTIONS[action]
    if not valid_row(r):
        return False
    if not a["restore_fi"] and airline == "FI":
        return False
    if not a["restore_lhr"] and (src == "LHR" or dst == "LHR"):
        return False
    return True


def graph_for(action):
    g = defaultdict(set)
    for r in rows:
        if keep(r, action):
            g[r[2]].add(r[4])
    return g


def bfs(g, start):
    d = {start: 0}
    q = deque([start])
    while q:
        u = q.popleft()
        for v in g.get(u, ()):
            if v not in d:
                d[v] = d[u] + 1
                q.append(v)
    return d


def joint_depth(pairwise, bundle):
    best = None
    for perm in itertools.permutations(bundle):
        total = 0
        cur = START
        ok = True
        for nxt in perm:
            dv = pairwise[cur].get(nxt)
            if dv is None:
                ok = False
                break
            total += dv
            cur = nxt
        if ok and (best is None or total < best):
            best = total
    return best


bundles = []
for k in range(1, MAX_BUNDLE + 1):
    bundles.extend(itertools.combinations(REQUIRED, k))

# Uniform law on the finite catalogue Γ.  Every bundle has mass 1/|Γ|.
N = len(bundles)
assert N == 2625

results = {}
for action, spec in ACTIONS.items():
    g = graph_for(action)
    pairwise = {s: bfs(g, s) for s in [START] + REQUIRED}
    depths = {bundle: joint_depth(pairwise, bundle) for bundle in bundles}
    irreversible = sum(d is None for d in depths.values())
    deadline_miss = sum(d is None or d > DEADLINE for d in depths.values())
    safe = N - deadline_miss
    finite = N - irreversible
    results[action] = {
        "cost": spec["cost"],
        "irreversible": irreversible,
        "deadline_miss": deadline_miss,
        "safe": safe,
        "finite": finite,
    }

feasible = [a for a in ACTIONS if ACTIONS[a]["cost"] <= BUDGET]
irr_best = min(feasible, key=lambda a: (results[a]["irreversible"], results[a]["deadline_miss"], ACTIONS[a]["cost"], a))
deadline_best = min(feasible, key=lambda a: (results[a]["deadline_miss"], results[a]["irreversible"], ACTIONS[a]["cost"], a))

print("INSACERMO_FINAL_E2E_OPENFLIGHTS_DECISION_V1")
print("STATUS CONFIRMATORY_INTEGRATION_VALIDATION")
print("SOURCE_COMMIT", SOURCE_COMMIT)
print("SOURCE_SHA256", sha)
print("START", START)
print("REQUIRED", len(REQUIRED))
print("CATALOGUE_BUNDLES", N)
print("FUTURE_LAW UNIFORM_OVER_ALL_SIZE_1_TO_3_BUNDLES")
print("DEADLINE", DEADLINE)
print("BUDGET_REPAIR_CLASSES", BUDGET)
print("COST_SEMANTICS unit cost per restored repair class; not monetary")

for action in ACTIONS:
    r = results[action]
    print(
        "ACTION", action,
        "COST", r["cost"],
        "FINITE", r["finite"],
        "IRREVERSIBLE", r["irreversible"],
        "IRREVERSIBLE_RISK", f"{r['irreversible']/N:.12f}",
        "SAFE_H3", r["safe"],
        "DEADLINE_MISS", r["deadline_miss"],
        "DEADLINE_RISK", f"{r['deadline_miss']/N:.12f}",
        "FEASIBLE", int(r["cost"] <= BUDGET),
    )

print("IRREVERSIBLE_RISK_OPTIMAL_UNDER_BUDGET", irr_best)
print("DEADLINE_RISK_OPTIMAL_UNDER_BUDGET", deadline_best)

# Fixed integration expectations from the already-audited component scenarios:
# NONE = NO_FI_NO_LHR, RESTORE_FI = NO_LHR,
# RESTORE_LHR = NO_FI, RESTORE_BOTH = BASELINE.
expected = {
    "NONE": {"irreversible": 301, "safe": 339},
    "RESTORE_FI": {"irreversible": 301, "safe": 788},
    "RESTORE_LHR": {"irreversible": 0, "safe": 383},
    "RESTORE_BOTH": {"irreversible": 0, "safe": 992},
}
for action, exp in expected.items():
    assert results[action]["irreversible"] == exp["irreversible"], (action, results[action], exp)
    assert results[action]["safe"] == exp["safe"], (action, results[action], exp)

assert irr_best == "RESTORE_LHR", irr_best
assert deadline_best == "RESTORE_FI", deadline_best

print("RESULT VERIFIED_COMPONENT_COUNTS")
print("INTERPRETATION irreversible-risk and H3-deadline-risk select different feasible actions under the same budget")
