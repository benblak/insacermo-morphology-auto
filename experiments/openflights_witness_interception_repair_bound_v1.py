import csv
import hashlib
import io
import itertools
import urllib.request
from collections import defaultdict

SOURCE_COMMIT = "5d623a6969a1adee7961cf1c9a8a212c4a784713"
SOURCE_SHA256 = "bd373706238134f619c624c606dccc74c05c2582a977c489c81de501735f2390"
URL = f"https://raw.githubusercontent.com/jpatokal/openflights/{SOURCE_COMMIT}/data/routes.dat"

START = "KEF"
REQUIRED = [
    "LHR","CDG","FRA","AMS","MAD","FCO","ATH","IST","DXB","DOH",
    "JFK","YYZ","MEX","GRU","EZE","CPT","JNB","DEL","SIN","HKG",
    "NRT","SYD","AKL","LAX","SFO"
]
H = 3
MAX_BUNDLE = 3

ACTIONS = {
    "NONE": {"restore_fi": False, "restore_lhr": False, "cost": 0},
    "RESTORE_FI": {"restore_fi": True, "restore_lhr": False, "cost": 1},
    "RESTORE_LHR": {"restore_fi": False, "restore_lhr": True, "cost": 1},
    "RESTORE_BOTH": {"restore_fi": True, "restore_lhr": True, "cost": 2},
}

raw = urllib.request.urlopen(URL, timeout=60).read()
assert hashlib.sha256(raw).hexdigest() == SOURCE_SHA256
rows = list(csv.reader(io.StringIO(raw.decode("utf-8"))))

def valid(r):
    return len(r) >= 5 and r[2] not in ("", "\\N") and r[4] not in ("", "\\N")

def keep(r, action):
    if not valid(r):
        return False
    airline, src, dst = r[0], r[2], r[4]
    spec = ACTIONS[action]
    if not spec["restore_fi"] and airline == "FI":
        return False
    if not spec["restore_lhr"] and (src == "LHR" or dst == "LHR"):
        return False
    return True

def graph_for(action):
    g = defaultdict(set)
    for r in rows:
        if keep(r, action):
            g[r[2]].add(r[4])
    return {u: tuple(sorted(v)) for u, v in g.items()}

graphs = {a: graph_for(a) for a in ACTIONS}
baseline = graphs["RESTORE_BOTH"]
degraded = graphs["NONE"]

baseline_edges = {(u,v) for u, vs in baseline.items() for v in vs}
degraded_edges = {(u,v) for u, vs in degraded.items() for v in vs}
removed_support = baseline_edges - degraded_edges

# Enumerate every directed path from KEF of <= H edges in the baseline graph.
# H=3 makes this finite and exact.
all_paths = [(START,)]
frontier = [(START,)]
for _ in range(H):
    nxt = []
    for p in frontier:
        for v in baseline.get(p[-1], ()):
            q = p + (v,)
            all_paths.append(q)
            nxt.append(q)
    frontier = nxt

bundles = [
    tuple(c)
    for k in range(1, MAX_BUNDLE + 1)
    for c in itertools.combinations(REQUIRED, k)
]
bundle_set = set(bundles)
required_set = set(REQUIRED)

# One-pass exact feasibility catalogue for each action.
# A path contributes every size<=3 subset of required airports that it visits.
feasible = {a: {b: False for b in bundles} for a in ACTIONS}
path_edges_by_action = {
    a: {(u,v) for u, vs in graphs[a].items() for v in vs}
    for a in ACTIONS
}
path_records = []
for p in all_paths:
    pedges = tuple((p[i], p[i+1]) for i in range(len(p)-1))
    seen_targets = tuple(sorted(required_set.intersection(p)))
    path_records.append((p, pedges, seen_targets))
    for action in ACTIONS:
        aedges = path_edges_by_action[action]
        if all(e in aedges for e in pedges):
            for k in range(1, min(MAX_BUNDLE, len(seen_targets)) + 1):
                for b in itertools.combinations(seen_targets, k):
                    if b in bundle_set:
                        feasible[action][b] = True

def proper_nonempty(bundle):
    for k in range(1, len(bundle)):
        yield from itertools.combinations(bundle, k)

def minimal_obstructions(action):
    out = []
    for b in bundles:
        if len(b) < 2 or feasible[action][b]:
            continue
        if all(feasible[action][tuple(s)] for s in proper_nonempty(b)):
            out.append(b)
    return out

obs_base = set(minimal_obstructions("RESTORE_BOTH"))
obs_deg = set(minimal_obstructions("NONE"))
new_obs = sorted(obs_deg - obs_base)

# Exact witness-interception audit: every baseline path witnessing a bundle
# that becomes infeasible after the decision must cross a removed support edge.
lost_set = {
    b for b in bundles
    if feasible["RESTORE_BOTH"][b] and not feasible["NONE"][b]
}
interception_checks = 0
witness_count = 0
for p, pedges, seen_targets in path_records:
    crosses = any(e in removed_support for e in pedges)
    for k in range(1, min(MAX_BUNDLE, len(seen_targets)) + 1):
        for b in itertools.combinations(seen_targets, k):
            if b in lost_set:
                witness_count += 1
                assert crosses, (b, p)
                interception_checks += 1

lost = sorted(lost_set)

# Repair-atom capabilities are derived by actual single-class restoration.
atoms = ("FI", "LHR")
def atom_resolves(atom, obstruction):
    action = "RESTORE_FI" if atom == "FI" else "RESTORE_LHR"
    return feasible[action][obstruction]

capability = {
    b: {a for a in atoms if atom_resolves(a, b)}
    for b in new_obs
}
atomic_obs = [b for b in new_obs if capability[b]]
non_atomic_obs = [b for b in new_obs if not capability[b]]

def hits_all(subset):
    S = set(subset)
    return all(S & capability[b] for b in atomic_obs)

tau = None
tau_set = None
for k in range(len(atoms)+1):
    for sub in itertools.combinations(atoms, k):
        if hits_all(sub):
            tau = k
            tau_set = sub
            break
    if tau is not None:
        break

# Exact repair cost among the four concrete repair actions for restoring every
# atomically repairable new obstruction simultaneously.
def action_restores_all(action):
    return all(feasible[action][b] for b in atomic_obs)

exact_candidates = [
    (spec["cost"], a)
    for a, spec in ACTIONS.items()
    if action_restores_all(a)
]
assert exact_candidates
Cstar, best_action = min(exact_candidates)
trivial = 1 if atomic_obs else 0

assert tau is not None
assert tau <= Cstar

print("INSACERMO_OPENFLIGHTS_WITNESS_INTERCEPTION_REPAIR_BOUND_V1")
print("SOURCE_COMMIT", SOURCE_COMMIT)
print("SOURCE_SHA256", SOURCE_SHA256)
print("START", START)
print("HORIZON", H)
print("TARGETS", len(REQUIRED))
print("BUNDLES", len(bundles))
print("BASELINE_PATHS_ENUMERATED", len(all_paths))
print("REMOVED_SUPPORT_EDGES", len(removed_support))
print("LOST_BUNDLES", len(lost))
print("BASELINE_WITNESSES_AUDITED", witness_count)
print("WITNESS_INTERCEPTION_CHECKS", interception_checks)
print("WITNESS_INTERCEPTION", "PASS")
print("BASELINE_MINIMAL_OBSTRUCTIONS", len(obs_base))
print("DEGRADED_MINIMAL_OBSTRUCTIONS", len(obs_deg))
print("NEW_MINIMAL_OBSTRUCTIONS", len(new_obs))
print("ATOMICALLY_REPAIRABLE_NEW_OBSTRUCTIONS", len(atomic_obs))
print("NONATOMIC_NEW_OBSTRUCTIONS", len(non_atomic_obs))
print("CAPABILITY_ONLY_FI", sum(capability[b] == {"FI"} for b in atomic_obs))
print("CAPABILITY_ONLY_LHR", sum(capability[b] == {"LHR"} for b in atomic_obs))
print("CAPABILITY_EITHER", sum(capability[b] == {"FI","LHR"} for b in atomic_obs))
print("TRIVIAL_LOWER_BOUND", trivial)
print("TRANSVERSAL_TAU", tau)
print("TRANSVERSAL_SET", ",".join(tau_set))
print("EXACT_REPAIR_COST", Cstar)
print("EXACT_REPAIR_ACTION", best_action)
print("BOUND_RATIO_TAU_OVER_CSTAR", f"{tau/Cstar:.6f}" if Cstar else "1.000000")
print("RESULT", "COMPLETE")
