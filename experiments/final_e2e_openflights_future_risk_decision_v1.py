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
# Frozen legacy confirmatory scope.  The structural certificate below may
# require a larger order for a complete finite-horizon audit.
MAX_BUNDLE = 3
UNIT_EDGE_COST = 1

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
    # NOTE: the historical field name "irreversible" is preserved below for
    # frozen-output compatibility.  Semantically, d=None for one action is a
    # HARD LOSS under that action.  True IRREVERSIBLE loss is computed later
    # across the admissible repair set.
    results[action] = {
        "cost": spec["cost"],
        "irreversible": irreversible,
        "hard_loss": irreversible,
        "deadline_miss": deadline_miss,
        "soft_loss": deadline_miss - irreversible,
        "safe": safe,
        "finite": finite,
        "pairwise": pairwise,
        "depths": depths,
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


# ---------------------------------------------------------------------------
# STRUCTURAL AUDIT CERTIFICATE V1
#
# Lean-verified theorem used by this integration:
# for state-valued goals under finite directed agent-choice dynamics,
# eventual joint feasibility is equivalent to:
#   (i) every goal is reachable from START, and
#   (ii) every pair of goals is comparable by directed reachability.
# Hence every minimal HARD obstruction has cardinality <= 2.
#
# For the finite deadline, positive unit edge cost gives the audit-rank bound
#   k <= 2 + floor((H - d)/delta)
# for minimal obstructions of size >= 2, where d is the minimum singleton
# distance and delta=1 here.
# ---------------------------------------------------------------------------

def hard_witness_certificate(pairwise):
    unreachable = tuple(q for q in REQUIRED if q not in pairwise[START])
    incomparable = []
    for q, r in itertools.combinations(REQUIRED, 2):
        # Only retain minimal pair witnesses: both singleton goals must be
        # individually reachable, otherwise the singleton already witnesses
        # the hard failure.
        if q in pairwise[START] and r in pairwise[START]:
            if r not in pairwise[q] and q not in pairwise[r]:
                incomparable.append((q, r))
    return unreachable, tuple(incomparable)


def bundle_has_hard_witness(bundle, unreachable, incomparable):
    b = set(bundle)
    if any(q in b for q in unreachable):
        return True
    return any(q in b and r in b for q, r in incomparable)


def finite_horizon_audit_bound(pairwise):
    finite_singletons = [
        pairwise[START][q]
        for q in REQUIRED
        if q in pairwise[START]
    ]
    if not finite_singletons:
        # Every nonempty contract already fails at order 1.
        return 1, None, UNIT_EDGE_COST
    d = min(finite_singletons)
    delta = UNIT_EDGE_COST
    if d > DEADLINE:
        # Any deadline obstruction is already visible at singleton order.
        return 1, d, delta
    return 2 + (DEADLINE - d) // delta, d, delta


structural = {}
for action in ACTIONS:
    pairwise = results[action]["pairwise"]
    unreachable, incomparable = hard_witness_certificate(pairwise)
    kmax, dmin, delta = finite_horizon_audit_bound(pairwise)

    # Cross-check the Lean theorem against every hard failure in the frozen
    # legacy catalogue.  This is validation, not the source of the theorem.
    for bundle, depth in results[action]["depths"].items():
        if depth is None:
            assert bundle_has_hard_witness(bundle, unreachable, incomparable), (
                action, bundle, unreachable, incomparable
            )

    structural[action] = {
        "hard_audit_order": 2,
        "unreachable_singletons": unreachable,
        "incomparable_pairs": incomparable,
        "finite_audit_bound": kmax,
        "dmin": dmin,
        "delta": delta,
    }

CERTIFIED_MAX_BUNDLE = max(
    MAX_BUNDLE,
    max(s["finite_audit_bound"] for s in structural.values()),
)

certified_bundles = []
for k in range(1, CERTIFIED_MAX_BUNDLE + 1):
    certified_bundles.extend(itertools.combinations(REQUIRED, k))

certified_results = {}
for action in ACTIONS:
    pairwise = results[action]["pairwise"]
    depths = {
        bundle: joint_depth(pairwise, bundle)
        for bundle in certified_bundles
    }
    hard = sum(depth is None for depth in depths.values())
    deadline_miss = sum(
        depth is None or depth > DEADLINE
        for depth in depths.values()
    )
    certified_results[action] = {
        "depths": depths,
        "hard_loss": hard,
        "soft_loss": deadline_miss - hard,
        "deadline_miss": deadline_miss,
        "safe": len(certified_bundles) - deadline_miss,
    }

    # Global hard-loss completeness: arbitrary larger bundles cannot create a
    # new minimal hard obstruction beyond these singleton/pair witnesses.
    unreachable = structural[action]["unreachable_singletons"]
    incomparable = structural[action]["incomparable_pairs"]
    for bundle, depth in depths.items():
        if depth is None:
            assert bundle_has_hard_witness(
                bundle, unreachable, incomparable
            ), (action, bundle)

    # Empirical check that every minimal finite-horizon obstruction in the
    # certified search range respects the structural rank certificate.
    minimal_deadline = []
    for bundle, depth in depths.items():
        failed = depth is None or depth > DEADLINE
        if not failed:
            continue
        is_minimal = True
        if len(bundle) > 1:
            for r in range(1, len(bundle)):
                for sub in itertools.combinations(bundle, r):
                    sd = depths[sub]
                    if sd is None or sd > DEADLINE:
                        is_minimal = False
                        break
                if not is_minimal:
                    break
        if is_minimal:
            minimal_deadline.append(bundle)

    observed_rank = max((len(b) for b in minimal_deadline), default=0)
    assert observed_rank <= structural[action]["finite_audit_bound"], (
        action, observed_rank, structural[action]["finite_audit_bound"]
    )
    certified_results[action]["minimal_deadline_obstructions"] = minimal_deadline
    certified_results[action]["observed_deadline_rank"] = observed_rank

# True irreversibility is relative to the admissible repair set: a future
# bundle is IRREVERSIBLE only if every repair action allowed by the budget
# leaves it hard-impossible.
feasible_actions = [
    a for a in ACTIONS if ACTIONS[a]["cost"] <= BUDGET
]
repair_irreversible = [
    bundle
    for bundle in certified_bundles
    if all(
        certified_results[a]["depths"][bundle] is None
        for a in feasible_actions
    )
]

cert_hard_best = min(
    feasible_actions,
    key=lambda a: (
        certified_results[a]["hard_loss"],
        certified_results[a]["deadline_miss"],
        ACTIONS[a]["cost"],
        a,
    ),
)
cert_deadline_best = min(
    feasible_actions,
    key=lambda a: (
        certified_results[a]["deadline_miss"],
        certified_results[a]["hard_loss"],
        ACTIONS[a]["cost"],
        a,
    ),
)

print("STRUCTURAL_AUDIT_CERTIFICATE_V1")
print("LEAN_THEOREM HARD_MINIMAL_OBSTRUCTION_ORDER_LE_2")
print("CERTIFIED_HARD_AUDIT_ORDER", 2)
print("LEGACY_MAX_BUNDLE", MAX_BUNDLE)
print("CERTIFIED_FINITE_HORIZON_MAX_BUNDLE", CERTIFIED_MAX_BUNDLE)
print("CERTIFIED_CATALOGUE_BUNDLES", len(certified_bundles))

for action in ACTIONS:
    s = structural[action]
    cr = certified_results[action]
    print(
        "STRUCTURAL_ACTION", action,
        "UNREACHABLE_SINGLETONS", len(s["unreachable_singletons"]),
        "INCOMPARABLE_MINIMAL_PAIRS", len(s["incomparable_pairs"]),
        "D_MIN", s["dmin"],
        "DELTA", s["delta"],
        "FINITE_AUDIT_BOUND", s["finite_audit_bound"],
        "OBSERVED_DEADLINE_RANK", cr["observed_deadline_rank"],
        "HARD_LOSS", cr["hard_loss"],
        "SOFT_LOSS", cr["soft_loss"],
        "SAFE_H", cr["safe"],
    )

print("ADMISSIBLE_REPAIR_ACTIONS", ",".join(feasible_actions))
print("TRUE_IRREVERSIBLE_BUNDLES", len(repair_irreversible))
print("CERTIFIED_HARD_RISK_OPTIMAL_UNDER_BUDGET", cert_hard_best)
print("CERTIFIED_DEADLINE_RISK_OPTIMAL_UNDER_BUDGET", cert_deadline_best)
print("STRUCTURAL_CERTIFICATE_STATUS VERIFIED_BY_RUNTIME_CROSSCHECK")
