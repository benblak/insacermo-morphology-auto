import gzip
import hashlib
import itertools
import urllib.request
from collections import Counter, defaultdict, deque

EDGE_URL = "https://snap.stanford.edu/data/email-Eu-core.txt.gz"
LABEL_URL = "https://snap.stanford.edu/data/email-Eu-core-department-labels.txt.gz"

EXPECTED_NODES = 1005
EXPECTED_EDGES = 25571
TARGET_COUNT = 12
DEADLINE = 4
BUDGET = 1
UNIT_EDGE_COST = 1

def download(url):
    with urllib.request.urlopen(url, timeout=120) as r:
        return r.read()

edge_raw = download(EDGE_URL)
label_raw = download(LABEL_URL)
edge_sha = hashlib.sha256(edge_raw).hexdigest()
label_sha = hashlib.sha256(label_raw).hexdigest()

edge_text = gzip.decompress(edge_raw).decode("utf-8")
label_text = gzip.decompress(label_raw).decode("utf-8")

edges = []
nodes = set()
outdeg = Counter()
indeg = Counter()
for line in edge_text.splitlines():
    if not line.strip():
        continue
    u, v = map(int, line.split())
    edges.append((u, v))
    nodes.add(u); nodes.add(v)
    outdeg[u] += 1
    indeg[v] += 1

labels = {}
dept_nodes = defaultdict(list)
for line in label_text.splitlines():
    if not line.strip():
        continue
    n, d = map(int, line.split())
    labels[n] = d
    dept_nodes[d].append(n)

assert len(nodes) == EXPECTED_NODES
assert len(edges) == EXPECTED_EDGES
assert set(labels) == nodes

source = min(nodes, key=lambda n: (-outdeg[n], n))
source_dept = labels[source]
ranked_depts = sorted(
    (d for d in dept_nodes if d != source_dept),
    key=lambda d: (-len(dept_nodes[d]), d),
)
selected_depts = ranked_depts[:TARGET_COUNT]

def totaldeg(n):
    return outdeg[n] + indeg[n]

targets = [
    min(dept_nodes[d], key=lambda n: (-totaldeg(n), n))
    for d in selected_depts
]
damaged_depts = [selected_depts[0], selected_depts[5], selected_depts[11]]

restoration_sets = [frozenset()]
for d in damaged_depts:
    restoration_sets.append(frozenset([d]))
for pair in itertools.combinations(damaged_depts, 2):
    restoration_sets.append(frozenset(pair))
restoration_sets.append(frozenset(damaged_depts))

def graph_for(restored):
    restored = set(restored)
    g = defaultdict(set)
    for u, v in edges:
        du, dv = labels[u], labels[v]
        if (du in damaged_depts and du not in restored) or (dv in damaged_depts and dv not in restored):
            continue
        g[u].add(v)
    for n in nodes:
        g[n]
    return g

def bfs(g, s):
    dist = {s: 0}
    q = deque([s])
    while q:
        u = q.popleft()
        for v in g[u]:
            if v not in dist:
                dist[v] = dist[u] + 1
                q.append(v)
    return dist

def joint_depth(pairwise, bundle):
    best = None
    for perm in itertools.permutations(bundle):
        cur = source
        total = 0
        ok = True
        for nxt in perm:
            step = pairwise[cur].get(nxt)
            if step is None:
                ok = False
                break
            total += step
            cur = nxt
        if ok and (best is None or total < best):
            best = total
    return best

def hard_witness_certificate(pairwise):
    unreachable = tuple(q for q in targets if q not in pairwise[source])
    incomparable = []
    for q, r in itertools.combinations(targets, 2):
        if q in pairwise[source] and r in pairwise[source]:
            if r not in pairwise[q] and q not in pairwise[r]:
                incomparable.append((q, r))
    return unreachable, tuple(incomparable)

def bundle_has_hard_witness(bundle, unreachable, incomparable):
    s = set(bundle)
    return (
        any(q in s for q in unreachable) or
        any(q in s and r in s for q, r in incomparable)
    )

def finite_horizon_audit_bound(pairwise):
    ds = [pairwise[source][q] for q in targets if q in pairwise[source]]
    if not ds:
        return 1, None, UNIT_EDGE_COST
    dmin = min(ds)
    if dmin > DEADLINE:
        return 1, dmin, UNIT_EDGE_COST
    return 2 + (DEADLINE - dmin) // UNIT_EDGE_COST, dmin, UNIT_EDGE_COST

pairwise_by_state = {}
structural = {}
for restored in restoration_sets:
    g = graph_for(restored)
    pairwise = {s: bfs(g, s) for s in [source] + targets}
    pairwise_by_state[restored] = pairwise
    unreachable, incomparable = hard_witness_certificate(pairwise)
    kmax, dmin, delta = finite_horizon_audit_bound(pairwise)
    structural[restored] = {
        "unreachable": unreachable,
        "incomparable": incomparable,
        "kmax": min(kmax, len(targets)),
        "dmin": dmin,
        "delta": delta,
    }

CERTIFIED_MAX_BUNDLE = max(s["kmax"] for s in structural.values())
bundles = [
    b
    for k in range(1, CERTIFIED_MAX_BUNDLE + 1)
    for b in itertools.combinations(targets, k)
]

depths = {
    restored: {
        b: joint_depth(pairwise_by_state[restored], b)
        for b in bundles
    }
    for restored in restoration_sets
}

full = frozenset(damaged_depts)
Gamma = [b for b in bundles if depths[full][b] is not None]
assert Gamma

results = {}
for restored in restoration_sets:
    s = structural[restored]
    dmap = depths[restored]

    for b in Gamma:
        if dmap[b] is None:
            assert bundle_has_hard_witness(
                b, s["unreachable"], s["incomparable"]
            ), (restored, b)

    minimal_deadline = []
    for b in Gamma:
        d = dmap[b]
        if d is not None and d <= DEADLINE:
            continue
        is_minimal = True
        for r in range(1, len(b)):
            for sub in itertools.combinations(b, r):
                sd = dmap[sub]
                if sd is None or sd > DEADLINE:
                    is_minimal = False
                    break
            if not is_minimal:
                break
        if is_minimal:
            minimal_deadline.append(b)

    observed_rank = max((len(b) for b in minimal_deadline), default=0)
    assert observed_rank <= s["kmax"], (restored, observed_rank, s["kmax"])

    hard = sum(dmap[b] is None for b in Gamma)
    miss = sum(dmap[b] is None or dmap[b] > DEADLINE for b in Gamma)
    results[restored] = {
        "hard": hard,
        "soft": miss - hard,
        "miss": miss,
        "rank": observed_rank,
    }

admissible = [s for s in restoration_sets if len(s) <= BUDGET]
true_irreversible = [
    b for b in Gamma
    if all(depths[s][b] is None for s in admissible)
]

print("INSACERMO_EMAIL_EU_CORE_STRUCTURAL_AUDIT_V1")
print("EDGE_SHA256", edge_sha)
print("LABEL_SHA256", label_sha)
print("NODES", len(nodes))
print("EDGES", len(edges))
print("SOURCE", source)
print("TARGETS", len(targets))
print("CERTIFIED_HARD_AUDIT_ORDER", 2)
print("CERTIFIED_FINITE_HORIZON_MAX_BUNDLE", CERTIFIED_MAX_BUNDLE)
print("CERTIFIED_CATALOGUE_BUNDLES", len(bundles))
print("CERTIFIED_INTACT_EVENTUAL_GAMMA", len(Gamma))

for restored in sorted(restoration_sets, key=lambda x: (len(x), tuple(sorted(x)))):
    label = "NONE" if not restored else "+".join(f"D{d}" for d in sorted(restored))
    s = structural[restored]
    r = results[restored]
    print(
        "STRUCTURAL_RESTORED", label,
        "UNREACHABLE_SINGLETONS", len(s["unreachable"]),
        "INCOMPARABLE_MINIMAL_PAIRS", len(s["incomparable"]),
        "D_MIN", s["dmin"],
        "DELTA", s["delta"],
        "FINITE_AUDIT_BOUND", s["kmax"],
        "OBSERVED_DEADLINE_RANK", r["rank"],
        "HARD_LOSS", r["hard"],
        "SOFT_LOSS", r["soft"],
    )

print("ADMISSIBLE_REPAIR_STATES", len(admissible))
print("TRUE_IRREVERSIBLE_BUNDLES", len(true_irreversible))
print("STRUCTURAL_CERTIFICATE_STATUS VERIFIED_BY_RUNTIME_CROSSCHECK")
print("RESULT COMPLETE")
