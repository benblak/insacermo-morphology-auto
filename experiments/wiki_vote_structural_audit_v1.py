import gzip
import hashlib
import itertools
import sys
import urllib.request
from collections import Counter, defaultdict, deque

URL = "https://snap.stanford.edu/data/wiki-Vote.txt.gz"
EXPECTED_NODES = 7115
EXPECTED_EDGES = 103689
TARGET_COUNT = 12
DEADLINE = 4
BUDGET = 1
UNIT_EDGE_COST = 1

sys.setrecursionlimit(100000)

with urllib.request.urlopen(URL, timeout=120) as r:
    raw = r.read()
sha = hashlib.sha256(raw).hexdigest()
text = gzip.decompress(raw).decode("utf-8")

g = defaultdict(set)
rg = defaultdict(set)
nodes = set()
indeg = Counter()
outdeg = Counter()
edges = 0
for line in text.splitlines():
    line = line.strip()
    if not line or line.startswith("#"):
        continue
    u, v = map(int, line.split()[:2])
    if v not in g[u]:
        g[u].add(v)
        rg[v].add(u)
        nodes.add(u); nodes.add(v)
        outdeg[u] += 1
        indeg[v] += 1
        edges += 1
for n in nodes:
    g[n]
    rg[n]

assert len(nodes) == EXPECTED_NODES, len(nodes)
assert edges == EXPECTED_EDGES, edges

# Fixed, outcome-independent source rule.
source = min(nodes, key=lambda n: (-outdeg[n], n))

# Kosaraju SCC decomposition.
seen = set()
order = []

def dfs1(u):
    seen.add(u)
    for v in g[u]:
        if v not in seen:
            dfs1(v)
    order.append(u)

for n in sorted(nodes):
    if n not in seen:
        dfs1(n)

comp_of = {}
components = []

def dfs2(u, cid):
    comp_of[u] = cid
    components[cid].append(u)
    for v in rg[u]:
        if v not in comp_of:
            dfs2(v, cid)

for u in reversed(order):
    if u in comp_of:
        continue
    components.append([])
    dfs2(u, len(components) - 1)

# Reachability from the fixed source in the intact graph.
def bfs_graph(graph, s):
    d = {s: 0}
    q = deque([s])
    while q:
        u = q.popleft()
        for v in graph[u]:
            if v not in d:
                d[v] = d[u] + 1
                q.append(v)
    return d

intact_from_source = bfs_graph(g, source)
source_comp = comp_of[source]

# Targets: representatives of the 12 largest SCCs reachable from source,
# excluding the source SCC. Tie-break SCCs by smallest node id; representative
# is max total degree, then smallest node id.
reachable_cids = {
    comp_of[n] for n in intact_from_source if comp_of[n] != source_comp
}
ranked_cids = sorted(
    reachable_cids,
    key=lambda cid: (-len(components[cid]), min(components[cid])),
)
assert len(ranked_cids) >= TARGET_COUNT, len(ranked_cids)
selected_cids = ranked_cids[:TARGET_COUNT]

def totaldeg(n):
    return indeg[n] + outdeg[n]

targets = [
    min(components[cid], key=lambda n: (-totaldeg(n), n))
    for cid in selected_cids
]

# Fixed perturbation classes: ranks 1, 6, 12 among the selected reachable SCCs.
damaged_cids = [selected_cids[0], selected_cids[5], selected_cids[11]]

restoration_sets = [frozenset()]
for cid in damaged_cids:
    restoration_sets.append(frozenset([cid]))
for pair in itertools.combinations(damaged_cids, 2):
    restoration_sets.append(frozenset(pair))
restoration_sets.append(frozenset(damaged_cids))

def graph_for(restored):
    restored = set(restored)
    blocked_nodes = set()
    for cid in damaged_cids:
        if cid not in restored:
            blocked_nodes.update(components[cid])
    gg = defaultdict(set)
    for u in nodes:
        for v in g[u]:
            if u in blocked_nodes or v in blocked_nodes:
                continue
            gg[u].add(v)
    for n in nodes:
        gg[n]
    return gg

def hard_witness_certificate(pairwise):
    unreachable = tuple(q for q in targets if q not in pairwise[source])
    incomparable = []
    for q, r in itertools.combinations(targets, 2):
        if q in pairwise[source] and r in pairwise[source]:
            if r not in pairwise[q] and q not in pairwise[r]:
                incomparable.append((q, r))
    return unreachable, tuple(incomparable)

def bundle_has_hard_witness(bundle, unreachable, incomparable):
    b = set(bundle)
    return (
        any(q in b for q in unreachable)
        or any(q in b and r in b for q, r in incomparable)
    )

def finite_horizon_audit_bound(pairwise):
    ds = [pairwise[source][q] for q in targets if q in pairwise[source]]
    if not ds:
        return 1, None, UNIT_EDGE_COST
    dmin = min(ds)
    if dmin > DEADLINE:
        return 1, dmin, UNIT_EDGE_COST
    return 2 + (DEADLINE - dmin) // UNIT_EDGE_COST, dmin, UNIT_EDGE_COST

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

pairwise_by_state = {}
structural = {}
for restored in restoration_sets:
    gg = graph_for(restored)
    pairwise = {s: bfs_graph(gg, s) for s in [source] + targets}
    pairwise_by_state[restored] = pairwise
    unreachable, incomparable = hard_witness_certificate(pairwise)
    kmax, dmin, delta = finite_horizon_audit_bound(pairwise)
    structural[restored] = {
        "unreachable": unreachable,
        "incomparable": incomparable,
        "kmax": min(kmax, TARGET_COUNT),
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

full = frozenset(damaged_cids)
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
                if sub not in dmap:
                    continue
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

# Baseline target geometry explicitly exercises the pairwise branch when the
# selected reachable SCCs are incomparable in the condensation DAG.
base_unreachable, base_incomparable = hard_witness_certificate(
    pairwise_by_state[full]
)

print("INSACERMO_WIKI_VOTE_STRUCTURAL_AUDIT_V1")
print("SOURCE_URL", URL)
print("SOURCE_SHA256", sha)
print("NODES", len(nodes))
print("EDGES", edges)
print("SCC_COUNT", len(components))
print("SOURCE", source, "SOURCE_SCC_SIZE", len(components[source_comp]))
print("TARGETS", len(targets), " ".join(map(str, targets)))
print("TARGET_SCC_SIZES", " ".join(str(len(components[cid])) for cid in selected_cids))
print("BASELINE_UNREACHABLE_SINGLETONS", len(base_unreachable))
print("BASELINE_INCOMPARABLE_MINIMAL_PAIRS", len(base_incomparable))
print("CERTIFIED_HARD_AUDIT_ORDER", 2)
print("DEADLINE", DEADLINE)
print("CERTIFIED_FINITE_HORIZON_MAX_BUNDLE", CERTIFIED_MAX_BUNDLE)
print("CERTIFIED_CATALOGUE_BUNDLES", len(bundles))
print("CERTIFIED_INTACT_EVENTUAL_GAMMA", len(Gamma))

for restored in sorted(restoration_sets, key=lambda x: (len(x), tuple(sorted(x)))):
    label = "NONE" if not restored else "+".join(f"C{cid}" for cid in sorted(restored))
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
