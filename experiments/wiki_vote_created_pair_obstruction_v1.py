import gzip
import hashlib
import sys
import urllib.request
from collections import Counter, defaultdict, deque

URL = "https://snap.stanford.edu/data/wiki-Vote.txt.gz"
EXPECTED_NODES = 7115
EXPECTED_EDGES = 103689
MAX_CANDIDATE_SCCS = 300

sys.setrecursionlimit(100000)

with urllib.request.urlopen(URL, timeout=120) as r:
    raw = r.read()
sha = hashlib.sha256(raw).hexdigest()
text = gzip.decompress(raw).decode("utf-8")

g = defaultdict(set)
rg = defaultdict(set)
nodes = set()
outdeg = Counter()
indeg = Counter()
edges = []
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
        edges.append((u, v))
for n in nodes:
    g[n]
    rg[n]

assert len(nodes) == EXPECTED_NODES, len(nodes)
assert len(edges) == EXPECTED_EDGES, len(edges)

source = min(nodes, key=lambda n: (-outdeg[n], n))

# SCC decomposition (Kosaraju).
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

C = len(components)
cg = defaultdict(set)
edge_class_count = Counter()
for u, v in edges:
    cu, cv = comp_of[u], comp_of[v]
    if cu != cv:
        cg[cu].add(cv)
        edge_class_count[(cu, cv)] += 1
for cid in range(C):
    cg[cid]

source_c = comp_of[source]

def bfs_dag(start, blocked_edge=None, want_parent=False):
    dist = {start: 0}
    parent = {}
    q = deque([start])
    while q:
        u = q.popleft()
        for v in sorted(cg[u]):
            if blocked_edge is not None and (u, v) == blocked_edge:
                continue
            if v not in dist:
                dist[v] = dist[u] + 1
                parent[v] = u
                q.append(v)
    return (dist, parent) if want_parent else dist

source_reach = bfs_dag(source_c)
reachable_cids = [cid for cid in source_reach if cid != source_c]
ranked = sorted(
    reachable_cids,
    key=lambda cid: (-len(components[cid]), min(components[cid]))
)[:MAX_CANDIDATE_SCCS]

# Representative rule is fixed by SCC: highest total degree, tie smallest id.
def totaldeg(n):
    return indeg[n] + outdeg[n]

rep = {
    cid: min(components[cid], key=lambda n: (-totaldeg(n), n))
    for cid in ranked
}

# Deterministic exploratory witness search:
# candidate SCCs by size; first ordered comparable pair; first edge on its
# shortest condensation path whose removal preserves source access to both
# endpoints but destroys q->r reachability.
witness = None
for cq in ranked:
    q_reach, q_parent = bfs_dag(cq, want_parent=True)
    for cr in ranked:
        if cq == cr or cr not in q_reach:
            continue
        # Reconstruct one shortest cq -> cr condensation path.
        path = [cr]
        cur = cr
        while cur != cq:
            cur = q_parent[cur]
            path.append(cur)
        path.reverse()
        for a, b in zip(path, path[1:]):
            blocked = (a, b)
            src_after = bfs_dag(source_c, blocked)
            if cq not in src_after or cr not in src_after:
                continue
            q_after = bfs_dag(cq, blocked)
            if cr in q_after:
                continue
            # Condensation is acyclic, so cr cannot reach cq when cq != cr.
            witness = (cq, cr, blocked, tuple(path))
            break
        if witness is not None:
            break
    if witness is not None:
        break

assert witness is not None, "no pair-separation witness found in candidate SCCs"
cq, cr, blocked, path = witness
q = rep[cq]
r = rep[cr]
a, b = blocked

# Verify on original graph after deleting the entire real edge class a -> b.
def bfs_original(start, blocked_class=None):
    dist = {start: 0}
    qq = deque([start])
    while qq:
        u = qq.popleft()
        cu = comp_of[u]
        for v in g[u]:
            if blocked_class is not None and (cu, comp_of[v]) == blocked_class:
                continue
            if v not in dist:
                dist[v] = dist[u] + 1
                qq.append(v)
    return dist

before_s = bfs_original(source)
before_q = bfs_original(q)
before_r = bfs_original(r)

after_s = bfs_original(source, blocked)
after_q = bfs_original(q, blocked)
after_r = bfs_original(r, blocked)

assert q in before_s and r in before_s
assert r in before_q
assert q not in before_r  # distinct SCCs in a DAG order

assert q in after_s and r in after_s
assert r not in after_q
assert q not in after_r

# Thus both singleton contracts remain feasible, while the pair becomes a
# minimal hard obstruction of order exactly 2.
before_pair_feasible = (r in before_q) or (q in before_r)
after_pair_feasible = (r in after_q) or (q in after_r)
assert before_pair_feasible
assert not after_pair_feasible

removed_edges = [
    (u, v) for (u, v) in edges
    if (comp_of[u], comp_of[v]) == blocked
]
assert len(removed_edges) == edge_class_count[blocked]

print("INSACERMO_WIKI_VOTE_CREATED_PAIR_OBSTRUCTION_V1")
print("STATUS EXPLORATORY_MECHANISM_WITNESS")
print("SOURCE_URL", URL)
print("SOURCE_SHA256", sha)
print("NODES", len(nodes))
print("EDGES", len(edges))
print("SCC_COUNT", C)
print("SOURCE", source, "SOURCE_SCC", source_c)
print("Q", q, "Q_SCC", cq, "Q_SCC_SIZE", len(components[cq]))
print("R", r, "R_SCC", cr, "R_SCC_SIZE", len(components[cr]))
print("BASELINE_Q_REACHABLE", int(q in before_s))
print("BASELINE_R_REACHABLE", int(r in before_s))
print("BASELINE_Q_TO_R", int(r in before_q))
print("BASELINE_R_TO_Q", int(q in before_r))
print("DESTROYED_EDGE_CLASS", a, b)
print("DESTROYED_EDGE_CLASS_REAL_EDGES", len(removed_edges))
print("CONDENSATION_SHORTEST_PATH_LENGTH", len(path) - 1)
print("AFTER_Q_REACHABLE", int(q in after_s))
print("AFTER_R_REACHABLE", int(r in after_s))
print("AFTER_Q_TO_R", int(r in after_q))
print("AFTER_R_TO_Q", int(q in after_r))
print("SINGLETON_Q_PRESERVED", int(q in after_s))
print("SINGLETON_R_PRESERVED", int(r in after_s))
print("PAIR_BEFORE_FEASIBLE", int(before_pair_feasible))
print("PAIR_AFTER_HARD_LOSS", int(not after_pair_feasible))
print("MINIMAL_HARD_OBSTRUCTION_ORDER", 2)
print("MECHANISM CREATED_INCOMPARABILITY")
print("RESULT COMPLETE")
