import csv
import hashlib
import io
import urllib.request
from collections import Counter, defaultdict, deque

SOURCE_COMMIT = "5d623a6969a1adee7961cf1c9a8a212c4a784713"
URL = f"https://raw.githubusercontent.com/jpatokal/openflights/{SOURCE_COMMIT}/data/routes.dat"

raw = urllib.request.urlopen(URL, timeout=60).read()
print("SOURCE_COMMIT", SOURCE_COMMIT)
print("SOURCE_SHA256", hashlib.sha256(raw).hexdigest())
rows = list(csv.reader(io.StringIO(raw.decode("utf-8"))))

g = defaultdict(set)
rg = defaultdict(set)
degree = Counter()
airports = set()
valid_routes = 0
for r in rows:
    if len(r) < 5:
        continue
    src, dst = r[2], r[4]
    if src == "\\N" or dst == "\\N" or not src or not dst:
        continue
    airports.add(src)
    airports.add(dst)
    if dst not in g[src]:
        g[src].add(dst)
        rg[dst].add(src)
    degree[src] += 1
    degree[dst] += 1
    valid_routes += 1

for a in airports:
    g[a]
    rg[a]

# Kosaraju SCC decomposition.
seen = set()
order = []
for root in sorted(airports):
    if root in seen:
        continue
    stack = [(root, 0, None)]
    seen.add(root)
    while stack:
        u, idx, nbrs = stack[-1]
        if nbrs is None:
            nbrs = sorted(g[u])
            stack[-1] = (u, 0, nbrs)
        if idx < len(nbrs):
            v = nbrs[idx]
            stack[-1] = (u, idx + 1, nbrs)
            if v not in seen:
                seen.add(v)
                stack.append((v, 0, None))
        else:
            order.append(u)
            stack.pop()

comp_of = {}
components = []
for root in reversed(order):
    if root in comp_of:
        continue
    cid = len(components)
    members = []
    q = [root]
    comp_of[root] = cid
    while q:
        u = q.pop()
        members.append(u)
        for v in rg[u]:
            if v not in comp_of:
                comp_of[v] = cid
                q.append(v)
    components.append(sorted(members))

ncomp = len(components)
dag = [set() for _ in range(ncomp)]
indeg = [0] * ncomp
for u in airports:
    cu = comp_of[u]
    for v in g[u]:
        cv = comp_of[v]
        if cu != cv and cv not in dag[cu]:
            dag[cu].add(cv)
            indeg[cv] += 1

# Topological order of SCC condensation DAG.
q = deque(sorted(i for i, d in enumerate(indeg) if d == 0))
topo = []
while q:
    u = q.popleft()
    topo.append(u)
    for v in sorted(dag[u]):
        indeg[v] -= 1
        if indeg[v] == 0:
            q.append(v)
assert len(topo) == ncomp

# Exact transitive closure on the SCC DAG using Python integer bitsets.
reach = [0] * ncomp
for u in reversed(topo):
    bits = 1 << u
    for v in dag[u]:
        bits |= reach[v]
    reach[u] = bits

rep = [members[0] for members in components]

def reaches_airport(a, b):
    return bool(reach[comp_of[a]] & (1 << comp_of[b]))

def bfs_distance(start, target):
    if start == target:
        return 0
    dist = {start: 0}
    qq = deque([start])
    while qq:
        u = qq.popleft()
        for v in g[u]:
            if v in dist:
                continue
            dist[v] = dist[u] + 1
            if v == target:
                return dist[v]
            qq.append(v)
    return None

# A pair {q1,q2} is jointly impossible from start under one unbounded common
# trajectory iff both singletons are reachable from start but q1 and q2 lie in
# incomparable reachable SCCs. This is exact for the progressive common-path
# semantics: one can visit both iff one target can be reached from the other.
#
# We search all airports. Witness selection is fixed independently of outcome:
# maximize the minimum observed route incidence among (start,q1,q2), then total
# incidence, then use lexicographic tie-breaking.
best = None
starts_with_hidden_pair = 0
hidden_scc_pair_count = 0

for start in sorted(airports):
    cs = comp_of[start]
    reachable_cids = [c for c in range(ncomp) if c != cs and (reach[cs] & (1 << c))]
    found_for_start = False
    for i, c1 in enumerate(reachable_cids):
        for c2 in reachable_cids[i + 1:]:
            if (reach[c1] & (1 << c2)) or (reach[c2] & (1 << c1)):
                continue
            hidden_scc_pair_count += 1
            found_for_start = True
            # Pick the highest-degree airport inside each incomparable SCC.
            q1 = min(components[c1], key=lambda a: (-degree[a], a))
            q2 = min(components[c2], key=lambda a: (-degree[a], a))
            if q2 < q1:
                q1, q2 = q2, q1
            score = (
                min(degree[start], degree[q1], degree[q2]),
                degree[start] + degree[q1] + degree[q2],
                -max(len(components[c1]), len(components[c2])),
            )
            key = (score, tuple(-ord(ch) for ch in (start + "|" + q1 + "|" + q2)))
            # Explicit comparison: maximize score, then lexicographically smallest.
            candidate = (score, start, q1, q2, c1, c2)
            if best is None:
                best = candidate
            else:
                bscore, bs, b1, b2, _, _ = best
                if score > bscore or (score == bscore and (start, q1, q2) < (bs, b1, b2)):
                    best = candidate
    if found_for_start:
        starts_with_hidden_pair += 1

print("INSACERMO_EXACT_HIDDEN_JOINT_IMPOSSIBILITY_OPENFLIGHTS_V1")
print("RAW_ROWS", len(rows))
print("VALID_ROUTES", valid_routes)
print("AIRPORTS", len(airports))
print("SCC_COUNT", ncomp)
print("LARGEST_SCC", max(map(len, components)))
print("STARTS_WITH_HIDDEN_JOINT_PAIR", starts_with_hidden_pair)
print("HIDDEN_REACHABLE_INCOMPARABLE_SCC_PAIRS_ACROSS_STARTS", hidden_scc_pair_count)

if best is None:
    print("EXACT_HIDDEN_JOINT_WITNESS NONE")
else:
    score, start, q1, q2, c1, c2 = best
    d1 = bfs_distance(start, q1)
    d2 = bfs_distance(start, q2)
    q1_to_q2 = reaches_airport(q1, q2)
    q2_to_q1 = reaches_airport(q2, q1)
    assert d1 is not None and d2 is not None
    assert not q1_to_q2 and not q2_to_q1
    print("EXACT_HIDDEN_JOINT_WITNESS", start, q1, q2)
    print("SINGLETON_DEPTHS", q1, d1, q2, d2)
    print("TARGET_MUTUAL_REACHABILITY", f"{q1}_TO_{q2}", int(q1_to_q2), f"{q2}_TO_{q1}", int(q2_to_q1))
    print("TARGET_SCC_SIZES", q1, len(components[c1]), q2, len(components[c2]))
    print("ROUTE_INCIDENCE", start, degree[start], q1, degree[q1], q2, degree[q2])
    print("JOINT_DEPTH INF")
    print("CERTIFICATE both singleton futures are finite from START, but neither target can reach the other; therefore no single finite trajectory can visit both in any order")
