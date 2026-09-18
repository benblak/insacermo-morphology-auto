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
MAX_BUNDLE = 3
DEADLINE = 4
BUDGET = 1

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

assert len(nodes) == EXPECTED_NODES, len(nodes)
assert len(edges) == EXPECTED_EDGES, len(edges)
assert set(labels) == nodes, (len(labels), len(nodes))

# Blind predeclared structural selection rule:
# 1) source = maximum out-degree node, tie by smallest node id;
# 2) candidate departments = all departments except source's department,
#    ranked by descending department size, tie by department id;
# 3) targets = one representative from each of the first 12 departments,
#    representative = maximum total degree, tie by smallest node id;
# 4) damaged departments = ranks 1, 6 and 12 among those same 12.
source = min(nodes, key=lambda n: (-outdeg[n], n))
source_dept = labels[source]

ranked_depts = sorted(
    (d for d in dept_nodes if d != source_dept),
    key=lambda d: (-len(dept_nodes[d]), d),
)
selected_depts = ranked_depts[:TARGET_COUNT]
assert len(selected_depts) == TARGET_COUNT

def totaldeg(n):
    return outdeg[n] + indeg[n]

targets = []
for d in selected_depts:
    rep = min(dept_nodes[d], key=lambda n: (-totaldeg(n), n))
    targets.append(rep)

damaged_depts = [selected_depts[0], selected_depts[5], selected_depts[11]]

bundles = []
for k in range(1, MAX_BUNDLE + 1):
    bundles.extend(itertools.combinations(targets, k))

def graph_for(restored):
    restored = set(restored)
    g = defaultdict(set)
    for u, v in edges:
        du, dv = labels[u], labels[v]
        blocked_u = du in damaged_depts and du not in restored
        blocked_v = dv in damaged_depts and dv not in restored
        if blocked_u or blocked_v:
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

def joint_depth(g, bundle):
    sources = [source] + list(bundle)
    dmap = {s: bfs(g, s) for s in sources}
    best = None
    for perm in itertools.permutations(bundle):
        total = 0
        cur = source
        ok = True
        for nxt in perm:
            step = dmap[cur].get(nxt)
            if step is None:
                ok = False
                break
            total += step
            cur = nxt
        if ok and (best is None or total < best):
            best = total
    return best

restoration_sets = [frozenset()]
for d in damaged_depts:
    restoration_sets.append(frozenset([d]))
for pair in itertools.combinations(damaged_depts, 2):
    restoration_sets.append(frozenset(pair))
restoration_sets.append(frozenset(damaged_depts))

results = {}
depths_by_state = {}
for restored in restoration_sets:
    g = graph_for(restored)
    depths = {b: joint_depth(g, b) for b in bundles}
    depths_by_state[restored] = depths
    finite = sum(v is not None for v in depths.values())
    irreversible = len(bundles) - finite
    safe_h = sum(v is not None and v <= DEADLINE for v in depths.values())
    results[restored] = {
        "finite": finite,
        "irreversible": irreversible,
        "safe_h": safe_h,
        "deadline_miss": len(bundles) - safe_h,
    }

# Intact baseline family: every bundle finite in the fully restored graph.
full = frozenset(damaged_depts)
Gamma = [b for b in bundles if depths_by_state[full][b] is not None]
assert Gamma, "empty intact feasible family"

def minimal_obstructions(restored):
    depths = depths_by_state[restored]
    obs = []
    for b in Gamma:
        if depths[b] is not None:
            continue
        proper_ok = True
        for r in range(1, len(b)):
            for sub in itertools.combinations(b, r):
                if depths.get(sub) is None:
                    proper_ok = False
                    break
            if not proper_ok:
                break
        if proper_ok:
            obs.append(b)
    return obs

repair_price = {}
for b in Gamma:
    opts = [len(s) for s in restoration_sets if depths_by_state[s][b] is not None]
    assert opts, b
    repair_price[b] = min(opts)

hist = Counter(repair_price.values())

one_actions = [frozenset([d]) for d in damaged_depts]
action_stats = []
for a in one_actions:
    depths = depths_by_state[a]
    irre = sum(depths[b] is None for b in Gamma)
    miss = sum(depths[b] is None or depths[b] > DEADLINE for b in Gamma)
    action_stats.append((next(iter(a)), irre, miss))

best_irrev = min(action_stats, key=lambda x: (x[1], x[2], x[0]))
best_deadline = min(action_stats, key=lambda x: (x[2], x[1], x[0]))

print("INSACERMO_POSTFREEZE_EMAIL_EU_CORE_BLIND_V1")
print("STATUS BLIND_CONFIRMATORY_POSTFREEZE")
print("EDGE_URL", EDGE_URL)
print("LABEL_URL", LABEL_URL)
print("EDGE_SHA256", edge_sha)
print("LABEL_SHA256", label_sha)
print("NODES", len(nodes))
print("EDGES", len(edges))
print("DEPARTMENTS", len(dept_nodes))
print("SOURCE", source, "SOURCE_DEPT", source_dept, "OUTDEG", outdeg[source])
print("TARGET_COUNT", len(targets))
print("TARGETS", " ".join(map(str, targets)))
print("TARGET_DEPARTMENTS", " ".join(map(str, selected_depts)))
print("DAMAGED_DEPARTMENTS", " ".join(map(str, damaged_depts)))
print("CATALOGUE_BUNDLES", len(bundles))
print("INTACT_FEASIBLE_GAMMA", len(Gamma))
print("MAX_BUNDLE", MAX_BUNDLE)
print("DEADLINE", DEADLINE)
print("BUDGET", BUDGET)
print("SEMANTICS directed common-path progressive bundle recovery; damaged department removes all incident email edges until restored")

for s in sorted(restoration_sets, key=lambda x: (len(x), tuple(sorted(x)))):
    label = "NONE" if not s else "+".join(f"D{d}" for d in sorted(s))
    r = results[s]
    obs = minimal_obstructions(s)
    gamma_irrev = sum(depths_by_state[s][b] is None for b in Gamma)
    gamma_safe = sum(depths_by_state[s][b] is not None and depths_by_state[s][b] <= DEADLINE for b in Gamma)
    print(
        "RESTORED", label,
        "COST", len(s),
        "GAMMA_FINITE", len(Gamma) - gamma_irrev,
        "GAMMA_IRREVERSIBLE", gamma_irrev,
        "IRREVERSIBLE_RISK", f"{gamma_irrev/len(Gamma):.12f}",
        "GAMMA_SAFE_H", gamma_safe,
        "DEADLINE_MISS", len(Gamma) - gamma_safe,
        "DEADLINE_RISK", f"{(len(Gamma)-gamma_safe)/len(Gamma):.12f}",
        "MINIMAL_OBSTRUCTIONS", len(obs),
        "MIN_OBS_SIZE1", sum(len(b)==1 for b in obs),
        "MIN_OBS_SIZE2", sum(len(b)==2 for b in obs),
        "MIN_OBS_SIZE3", sum(len(b)==3 for b in obs),
    )

print("REPAIR_PRICE_HIST", " ".join(f"C{k}:{hist[k]}" for k in sorted(hist)))
for d, irre, miss in action_stats:
    print(
        "ACTION", f"RESTORE_D{d}",
        "COST 1",
        "IRREVERSIBLE", irre,
        "IRREVERSIBLE_RISK", f"{irre/len(Gamma):.12f}",
        "DEADLINE_MISS", miss,
        "DEADLINE_RISK", f"{miss/len(Gamma):.12f}",
    )
print("BUDGET1_MIN_IRREVERSIBLE_RISK", f"RESTORE_D{best_irrev[0]}")
print("BUDGET1_MIN_DEADLINE_RISK", f"RESTORE_D{best_deadline[0]}")
print("RESULT COMPLETE")
