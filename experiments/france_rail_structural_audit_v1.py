import csv
import hashlib
import io
import itertools
import urllib.request
import zipfile
from collections import Counter, defaultdict, deque

GTFS_URL = "https://eu.ftp.opendatasoft.com/sncf/plandata/Export_OpenData_SNCF_GTFS_NewTripId.zip"
TARGET_COUNT = 12
DEADLINE = 4
BUDGET = 1
UNIT_EDGE_COST = 1

raw = urllib.request.urlopen(GTFS_URL, timeout=120).read()
sha = hashlib.sha256(raw).hexdigest()
z = zipfile.ZipFile(io.BytesIO(raw))

def read_csv(name):
    with z.open(name) as f:
        return list(csv.DictReader(io.TextIOWrapper(f, encoding="utf-8-sig")))

stops = read_csv("stops.txt")
routes = read_csv("routes.txt")
trips = read_csv("trips.txt")
stop_times = read_csv("stop_times.txt")

# Rail-only. Standard GTFS railway route_type=2.
rail_routes = {r["route_id"] for r in routes if r.get("route_type") == "2"}
rail_trips = {t["trip_id"] for t in trips if t["route_id"] in rail_routes}
assert rail_routes, "no rail routes found"
assert rail_trips, "no rail trips found"

stop_info = {s["stop_id"]: s for s in stops}

def station_id(stop_id):
    s = stop_info[stop_id]
    parent = (s.get("parent_station") or "").strip()
    return parent or stop_id

station_name = {}
for s in stops:
    sid = station_id(s["stop_id"])
    # Prefer parent station name when available.
    if sid in stop_info:
        station_name[sid] = stop_info[sid].get("stop_name", sid)
    else:
        station_name.setdefault(sid, s.get("stop_name", sid))

seqs = defaultdict(list)
for st in stop_times:
    trip = st["trip_id"]
    if trip not in rail_trips:
        continue
    sid = st["stop_id"]
    if sid not in stop_info:
        continue
    try:
        seq = int(st["stop_sequence"])
    except Exception:
        continue
    seqs[trip].append((seq, station_id(sid)))

g = defaultdict(set)
edge_freq = Counter()
nodes = set()
for trip, seq in seqs.items():
    seq.sort()
    path = []
    last = None
    for _, s in seq:
        if s != last:
            path.append(s)
            last = s
    for a, b in zip(path, path[1:]):
        if a == b:
            continue
        g[a].add(b)
        edge_freq[(a, b)] += 1
        nodes.add(a); nodes.add(b)
for n in nodes:
    g[n]

outdeg = {n: len(g[n]) for n in nodes}
indeg = Counter()
for u in nodes:
    for v in g[u]:
        indeg[v] += 1

def bfs(graph, start):
    d = {start: 0}
    q = deque([start])
    while q:
        u = q.popleft()
        for v in graph.get(u, ()):
            if v not in d:
                d[v] = d[u] + 1
                q.append(v)
    return d

# Frozen structural selection: max out-degree source, tie by station name/id.
source = min(nodes, key=lambda n: (-outdeg[n], station_name.get(n, n), n))
source_reach = bfs(g, source)

def degree(n):
    return outdeg.get(n, 0) + indeg.get(n, 0)

candidates = [n for n in nodes if n != source and n in source_reach]
targets = sorted(
    candidates,
    key=lambda n: (-degree(n), station_name.get(n, n), n)
)[:TARGET_COUNT]
assert len(targets) == TARGET_COUNT

# Three fixed closure classes selected by target ranks 1, 6, 12.
closure_stations = [targets[0], targets[5], targets[11]]

restoration_sets = [frozenset()]
for s in closure_stations:
    restoration_sets.append(frozenset([s]))
for p in itertools.combinations(closure_stations, 2):
    restoration_sets.append(frozenset(p))
restoration_sets.append(frozenset(closure_stations))

def graph_for(restored):
    restored = set(restored)
    blocked = set(closure_stations) - restored
    gg = defaultdict(set)
    for u in nodes:
        if u in blocked:
            continue
        for v in g[u]:
            if v in blocked:
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
    return any(q in b for q in unreachable) or any(
        q in b and r in b for q, r in incomparable
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
        total = 0
        cur = source
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
    pairwise = {s: bfs(gg, s) for s in [source] + targets}
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
    b for k in range(1, CERTIFIED_MAX_BUNDLE + 1)
    for b in itertools.combinations(targets, k)
]

depths = {
    restored: {
        b: joint_depth(pairwise_by_state[restored], b)
        for b in bundles
    }
    for restored in restoration_sets
}

full = frozenset(closure_stations)
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
        "rank": observed_rank,
        "miss": miss,
        "safe": len(Gamma) - miss,
    }

admissible = [s for s in restoration_sets if len(s) <= BUDGET]
true_irreversible = [
    b for b in Gamma if all(depths[s][b] is None for s in admissible)
]

print("INSACERMO_FRANCE_RAIL_STRUCTURAL_AUDIT_V1")
print("STATUS EXPLORATORY_NATIONAL_TRANSPORT_PILOT")
print("GTFS_URL", GTFS_URL)
print("GTFS_SHA256", sha)
print("RAIL_ROUTES", len(rail_routes))
print("RAIL_TRIPS", len(rail_trips))
print("STATION_NODES", len(nodes))
print("DIRECTED_STATION_EDGES", sum(len(v) for v in g.values()))
print("SOURCE_ID", source)
print("SOURCE_NAME", station_name.get(source, source))
print("TARGET_COUNT", len(targets))
for i, t in enumerate(targets, 1):
    print("TARGET", i, t, station_name.get(t, t), "DEGREE", degree(t), "SOURCE_DEPTH", source_reach[t])
print("CLOSURE_CLASSES", " | ".join(station_name.get(s, s) for s in closure_stations))
print("CERTIFIED_HARD_AUDIT_ORDER", 2)
print("DEADLINE", DEADLINE)
print("CERTIFIED_FINITE_HORIZON_MAX_BUNDLE", CERTIFIED_MAX_BUNDLE)
print("CERTIFIED_CATALOGUE_BUNDLES", len(bundles))
print("CERTIFIED_INTACT_EVENTUAL_GAMMA", len(Gamma))

for restored in sorted(restoration_sets, key=lambda x: (len(x), tuple(sorted(x)))):
    label = "NONE" if not restored else "+".join(station_name.get(s, s) for s in sorted(restored))
    s = structural[restored]
    r = results[restored]
    print(
        "STRUCTURAL_RESTORED", label,
        "UNREACHABLE_SINGLETONS", len(s["unreachable"]),
        "INCOMPARABLE_MINIMAL_PAIRS", len(s["incomparable"]),
        "D_MIN", s["dmin"],
        "FINITE_AUDIT_BOUND", s["kmax"],
        "OBSERVED_DEADLINE_RANK", r["rank"],
        "HARD_LOSS", r["hard"],
        "SOFT_LOSS", r["soft"],
        "SAFE", r["safe"],
    )

print("ADMISSIBLE_REPAIR_STATES", len(admissible))
print("TRUE_IRREVERSIBLE_BUNDLES", len(true_irreversible))
print("STRUCTURAL_CERTIFICATE_STATUS VERIFIED_BY_RUNTIME_CROSSCHECK")
print("RESULT COMPLETE")
