import csv, hashlib, io, itertools, urllib.request
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

raw = urllib.request.urlopen(URL, timeout=60).read()
assert hashlib.sha256(raw).hexdigest() == SOURCE_SHA256
rows = list(csv.reader(io.StringIO(raw.decode("utf-8"))))

g = defaultdict(set)
for r in rows:
    if len(r) >= 5 and r[2] not in ("", "\\N") and r[4] not in ("", "\\N"):
        g[r[2]].add(r[4])
g = {u: tuple(sorted(vs)) for u, vs in g.items()}

# Enumerate all baseline paths of <=H edges.
paths=[(START,)]
frontier=[(START,)]
for _ in range(H):
    nxt=[]
    for p in frontier:
        for v in g.get(p[-1],()):
            q=p+(v,)
            paths.append(q)
            nxt.append(q)
    frontier=nxt

bundles=[tuple(c) for k in range(1,MAX_BUNDLE+1) for c in itertools.combinations(REQUIRED,k)]
bundle_index={b:i for i,b in enumerate(bundles)}
required_set=set(REQUIRED)

# For each bundle, collect masks of required airports whose isolation would kill a witness.
# A witness survives cut C iff its touched-airport set is disjoint from C.
# We only need touched REQUIRED airports to scan candidate cuts.
witness_touch=[set() for _ in bundles]
for p in paths:
    seen=tuple(sorted(required_set.intersection(p)))
    touched=frozenset(required_set.intersection(p))
    for k in range(1,min(MAX_BUNDLE,len(seen))+1):
        for b in itertools.combinations(seen,k):
            witness_touch[bundle_index[b]].add(touched)

def feasible_under(cut, b):
    ws=witness_touch[bundle_index[b]]
    return any(t.isdisjoint(cut) for t in ws)

def proper_nonempty(b):
    for k in range(1,len(b)):
        yield from itertools.combinations(b,k)

def minobs(cut):
    feas={b: feasible_under(cut,b) for b in bundles}
    obs=[]
    for b in bundles:
        if len(b)<2 or feas[b]:
            continue
        if all(feas[tuple(s)] for s in proper_nonempty(b)):
            obs.append(b)
    return feas, set(obs)

base_feas, base_obs=minobs(frozenset())

hits=[]
for a,b in itertools.combinations(REQUIRED,2):
    cut=frozenset((a,b))
    deg_feas, deg_obs=minobs(cut)
    new_obs=sorted(deg_obs-base_obs)
    if not new_obs:
        continue
    feas_a,_=minobs(frozenset((b,)))  # restore a, keep b cut
    feas_b,_=minobs(frozenset((a,)))  # restore b, keep a cut
    only_a=sum(feas_a[o] and not feas_b[o] for o in new_obs)
    only_b=sum(feas_b[o] and not feas_a[o] for o in new_obs)
    either=sum(feas_a[o] and feas_b[o] for o in new_obs)
    neither=sum((not feas_a[o]) and (not feas_b[o]) for o in new_obs)
    # Exact 2-atom transversal is nontrivial when at least one obstruction
    # requires each distinct repair class.
    tau2=(only_a>0 and only_b>0)
    if tau2:
        hits.append((-(only_a+only_b), a,b,len(new_obs),only_a,only_b,either,neither))

hits.sort()
print("INSACERMO_OPENFLIGHTS_NONTRIVIAL_BOUND_SCAN_V1")
print("SOURCE_COMMIT",SOURCE_COMMIT)
print("PATHS",len(paths))
print("BUNDLES",len(bundles))
print("CANDIDATES_FOUND",len(hits))
for row in hits[:20]:
    _,a,b,n,oa,ob,e,ne=row
    print("CANDIDATE",a,b,"NEW_OBS",n,"ONLY_A",oa,"ONLY_B",ob,"EITHER",e,"NEITHER",ne)
print("RESULT","COMPLETE")
