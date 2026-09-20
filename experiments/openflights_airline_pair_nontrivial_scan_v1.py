import csv, hashlib, io, itertools, urllib.request
from collections import defaultdict, Counter

SOURCE_COMMIT="5d623a6969a1adee7961cf1c9a8a212c4a784713"
SOURCE_SHA256="bd373706238134f619c624c606dccc74c05c2582a977c489c81de501735f2390"
URL=f"https://raw.githubusercontent.com/jpatokal/openflights/{SOURCE_COMMIT}/data/routes.dat"
START="KEF"
REQUIRED=["LHR","CDG","FRA","AMS","MAD","FCO","ATH","IST","DXB","DOH","JFK","YYZ","MEX","GRU","EZE","CPT","JNB","DEL","SIN","HKG","NRT","SYD","AKL","LAX","SFO"]
H=3
MAX_BUNDLE=3
TOP_AIRLINES=40

raw=urllib.request.urlopen(URL,timeout=60).read()
assert hashlib.sha256(raw).hexdigest()==SOURCE_SHA256
rows=list(csv.reader(io.StringIO(raw.decode("utf-8"))))

edge_airlines=defaultdict(set)
for r in rows:
    if len(r)>=5 and r[0] not in ("","\\N") and r[2] not in ("","\\N") and r[4] not in ("","\\N"):
        edge_airlines[(r[2],r[4])].add(r[0])

g=defaultdict(set)
for u,v in edge_airlines:
    g[u].add(v)
g={u:tuple(sorted(vs)) for u,vs in g.items()}

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
bidx={frozenset(b):i for i,b in enumerate(bundles)}
req=set(REQUIRED)

# baseline witness records, indexed by each bundle they witness
witnesses=[[] for _ in bundles]
for p in paths:
    seen=tuple(sorted(req.intersection(p)))
    edges=tuple((p[i],p[i+1]) for i in range(len(p)-1))
    carriers=tuple(frozenset(edge_airlines[e]) for e in edges)
    for k in range(1,min(MAX_BUNDLE,len(seen))+1):
        for b in itertools.combinations(seen,k):
            witnesses[bidx[frozenset(b)]].append(carriers)

# Rank airlines by number of graph edges for which they are the sole carrier;
# these are the only one-airline deletions that can alter the collapsed graph.
sole=Counter()
for e,als in edge_airlines.items():
    if len(als)==1:
        sole[next(iter(als))]+=1
candidates=[a for a,_ in sole.most_common(TOP_AIRLINES)]

def survives(carriers, deleted):
    return all(bool(cs-set(deleted)) for cs in carriers)

def feasible(deleted,b):
    return any(survives(w,deleted) for w in witnesses[bidx[frozenset(b)]])

def proper(b):
    for k in range(1,len(b)):
        yield from itertools.combinations(b,k)

def complex_for(deleted):
    feas={b:feasible(deleted,b) for b in bundles}
    obs=set()
    for b in bundles:
        if feas[b]:
            continue
        if all(feas[tuple(s)] for s in proper(b)):
            # include singleton minimal nonfaces too, but later require
            # higher-order witnesses for the nontrivial endpoint.
            obs.add(b)
    return feas,obs

base_feas,base_obs=complex_for(frozenset())
single={}
for a in candidates:
    single[a]=complex_for(frozenset((a,)))

hits=[]
for a,b in itertools.combinations(candidates,2):
    deg_feas,deg_obs=complex_for(frozenset((a,b)))
    new=sorted(deg_obs-base_obs)
    # Require at least one higher-order new obstruction repaired exclusively
    # by each distinct atom. This avoids a tau=2 result driven only by
    # singleton airport-like failures.
    only_a=[]; only_b=[]; either=[]; neither=[]
    feas_restore_a=single[b][0]  # a restored, b remains deleted
    feas_restore_b=single[a][0]  # b restored, a remains deleted
    for o in new:
        aa=feas_restore_a[o]
        bb=feas_restore_b[o]
        bucket = only_a if aa and not bb else only_b if bb and not aa else either if aa and bb else neither
        bucket.append(o)
    hoa=any(len(o)>=2 for o in only_a)
    hob=any(len(o)>=2 for o in only_b)
    if hoa and hob:
        hits.append((-(len(only_a)+len(only_b)),a,b,len(new),len(only_a),len(only_b),len(either),len(neither),
                     min(len(o) for o in only_a),min(len(o) for o in only_b)))

hits.sort()
print("INSACERMO_OPENFLIGHTS_AIRLINE_PAIR_NONTRIVIAL_SCAN_V1")
print("SOURCE_COMMIT",SOURCE_COMMIT)
print("PATHS",len(paths))
print("BUNDLES",len(bundles))
print("AIRLINE_CANDIDATES",len(candidates))
print("TOP_AIRLINES"," ".join(candidates))
print("CANDIDATES_FOUND",len(hits))
for row in hits[:20]:
    _,a,b,n,oa,ob,e,ne,mina,minb=row
    print("CANDIDATE",a,b,"NEW_OBS",n,"ONLY_A",oa,"ONLY_B",ob,"EITHER",e,"NEITHER",ne,"MIN_ORDER_A",mina,"MIN_ORDER_B",minb)
print("RESULT COMPLETE")
