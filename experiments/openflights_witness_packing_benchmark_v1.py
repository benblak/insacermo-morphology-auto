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
            paths.append(q); nxt.append(q)
    frontier=nxt

bundles=[tuple(c) for k in range(1,MAX_BUNDLE+1) for c in itertools.combinations(REQUIRED,k)]
bidx={frozenset(b):i for i,b in enumerate(bundles)}
req=set(REQUIRED)

# For each bundle, store baseline witness paths as edge-carrier tuples.
witnesses=[[] for _ in bundles]
for p in paths:
    seen=tuple(sorted(req.intersection(p)))
    carriers=tuple(frozenset(edge_airlines[(p[i],p[i+1])]) for i in range(len(p)-1))
    for k in range(1,min(MAX_BUNDLE,len(seen))+1):
        for b in itertools.combinations(seen,k):
            witnesses[bidx[frozenset(b)]].append(carriers)

sole=Counter()
for e,als in edge_airlines.items():
    if len(als)==1:
        sole[next(iter(als))]+=1
airlines=[a for a,_ in sole.most_common(TOP_AIRLINES)]

def path_survives(carriers, deleted, restored):
    unavailable=set(deleted)-set(restored)
    return all(bool(cs-unavailable) for cs in carriers)

def feasible(bundle, deleted, restored=frozenset()):
    return any(path_survives(w,deleted,restored) for w in witnesses[bidx[frozenset(bundle)]])

def proper(b):
    for k in range(1,len(b)):
        yield from itertools.combinations(b,k)

def minimal_obs(deleted,restored=frozenset()):
    feas={b:feasible(b,deleted,restored) for b in bundles}
    obs=set()
    for b in bundles:
        if feas[b]:
            continue
        if all(feas[tuple(s)] for s in proper(b)):
            obs.add(b)
    return feas,obs

base_feas,base_obs=minimal_obs(frozenset())

def min_signatures(bundle, deleted):
    atoms=tuple(sorted(deleted))
    good=[]
    for k in range(len(atoms)+1):
        for sub in itertools.combinations(atoms,k):
            S=frozenset(sub)
            if feasible(bundle,deleted,S):
                if not any(T < S for T in good):
                    good.append(S)
    mins=[S for S in good if not any(T < S for T in good)]
    return mins

def packing_bound(futures, sigs):
    # Exhaustive over all subfamilies is unnecessary for two atoms:
    # a positive packed contribution can contain at most two nonempty,
    # pairwise-disjoint repair universes.
    data=[]
    for f in futures:
        ms=sigs[f]
        if not ms: continue
        universe=frozenset().union(*ms)
        floor=min(len(s) for s in ms)
        if floor>0:
            data.append((f,universe,floor))
    best=0
    for _,u,c in data:
        best=max(best,c)
    for (_,u,c),(_,v,d) in itertools.combinations(data,2):
        if u.isdisjoint(v):
            best=max(best,c+d)
    return best

rows_out=[]
for a,b in itertools.combinations(airlines,2):
    deleted=frozenset((a,b))
    deg_feas,deg_obs=minimal_obs(deleted)
    new=sorted(deg_obs-base_obs)
    if not new:
        continue
    sigs={f:min_signatures(f,deleted) for f in new}
    # exact repair cost restoring all new obstructions
    actions=[frozenset(),frozenset((a,)),frozenset((b,)),frozenset((a,b))]
    exact=min(len(S) for S in actions if all(feasible(f,deleted,S) for f in new))
    pack=packing_bound(new,sigs)
    # old transversal over necessary-touch universes
    universes={f:frozenset().union(*sigs[f]) if sigs[f] else frozenset() for f in new}
    tau=None
    for S in actions:
        if all(S & universes[f] for f in new if universes[f]):
            tau=len(S); break
    if tau is None: tau=0
    rows_out.append((a,b,len(new),pack,tau,exact))

n=len(rows_out)
pack_eq=sum(p==c for _,_,_,p,_,c in rows_out)
tau_eq=sum(t==c for _,_,_,_,t,c in rows_out)
pack_nontriv=sum(p>1 for _,_,_,p,_,_ in rows_out)
pack_stronger=sum(p>t for _,_,_,p,t,_ in rows_out)
violations=[r for r in rows_out if r[3]>r[5]]

print("INSACERMO_OPENFLIGHTS_WITNESS_PACKING_BENCHMARK_V1")
print("STATUS EXPLORATORY_SYSTEMATIC")
print("SOURCE_COMMIT",SOURCE_COMMIT)
print("AIRLINE_PAIRS_WITH_NEW_OBS",n)
print("PACKING_EQ_CSTAR",pack_eq)
print("TAU_EQ_CSTAR",tau_eq)
print("PACKING_NONTRIVIAL_GT1",pack_nontriv)
print("PACKING_STRONGER_THAN_TAU",pack_stronger)
print("PACKING_BOUND_VIOLATIONS",len(violations))
from collections import Counter as C
print("PACKING_DISTRIBUTION",dict(sorted(C(r[3] for r in rows_out).items())))
print("CSTAR_DISTRIBUTION",dict(sorted(C(r[5] for r in rows_out).items())))
for r in sorted(rows_out,key=lambda x:(-(x[3]/x[5] if x[5] else 0),-x[2],x[0],x[1]))[:20]:
    print("PAIR",r[0],r[1],"NEW_OBS",r[2],"PACK",r[3],"TAU",r[4],"CSTAR",r[5])
print("RESULT COMPLETE")
