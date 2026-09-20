import csv, hashlib, io, itertools, urllib.request
from collections import defaultdict

SOURCE_COMMIT="5d623a6969a1adee7961cf1c9a8a212c4a784713"
SOURCE_SHA256="bd373706238134f619c624c606dccc74c05c2582a977c489c81de501735f2390"
URL=f"https://raw.githubusercontent.com/jpatokal/openflights/{SOURCE_COMMIT}/data/routes.dat"
START="KEF"
REQUIRED=["LHR","CDG","FRA","AMS","MAD","FCO","ATH","IST","DXB","DOH","JFK","YYZ","MEX","GRU","EZE","CPT","JNB","DEL","SIN","HKG","NRT","SYD","AKL","LAX","SFO"]
H=3
MAX_BUNDLE=3
A="TK"
B="QR"

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
witnesses=[[] for _ in bundles]
for p in paths:
    seen=tuple(sorted(req.intersection(p)))
    carriers=tuple(frozenset(edge_airlines[(p[i],p[i+1])]) for i in range(len(p)-1))
    for k in range(1,min(MAX_BUNDLE,len(seen))+1):
        for b in itertools.combinations(seen,k):
            witnesses[bidx[frozenset(b)]].append(carriers)

def survives(carriers,deleted):
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
            obs.add(b)
    return feas,obs

base_feas,base_obs=complex_for(frozenset())
deg_feas,deg_obs=complex_for(frozenset((A,B)))
restore_A_feas,_=complex_for(frozenset((B,)))
restore_B_feas,_=complex_for(frozenset((A,)))
new_obs=sorted(deg_obs-base_obs)

caps={}
for o in new_obs:
    s=set()
    if restore_A_feas[o]:
        s.add(A)
    if restore_B_feas[o]:
        s.add(B)
    caps[o]=frozenset(s)

only_A=[o for o in new_obs if caps[o]==frozenset((A,))]
only_B=[o for o in new_obs if caps[o]==frozenset((B,))]
either=[o for o in new_obs if caps[o]==frozenset((A,B))]
neither=[o for o in new_obs if not caps[o]]

atoms=(A,B)
def hits_all(sub):
    S=set(sub)
    return all(S & set(caps[o]) for o in new_obs if caps[o])

tau=None
tau_set=None
for k in range(3):
    for sub in itertools.combinations(atoms,k):
        if hits_all(sub):
            tau=k
            tau_set=sub
            break
    if tau is not None:
        break

ACTIONS={
    "NONE": (0,frozenset((A,B))),
    "RESTORE_TK": (1,frozenset((B,))),
    "RESTORE_QR": (1,frozenset((A,))),
    "RESTORE_BOTH": (2,frozenset()),
}
def restores_all(deleted):
    return all(feasible(deleted,o) for o in new_obs)

candidates=[(cost,name) for name,(cost,deleted) in ACTIONS.items() if restores_all(deleted)]
assert candidates
Cstar,best=min(candidates)
trivial=1 if new_obs else 0

# Fixed expectations from the exploratory selection report.
assert len(new_obs)==11
assert len(only_A)==4
assert len(only_B)==6
assert len(either)==1
assert len(neither)==0
assert tau==2
assert Cstar==2
assert trivial==1

print("INSACERMO_OPENFLIGHTS_NONTRIVIAL_REPAIR_BOUND_SELECTED_AUDIT_V1")
print("STATUS POST_SELECTION_SAME_DATA_NOT_CONFIRMATORY")
print("SOURCE_COMMIT",SOURCE_COMMIT)
print("SOURCE_SHA256",SOURCE_SHA256)
print("AIRLINE_PAIR",A,B)
print("PATHS",len(paths))
print("BUNDLES",len(bundles))
print("BASELINE_MINIMAL_OBSTRUCTIONS",len(base_obs))
print("DEGRADED_MINIMAL_OBSTRUCTIONS",len(deg_obs))
print("NEW_MINIMAL_OBSTRUCTIONS",len(new_obs))
print("ONLY_TK",len(only_A))
print("ONLY_QR",len(only_B))
print("EITHER",len(either))
print("NEITHER",len(neither))
print("MIN_ORDER_ONLY_TK",min(map(len,only_A)))
print("MIN_ORDER_ONLY_QR",min(map(len,only_B)))
print("TRIVIAL_LOWER_BOUND",trivial)
print("TRANSVERSAL_TAU",tau)
print("TRANSVERSAL_SET",",".join(tau_set))
print("EXACT_REPAIR_COST",Cstar)
print("EXACT_REPAIR_ACTION",best)
print("BOUND_RATIO_TAU_OVER_CSTAR",f"{tau/Cstar:.6f}")
print("NONTRIVIAL_GAP",tau-trivial)
print("RESULT COMPLETE")
