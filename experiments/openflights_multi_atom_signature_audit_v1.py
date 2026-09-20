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

def path_survives(carriers, deleted, restored=frozenset()):
    unavailable=set(deleted)-set(restored)
    return all(bool(cs-unavailable) for cs in carriers)

def feasible(bundle, deleted, restored=frozenset()):
    return any(path_survives(w,deleted,restored) for w in witnesses[bidx[frozenset(bundle)]])

def proper(b):
    for k in range(1,len(b)):
        yield from itertools.combinations(b,k)

def minimal_obs(deleted, restored=frozenset()):
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
    restoring=[]
    for k in range(len(atoms)+1):
        for sub in itertools.combinations(atoms,k):
            S=frozenset(sub)
            if feasible(bundle,deleted,S):
                restoring.append(S)
    mins=[S for S in restoring if not any(T < S for T in restoring)]
    return sorted(mins,key=lambda s:(len(s),tuple(sorted(s))))

pair_rows=[]
global_hist=Counter()
multi_examples=[]
for a,b in itertools.combinations(airlines,2):
    deleted=frozenset((a,b))
    _,deg_obs=minimal_obs(deleted)
    new=sorted(deg_obs-base_obs)
    if not new:
        continue
    costs=[]
    local_multi=[]
    for f in new:
        mins=min_signatures(f,deleted)
        if not mins:
            continue
        c=min(len(s) for s in mins)
        costs.append(c)
        global_hist[c]+=1
        if c>=2:
            local_multi.append((f,mins))
            multi_examples.append((a,b,f,mins))
    pair_rows.append((a,b,len(new),Counter(costs),len(local_multi)))

pairs_with_multi=sum(r[4]>0 for r in pair_rows)
total_new=sum(r[2] for r in pair_rows)
total_audited=sum(sum(r[3].values()) for r in pair_rows)
total_multi=sum(r[4] for r in pair_rows)

print("INSACERMO_OPENFLIGHTS_MULTI_ATOM_SIGNATURE_AUDIT_V1")
print("STATUS EXPLORATORY_SYSTEMATIC")
print("SOURCE_COMMIT",SOURCE_COMMIT)
print("SOURCE_SHA256",SOURCE_SHA256)
print("START",START)
print("HORIZON",H)
print("TARGETS",len(REQUIRED))
print("BUNDLES",len(bundles))
print("AIRLINE_CLASSES",len(airlines))
print("PAIRS_WITH_NEW_OBS",len(pair_rows))
print("TOTAL_NEW_MINIMAL_OBSTRUCTIONS",total_new)
print("TOTAL_AUDITED_SIGNATURE_COSTS",total_audited)
print("SIGNATURE_MIN_COST_HISTOGRAM",dict(sorted(global_hist.items())))
print("PAIRS_WITH_MULTI_ATOM_OBSTRUCTION",pairs_with_multi)
print("MULTI_ATOM_OBSTRUCTIONS",total_multi)
print("MULTI_ATOM_FREQUENCY",f"{(total_multi/total_audited if total_audited else 0):.8f}")

if multi_examples:
    for a,b,f,mins in multi_examples[:50]:
        print("MULTI_ATOM",a,b,"BUNDLE","|".join(f),
              "MIN_COST",min(len(s) for s in mins),
              "MIN_SIGNATURES",";".join(",".join(sorted(s)) for s in mins))
else:
    print("MULTI_ATOM NONE")

for a,b,n,hist,nmulti in sorted(pair_rows,key=lambda r:(-r[4],-r[2],r[0],r[1]))[:40]:
    print("PAIR",a,b,"NEW_OBS",n,"COST_HIST",dict(sorted(hist.items())),"MULTI_ATOM",nmulti)

print("PRIMARY_QUESTION_EXISTS_C_GE_2","YES" if total_multi>0 else "NO")
print("RESULT COMPLETE")
