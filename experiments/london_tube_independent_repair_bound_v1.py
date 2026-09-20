import csv, hashlib, io, itertools, urllib.request
from collections import defaultdict, deque, Counter

REPO_RAW="https://raw.githubusercontent.com/nicola/tubemaps/f20f2ad9397e4a1756770d1111b7f5d2413244bc/datasets"
CONNECTIONS_URL=f"{REPO_RAW}/london.connections.csv"
STATIONS_URL=f"{REPO_RAW}/london.stations.csv"
LINES_URL=f"{REPO_RAW}/london.lines.csv"

START_NAME="Baker Street"
H=8
MAX_BUNDLE=3
TARGET_COUNT=25

def read_csv(url):
    raw=urllib.request.urlopen(url,timeout=60).read()
    return raw, list(csv.DictReader(io.StringIO(raw.decode("utf-8-sig"))))

raw_conn, conns = read_csv(CONNECTIONS_URL)
raw_st, stations = read_csv(STATIONS_URL)
raw_lines, lines = read_csv(LINES_URL)

# Frozen blob content hashes are not SHA256 commitments, so report SHA256 here.
sha_conn=hashlib.sha256(raw_conn).hexdigest()
sha_st=hashlib.sha256(raw_st).hexdigest()
sha_lines=hashlib.sha256(raw_lines).hexdigest()

id_to_name={int(r["id"]):r["name"] for r in stations}
name_to_id={r["name"]:int(r["id"]) for r in stations}
line_to_name={int(r["line"]):r["name"] for r in lines}
assert START_NAME in name_to_id
START=name_to_id[START_NAME]

edge_lines=defaultdict(set)
line_row_counts=Counter()
for r in conns:
    u=int(r["station1"]); v=int(r["station2"]); line=int(r["line"])
    e=(u,v) if u<v else (v,u)
    edge_lines[e].add(line)
    line_row_counts[line]+=1

# Frozen selection rule: top two line ids by descending raw row count, id tie-break.
ranked_lines=sorted(line_row_counts, key=lambda lid:(-line_row_counts[lid], lid))
A,B=ranked_lines[:2]

def graph(deleted_lines=frozenset()):
    g=defaultdict(set)
    for (u,v), served in edge_lines.items():
        if served-set(deleted_lines):
            g[u].add(v); g[v].add(u)
    return {u:tuple(sorted(vs)) for u,vs in g.items()}

def bfs(g, src):
    d={src:0}
    q=deque([src])
    while q:
        u=q.popleft()
        for v in g.get(u,()):
            if v not in d:
                d[v]=d[u]+1
                q.append(v)
    return d

base_g=graph()
base_dist=bfs(base_g, START)
eligible=[
    sid for sid,name in id_to_name.items()
    if sid!=START and 3 <= base_dist.get(sid,10**9) <= 8
]
eligible.sort(key=lambda sid:(hashlib.sha256(id_to_name[sid].encode()).hexdigest(), id_to_name[sid]))
assert len(eligible) >= TARGET_COUNT, len(eligible)
TARGETS=eligible[:TARGET_COUNT]

bundles=[]
for k in range(1,MAX_BUNDLE+1):
    bundles.extend(itertools.combinations(TARGETS,k))

def scenario(deleted):
    g=graph(frozenset(deleted))
    nodes=[START]+TARGETS
    dists={s:bfs(g,s) for s in nodes}
    def depth(bundle):
        best=None
        for perm in itertools.permutations(bundle):
            cur=START
            total=0
            ok=True
            for nxt in perm:
                dv=dists[cur].get(nxt)
                if dv is None:
                    ok=False; break
                total+=dv
                cur=nxt
            if ok and (best is None or total<best):
                best=total
        return best
    depths={b:depth(b) for b in bundles}
    feas={b:(depths[b] is not None and depths[b] <= H) for b in bundles}
    def proper(b):
        for k in range(1,len(b)):
            yield from itertools.combinations(b,k)
    obs=set()
    for b in bundles:
        if feas[b]:
            continue
        if all(feas[tuple(s)] for s in proper(b)):
            obs.add(b)
    return feas,obs,depths

base_feas,base_obs,base_depth=scenario(())
deg_feas,deg_obs,deg_depth=scenario((A,B))
restore_A_feas,_,_=scenario((B,))
restore_B_feas,_,_=scenario((A,))
new_obs=sorted(deg_obs-base_obs)

caps={}
for o in new_obs:
    c=set()
    if restore_A_feas[o]: c.add(A)
    if restore_B_feas[o]: c.add(B)
    caps[o]=frozenset(c)

atomic=[o for o in new_obs if caps[o]]
only_A=[o for o in atomic if caps[o]==frozenset((A,))]
only_B=[o for o in atomic if caps[o]==frozenset((B,))]
either=[o for o in atomic if caps[o]==frozenset((A,B))]
neither=[o for o in new_obs if not caps[o]]

atoms=(A,B)
def hits_all(sub):
    S=set(sub)
    return all(S & set(caps[o]) for o in atomic)

tau=None
tau_set=None
for k in range(3):
    for sub in itertools.combinations(atoms,k):
        if hits_all(sub):
            tau=k; tau_set=sub; break
    if tau is not None: break

ACTIONS={
    "NONE":(0,(A,B)),
    "RESTORE_A":(1,(B,)),
    "RESTORE_B":(1,(A,)),
    "RESTORE_BOTH":(2,()),
}
action_scenarios={}
for name,(cost,deleted) in ACTIONS.items():
    action_scenarios[name]=scenario(deleted)[0]

def restores_atomic(name):
    feas=action_scenarios[name]
    return all(feas[o] for o in atomic)

candidates=[(cost,name) for name,(cost,_) in ACTIONS.items() if restores_atomic(name)]
assert candidates
Cstar,best=min(candidates)
trivial=1 if atomic else 0

primary=(
    trivial==1 and tau is not None and trivial < tau <= Cstar
    and any(len(o)>=2 for o in only_A)
    and any(len(o)>=2 for o in only_B)
)

print("INSACERMO_LONDON_TUBE_INDEPENDENT_REPAIR_BOUND_V1")
print("STATUS PREREGISTERED_BEFORE_ENDPOINT")
print("CONNECTIONS_SHA256",sha_conn)
print("STATIONS_SHA256",sha_st)
print("LINES_SHA256",sha_lines)
print("START",START_NAME,START)
print("HORIZON",H)
print("TARGET_COUNT",len(TARGETS))
print("TARGETS"," | ".join(id_to_name[s] for s in TARGETS))
print("LINE_A",A,line_to_name.get(A,str(A)),"ROWS",line_row_counts[A])
print("LINE_B",B,line_to_name.get(B,str(B)),"ROWS",line_row_counts[B])
print("BUNDLES",len(bundles))
print("BASELINE_FEASIBLE",sum(base_feas.values()))
print("DEGRADED_FEASIBLE",sum(deg_feas.values()))
print("BASELINE_MINIMAL_OBSTRUCTIONS",len(base_obs))
print("DEGRADED_MINIMAL_OBSTRUCTIONS",len(deg_obs))
print("NEW_MINIMAL_OBSTRUCTIONS",len(new_obs))
print("ATOMIC_NEW_OBSTRUCTIONS",len(atomic))
print("ONLY_A",len(only_A))
print("ONLY_B",len(only_B))
print("EITHER",len(either))
print("NEITHER",len(neither))
print("MIN_ORDER_ONLY_A",min(map(len,only_A)) if only_A else "NA")
print("MIN_ORDER_ONLY_B",min(map(len,only_B)) if only_B else "NA")
print("TRIVIAL_LOWER_BOUND",trivial)
print("TRANSVERSAL_TAU",tau if tau is not None else "NA")
print("TRANSVERSAL_SET",",".join(line_to_name.get(x,str(x)) for x in tau_set) if tau_set else "")
print("EXACT_REPAIR_COST",Cstar)
print("EXACT_REPAIR_ACTION",best)
print("BOUND_RATIO_TAU_OVER_CSTAR",f"{tau/Cstar:.6f}" if tau is not None and Cstar else "NA")
print("PRIMARY_ENDPOINT","PASS" if primary else "NULL")
print("RESULT COMPLETE")
