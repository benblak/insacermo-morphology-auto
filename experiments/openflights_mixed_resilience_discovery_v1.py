#!/usr/bin/env python3
import csv, io, json, hashlib, urllib.request, functools
from collections import Counter
from itertools import combinations

OPENFLIGHTS_COMMIT="7d1a611e070295dba776d6afb86e57d0d1aa1cef"
ROUTES_URL=f"https://raw.githubusercontent.com/jpatokal/openflights/{OPENFLIGHTS_COMMIT}/data/routes.dat"

AIRPORTS=("CDG","ORY","LHR","AMS","FRA","MAD","BCN","LIS","FCO","MXP","MUC","BRU","ZRH","VIE","CPH","DUB","NTE","LYS")
MAX_PATHS=14
N_FRAGILE=7
INF=999

def download_routes():
    raw=urllib.request.urlopen(ROUTES_URL,timeout=60).read()
    return raw, hashlib.sha256(raw).hexdigest()

def graph_from_routes(raw):
    adj={a:set() for a in AIRPORTS}
    rows=csv.reader(io.StringIO(raw.decode("utf-8",errors="replace")))
    count=0
    for r in rows:
        if len(r)<6: continue
        s,d=r[2],r[4]
        if s in adj and d in adj and s!=d:
            adj[s].add(d); count+=1
    return adj,count

def shortest_simple_paths(adj,s,t,limit=MAX_PATHS,max_hops=5):
    out=[]
    q=[(s,(s,))]
    while q and len(out)<limit:
        node,path=q.pop(0)
        if len(path)-1>max_hops: continue
        if node==t:
            out.append(path); continue
        for nb in sorted(adj[node]):
            if nb not in path:
                q.append((nb,path+(nb,)))
        q.sort(key=lambda z:(len(z[1]),z[1]))
    return out

def pedges(path):
    return tuple(zip(path[:-1],path[1:]))

def common_path(worlds,paths):
    for i,E in enumerate(paths):
        if all(not (set(E)&set(w)) for w in worlds):
            return i
    return None

def transform_repair(worlds,e):
    return tuple(sorted(set(tuple(sorted(set(w)-{e})) for w in worlds)))

def probe_split(worlds,e):
    yes=[]; no=[]
    for w in worlds:
        (yes if e in w else no).append(w)
    return tuple(yes),tuple(no)

def exact_planner(worlds,paths,fragile,allow_probe=True,allow_repair=True):
    psets=[set(pedges(p)) for p in paths]

    def common(ws):
        for i,P in enumerate(psets):
            if all(not (P & set(w)) for w in ws): return i
        return None

    @functools.lru_cache(None)
    def sol(ws,repaired,used):
        cp=common(ws)
        if cp is not None:
            return (0,0,("ACT",cp))
        best=(INF,-INF,("REFUSE",None))
        # score second component rewards alternation/tie richness, not depth.
        if allow_probe:
            for pi,e in enumerate(fragile):
                if (used>>pi)&1: continue
                y,n=probe_split(ws,e)
                if not y or not n: continue
                a=sol(y,repaired,used|(1<<pi))
                b=sol(n,repaired,used|(1<<pi))
                if a[0]>=INF or b[0]>=INF: continue
                depth=1+max(a[0],b[0])
                richness=a[1]+b[1]+1
                cand=(depth,richness,("PROBE",pi))
                if depth<best[0] or (depth==best[0] and richness>best[1]):
                    best=cand
        if allow_repair and repaired==0:
            for ri,e in enumerate(fragile):
                nws=transform_repair(ws,e)
                if nws==ws: continue
                a=sol(nws,ri+1,0)
                if a[0]>=INF: continue
                depth=1+a[0]
                richness=a[1]+1
                cand=(depth,richness,("REPAIR",ri))
                if depth<best[0] or (depth==best[0] and richness>best[1]):
                    best=cand
        return best

    root=tuple(sorted(set(tuple(sorted(w)) for w in worlds)))
    ans=sol(root,0,0)

    paths_out=[]
    def walk(ws,repaired,used,seq):
        d,rich,ch=sol(ws,repaired,used)
        if d>=INF:
            paths_out.append(seq+["REFUSE"]); return
        kind,val=ch
        if kind=="ACT":
            paths_out.append(seq+[f"ACT:{'->'.join(paths[val])}"]); return
        if kind=="PROBE":
            e=fragile[val]; y,n=probe_split(ws,e)
            walk(y,repaired,used|(1<<val),seq+[f"PROBE:{e[0]}->{e[1]}=DOWN"])
            walk(n,repaired,used|(1<<val),seq+[f"PROBE:{e[0]}->{e[1]}=UP"])
        elif kind=="REPAIR":
            e=fragile[val]
            walk(transform_repair(ws,e),val+1,0,seq+[f"REPAIR:{e[0]}->{e[1]}"])
    if ans[0]<INF: walk(root,0,0,[])
    return ans[0],paths_out,sol.cache_info().currsize

def has_prp(seq):
    kinds=[x.split(":")[0] for x in seq]
    s="→".join(kinds)
    return "PROBE→REPAIR→PROBE" in s

def analyze_pair(adj,s,t):
    nodepaths=shortest_simple_paths(adj,s,t)
    if len(nodepaths)<5: return None
    ecount=Counter()
    for p in nodepaths:
        ecount.update(pedges(p))
    fragile=tuple(e for e,_ in sorted(ecount.items(),key=lambda kv:(-kv[1],kv[0]))[:N_FRAGILE])
    if len(fragile)<5: return None
    psets=[tuple(pedges(p)) for p in nodepaths]
    worlds=tuple(tuple(sorted(w)) for w in combinations(fragile,2))

    # Require genuine hard worlds and one-repair recoverability per world.
    broken=0
    recoverable=True
    for w in worlds:
        if common_path((w,),psets) is None:
            broken+=1
            ok=False
            for e in w:
                nw=tuple(sorted(set(w)-{e}))
                if common_path((nw,),psets) is not None:
                    ok=True; break
            if not ok: recoverable=False
    if broken==0 or not recoverable: return None

    pd,pp,_=exact_planner(worlds,nodepaths,fragile,True,False)
    rd,rp,_=exact_planner(worlds,nodepaths,fragile,False,True)
    md,mp,states=exact_planner(worlds,nodepaths,fragile,True,True)
    if md>=INF: return None
    prp=sum(has_prp(p) for p in mp)
    return {
      "source":s,"target":t,
      "candidate_paths":["->".join(p) for p in nodepaths],
      "fragile_routes":[f"{a}->{b}" for a,b in fragile],
      "double_outage_worlds":len(worlds),
      "worlds_with_no_initial_route":broken,
      "probe_only_depth":None if pd>=INF else pd,
      "repair_only_depth":None if rd>=INF else rd,
      "mixed_depth":md,
      "mixed_policy_leaf_count":len(mp),
      "mixed_paths_with_PROBE_REPAIR_PROBE":prp,
      "sample_mixed_paths":mp[:12],
      "memo_states":states
    }

def main():
    raw,sha=download_routes()
    adj,nrows=graph_from_routes(raw)
    results=[]
    for s,t in combinations(AIRPORTS,2):
        # test both directions; topology is directed
        for a,b in ((s,t),(t,s)):
            x=analyze_pair(adj,a,b)
            if x: results.append(x)

    # Discovery criterion fixed in advance:
    # prefer cases unsolved by both pure strategies, then PRP-rich,
    # then deeper mixed plan, then lexicographic source/target.
    def score(x):
        pure_fail=(x["probe_only_depth"] is None and x["repair_only_depth"] is None)
        return (1 if pure_fail else 0,
                x["mixed_paths_with_PROBE_REPAIR_PROBE"],
                x["mixed_depth"],
                x["worlds_with_no_initial_route"])
    ranked=sorted(results,key=lambda x:(score(x),x["source"],x["target"]),reverse=True)
    witness=ranked[0] if ranked else None
    out={
      "experiment":"INSACERMO_OPENFLIGHTS_MIXED_RESILIENCE_DISCOVERY_V1",
      "data":{
        "dataset":"OpenFlights routes.dat",
        "commit":OPENFLIGHTS_COMMIT,
        "sha256":sha,
        "selected_airports":AIRPORTS,
        "route_rows_within_selected_airports":nrows,
        "note":"Real route topology; outage worlds are generated exhaustively, not historical incidents."
      },
      "protocol":{
        "candidate_paths_per_pair_max":MAX_PATHS,
        "fragile_routes_per_pair":N_FRAGILE,
        "worlds":"all double outages among selected fragile directed routes",
        "probe":"observe whether one fragile route is down",
        "repair":"restore one fragile route; at most one repair per branch",
        "act":"choose one source-target path guaranteed intact in every remaining world"
      },
      "pairs_passing_structural_filter":len(results),
      "witness":witness,
      "top5":ranked[:5],
      "status":"PASS" if witness else "NO_WITNESS"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("OPENFLIGHTS_MIXED_RESILIENCE_DISCOVERY_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
