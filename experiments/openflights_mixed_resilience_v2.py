#!/usr/bin/env python3
import csv, io, json, hashlib, urllib.request, functools
from collections import Counter, deque
from itertools import combinations

COMMIT="7d1a611e070295dba776d6afb86e57d0d1aa1cef"
ROUTES_URL=f"https://raw.githubusercontent.com/jpatokal/openflights/{COMMIT}/data/routes.dat"
AIRPORTS=("CDG","ORY","NTE","RNS","BES","BOD","TLS","LIL","LYS","MPL","NCE","SXB","BIQ","CFE","PIS","LRT","MRS","GVA","BRU","LUX")
N_FRAGILE=8
INF=99

def fetch():
    raw=urllib.request.urlopen(ROUTES_URL,timeout=60).read()
    return raw,hashlib.sha256(raw).hexdigest()

def graph(raw):
    adj={a:set() for a in AIRPORTS}
    rows=0
    for r in csv.reader(io.StringIO(raw.decode("utf-8",errors="replace"))):
        if len(r)<6: continue
        s,d=r[2],r[4]
        if s in adj and d in adj and s!=d:
            adj[s].add(d); rows+=1
    return adj,rows

def reachable_edges(adj,s,t,down_edges):
    if s==t:return True
    q=deque([s]); seen={s}
    while q:
        u=q.popleft()
        for v in adj[u]:
            if (u,v) in down_edges: continue
            if v==t:return True
            if v not in seen:
                seen.add(v); q.append(v)
    return False

def one_path_edges(adj,s,t,down_edges):
    q=deque([s]); prev={s:None}
    while q:
        u=q.popleft()
        if u==t: break
        for v in sorted(adj[u]):
            if (u,v) in down_edges or v in prev: continue
            prev[v]=u; q.append(v)
    if t not in prev:return None
    p=[]; x=t
    while x is not None:
        p.append(x); x=prev[x]
    return tuple(reversed(p))

def simple_paths(adj,s,t,limit=30,max_hops=6):
    out=[]; q=[(s,(s,))]
    while q and len(out)<limit:
        u,p=q.pop(0)
        if len(p)-1>max_hops:continue
        if u==t:
            out.append(p);continue
        for v in sorted(adj[u]):
            if v not in p:q.append((v,p+(v,)))
        q.sort(key=lambda z:(len(z[1]),z[1]))
    return out

def edge_score(paths):
    c=Counter()
    for p in paths:c.update(zip(p[:-1],p[1:]))
    return c

def signature(path):
    return "→".join(x.split(":")[0] for x in path)

def analyze(adj,s,t):
    ps=simple_paths(adj,s,t)
    if len(ps)<3:return None
    score=edge_score(ps)
    fragile=tuple(e for e,_ in sorted(score.items(),key=lambda kv:(-kv[1],kv[0]))[:N_FRAGILE])
    if len(fragile)<6:return None

    edge_to_i={e:i for i,e in enumerate(fragile)}
    worlds=tuple(sum(1<<i for i in comb) for comb in combinations(range(len(fragile)),3))

    @functools.lru_cache(None)
    def down_edges(mask):
        return frozenset(fragile[i] for i in range(len(fragile)) if (mask>>i)&1)

    @functools.lru_cache(None)
    def reachable_mask(mask):
        return reachable_edges(adj,s,t,down_edges(mask))

    @functools.lru_cache(None)
    def path_mask(mask):
        return one_path_edges(adj,s,t,down_edges(mask))

    broken_masks=tuple(w for w in worlds if not reachable_mask(w))
    if not broken_masks:return None

    # Structural filter: every actually broken triple must be recoverable
    # by restoring one of its failed fragile edges.
    for w in broken_masks:
        if not any(reachable_mask(w & ~(1<<i))
                   for i in range(len(fragile)) if (w>>i)&1):
            return None

    # PROBE-only is impossible immediately because at least one actual world
    # has no route at all. This is a theorem of the declared semantics, not a heuristic.
    probe_only_depth=None

    # REPAIR-only: same repair before observing anything.
    repair_only_choices=[]
    union0=0
    for w in worlds: union0 |= w
    for i,e in enumerate(fragile):
        repaired_union=union0 & ~(1<<i)
        if reachable_mask(repaired_union):
            repair_only_choices.append(i)
    repair_only_depth=1 if repair_only_choices else None

    def canonical(ws):
        return tuple(sorted(set(ws)))

    @functools.lru_cache(None)
    def union_mask(ws):
        u=0
        for w in ws:u|=w
        return u

    @functools.lru_cache(None)
    def split_state(ws,i):
        bit=1<<i
        y=tuple(w for w in ws if w&bit)
        n=tuple(w for w in ws if not (w&bit))
        return y,n

    @functools.lru_cache(None)
    def repair_state(ws,i):
        bit=~(1<<i)
        return canonical(tuple(w&bit for w in ws))

    # Exact minimax mixed planner. State = remaining possible outage masks,
    # whether the one repair budget is spent, and already-used probes.
    # Branch-and-bound uses the best known depth and orders repairs/probes by
    # immediate structural gain; it never prunes a potentially better exact plan.
    @functools.lru_cache(None)
    def sol(ws,repaired,used):
        um=union_mask(ws)
        if reachable_mask(um):
            return (0,("ACT",path_mask(um)))

        best_depth=INF
        best_choice=("REFUSE",None)

        # Try repair first when available, ordered by reduction of union uncertainty.
        if not repaired:
            cand=[]
            for i in range(len(fragile)):
                nws=repair_state(ws,i)
                if nws==ws:continue
                # cheap hopeful ordering: fewer distinct worlds / smaller union
                cand.append((len(nws), union_mask(nws).bit_count(), i, nws))
            cand.sort()
            for _,__,i,nws in cand:
                a=sol(nws,1,0)[0]
                if a<INF:
                    d=1+a
                    if d<best_depth:
                        best_depth=d;best_choice=("REPAIR",i)
                        if best_depth==1:return (best_depth,best_choice)

        # Probe branches ordered by balance (most informative first).
        candp=[]
        for i in range(len(fragile)):
            if (used>>i)&1:continue
            y,n=split_state(ws,i)
            if not y or not n:continue
            candp.append((max(len(y),len(n)),abs(len(y)-len(n)),i,y,n))
        candp.sort()
        for _,__,i,y,n in candp:
            # lower bound is at least one for this probe; if best is already 1,
            # no probe can improve it.
            if best_depth<=1:break
            nxt=used|(1<<i)
            a=sol(y,repaired,nxt)[0]
            if a>=INF:continue
            # exact bound: if 1+a already exceeds current best in one branch,
            # no need to solve the other branch for this candidate.
            if 1+a>best_depth:continue
            b=sol(n,repaired,nxt)[0]
            if b>=INF:continue
            d=1+max(a,b)
            if d<best_depth:
                best_depth=d;best_choice=("PROBE",i)

        return (best_depth,best_choice)

    root=canonical(worlds)
    md,root_choice=sol(root,0,0)
    if md>=INF:return None

    mixed_paths=[]
    def walk(ws,repaired,used,seq):
        d,ch=sol(ws,repaired,used)
        if d>=INF:
            mixed_paths.append(seq+["REFUSE"]);return
        kind,val=ch
        if kind=="ACT":
            p=val
            mixed_paths.append(seq+["ACT:"+("->".join(p) if p else "NONE")]);return
        if kind=="PROBE":
            e=fragile[val];y,n=split_state(ws,val)
            walk(y,repaired,used|(1<<val),seq+[f"PROBE:{e[0]}->{e[1]}=DOWN"])
            walk(n,repaired,used|(1<<val),seq+[f"PROBE:{e[0]}->{e[1]}=UP"])
        elif kind=="REPAIR":
            e=fragile[val]
            walk(repair_state(ws,val),1,0,seq+[f"REPAIR:{e[0]}->{e[1]}"])
    walk(root,0,0,[])

    prp=sum("PROBE→REPAIR→PROBE" in signature(p) for p in mixed_paths)
    return {
      "source":s,"target":t,
      "fragile":[f"{a}->{b}" for a,b in fragile],
      "triple_worlds":len(worlds),
      "broken_worlds":len(broken_masks),
      "probe_only_depth":probe_only_depth,
      "repair_only_depth":repair_only_depth,
      "repair_only_choices":[f"{fragile[i][0]}->{fragile[i][1]}" for i in repair_only_choices],
      "mixed_depth":md,
      "mixed_root_choice":root_choice[0],
      "prp_leaves":prp,
      "path_signatures":dict(Counter(signature(p) for p in mixed_paths)),
      "sample_paths":mixed_paths[:15],
      "memo_states":sol.cache_info().currsize
    }

def main():
    raw,sha=fetch();adj,nrows=graph(raw)
    res=[]
    scanned=0
    for s,t in combinations(AIRPORTS,2):
        for a,b in ((s,t),(t,s)):
            scanned+=1
            x=analyze(adj,a,b)
            if x:res.append(x)

    # Fixed ranking declared before seeing results.
    def rank(x):
        purefail=(x["probe_only_depth"] is None and x["repair_only_depth"] is None)
        return (1 if purefail else 0,x["prp_leaves"],x["mixed_depth"],x["broken_worlds"])
    res.sort(key=lambda x:(rank(x),x["source"],x["target"]),reverse=True)
    wit=res[0] if res else None
    out={
      "experiment":"INSACERMO_OPENFLIGHTS_MIXED_RESILIENCE_V2_OPTIMIZED",
      "data":{
        "commit":COMMIT,"sha256":sha,"airports":AIRPORTS,
        "route_rows_within_selected_airports":nrows,
        "note":"real OpenFlights route topology; triple outages are exhaustive generated scenarios, not historical failures"
      },
      "protocol":{
        "unchanged_from_v2":True,
        "fragile_edges":N_FRAGILE,
        "worlds":"all 3-edge outages among fragile edges",
        "ACT":"one route must remain intact under every world still possible",
        "REPAIR":"restore one fragile edge at most once per branch",
        "PROBE":"observe one fragile edge up/down",
        "optimization":"bitmask state representation, cached reachability, exact dominance/bound pruning only"
      },
      "directed_pairs_scanned":scanned,
      "qualifying_pairs":len(res),
      "witness":wit,
      "top5":res[:5],
      "status":"PASS" if wit else "NO_WITNESS"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("OPENFLIGHTS_MIXED_RESILIENCE_V2.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
