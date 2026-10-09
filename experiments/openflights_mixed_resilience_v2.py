#!/usr/bin/env python3
import csv, io, json, hashlib, urllib.request, functools
from collections import Counter, deque
from itertools import combinations

COMMIT="7d1a611e070295dba776d6afb86e57d0d1aa1cef"
ROUTES_URL=f"https://raw.githubusercontent.com/jpatokal/openflights/{COMMIT}/data/routes.dat"
AIRPORTS=("CDG","ORY","NTE","RNS","BES","BOD","TLS","LIL","LYS","MPL","NCE","SXB","BIQ","CFE","PIS","LRT","MRS","GVA","BRU","LUX")
N_FRAGILE=8
INF=999

def fetch():
    raw=urllib.request.urlopen(ROUTES_URL,timeout=60).read()
    return raw,hashlib.sha256(raw).hexdigest()

def graph(raw):
    adj={a:set() for a in AIRPORTS}
    for r in csv.reader(io.StringIO(raw.decode("utf-8",errors="replace"))):
        if len(r)<6: continue
        s,d=r[2],r[4]
        if s in adj and d in adj and s!=d: adj[s].add(d)
    return adj

def reachable(adj,s,t,down):
    if s==t:return True
    q=deque([s]); seen={s}
    while q:
        u=q.popleft()
        for v in adj[u]:
            if (u,v) in down: continue
            if v==t:return True
            if v not in seen:
                seen.add(v); q.append(v)
    return False

def one_path(adj,s,t,down):
    q=deque([s]); prev={s:None}
    while q:
        u=q.popleft()
        if u==t: break
        for v in sorted(adj[u]):
            if (u,v) in down or v in prev: continue
            prev[v]=u;q.append(v)
    if t not in prev:return None
    p=[];x=t
    while x is not None:p.append(x);x=prev[x]
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

def transform(ws,e):
    return tuple(sorted(set(tuple(sorted(set(w)-{e})) for w in ws)))

def split(ws,e):
    a=[];b=[]
    for w in ws:(a if e in w else b).append(w)
    return tuple(a),tuple(b)

def planner(adj,s,t,worlds,fragile,allow_probe,allow_repair):
    @functools.lru_cache(None)
    def sol(ws,repaired,used):
        # ACT iff one fixed route exists that is intact for every remaining world.
        # Equivalent: reachable after union of all possibly-down edges.
        poss=set()
        for w in ws: poss.update(w)
        if reachable(adj,s,t,poss):
            return (0,("ACT",one_path(adj,s,t,poss)))
        best=(INF,("REFUSE",None))
        if allow_probe:
            for i,e in enumerate(fragile):
                if (used>>i)&1:continue
                y,n=split(ws,e)
                if not y or not n:continue
                a=sol(y,repaired,used|(1<<i))[0]
                b=sol(n,repaired,used|(1<<i))[0]
                if a<INF and b<INF and 1+max(a,b)<best[0]:
                    best=(1+max(a,b),("PROBE",i))
        if allow_repair and repaired==0:
            for i,e in enumerate(fragile):
                nws=transform(ws,e)
                if nws==ws:continue
                a=sol(nws,i+1,0)[0]
                if a<INF and 1+a<best[0]:
                    best=(1+a,("REPAIR",i))
        return best
    root=tuple(sorted(set(tuple(sorted(w)) for w in worlds)))
    depth=sol(root,0,0)[0]
    paths=[]
    def walk(ws,repaired,used,seq):
        d,ch=sol(ws,repaired,used)
        if d>=INF:paths.append(seq+["REFUSE"]);return
        k,v=ch
        if k=="ACT":
            paths.append(seq+["ACT:"+("->".join(v) if v else "NONE")]);return
        if k=="PROBE":
            e=fragile[v];y,n=split(ws,e)
            walk(y,repaired,used|(1<<v),seq+[f"PROBE:{e[0]}->{e[1]}=DOWN"])
            walk(n,repaired,used|(1<<v),seq+[f"PROBE:{e[0]}->{e[1]}=UP"])
        else:
            e=fragile[v]
            walk(transform(ws,e),v+1,0,seq+[f"REPAIR:{e[0]}->{e[1]}"])
    if depth<INF:walk(root,0,0,[])
    return depth,paths,sol.cache_info().currsize

def signature(p):
    return "→".join(x.split(":")[0] for x in p)

def analyze(adj,s,t):
    ps=simple_paths(adj,s,t)
    if len(ps)<3:return None
    score=edge_score(ps)
    fragile=tuple(e for e,_ in sorted(score.items(),key=lambda kv:(-kv[1],kv[0]))[:N_FRAGILE])
    if len(fragile)<6:return None
    worlds=tuple(tuple(sorted(w)) for w in combinations(fragile,3))
    broken=sum(not reachable(adj,s,t,set(w)) for w in worlds)
    if broken==0:return None
    # every broken world must be rescuable by repairing one of its failed edges
    for w in worlds:
        if not reachable(adj,s,t,set(w)):
            if not any(reachable(adj,s,t,set(w)-{e}) for e in w):
                return None
    pd,pp,_=planner(adj,s,t,worlds,fragile,True,False)
    rd,rp,_=planner(adj,s,t,worlds,fragile,False,True)
    md,mp,states=planner(adj,s,t,worlds,fragile,True,True)
    if md>=INF:return None
    prp=sum("PROBE→REPAIR→PROBE" in signature(p) for p in mp)
    return {
      "source":s,"target":t,"fragile":[f"{a}->{b}" for a,b in fragile],
      "triple_worlds":len(worlds),"broken_worlds":broken,
      "probe_only_depth":None if pd>=INF else pd,
      "repair_only_depth":None if rd>=INF else rd,
      "mixed_depth":md,"prp_leaves":prp,
      "path_signatures":dict(Counter(signature(p) for p in mp)),
      "sample_paths":mp[:15],"memo_states":states
    }

def main():
    raw,sha=fetch();adj=graph(raw)
    res=[]
    for s,t in combinations(AIRPORTS,2):
        for a,b in ((s,t),(t,s)):
            x=analyze(adj,a,b)
            if x:res.append(x)
    def rank(x):
        purefail=(x["probe_only_depth"] is None and x["repair_only_depth"] is None)
        return (purefail,x["prp_leaves"],x["mixed_depth"],x["broken_worlds"])
    res.sort(key=lambda x:(rank(x),x["source"],x["target"]),reverse=True)
    wit=res[0] if res else None
    out={"experiment":"INSACERMO_OPENFLIGHTS_MIXED_RESILIENCE_V2",
         "data":{"commit":COMMIT,"sha256":sha,"airports":AIRPORTS,
                 "note":"real OpenFlights route topology; triple outages are exhaustive generated scenarios, not historical failures"},
         "protocol":{"fragile_edges":N_FRAGILE,"worlds":"all 3-edge outages among fragile edges",
                     "ACT":"one route must remain intact under every world still possible",
                     "REPAIR":"restore one edge at most once per branch",
                     "PROBE":"observe one edge up/down"},
         "qualifying_pairs":len(res),"witness":wit,"top5":res[:5],
         "status":"PASS" if wit else "NO_WITNESS"}
    print(json.dumps(out,indent=2,sort_keys=True))
    open("OPENFLIGHTS_MIXED_RESILIENCE_V2.json","w").write(json.dumps(out,indent=2,sort_keys=True))
if __name__=="__main__":main()
