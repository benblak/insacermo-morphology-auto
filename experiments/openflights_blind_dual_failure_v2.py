#!/usr/bin/env python3
"""Blind OpenFlights edge-failure test. No ML; exact 1 and minimal 2 cuts."""
import csv,io,json,hashlib,random,urllib.request,itertools
from collections import deque

SHA="bd373706238134f619c624c606dccc74c05c2582a977c489c81de501735f2390"
COMMIT="7d1a611e070295dba776d6afb86e57d0d1aa1cef"
URL=f"https://raw.githubusercontent.com/jpatokal/openflights/{COMMIT}/data/routes.dat"
SEED=20261009
N=240

def makegraph(edges):
    a={}
    for x,y in edges:
        if x!=y: a.setdefault(x,set()).add(y)
    return {x:tuple(sorted(v)) for x,v in a.items()}

def path(adj,s,t,removed=frozenset()):
    if s==t:return ()
    q=deque([s]); seen={s};parent={}
    while q:
        x=q.popleft()
        for y in adj.get(x,()):
            if (x,y) in removed or y in seen:continue
            parent[y]=x
            if y==t:
                p=[];z=t
                while z!=s:
                    w=parent[z];p.append((w,z));z=w
                return tuple(reversed(p))
            seen.add(y);q.append(y)
    return None

def derive(adj,s,t):
    base=path(adj,s,t)
    if base is None:return None
    singles=set(); pairs=set()
    for e in base:
        alt=path(adj,s,t,frozenset((e,)))
        if alt is None: singles.add(e);continue
        for f in alt:
            if path(adj,s,t,frozenset((e,f))) is None:
                pairs.add(tuple(sorted((e,f))))
    pairs={p for p in pairs if not any(e in singles for e in p)}
    return {"distance":len(base),"singles":sorted(singles),"minimal_pairs":sorted(pairs)}

def oracle(adj,s,t):
    if path(adj,s,t) is None:return None
    edges=sorted((u,v) for u,neighbors in adj.items() for v in neighbors)
    ss={e for e in edges if path(adj,s,t,frozenset((e,))) is None}
    pp={p for p in itertools.combinations(edges,2) if not ss.intersection(p) and path(adj,s,t,frozenset(p)) is None}
    return sorted(ss),sorted(pp)

def selftest():
    r=random.Random(1109);n=0
    for k in range(3,8):
        nodes=list(range(k))
        for _ in range(90):
            adj=makegraph((u,v) for u in nodes for v in nodes if u!=v and r.random()<0.35)
            for s,t in ((0,k-1),(k-1,0)):
                d=derive(adj,s,t);o=oracle(adj,s,t)
                if d is None:assert o is None
                else: assert (d["singles"],d["minimal_pairs"])==o
                n+=1
    return n

def main():
    ntest=selftest()
    raw=urllib.request.urlopen(URL,timeout=60).read()
    actual=hashlib.sha256(raw).hexdigest()
    assert actual==SHA,(actual,SHA)
    edges=set();rows=0
    for r in csv.reader(io.StringIO(raw.decode("utf-8",errors="replace"))):
        if len(r)<6:continue
        s,t=r[2],r[4]
        if s and t and s!=r"\N" and t!=r"\N" and s!=t:
            rows+=1;edges.add((s,t))
    edges=sorted(edges);adj=makegraph(edges)
    rng=random.Random(SEED)
    nodes=sorted(set(adj)|{t for _,t in edges})
    samples=[];seen=set();attempts=0
    while len(samples)<N and attempts<100000:
        attempts+=1
        s,t=rng.sample(nodes,2)
        if (s,t) not in seen and path(adj,s,t) is not None:
            samples.append((s,t));seen.add((s,t))
    assert len(samples)==N,(len(samples),attempts)
    cohorts={"random_reachable_pairs":samples,"random_direct_routes":rng.sample(edges,N)}
    out={
      "experiment":"INSACERMO_OPENFLIGHTS_BLIND_DUAL_FAILURE_V2",
      "status":"PASS",
      "data":{"commit":COMMIT,"sha256":actual,"route_rows":rows,"unique_edges":len(edges),"nodes":len(nodes)},
      "design":{"seed":SEED,"n_per_cohort":N,"random_pairs_attempted":attempts,
        "selection":"fixed RNG + baseline reachability (A), direct route (B); no checking sensitivity during selection",
        "universe":"one or two distinct directed edge failures"},
      "selftest":{"exhaustive_small_graph_s_t_instances":ntest},
      "cohorts":{}
    }
    for name,st in cohorts.items():
        n1=n2=hidden=0;examples=[];dist1={};dist2={}
        for s,t in st:
            d=derive(adj,s,t)
            a=len(d["singles"]);b=len(d["minimal_pairs"])
            n1+=a>0;n2+=b>0;hidden+=(a==0 and b>0)
            dist1[a]=dist1.get(a,0)+1;dist2[b]=dist2.get(b,0)+1
            if a==0 and b>0 and len(examples)<8:
                examples.append({"source":s,"target":t,"shortest_path_edges":d["distance"],"number_two_edge_cuts":b,
                  "cut_pair_examples":[[f"{u}->{v}" for u,v in p] for p in d["minimal_pairs"][:6]]})
        out["cohorts"][name]={"tested":len(st),"one_edge_fragile":n1,
          "minimal_two_edge_fragile":n2,"zero_single_but_double_fragile":hidden,
          "distribution_singles":dict(sorted(dist1.items())),
          "distribution_minimal_pairs":dict(sorted(dist2.items())),
          "witnesses":examples}
    print(json.dumps(out,sort_keys=True,indent=2))
    with open("INSACERMO_OPENFLIGHTS_BLIND_DUAL_FAILURE_V2.json","w") as f:json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":main()
