#!/usr/bin/env python3
"""Contract-relative exact minimum fixed per-edge probes for <=2 outages.

Restriction: perfect, independent binary edge-status observations; must
decide source->target reachability correctly for every failure set |F|<=2.
No learning, no priors, no optimization by changed contract.
"""
import csv,io,hashlib,random,json,statistics
from collections import Counter
import urllib.request
import openflights_blind_dual_failure_v2 as b

def quantiles(a):
    a=sorted(a)
    return {"min":a[0],"median":statistics.median(a),"max":a[-1],
            "mean":round(statistics.mean(a),4),
            "p90":a[int(.9*(len(a)-1))]}

def load():
    raw=urllib.request.urlopen(b.URL,timeout=60).read()
    sha=hashlib.sha256(raw).hexdigest()
    assert sha==b.SHA
    es=set();rows=0
    for r in csv.reader(io.StringIO(raw.decode("utf-8",errors="replace"))):
        if len(r)<6:continue
        s,t=r[2],r[4]
        if s and t and s!=r"\N" and t!=r"\N" and s!=t:es.add((s,t));rows+=1
    es=sorted(es)
    return es,b.makegraph(es),rows,sha

def samples(adj,edges):
    rng=random.Random(b.SEED)
    nodes=sorted(set(adj)|{t for _,t in edges})
    sample=[];seen=set();attempts=0
    while len(sample)<b.N and attempts<100000:
        attempts+=1;s,t=rng.sample(nodes,2)
        if (s,t) not in seen and b.path(adj,s,t) is not None:
            sample.append((s,t));seen.add((s,t))
    assert len(sample)==b.N
    return {"random_reachable_pairs":sample,"random_direct_routes":rng.sample(edges,b.N)}

def run():
    passed=b.selftest()
    edges,adj,rows,sha=load()
    rng=random.Random(10493)
    out={"experiment":"INSACERMO_OPENFLIGHTS_FAILURE_BUDGET_MIN_PROBES_V3",
         "data":{"sha256":sha,"unique_edges":len(edges),"raw_rows":rows},
         "contract":"Binary reachability decision under at most k failed directed edges, k=1 or 2",
         "probes":"fixed, individual, perfect binary edge-status",
         "proof":"Let C be all inclusion-minimal source-target edge cuts of size <=k. P=union(C). Sufficiency: F blocks reachability iff F contains some C, which lies in P. Necessity: for every e in P choose C containing e; C and C minus {e} have opposite decisions, and cannot be distinguished if e is not probed.",
         "selftest":{"small_graph_st_instances":passed},
         "cohorts":{}}
    for name,cohort in samples(adj,edges).items():
        results=[];numoracle=0; witnesses=[]
        for s,t in cohort:
            d=b.derive(adj,s,t)
            cuts1=set(d["singles"])
            cuts2=[tuple(pair) for pair in d["minimal_pairs"]]
            P1=set(cuts1)
            P2=P1|{e for pair in cuts2 for e in pair}
            assert P1<=P2
            # independently validate every necessity witness C and C\{e}
            for e in cuts1:
                assert b.path(adj,s,t,frozenset((e,))) is None
                assert b.path(adj,s,t) is not None
                numoracle+=2
            for x,y in cuts2:
                assert b.path(adj,s,t,frozenset(((x),(y)))) is None
                assert b.path(adj,s,t,frozenset((x,))) is not None
                assert b.path(adj,s,t,frozenset((y,))) is not None
                numoracle+=3
            # randomized sufficient-prediction cross-check, including controlled cuts
            fs=[frozenset(),*(frozenset((e,)) for e in cuts1),
                *(frozenset(p) for p in cuts2)]
            for _ in range(20):
                k=rng.randint(0,2)
                fs.append(frozenset(rng.sample(edges,k)))
            for F in fs:
                true_blocked=b.path(adj,s,t,F) is None
                observed=F & P2
                predicted_blocked=(bool(cuts1&observed) or
                     any(x in observed and y in observed for x,y in cuts2))
                assert true_blocked==predicted_blocked,(s,t,F,observed,d)
                numoracle+=1
            datum={"s":s,"t":t,"min_probe_one":len(P1),"min_probe_two":len(P2),
                   "minimal_pair_cuts":len(cuts2)}
            results.append(datum)
            if len(P1)==0 and len(P2)>0 and len(witnesses)<5:
                witnesses.append({"source":s,"target":t,
                                  "min_probes_single_failure":0,
                                  "min_probes_double_failure":len(P2),
                                  "example_minimal_cut":[f"{u}->{v}" for u,v in cuts2[0]]})
        k1=[x["min_probe_one"] for x in results]
        k2=[x["min_probe_two"] for x in results]
        out["cohorts"][name]={
          "tested":len(cohort),"exact_single_budget_probes":quantiles(k1),
          "exact_double_budget_probes":quantiles(k2),
          "new_probes_required_under_double_budget":quantiles([y-x for x,y in zip(k1,k2)]),
          "zero_probes_single_but_nonzero_double":sum(x==0 and y>0 for x,y in zip(k1,k2)),
          "oracle_reachability_checks":numoracle,
          "witnesses":witnesses}
    out["status"]="PASS"
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("INSACERMO_OPENFLIGHTS_FAILURE_BUDGET_MIN_PROBES_V3.json","w") as f:json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":run()
