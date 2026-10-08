#!/usr/bin/env python3
from functools import lru_cache
import math, statistics, json

def subsets(n):
    return [frozenset(i for i in range(n) if mask>>i & 1) for mask in range(1<<n)]

def all_antichains(n):
    subs=subsets(n)
    fam=[]
    out=[]
    def rec(i):
        if i==len(subs):
            if fam:
                out.append(tuple(fam))
            return
        rec(i+1)
        S=subs[i]
        if all(not (S<T or T<S) for T in fam):
            fam.append(S); rec(i+1); fam.pop()
    rec(0)
    return out

def face(S,facets):
    return any(S<=F for F in facets)

def signature(n,facets):
    return tuple(face(S,facets) for S in subsets(n))

def minobs(n,facets):
    ss=subsets(n)
    out=[]
    for S in ss:
        if face(S,facets): continue
        if all(face(S-{x},facets) for x in S):
            out.append(S)
    return tuple(sorted(out,key=lambda s:(len(s),tuple(sorted(s)))))

def choose_query(cands,sigs,asked):
    m=len(sigs[0]); N=len(cands); best=None
    for q in range(m):
        if q in asked: continue
        t=sum(1 for i in cands if sigs[i][q])
        f=N-t
        if t==0 or f==0: continue
        # maximin then closest split, then prefer smaller query cardinality
        key=(min(t,f), -abs(t-f), -q)
        if best is None or key>best[0]:
            best=(key,q)
    return None if best is None else best[1]

def build_depths(sigs):
    m=len(sigs[0])
    depths=[None]*len(sigs)
    nodes=0
    max_branch=0
    def rec(cands,asked,depth):
        nonlocal nodes,max_branch
        nodes+=1
        max_branch=max(max_branch,len(cands))
        if len(cands)==1:
            depths[cands[0]]=depth
            return
        q=choose_query(cands,sigs,asked)
        if q is None:
            raise RuntimeError("indistinguishable candidates")
        yes=[i for i in cands if sigs[i][q]]
        no=[i for i in cands if not sigs[i][q]]
        rec(yes,asked|{q},depth+1)
        rec(no,asked|{q},depth+1)
    rec(list(range(len(sigs))),set(),0)
    assert all(d is not None for d in depths)
    return depths,nodes,max_branch

def main():
    n=5
    complexes=all_antichains(n)
    sigs=[signature(n,F) for F in complexes]
    assert len(complexes)==7580 or len(complexes)==7581
    assert len(set(sigs))==len(sigs)
    depths,nodes,max_branch=build_depths(sigs)
    out={
      "experiment":"INSACERMO_EXACT_THEORY_IDENTIFICATION_5W_V1",
      "n_worlds":n,
      "candidate_geometries":len(complexes),
      "full_truth_table_queries":2**n,
      "information_lower_bound_bits":math.ceil(math.log2(len(complexes))),
      "adaptive_query_min":min(depths),
      "adaptive_query_mean":statistics.mean(depths),
      "adaptive_query_median":statistics.median(depths),
      "adaptive_query_max":max(depths),
      "all_geometries_identified_exactly":True,
      "decision_tree_nodes":nodes,
      "root_candidate_count":max_branch,
      "status":"PASS"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("EXACT_THEORY_IDENTIFICATION_5W_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
