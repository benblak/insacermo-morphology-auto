#!/usr/bin/env python3
from functools import lru_cache

def subsets(n):
    return [frozenset(i for i in range(n) if mask>>i & 1) for mask in range(1<<n)]

def antichain(fam):
    fam=list(fam)
    return all(not (a<b or b<a) for i,a in enumerate(fam) for b in fam[i+1:])

def all_complex_facets(n):
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
    subs=subsets(n)
    return tuple(face(S,facets) for S in subs)

def minobs(n,facets):
    subs=subsets(n)
    out=[]
    for S in subs:
        if face(S,facets): continue
        if all(face(S-{x},facets) for x in S):
            out.append(S)
    return tuple(sorted(out,key=lambda s:(len(s),tuple(sorted(s)))))

def choose_query(cands, sigs, asked):
    # exact deterministic maximin split among unanswered ambiguity sets
    m=len(sigs[0])
    best=None
    for q in range(m):
        if q in asked: continue
        t=sum(1 for i in cands if sigs[i][q])
        f=len(cands)-t
        if t==0 or f==0: continue
        score=min(t,f)
        imbalance=abs(t-f)
        key=(score,-imbalance,-q)
        if best is None or key>best[0]:
            best=(key,q)
    return None if best is None else best[1]

def identify(target_idx,sigs):
    cands=list(range(len(sigs)))
    asked=[]
    transcript=[]
    while len(cands)>1:
        q=choose_query(cands,sigs,set(asked))
        if q is None:
            raise RuntimeError("indistinguishable candidates")
        ans=sigs[target_idx][q]
        before=len(cands)
        cands=[i for i in cands if sigs[i][q]==ans]
        asked.append(q)
        transcript.append((q,ans,before,len(cands)))
    assert cands[0]==target_idx
    return transcript

def main():
    import json,statistics,math
    n=4
    complexes=all_complex_facets(n)
    sigs=[signature(n,F) for F in complexes]
    assert len(set(sigs))==len(sigs)
    subs=subsets(n)

    depths=[]
    examples=[]
    for i,F in enumerate(complexes):
        tr=identify(i,sigs)
        depths.append(len(tr))
        if len(examples)<5 or len(tr)==max(depths):
            examples.append({
              "target_index":i,
              "queries":len(tr),
              "minimal_obstructions":[sorted(x) for x in minobs(n,F)],
              "transcript":[
                {"ask":sorted(subs[q]),"answer":"ACT" if ans else "REFUSE",
                 "candidates_before":before,"candidates_after":after}
                for q,ans,before,after in tr
              ]
            })
            examples=examples[-8:]

    out={
      "experiment":"INSACERMO_EXACT_THEORY_IDENTIFICATION_V1",
      "n_worlds":n,
      "candidate_geometries":len(complexes),
      "full_truth_table_queries":2**n,
      "information_lower_bound_bits":math.ceil(math.log2(len(complexes))),
      "adaptive_query_min":min(depths),
      "adaptive_query_mean":statistics.mean(depths),
      "adaptive_query_median":statistics.median(depths),
      "adaptive_query_max":max(depths),
      "all_geometries_identified_exactly":True,
      "method":"deterministic adaptive maximin ACT/REFUSE membership queries; no training, no statistical generalization",
      "interpretation":"The hidden finite actionability theory can be reconstructed exactly from adaptive decision queries alone.",
      "examples":examples,
      "status":"PASS"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("EXACT_THEORY_IDENTIFICATION_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
