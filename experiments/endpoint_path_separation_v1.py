#!/usr/bin/env python3
from itertools import combinations, permutations

def subsets(n):
    for mask in range(1<<n):
        yield frozenset(i for i in range(n) if mask>>i & 1)

def is_antichain(fam):
    fam=list(fam)
    return all(not (a < b or b < a) for i,a in enumerate(fam) for b in fam[i+1:])

def all_complex_facets(n):
    subs=list(subsets(n))
    for mask in range(1,1<<len(subs)):
        fam=[subs[i] for i in range(len(subs)) if mask>>i & 1]
        if is_antichain(fam):
            yield tuple(fam)

def face(B,facets):
    return any(B <= F for F in facets)

def minobs(n,facets):
    out=[]
    for B in subsets(n):
        if face(B,facets): continue
        if all(face(B-{x},facets) for x in B):
            out.append(B)
    return frozenset(out)

def fill(facets,G):
    cand=list(facets)+[G]
    return tuple(F for F in cand if not any(F<H for H in cand))

def endpoint(facets, repairs):
    cur=facets
    for G in repairs:
        cur=fill(cur,G)
    return minobs(N,cur)

def path_signature(facets, repairs):
    cur=facets
    sig=[minobs(N,cur)]
    for G in repairs:
        cur=fill(cur,G)
        sig.append(minobs(N,cur))
    return tuple(sig)

N=4
def main():
    complexes=list(all_complex_facets(N))
    reps=list(subsets(N))
    checked_batches=0
    order_independent=0
    path_dependent=0
    examples=[]
    # unordered pairs of distinct repairs; compare both orders
    for facets in complexes:
        for A,B in combinations(reps,2):
            checked_batches += 1
            e1=endpoint(facets,[A,B])
            e2=endpoint(facets,[B,A])
            assert e1==e2
            order_independent += 1
            p1=path_signature(facets,[A,B])
            p2=path_signature(facets,[B,A])
            if p1!=p2:
                path_dependent += 1
                if len(examples)<5:
                    examples.append({
                      "initial_facets":[sorted(x) for x in facets],
                      "repair_A":sorted(A),"repair_B":sorted(B),
                      "path_AB":[[sorted(x) for x in step] for step in p1],
                      "path_BA":[[sorted(x) for x in step] for step in p2],
                      "same_endpoint":[sorted(x) for x in e1]
                    })
    import json
    out={
      "experiment":"INSACERMO_ENDPOINT_PATH_SEPARATION_V1",
      "n_worlds":N,
      "complexes":len(complexes),
      "repair_pairs_checked":checked_batches,
      "endpoint_order_independent":order_independent,
      "path_dependent_pairs":path_dependent,
      "path_dependence_fraction":path_dependent/checked_batches,
      "examples":examples,
      "status":"PASS"
    }
    assert path_dependent>0
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("ENDPOINT_PATH_SEPARATION_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
