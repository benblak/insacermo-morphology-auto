#!/usr/bin/env python3
from itertools import combinations

def subsets(n):
    for mask in range(1<<n):
        yield frozenset(i for i in range(n) if mask>>i & 1)

def is_antichain(fam):
    fam=list(fam)
    return all(not (a < b or b < a) for i,a in enumerate(fam) for b in fam[i+1:])

def all_complex_facets(n):
    subs=list(subsets(n))
    # Every finite simplicial complex is represented by its antichain of maximal faces.
    for mask in range(1<<len(subs)):
        fam=[subs[i] for i in range(len(subs)) if mask>>i & 1]
        if is_antichain(fam):
            yield tuple(fam)

def actionable(B,facets):
    return any(B <= F for F in facets)

def minobs(n,facets):
    out=[]
    for B in subsets(n):
        if not B or actionable(B,facets): continue
        if all(actionable(frozenset(B-{x}),facets) for x in B):
            out.append(B)
    return set(out)

def analyze(n=4):
    repairs=list(subsets(n))
    exposure_deltas=set()
    max_order_changes=set()
    transition_count=0
    new_count=0
    counterexamples=[]
    complexes=0
    for facets in all_complex_facets(n):
        complexes+=1
        old=minobs(n,facets)
        oldmax=max(map(len,old),default=0)
        for G in repairs:
            after_facets=tuple(list(facets)+[G])
            new=minobs(n,after_facets)
            newmax=max(map(len,new),default=0)
            max_order_changes.add(newmax-oldmax)
            transition_count+=1
            for B in new-old:
                new_count+=1
                ancestors=[H for H in old if H < B and H <= G and len(B-G)==1 and B==H|(B-G)]
                if ancestors:
                    exposure_deltas.update(len(B)-len(H) for H in ancestors)
                else:
                    counterexamples.append({
                      "facets":[sorted(x) for x in facets],
                      "repair":sorted(G),"old":[sorted(x) for x in old],
                      "new":[sorted(x) for x in new],"offender":sorted(B)
                    })
                    if len(counterexamples)>=3:
                        return None
    observed={
      "n_worlds":n,
      "complexes_profiled":complexes,
      "repair_transitions":transition_count,
      "new_minimal_obstructions":new_count,
      "observed_exposure_rank_deltas":sorted(exposure_deltas),
      "observed_max_obstruction_order_changes":sorted(max_order_changes),
      "counterexamples":counterexamples,
    }
    candidates=[]
    if exposure_deltas=={1} and not counterexamples:
        candidates.append("NEW_MINIMAL_EXPOSURE_DELTA_EQUALS_ONE")
    if max(max_order_changes,default=0)<=1:
        candidates.append("MAX_OBSTRUCTION_ORDER_INCREASE_AT_MOST_ONE_PER_ADDED_CAPABILITY")
    if not counterexamples:
        candidates.append("NEW_MINIMAL_EQUALS_REPAIRED_OLD_MINIMAL_PLUS_ONE_OUTSIDER")
    observed["automatically_surfaced_candidates"]=candidates
    return observed

def main():
    import json
    out=analyze(4)
    assert out is not None
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("STRUCTURE_DISCOVERY_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
