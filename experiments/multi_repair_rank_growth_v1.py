#!/usr/bin/env python3
from itertools import combinations, product

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
    out=set()
    for B in subsets(n):
        if face(B,facets): continue
        # include empty obstruction only for truly empty complex; excluded here by nonempty facets
        if all(face(B-{x},facets) for x in B):
            out.add(B)
    return out

def max_order(n,facets):
    obs=minobs(n,facets)
    return max(map(len,obs),default=0)

def fill(facets,G):
    # Add simplex G, then canonicalize maximal facets.
    cand=list(facets)+[G]
    return tuple(F for F in cand if not any(F<G for G in cand))

def exhaustive_sequences(n=4,max_steps=3):
    repairs=list(subsets(n))
    complexes=list(all_complex_facets(n))
    checked=0
    max_growth=-99
    witnesses={}
    violations=[]
    for facets in complexes:
        r0=max_order(n,facets)
        states=[(facets,())]
        for step in range(1,max_steps+1):
            nxt=[]
            for cur,seq in states:
                for G in repairs:
                    new=fill(cur,G)
                    rn=max_order(n,new)
                    growth=rn-r0
                    checked+=1
                    max_growth=max(max_growth,growth)
                    if growth>step:
                        violations.append((facets,seq+(G,),r0,rn))
                        return {"violations":violations}
                    witnesses.setdefault((step,growth),(facets,seq+(G,),r0,rn))
                    nxt.append((new,seq+(G,)))
            states=nxt
    return {
      "n_worlds":n,
      "complexes":len(complexes),
      "max_steps":max_steps,
      "transitions_checked":checked,
      "max_growth_seen":max_growth,
      "violations":violations,
      "observed_step_growth_pairs":[list(k) for k in sorted(witnesses)],
    }

def tight_family(steps=6):
    # n=steps+1 worlds. Initially one facet contains all worlds except z,
    # so {z} is a minimal obstruction of order 1.
    # Repair j adds the facet "all worlds except j". After all steps,
    # every proper subset is a face while the full world set is not:
    # the unique top obstruction has order steps+1.
    n=steps+1
    worlds=frozenset(range(n))
    z=steps
    facets=(frozenset(range(steps)),)
    records=[{"step":0,"max_order":max_order(n,facets),
              "minimal_obstructions":[sorted(x) for x in minobs(n,facets)]}]
    assert max_order(n,facets)==1
    for j in range(steps):
        G=worlds-{j}
        facets=fill(facets,G)
        records.append({"step":j+1,"repair":sorted(G),
                        "max_order":max_order(n,facets),
                        "minimal_obstructions":[sorted(x) for x in minobs(n,facets)]})
    assert worlds in minobs(n,facets)
    assert max_order(n,facets)==steps+1
    return {"steps":steps,"worlds":n,"records":records,
            "growth":max_order(n,facets)-1}

def main():
    import json
    audit=exhaustive_sequences(4,3)
    assert not audit["violations"]
    fam=tight_family(6)
    out={
      "experiment":"INSACERMO_MULTI_REPAIR_RANK_GROWTH_V1",
      "audit":audit,
      "tight_family":fam,
      "candidate_law":"After m single-capability fills, maximum minimal-obstruction order rises by at most m; an explicit family attains equality.",
      "status":"PASS"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("MULTI_REPAIR_RANK_GROWTH_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
