#!/usr/bin/env python3
from itertools import combinations

def subsets(n):
    for mask in range(1<<n):
        yield frozenset(i for i in range(n) if mask>>i & 1)

def is_antichain(fam):
    fam=list(fam)
    return all(not (a<b or b<a) for i,a in enumerate(fam) for b in fam[i+1:])

def all_complex_facets(n):
    subs=list(subsets(n))
    for mask in range(1,1<<len(subs)):
        fam=[subs[i] for i in range(len(subs)) if mask>>i & 1]
        if is_antichain(fam):
            yield tuple(fam)

def face(S,facets):
    return any(S<=F for F in facets)

def fill(facets,G):
    cand=list(facets)+[G]
    return tuple(F for F in cand if not any(F<H for H in cand))

def is_minimal_obstruction(B,facets):
    if face(B,facets): return False
    return all(face(B-{x},facets) for x in B)

def boundary_debt(B,facets):
    return sum(1 for x in B if not face(B-{x},facets))

def min_preserving_repairs_to_expose(B,facets):
    # In a target B, preserving repairs are proper subsets of B.
    candidates=[G for G in subsets(max(B)+1) if G < B]
    if face(B,facets):
        return None
    for k in range(len(candidates)+1):
        for combo in combinations(candidates,k):
            cur=facets
            for G in combo:
                cur=fill(cur,G)
            if is_minimal_obstruction(B,cur):
                return k
    return None

def exhaustive_n4():
    n=4
    B=frozenset(range(n))
    checked=0
    hist={}
    examples={}
    for facets in all_complex_facets(n):
        if face(B,facets):
            continue
        debt=boundary_debt(B,facets)
        price=min_preserving_repairs_to_expose(B,facets)
        assert price==debt,(facets,debt,price)
        checked+=1
        hist[debt]=hist.get(debt,0)+1
        examples.setdefault(debt,{"facets":[sorted(x) for x in facets],"price":price})
    return checked,hist,examples

def tight_family(max_n=9):
    rows=[]
    for n in range(2,max_n+1):
        B=frozenset(range(n))
        # initial complex contains only empty face: every codim-1 boundary face is blocked
        facets=(frozenset(),)
        debt=boundary_debt(B,facets)
        # Repair each codimension-one face separately.
        cur=facets
        repairs=[]
        for x in B:
            G=B-{x}
            repairs.append(sorted(G))
            cur=fill(cur,G)
        assert is_minimal_obstruction(B,cur)
        assert debt==n
        rows.append({"n":n,"boundary_debt":debt,"repairs_used":n,"target_order":n})
    return rows

def main():
    import json
    checked,hist,examples=exhaustive_n4()
    out={
      "experiment":"INSACERMO_BOUNDARY_DEBT_EXACT_PRICE_V1",
      "n4_targets_checked":checked,
      "debt_histogram":hist,
      "examples":examples,
      "tight_family":tight_family(9),
      "law":"For a fixed target obstruction B in the static fill model, the minimum number of B-preserving single-capability repairs needed to expose B as minimal equals the number of blocked codimension-one faces of B.",
      "status":"PASS"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("BOUNDARY_DEBT_EXACT_PRICE_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
