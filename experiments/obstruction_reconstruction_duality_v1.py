#!/usr/bin/env python3
from itertools import combinations

def subsets(n):
    for mask in range(1<<n):
        yield frozenset(i for i in range(n) if mask>>i & 1)

def antichain(fam):
    fam=list(fam)
    return all(not (a < b or b < a) for i,a in enumerate(fam) for b in fam[i+1:])

def all_complex_facets(n):
    subs=list(subsets(n))
    fam=[]
    def rec(i):
        if i==len(subs):
            if fam:
                yield tuple(fam)
            return
        # skip
        yield from rec(i+1)
        # include only if still an antichain with what is already chosen
        S=subs[i]
        if all(not (S<T or T<S) for T in fam):
            fam.append(S)
            yield from rec(i+1)
            fam.pop()
    yield from rec(0)

def is_face(S,facets):
    return any(S <= F for F in facets)

def minimal_nonfaces(n,facets):
    out=set()
    for S in subsets(n):
        if is_face(S,facets): continue
        if all(is_face(S-{x},facets) for x in S):
            out.add(S)
    return out

def reconstruct_faces(n,minobs):
    return {S for S in subsets(n) if not any(O <= S for O in minobs)}

def maximal_elements(fam):
    fam=set(fam)
    return {S for S in fam if not any(S<T for T in fam)}

def minimal_hitting_sets(n,edges):
    hs=[]
    for T in subsets(n):
        if all(T & E for E in edges):
            if not any(U < T and all(U & E for E in edges) for U in subsets(n)):
                hs.append(T)
    return set(hs)

def reconstruct_facets_via_blocker(n,minobs):
    X=frozenset(range(n))
    trans=minimal_hitting_sets(n,minobs)
    return {X-T for T in trans}

def audit(n):
    complexes=0
    face_checks=0
    blocker_checks=0
    examples=[]
    for facets in all_complex_facets(n):
        complexes += 1
        O=minimal_nonfaces(n,facets)
        faces={S for S in subsets(n) if is_face(S,facets)}
        recfaces=reconstruct_faces(n,O)
        assert faces==recfaces,(facets,O,faces^recfaces)
        face_checks += 1

        true_facets=maximal_elements(faces)
        recfacets=reconstruct_facets_via_blocker(n,O)
        assert true_facets==recfacets,(facets,O,true_facets,recfacets)
        blocker_checks += 1

        if len(examples)<3 and O:
            examples.append({
              "minimal_obstructions":[sorted(x) for x in sorted(O,key=lambda s:(len(s),sorted(s)))],
              "reconstructed_maximal_action_regions":[sorted(x) for x in sorted(recfacets,key=lambda s:(len(s),sorted(s)))]
            })
    return {
      "n_worlds":n,
      "complexes":complexes,
      "obstruction_basis_reconstruction_checks":face_checks,
      "blocker_duality_reconstruction_checks":blocker_checks,
      "examples":examples
    }

def main():
    import json
    rows=[audit(n) for n in range(1,6)]
    out={
      "experiment":"INSACERMO_OBSTRUCTION_RECONSTRUCTION_DUALITY_V1",
      "audits":rows,
      "total_complexes":sum(r["complexes"] for r in rows),
      "law_1":"A finite downward-closed actionability geometry is completely determined by its minimal obstructions.",
      "law_2":"Its maximal actionable regions are complements of the minimal hitting sets (blocker) of the minimal-obstruction hypergraph.",
      "interpretation":"Negative minimal certificates reconstruct the entire effective positive capability geometry, up to redundant/dominated action labels.",
      "status":"PASS"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("OBSTRUCTION_RECONSTRUCTION_DUALITY_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
