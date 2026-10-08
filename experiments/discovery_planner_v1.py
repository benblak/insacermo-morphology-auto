#!/usr/bin/env python3
from itertools import permutations

def subsets(n):
    for mask in range(1<<n):
        yield frozenset(i for i in range(n) if mask>>i & 1)

def face(B, facets):
    return any(B <= F for F in facets)

def minobs(n, facets):
    out=[]
    for B in subsets(n):
        if face(B,facets):
            continue
        if all(face(B-{x},facets) for x in B):
            out.append(B)
    return frozenset(out)

def fill(facets,G):
    cand=list(facets)+[G]
    return tuple(F for F in cand if not any(F<H for H in cand))

def path_signature(n,facets,repairs):
    cur=facets
    sig=[minobs(n,cur)]
    for G in repairs:
        cur=fill(cur,G)
        sig.append(minobs(n,cur))
    return tuple(sig)

def discovery_score(path):
    # Count obstruction-sets that appear after time 0 and were not visible earlier.
    seen=set(path[0])
    novelty=0
    rank_gain=0
    for step in path[1:]:
        new=set(step)-seen
        novelty += len(new)
        if new:
            rank_gain += sum(len(o) for o in new)
        seen.update(step)
    # deterministic lexicographic score
    return (novelty, rank_gain)

def canonical_endpoint(path):
    return frozenset(path[-1])

def plan(n,facets,repairs):
    rows=[]
    for order in permutations(repairs):
        p=path_signature(n,facets,order)
        rows.append({
          "order":[sorted(x) for x in order],
          "score":discovery_score(p),
          "path":[[sorted(x) for x in step] for step in p],
          "endpoint":[sorted(x) for x in canonical_endpoint(p)]
        })
    endpoints={tuple(tuple(x) for x in r["endpoint"]) for r in rows}
    assert len(endpoints)==1, "endpoint must be order-independent in this static fill model"
    rows.sort(key=lambda r:(r["score"],r["order"]),reverse=True)
    return rows

def witness():
    # Three worlds. Initial facet {0}; repairs {1} and {0,1}.
    n=3
    facets=(frozenset({0}),)
    repairs=(frozenset({1}),frozenset({0,1}))
    rows=plan(n,facets,repairs)
    assert rows[0]["score"] > rows[-1]["score"]
    return rows

def audit_all_small():
    # Exhaustive planner sanity on all 3-world antichain complexes and
    # all 2-repair selections: if paths differ, planner returns a max-score path.
    from itertools import combinations
    subs=list(subsets(3))
    complexes=[]
    for mask in range(1,1<<len(subs)):
        fam=[subs[i] for i in range(len(subs)) if mask>>i & 1]
        if all(not (a<b or b<a) for i,a in enumerate(fam) for b in fam[i+1:]):
            complexes.append(tuple(fam))
    checked=0
    discriminating=0
    for facets in complexes:
        for reps in combinations([x for x in subs if x],2):
            rows=plan(3,facets,reps)
            checked+=1
            if rows[0]["score"] != rows[-1]["score"]:
                discriminating+=1
            assert rows[0]["score"] == max(r["score"] for r in rows)
    return {"complexes":len(complexes),"instances":checked,"discriminating_instances":discriminating}

def main():
    import json
    rows=witness()
    audit=audit_all_small()
    out={
      "experiment":"INSACERMO_DISCOVERY_PLANNER_V1",
      "objective":"maximize exact structural novelty along repair order while preserving the same static endpoint",
      "witness_ranked_paths":rows,
      "audit":audit,
      "status":"PASS"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("DISCOVERY_PLANNER_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
