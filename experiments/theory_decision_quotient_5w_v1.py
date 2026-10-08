#!/usr/bin/env python3
import math, statistics, json

def subsets(n):
    return [frozenset(i for i in range(n) if mask>>i & 1) for mask in range(1<<n)]

def all_antichains(n):
    subs=subsets(n)
    fam=[]; out=[]
    def rec(i):
        if i==len(subs):
            if fam: out.append(tuple(fam))
            return
        rec(i+1)
        S=subs[i]
        if all(not (S<T or T<S) for T in fam):
            fam.append(S); rec(i+1); fam.pop()
    rec(0)
    return out

def face(S,facets):
    return any(S<=F for F in facets)

def signatures(n,complexes):
    ss=subsets(n)
    return ss,[tuple(face(S,F) for S in ss) for F in complexes]

def choose_query(cands,sigs,labels,asked):
    # Targeted exact experiment design:
    # choose a query minimizing the worst number of decision-equivalence
    # classes still possible after the answer.
    best=None
    m=len(sigs[0])
    for q in range(m):
        if q in asked: continue
        yes=[i for i in cands if sigs[i][q]]
        no=[i for i in cands if not sigs[i][q]]
        if not yes or not no: continue
        cy={labels[i] for i in yes}
        cn={labels[i] for i in no}
        key=(max(len(cy),len(cn)),
             len(cy)+len(cn),
             max(len(yes),len(no)),
             abs(len(yes)-len(no)),
             q)
        if best is None or key<best[0]:
            best=(key,q,yes,no)
    return best

def decision_tree_depths(sigs,labels):
    depths=[None]*len(sigs)
    nodes=0
    def rec(cands,asked,depth):
        nonlocal nodes
        nodes+=1
        if len({labels[i] for i in cands})==1:
            for i in cands: depths[i]=depth
            return
        best=choose_query(cands,sigs,labels,asked)
        if best is None:
            raise RuntimeError("decision classes not identifiable")
        _,q,yes,no=best
        rec(yes,asked|{q},depth+1)
        rec(no,asked|{q},depth+1)
    rec(list(range(len(sigs))),set(),0)
    assert all(d is not None for d in depths)
    return depths,nodes

def row_for_contract(k,ss,sigs):
    gamma=[i for i,S in enumerate(ss) if len(S)>=k]
    labels=[tuple(sig[i] for i in gamma) for sig in sigs]
    classes=len(set(labels))
    depths,nodes=decision_tree_depths(sigs,labels)
    return {
      "future_contract":"all ambiguity sets with cardinality >= %d"%k,
      "min_worlds_in_future_obligation":k,
      "future_obligations":len(gamma),
      "decision_equivalence_classes":classes,
      "class_information_lower_bound_bits":math.ceil(math.log2(classes)),
      "adaptive_queries_min":min(depths),
      "adaptive_queries_mean":statistics.mean(depths),
      "adaptive_queries_median":statistics.median(depths),
      "adaptive_queries_max":max(depths),
      "decision_tree_nodes":nodes,
      "all_hidden_theories_classified_to_correct_decision_quotient":True
    }

def main():
    n=5
    complexes=all_antichains(n)
    assert len(complexes)==7580
    ss,sigs=signatures(n,complexes)
    rows=[row_for_contract(k,ss,sigs) for k in range(1,n+1)]
    full=rows[0]["adaptive_queries_mean"]
    for r in rows:
        r["mean_query_saving_vs_full_theory"] = full-r["adaptive_queries_mean"]
        r["mean_query_saving_fraction_vs_full_theory"] = (
            0.0 if full==0 else (full-r["adaptive_queries_mean"])/full
        )
    out={
      "experiment":"INSACERMO_THEORY_DECISION_QUOTIENT_5W_V1",
      "n_worlds":n,
      "hidden_theories":len(complexes),
      "full_truth_table_queries":2**n,
      "result":rows,
      "interpretation":"Exact theory identification is unnecessary once every remaining theory lies in the same future-decision equivalence class.",
      "method":"deterministic exact adaptive ACT/REFUSE queries; stop on decision-class consensus; no training and no statistical generalization",
      "status":"PASS"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("THEORY_DECISION_QUOTIENT_5W_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
