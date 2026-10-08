#!/usr/bin/env python3
import json, statistics, math

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

def minobs_from_sig(n,ss,sig):
    out=[]
    idx={S:i for i,S in enumerate(ss)}
    for S in ss:
        if sig[idx[S]]: continue
        if all(sig[idx[S-{x}]] for x in S):
            out.append(S)
    return tuple(sorted(out,key=lambda s:(len(s),tuple(sorted(s)))))

def choose_query(cands,sigs,labels,asked):
    m=len(sigs[0]); best=None
    for q in range(m):
        if q in asked: continue
        yes=[i for i in cands if sigs[i][q]]
        no=[i for i in cands if not sigs[i][q]]
        if not yes or not no: continue
        cy={labels[i] for i in yes}; cn={labels[i] for i in no}
        key=(max(len(cy),len(cn)), len(cy)+len(cn),
             max(len(yes),len(no)), abs(len(yes)-len(no)), q)
        if best is None or key<best[0]:
            best=(key,q,yes,no)
    return best

def run_target(target,sigs,labels):
    cands=list(range(len(sigs))); asked=set(); transcript=[]
    while len({labels[i] for i in cands})>1:
        best=choose_query(cands,sigs,labels,asked)
        if best is None: raise RuntimeError("cannot distinguish decision classes")
        _,q,yes,no=best
        ans=sigs[target][q]
        before=len(cands)
        cands=yes if ans else no
        asked.add(q)
        transcript.append((q,ans,before,len(cands)))
    return cands,asked,transcript

def main():
    n=5
    ss=subsets(n)
    complexes=all_antichains(n)
    assert len(complexes)==7580
    sigs=[tuple(face(S,F) for S in ss) for F in complexes]
    assert len(set(sigs))==len(sigs)

    # A. Full blind discovery: identify exact theory, reconstruct all unqueried answers
    full_labels=list(sigs)
    full_depths=[]; unseen_total=0; unseen_errors=0; basis_errors=0
    for t in range(len(sigs)):
        cands,asked,tr=run_target(t,sigs,full_labels)
        assert len({full_labels[i] for i in cands})==1
        # unique full signature => exact theory
        leaf_sig=full_labels[cands[0]]
        full_depths.append(len(asked))
        for q in range(len(ss)):
            if q not in asked:
                unseen_total+=1
                if leaf_sig[q] != sigs[t][q]:
                    unseen_errors+=1
        inferred_basis=minobs_from_sig(n,ss,leaf_sig)
        true_basis=minobs_from_sig(n,ss,sigs[t])
        if inferred_basis!=true_basis:
            basis_errors+=1

    # B. Contract-limited blind discovery: only future obligations |B|>=4
    gamma=[i for i,S in enumerate(ss) if len(S)>=4]
    qlabels=[tuple(sig[i] for i in gamma) for sig in sigs]
    q_depths=[]; q_unseen_total=0; q_unseen_errors=0
    residual_sizes=[]; unresolved_offcontract_pairs=0
    for t in range(len(sigs)):
        cands,asked,tr=run_target(t,sigs,qlabels)
        q_depths.append(len(asked))
        residual_sizes.append(len(cands))
        # all remaining candidates must agree on Gamma; verify against hidden truth
        representative=cands[0]
        for q in gamma:
            if q not in asked:
                q_unseen_total+=1
                if sigs[representative][q] != sigs[t][q]:
                    q_unseen_errors+=1
        # Count whether exact theory is still unresolved outside Gamma.
        if len(cands)>1:
            unresolved_offcontract_pairs += 1

    out={
      "experiment":"INSACERMO_BLIND_STRUCTURAL_DISCOVERY_V1",
      "n_worlds":n,
      "hidden_theories_tested":len(sigs),
      "full_discovery":{
        "mean_queries":statistics.mean(full_depths),
        "median_queries":statistics.median(full_depths),
        "min_queries":min(full_depths),
        "max_queries":max(full_depths),
        "full_truth_table_queries":len(ss),
        "unqueried_answers_checked":unseen_total,
        "unqueried_prediction_errors":unseen_errors,
        "obstruction_basis_reconstruction_errors":basis_errors,
        "all_exact_theories_reconstructed":unseen_errors==0 and basis_errors==0
      },
      "contract_limited_discovery":{
        "contract":"all ambiguity sets of size >= 4",
        "decision_classes":len(set(qlabels)),
        "mean_queries":statistics.mean(q_depths),
        "median_queries":statistics.median(q_depths),
        "min_queries":min(q_depths),
        "max_queries":max(q_depths),
        "mean_residual_theories_at_stop":statistics.mean(residual_sizes),
        "median_residual_theories_at_stop":statistics.median(residual_sizes),
        "max_residual_theories_at_stop":max(residual_sizes),
        "targets_stopped_with_multiple_exact_theories_remaining":unresolved_offcontract_pairs,
        "future_unqueried_answers_checked":q_unseen_total,
        "future_unqueried_prediction_errors":q_unseen_errors,
        "all_future_decisions_exact":q_unseen_errors==0
      },
      "method":"hidden target; adaptive exact ACT/REFUSE membership queries; no training; no statistical generalization",
      "status":"PASS"
    }
    assert unseen_errors==0 and basis_errors==0 and q_unseen_errors==0
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("BLIND_STRUCTURAL_DISCOVERY_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
