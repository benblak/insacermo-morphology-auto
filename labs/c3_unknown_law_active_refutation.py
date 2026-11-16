#!/usr/bin/env python3
"""Blind-law identification via unchanged INSACERMO finite C3 and Lean.
Eight predeclared binary-polynomial candidates. Their actual parameters are
hidden from the runtime, but the *candidate response table* is supplied:
this is active model discrimination, NOT autonomous discovery of arbitrary laws.
One ninth out-of-class law tests a false universal-generalization claim.
"""
from __future__ import annotations
import hashlib,itertools,json,random
from functools import lru_cache
from pathlib import Path
from insacermo_one_engine import decide,replay,solve,validate

ENGINE_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
COEFS=((13,18,56),(1,22,48,50),(1,10,19,22,38,50),
       (11,12,37,38,42,50),(4,13,20,34,37,50),
       (5,6,18,34,41),(1,13,14,18,33,56),(9,12,26))
PROBES=(55,10,2,15,13,14,22,20)
N=8

def prediction(h,x):
    return sum((x&mask)==mask for mask in COEFS[h])%2

# A separate finite-recurrence oracle. No calls to C3 here.
@lru_cache(None)
def independent_minimax(worlds,unused):
    if len(worlds)<=1:return (0,None)
    best=(float("inf"),None)
    for q in unused:
        lo=tuple(w for w in worlds if prediction(w,PROBES[q])==0)
        hi=tuple(w for w in worlds if prediction(w,PROBES[q])==1)
        if not lo or not hi:continue
        rem=tuple(i for i in unused if i!=q)
        a=independent_minimax(lo,rem)[0]
        b=independent_minimax(hi,rem)[0]
        cost=1+max(a,b)
        if cost<best[0]:best=(cost,q)
    return best

def make_model(worlds,probe_indices,depth):
    # C3 uses LOCAL state indices, but observations come from the global truth table.
    n=len(worlds);a=n;q=len(probe_indices)
    m=dict(worldCount=n,actionCount=a,probeCount=q,
        good=[[j==i for j in range(a)] for i in range(n)],
        sense=[[2 if prediction(worlds[w],PROBES[p]) else 1
                for w in range(n)] for p in probe_indices],
        nextFalse=[list(range(n)) for _ in range(q)],
        nextTrue=[list(range(n)) for _ in range(q)],
        actionCost=[0]*a,probeCost=[1]*q,
        lowerWorld=list(range(n)),upperWorld=list(range(n)),
        mustActions=list(range(a)),mayActions=list(range(a)),
        probeKinds=["PROBE"]*q,depth=depth,budget=depth,
        reserve=10,debt=0)
    validate(m)
    return m

def fixed_baseline():
    best=(float("inf"),float("inf"),None)
    for order in itertools.permutations(range(N)):
        counts=[]
        for true_h in range(N):
            candidates=set(range(N))
            used=0
            for q in order:
                if len(candidates)==1:break
                y=prediction(true_h,PROBES[q])
                candidates={h for h in candidates if prediction(h,PROBES[q])==y}
                used+=1
            assert candidates=={true_h}
            counts.append(used)
        metric=(max(counts),sum(counts),order)
        if metric<best:best=metric
    return best

def main(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    source=(Path(__file__).resolve().parents[1]/"insacermo_one_engine.py").read_bytes()
    blob=hashlib.sha1(b"blob "+str(len(source)).encode()+bytes([0])+source).hexdigest()
    assert blob==ENGINE_BLOB,("FROZEN_SOURCE_CHANGED",blob)
    assert independent_minimax(tuple(range(N)),tuple(range(N)))[0]==3
    baseline=fixed_baseline()
    assert baseline[:2]==(4,25),baseline
    # Every root-to-leaf path should identify the hidden candidate
    # via the original executable, not the independent oracle.
    records=[];certificate_count=0
    for hidden in range(N):
        worlds=tuple(range(N))
        available=tuple(range(N))
        answers=[]
        for step in range(4):
            depth=3-step
            model=make_model(worlds,available,depth)
            folder=out/"certificates"/f"hidden_{hidden}"/f"step_{step}"
            result=decide(model,folder)
            assert replay(folder),(hidden,step,"LEAN_REPLAY_FAILED")
            certificate_count+=1
            if len(worlds)==1:
                assert worlds==(hidden,)
                assert result["verdict"]=="ACT"
                assert result["plan"]["act"]==0
                break
            assert result["verdict"]=="PROBE",(hidden,step,result)
            assert result["authorized"] and result["first_step_only"]
            local_index=result["plan"]["probe"]
            probe=available[local_index]
            observed=prediction(hidden,PROBES[probe])
            nxt=tuple(h for h in worlds if prediction(h,PROBES[probe])==observed)
            assert 0<len(nxt)<len(worlds)
            answers.append(dict(probe_input=PROBES[probe],observed=observed,
                                survivors=list(nxt),receipt_sha256=result["receipt_sha256"]))
            worlds=nxt
            available=tuple(q for q in available if q!=probe)
        assert len(answers)==3 and worlds==(hidden,),(hidden,worlds,answers)
        records.append(dict(hidden_candidate=hidden,chosen_experiments=answers,
                            final_identification=hidden))
        print("C3_IDENTIFIED",hidden,"in",len(answers),"experiments",flush=True)
    assert certificate_count==N*4

    # Out-of-model challenge: modify one untested input of hidden law 0.
    chosen={a["probe_input"] for a in records[0]["chosen_experiments"]}
    counterexample=next(x for x in range(64) if x not in chosen)
    def unknown_external(x):
        return prediction(0,x) ^ int(x==counterexample)
    assert all(unknown_external(x)==prediction(0,x) for x in chosen)
    assert unknown_external(counterexample)!=prediction(0,counterexample)
    # Query the falsification point; no catalogued model consistent with all
    # observations is left, so a sound closed-model identifier must refuse to
    # certify the external law as candidate 0.
    observed=unknown_external(counterexample)
    candidate0_prediction=prediction(0,counterexample)
    assert observed != candidate0_prediction
    # The original C3 consumes a *declared world model*, not raw unknown laws.
    # The contradiction is external to C3; it invalidates the declared hypothesis.
    assert len([h for h in [0] if prediction(h,counterexample)==observed])==0

    p=out/"certificates"/"hidden_0"/"step_0"/"receipt.json"
    saved=p.read_bytes()
    manipulated=saved.replace(b'"authorized":true',b'"authorized":false')
    assert manipulated!=saved
    try:
        p.write_bytes(manipulated)
        assert not replay(p.parent)
    finally:p.write_bytes(saved)
    assert replay(p.parent)
    assert not replay(p.parent,lean_binary="/missing-lean")
    report=dict(
        objective="Finite closed-class active model discrimination (not universal law discovery)",
        engine_git_blob=blob,truth_table_inputs=64,
        candidate_laws=N,experimental_queries=list(PROBES),
        independent_minimax_worst=3,
        information_lower_bound=3,
        fixed_order_best_worst=baseline[0],
        fixed_order_best_total=baseline[1],
        fixed_order_best_indices=list(baseline[2]),
        active_identifications=N,
        all_candidates_identified_in=3,
        Lean_certificates_replayed=certificate_count,
        unknown_law=dict(base_candidate=0,altered_input=counterexample,
                         observed=observed,candidate_prediction=candidate0_prediction,
                         agrees_on_all_selected_probes=True,
                         post_identification_falsifier_found=True,
                         verdict="OUT_OF_MODEL_COUNTEREXAMPLE"),
        negative_controls=["tampered_receipt_rejected","lean_missing_refused"],
        limitations=[
          "Hypothesis catalogue of 8 Boolean polynomials is specified, not generated by C3",
          "Experimental system is synthetic: no unknown real-world physical law inferred",
          "C3 certifies identification conditional on catalogued truths and exact observations",
          "External falsifier shows closed-class certification does not imply universal correctness",
          "The active experiments are selected from eight predeclared possible query inputs",
          "External code updates the set of candidate models after each observation",
          "No guarantee under unreliable sensor observations",
        ])
    (out/"audit.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
    (out/"trajectories.json").write_text(json.dumps(records,indent=2,ensure_ascii=False)+"\n")
    print("FROZEN_C3_UNKNOWN_LAW_LAB_PASS",certificate_count,"Lean certificates",
          "3 adaptive vs 4 fixed worst",flush=True)

if __name__=="__main__":
    import sys
    main(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_unknown_law")
