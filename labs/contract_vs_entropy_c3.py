#!/usr/bin/env python3
"""Ablation: C3 picks the information relevant to the contract, not max entropy.
Eight equally weighted finite worlds, two binary fixed probes:
A: partition 4+4 (1 Shannon bit);
B: partition 7+1 (H2(1/8) ~= .54356 bit).
Contracts tested independently: anomaly (7+1), balanced cohort (4+4),
full identification (8 distinct actions). One probe, one decision.
HISTORICAL C3 source completely unchanged; all certificates Lean-replayed.
"""
from pathlib import Path
from math import log2
import hashlib,json,sys
from insacermo_one_engine import decide,replay,validate

FROZEN="bd5310b3692bcbad4e874005b7dd8eda90616f74"
W=8
def h(p):
    return -(p*log2(p)+(1-p)*log2(1-p))
def contract(task,probe_ids):
    groups={"anomaly":[0,0,0,0,0,0,0,1],
            "cohort":[0,0,0,0,1,1,1,1],
            "identity":list(range(8))}
    group=groups[task]
    n=max(group)+1
    # A high entropy: first 4 worlds False, last four True;
    # B low entropy: only world 7 True.
    bins={
      "A":[0,0,0,0,1,1,1,1],
      "B":[0,0,0,0,0,0,0,1]}
    m=dict(worldCount=W,actionCount=n,probeCount=len(probe_ids),
      good=[[a==group[w] for a in range(n)] for w in range(W)],
      sense=[[2 if x else 1 for x in bins[q]] for q in probe_ids],
      nextFalse=[list(range(W)) for _ in probe_ids],
      nextTrue=[list(range(W)) for _ in probe_ids],
      actionCost=[0]*n,probeCost=[1]*len(probe_ids),
      lowerWorld=list(range(W)),upperWorld=list(range(W)),
      mustActions=list(range(n)),mayActions=list(range(n)),
      probeKinds=["PROBE"]*len(probe_ids),depth=1,budget=1,
      reserve=3,debt=0)
    validate(m)
    return m

def independent_possible(task,qs):
    labels={"anomaly":[0]*7+[1],
           "cohort":[0]*4+[1]*4,
           "identity":list(range(8))}[task]
    responses={
       "A":[0]*4+[1]*4,
       "B":[0]*7+[1]}
    for q in qs:
        for bit in (0,1):
            leaf=[i for i in range(W) if responses[q][i]==bit]
            if len({labels[i] for i in leaf})>1:break
        else:return True
    return False

def main(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    engine=(Path(__file__).resolve().parents[1]/"insacermo_one_engine.py").read_bytes()
    sha=hashlib.sha1(b"blob "+str(len(engine)).encode()+b"\0"+engine).hexdigest()
    assert sha==FROZEN,(sha,"FROZEN_SOURCE_CHANGED")
    rows=[];nchecks=0
    cases=[
      ("anomaly",("A",),"REFUSE_ROBUST",None),
      ("anomaly",("B",),"PROBE","B"),
      ("anomaly",("A","B"),"PROBE","B"),
      ("cohort",("A",),"PROBE","A"),
      ("cohort",("B",),"REFUSE_ROBUST",None),
      ("cohort",("B","A"),"PROBE","A"),
      ("identity",("A",),"REFUSE_ROBUST",None),
      ("identity",("B",),"REFUSE_ROBUST",None),
      ("identity",("A","B"),"REFUSE_ROBUST",None),
    ]
    for task,qs,expected,choice in cases:
        folder=out/"lean_receipts"/(task+"_"+"_".join(qs))
        r=decide(contract(task,qs),folder)
        assert r["verdict"]==expected,(task,qs,r)
        assert replay(folder),(task,qs,"FAILED_LEAN_REPLAY")
        nchecks+=1
        if choice:
            assert qs[r["plan"]["probe"]]==choice,(task,qs,r)
            assert r["authorized"] and r["first_step_only"]
        else:
            assert not r["authorized"]
        independently=independent_possible(task,qs)
        assert independently==(expected=="PROBE")
        rows.append(dict(task=task,probes=list(qs),verdict=r["verdict"],
          chosen_probe=choice,independent_feasibility=independently,
          receipt_sha256=r["receipt_sha256"]))
        print("CONTRACT_ENTROPY",task,qs,expected,choice,flush=True)

    # Negative controls: wrong bit, tampered receipt, no Lean.
    folder=out/"lean_receipts"/"anomaly_A_B"
    assert not replay(folder,lean_binary="/missing-lean")
    p=folder/"receipt.json";old=p.read_bytes()
    mutated=old.replace(b'"authorized":true',b'"authorized":false')
    assert mutated!=old
    try:
        p.write_bytes(mutated)
        assert not replay(folder)
    finally:p.write_bytes(old)
    assert replay(folder)

    report=dict(
      phenomenon="Actionability is contract-dependent, not maximization of Shannon information",
      model="Eight deterministic, equiprobable synthetic worlds; one binary probe, then safe action",
      frozen_c3_git_blob=sha,
      information_bits={"A_balanced_4_4":h(.5),"B_unbalanced_7_1":h(1/8)},
      one_probe_cost=1,
      contracts={"anomaly":"7 worlds action 0, world 7 action 1",
        "cohort":"worlds 0-3 action 0, 4-7 action 1",
        "identity":"every world needs its own action"},
      tests=rows,verified_lean_receipts=nchecks,
      negative_controls=["tampered_receipt_refused","missing_lean_refused"],
      limitations=[
        "The correct target partitions and probe responses are explicitly supplied.",
        "This is not induction or physical discovery, but a strict formal separation between entropy and decision sufficiency.",
        "Shannon entropy figures assume equiprobability; C3 itself uses no probabilities.",
        "The result is conditional on finite declared actions and exact observations.",
        "A and B are very simple synthetic probes; there is no claim that this distinction is novel in information theory."
      ])
    (out/"audit.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
    assert nchecks==9
    print("CONTRACT_VS_ENTROPY_LEAN_SUCCESS",nchecks,flush=True)

if __name__=="__main__":
    main(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_contract_entropy")
