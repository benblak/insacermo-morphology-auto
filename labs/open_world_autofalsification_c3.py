#!/usr/bin/env python3
"""INSACERMO open-world falsification LAB, NOT a new C3 engine.

Input oracle is an independent child process exposing only JSON line queries.
No importing the oracle: the learner is not given the hidden exception sites.
Falsifier first confirms an initial candidate at eight old probes; then
systematically challenges previously untested points (a sound finite-domain
method, not a general discovery algorithm). A generic algebraic normal form
(ANF) is synthesized from all observed Boolean values, with no preloaded
spike positions. C3 unchanged proves the declared 8-world 4-probe budget
obstruction, and the 2-world actual falsification experiment.
"""
from __future__ import annotations
import hashlib,itertools,json,subprocess,sys
from pathlib import Path
from insacermo_one_engine import decide,replay,validate

ENGINE_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
BASE_MONOMIALS=(13,18,56) # original first candidate ONLY, not the secret exceptions
OLD_PROBES=(55,10,2,15,13,14,22,20)
DOMAIN=tuple(range(64))

def old_claim(x):
    return sum((x&mask)==mask for mask in BASE_MONOMIALS)%2

class Device:
    def __init__(self,case):
        path=Path(__file__).with_name("unknown_oracle_query_only.py")
        self.p=subprocess.Popen([sys.executable,str(path),"--case",case],
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
            text=True,bufsize=1)
        self.observed={}
        self.calls=0
    def ask(self,x):
        self.p.stdin.write(json.dumps({"x":x})+"\n")
        self.p.stdin.flush()
        reply=self.p.stdout.readline()
        if not reply:raise RuntimeError("ORACLE_CLOSED")
        data=json.loads(reply)
        assert data.get("x")==x and data.get("y") in (0,1),data
        self.calls+=1
        self.observed.setdefault(x,[]).append(data["y"])
        return data["y"]
    def close(self):
        self.p.stdin.close();rc=self.p.wait(timeout=10)
        assert rc==0

def synthesize_anf(answers):
    """Möbius transform over F2, unique ANF on all 6-bit Boolean inputs."""
    a=[answers[i] for i in DOMAIN]
    assert len(a)==64
    for bit in range(6):
        for x in DOMAIN:
            if x&(1<<bit):a[x]^=a[x^(1<<bit)]
    terms=[m for m in DOMAIN if a[m]]
    def predict(x):
        return sum((x&mask)==mask for mask in terms)%2
    assert all(predict(x)==answers[x] for x in DOMAIN)
    return terms,predict

def c3_model(laws,queries,depth,budget):
    n=len(laws);q=len(queries)
    assert 1<=n<=8 and 1<=q<=8
    model=dict(worldCount=n,actionCount=n,probeCount=q,
        good=[[i==j for j in range(n)] for i in range(n)],
        sense=[[2 if laws[w](x) else 1 for w in range(n)] for x in queries],
        nextFalse=[list(range(n)) for _ in range(q)],
        nextTrue=[list(range(n)) for _ in range(q)],
        actionCost=[0]*n,probeCost=[1]*q,
        lowerWorld=list(range(n)),upperWorld=list(range(n)),
        mustActions=list(range(n)),mayActions=list(range(n)),
        probeKinds=["PROBE"]*q,depth=depth,budget=budget,
        reserve=10,debt=0)
    validate(model)
    return model

def main(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    original=(Path(__file__).resolve().parents[1]/"insacermo_one_engine.py").read_bytes()
    blob=hashlib.sha1(b"blob "+str(len(original)).encode()+b"\0"+original).hexdigest()
    assert blob==ENGINE_BLOB,("FROZEN_C3_SOURCE_CHANGED",blob)
    cases=[]
    for case in ("known","one_spike","two_spikes","unstable"):
        device=Device(case)
        evidence={}
        for x in OLD_PROBES:
            y=device.ask(x)
            assert y==old_claim(x),(case,"OLD_CATALOGUE_NOT_MATCHED",x,y)
            evidence[x]=y
        # Probe 0 twice to detect nonstationarity; no claim of detecting
        # arbitrary nonstationarity from only two observations.
        y0a=device.ask(0)
        y0b=device.ask(0)
        unstable=(y0a!=y0b)
        record=dict(case=case,initial_eight_agree=True,repeat_at_0=[y0a,y0b],
            unstable_observed=unstable,discovered_counterexamples=[],
            claims=[])
        if unstable:
            assert case=="unstable",("UNEXPECTED_INSTABILITY",case)
            record["outcome"]="REFUSE_NONSTATIONARY_DATA"
            record["claims"].append("A time-independent exact truth table cannot explain two different labels at x=0")
            device.close();cases.append(record)
            print("NONSTATIONARY_REFUSED",case,flush=True)
            continue
        assert case!="unstable","MISSED_NONSTATIONARITY"
        # Additional questions do not know which x, if any, is anomalous.
        for x in DOMAIN:
            if x in evidence:continue
            evidence[x]=device.ask(x)
            if evidence[x]!=old_claim(x):
                record["discovered_counterexamples"].append(x)
        assert len(evidence)==64
        # Evidence is now exhaustive for this *bounded* domain.
        terms,formula=synthesize_anf(evidence)
        assert all(formula(x)==evidence[x] for x in DOMAIN)
        assert all(evidence[x]==old_claim(x) for x in OLD_PROBES)
        record.update(outcome="EXACT_ON_OBSERVED_64_POINTS",counterexamples_count=len(record["discovered_counterexamples"]),
            synthesized_anf_mask_terms=terms,truth_table_sha256=hashlib.sha256(bytes(evidence[i] for i in DOMAIN)).hexdigest(),
            total_oracle_queries=device.calls,verified_inputs=64)
        record["claims"].append("ANF exactly reconstructs all 64 observed inputs, conditional on the oracle's stationarity")
        device.close();cases.append(record)
        print("SYNTHESIZED",case,"counterexamples",record["discovered_counterexamples"],
              "ANF_terms",len(terms),flush=True)
    assert [x["counterexamples_count"] for x in cases if x["case"]!="unstable"]==[0,1,2]
    assert cases[3]["outcome"]=="REFUSE_NONSTATIONARY_DATA"

    # Challenge C3: eight distinct possible worlds (one unmodified base law,
    # plus seven distinct single-exception alternatives). With only four
    # questions allowed, at least three such worlds stay indistinguishable.
    # We do NOT disclose exception sites from hidden oracle; these are a
    # separate, generic adversarial family with a declared finite contract.
    alternative_sites=tuple(x for x in DOMAIN if x not in OLD_PROBES)[:7]
    def single_exception(site):
        return lambda x: old_claim(x) ^ int(x==site)
    candidate_laws=[old_claim]+[single_exception(x) for x in alternative_sites]
    constrained_queries=alternative_sites
    no_guarantee=c3_model(candidate_laws,constrained_queries,depth=4,budget=4)
    rejectfolder=out/"C3_contracts"/"open_world_four_query_refusal"
    r=decide(no_guarantee,rejectfolder)
    assert r["verdict"]=="REFUSE_ROBUST" and not r["authorized"],r
    assert replay(rejectfolder),"C3_BUDGET_REFUSAL_REPLAY_FAILED"
    print("C3_OPEN_WORLD_REFUSE_ROBUST",flush=True)

    # Once an external experiment has *found* a contradictory input,
    # place the original and the revised hypothesis in C3's finite
    # candidate set. C3 must select a discriminating experiment and
    # generate a Lean certificate for that query.
    witness=cases[1]["discovered_counterexamples"][0]
    revised=lambda x:old_claim(x)^int(x==witness)
    m=c3_model([old_claim,revised],[witness],depth=1,budget=1)
    provefolder=out/"C3_contracts"/"falsifier_retest"
    t=decide(m,provefolder)
    assert t["verdict"]=="PROBE" and t["authorized"] and t["first_step_only"],t
    assert t["plan"]["probe"]==0
    assert replay(provefolder)
    new_device=Device("one_spike")
    y=new_device.ask(witness)
    assert y==revised(witness)!=old_claim(witness)
    new_device.close()
    # After observation, C3 must certify that revised hypothesis (only
    # within the explicit two-world candidate pair) is the remaining one.
    after=c3_model([revised],[witness],depth=0,budget=0)
    finalfolder=out/"C3_contracts"/"revised_act"
    accepted=decide(after,finalfolder)
    assert accepted["verdict"]=="ACT" and accepted["authorized"]
    assert replay(finalfolder)

    # Negative controls: no Lean => no authorization; receipt tamper rejected.
    assert not replay(provefolder,lean_binary="/missing-lean")
    p=provefolder/"receipt.json";old=p.read_bytes()
    try:
        mutated=old.replace(b'"authorized":true',b'"authorized":false')
        assert mutated!=old
        p.write_bytes(mutated)
        assert not replay(provefolder)
    finally:p.write_bytes(old)
    assert replay(provefolder)

    report=dict(experiment="Open-world synthesis & self-falsification lab",
        historical_engine_blob=blob,
        oracle_protocol="separate process JSON-lines input x in 0..63, output bit",
        initial_probe_inputs=list(OLD_PROBES),
        cases=cases,independent_anf_algorithm="GF2 Mobius transform across all 64 inputs",
        c3={
          "eight_worlds_four_probe_budget":"REFUSE_ROBUST",
          "falsifier_retest":"PROBE", "revised_model_after_observation":"ACT",
          "lean_replayed_contracts":3,
          "tampering_rejected":True,
          "missing_lean_refuses":True,
          "witness_input":witness},
        limitations=[
          "The oracle is synthetic; the physical discovery problem remains open.",
          "The hidden exception sites are not exposed through the query API, but stored in source control.",
          "The outer laboratory chooses and executes the 64-point exhaustive falsification campaign.",
          "The outer laboratory performs the ANF synthesis; original C3 does not generate law syntax.",
          "Exhaustive truth-table agreement is conditional on determinism/stationarity and limited to x=0..63.",
          "C3 certificates are conditional guarantees for the declared 8/2/1-world contracts.",
          "The C3 budget impossibility is for a separate declared adversarial family, not all conceivable laws.",
          "Two repeat readings cannot rule out every type of drift, noise, or adversarial deception."
        ])
    (out/"audit.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
    print("OPEN_WORLD_AUTOFALSIFICATION_SUCCESS",json.dumps({
        "counterexamples":[r.get("counterexamples_count") for r in cases],
        "stationarity_refused":cases[3]["unstable_observed"],
        "lean_contracts":3}),flush=True)

if __name__=="__main__":
    main(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_open_world")
