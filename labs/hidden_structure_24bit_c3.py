#!/usr/bin/env python3
"""A rigorous boundary test: can monotonicity be DISCOVERED rather than assumed?

We re-use the unchanged 24-bit external monotone discovery procedure as a
hypothesis generator. The investigator is given neither the hidden clause list
nor the type of external oracle, and checks an explicit monotonicity witness,
64 fresh random measurements, and a precommitted 24-bit needle alternative.

Critically the clean and rare-exception worlds can have identical finite
transcripts despite disagreeing globally. Thus we MUST NOT authorize the
unconditional claim that monotonicity is true. We can certify the conditional
inference and a local C3 epistemic openness/refusal/probe/act contract.
No universal claim about validating arbitrary structural properties from a
small number of finite observations.
"""
from __future__ import annotations
import hashlib,json,random,subprocess,sys
from pathlib import Path
from insacermo_one_engine import decide,replay,validate
from monotone_24bit_discovery_c3 import (
 N,FULL,WORLD_COUNT,reduce_positive,next_falsifier,snapshot
)
ENGINE_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
ORACLE=Path(__file__).with_name("hidden_structure_24bit_oracle.py")
SEED=177

class Query:
    def __init__(self,mode):
        self.p=subprocess.Popen([sys.executable,str(ORACLE),"--mode",mode],
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
            text=True,bufsize=1)
        self.answers={}
        self.order=[]
    def ask(self,x):
        assert isinstance(x,int) and 0<=x<=FULL
        if x in self.answers:return self.answers[x]
        self.p.stdin.write(json.dumps({"x":x})+"\n");self.p.stdin.flush()
        line=self.p.stdout.readline()
        if not line:raise RuntimeError("ORACLE_CLOSED")
        reply=json.loads(line)
        assert reply.get("x")==x and reply.get("y") in (0,1),reply
        self.answers[x]=reply["y"];self.order.append(x)
        return reply["y"]
    def close(self):
        self.p.stdin.close()
        assert self.p.wait(timeout=10)==0

def find_boundary_from_clean(dev):
    yes=[];no=[]
    assert dev.ask(0)==0;no.append(0)
    assert dev.ask(FULL)==1
    reduce_positive(dev,FULL,yes,no)
    while True:
        new,count=next_falsifier(dev,yes,no)
        if new is None:break
    result=snapshot(yes,no)
    assert result["unresolved_configurations"]==0
    return result

def local_model(variant):
    # Two model worlds: clean monotone completion and non-monotone needle.
    # The first seven probes have identical outcomes in both worlds.
    # The 8th is discriminating at the hidden input. These are abstract
    # logical witnesses, not proofs that the oracle equals either model.
    qs=7+(1 if variant=="with_probe" else 0)
    assert 1<=qs<=8
    if variant in ("without_probe","with_probe"):
        return make(qs,[[True,False],[False,True]],list(range(2)),
                    [0,1],discriminate=(variant=="with_probe"))
    if variant=="epistemic_open":
        return make(7,[[True,False],[False,True]],[0,1],
                    [0],discriminate=False)
    if variant=="one_world_act":
        return make(7,[[True,False]],[0],[0],discriminate=False,
                    nworlds=1)
    raise ValueError(variant)

def make(q,good,must,lower,discriminate=False,nworlds=2):
    sense=[[2]*nworlds for _ in range(q)]
    if discriminate:
        sense[-1]=[1,2]
    m=dict(worldCount=nworlds,actionCount=len(good[0]),probeCount=q,
      good=good,sense=sense,
      nextFalse=[list(range(nworlds)) for _ in range(q)],
      nextTrue=[list(range(nworlds)) for _ in range(q)],
      actionCost=[0]*len(good[0]),probeCost=[1]*q,
      lowerWorld=lower,upperWorld=list(range(nworlds)),
      mustActions=must,mayActions=must,
      probeKinds=["PROBE"]*q,depth=1,budget=1,reserve=4,debt=0)
    validate(m);return m

def c3_audit(out):
    records=[]
    for name,expected in (
        ("without_probe","REFUSE_ROBUST"),
        ("with_probe","PROBE"),
        ("epistemic_open","EPISTEMIC_OPEN"),
        ("one_world_act","ACT")
    ):
        folder=out/"c3_lean"/name
        r=decide(local_model(name),folder)
        assert r["verdict"]==expected,(name,r)
        assert replay(folder),(name,"LEAN_REPLAY_FAILURE")
        if name=="with_probe":
            assert r["plan"]["probe"]==7
        records.append(dict(variant=name,verdict=expected,
            receipt_sha256=r["receipt_sha256"]))
        print("C3_STRUCTURE_BOUNDARY",name,expected,flush=True)
    fail=out/"c3_lean"/"with_probe"
    assert not replay(fail,lean_binary="/no-Lean-binary")
    p=fail/"receipt.json";raw=p.read_bytes()
    try:
        bad=raw.replace(b'"authorized":true',b'"authorized":false')
        assert bad!=raw
        p.write_bytes(bad)
        assert not replay(fail)
    finally:p.write_bytes(raw)
    assert replay(fail)
    return records

def main(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    source=(Path(__file__).resolve().parents[1]/"insacermo_one_engine.py").read_bytes()
    blob=hashlib.sha1(b"blob "+str(len(source)).encode()+bytes([0])+source).hexdigest()
    assert blob==ENGINE_BLOB,"FROZEN_C3_MODIFIED"

    clean=Query("clean")
    conditional=find_boundary_from_clean(clean)
    original_queries=tuple(clean.order)
    assert len(original_queries)==212,(len(original_queries))
    assert conditional["minimal_positive_count"]==4
    assert conditional["unresolved_configurations"]==0
    # A challenging but not magic validation procedure: ask a known positive
    # subset and a strict superset, then 64 random inputs outside the sample.
    terms=conditional["minimal_positive_terms"]
    def included(x):return any((x&t)==t for t in terms)
    u=next(t for t in terms if (t&(FULL^(1<<23)))==t)
    v=FULL^(1<<23)
    assert u!=v and (u&v)==u and included(u) and included(v)
    random_probes=random.Random(SEED+2801).sample(range(WORLD_COUNT),64)
    audits=[u,v]+random_probes
    for x in audits:clean.ask(x)
    # This is the transcript of a possible, successful validation attempt
    # on a genuinely monotone but synthetic device.
    audit_transcript=list(clean.order)
    nclean=len(audit_transcript)
    clean.close()

    obvious=Query("obvious")
    obvious_values=[obvious.ask(x) for x in audit_transcript]
    assert obvious_values[audit_transcript.index(u)]==1
    assert obvious_values[audit_transcript.index(v)]==0
    assert (u&v)==u
    obvious_mismatches=[x for x in audit_transcript
        if obvious.answers[x]!=clean.answers[x]]
    assert v in obvious_mismatches
    obvious.close()

    # The needle is FIXED by a seed before the exploration, not selected
    # after seeing the transcript. Determine whether the actual experiment
    # happened to detect it; expected to remain indistinguishable.
    needle=Query("needle")
    needle_values=[needle.ask(x) for x in audit_transcript]
    needle_mismatches=[x for x in audit_transcript
        if needle.answers[x]!=clean.answers[x]]
    needle.close()
    assert not needle_mismatches,("PREDECLARED_NEEDLE_WAS_DISCOVERED",needle_mismatches)
    assert nclean<350
    # A second ADVERSARIAL COMPLETION may be constructed post-hoc by
    # altering one unobserved positive input. This is an impossibility
    # argument, not a fair holdout test.
    counterexample=next(
        x for x in range(WORLD_COUNT)
        if x not in clean.answers and included(x) and x!=FULL)
    witness_term=next(t for t in terms if (counterexample&t)==t)
    assert counterexample!=witness_term
    assert clean.answers[witness_term]==1
    assert (witness_term&counterexample)==witness_term
    # Adversarial completion and clean law agree on every observed query,
    # differ at counterexample, violating monotonicity.
    nonmonotone_completion=dict(
        candidate_input=counterexample,
        observed_positive_subset=witness_term,
        unobserved_exception_can_be_zero=True,
        indistinguishable_on_every_observed_query=True)

    receipts=c3_audit(out)
    # Reveal oracle's secret location ONLY for auditing after all outcomes
    # and C3 certificates are decided. Never pass this location to the
    # discovery or candidate query strategy.
    from importlib.util import spec_from_file_location,module_from_spec
    spec=spec_from_file_location("independent_oracle_audit",ORACLE)
    module=module_from_spec(spec);spec.loader.exec_module(module)
    fixed_needle=module.hidden_needle()
    assert fixed_needle not in audit_transcript
    assert module.evaluate("needle",fixed_needle)==0
    assert module.evaluate("clean",fixed_needle)==1
    fixed_subset=next(t for t in terms if (fixed_needle&t)==t)
    assert module.evaluate("needle",fixed_subset)==1
    assert (fixed_subset&fixed_needle)==fixed_subset
    report=dict(
        experiment="UNKNOWN_STRUCTURAL_ASSUMPTION_MONOTONICITY_ADVERSARIAL_TEST",
        n_variables=24,n_possible_inputs=WORLD_COUNT,
        original_c3_blob=blob,
        exploration_queries=len(original_queries),
        total_unique_queries_with_64_fresh_random_and_targeted=nclean,
        symbolic_classification_conditional_on_monotonicity=conditional,
        conditioned_on_monotonicity_unresolved=0,
        unconditional_monotonicity_certified=False,
        mode_clean=dict(monotone=True,query_trace_sha256=hashlib.sha256(
            json.dumps(audit_transcript).encode()).hexdigest()),
        mode_obvious=dict(violation_detected=True,
            positive_subset=u,negative_superset=v,
            observations_differing_from_clean=obvious_mismatches),
        mode_fixed_needle=dict(
            exception_precommitted_before_queries=True,
            fixed_exception_revealed_post_audit=fixed_needle,
            positive_subset=fixed_subset,
            observations_differing_from_clean=needle_mismatches,
            false_monotonicity_would_be_inferred_if_claimed=True),
        adversarial_posthoc_completion=nonmonotone_completion,
        historical_c3_certificates=receipts,
        verified_lean_certificates=len(receipts),
        limitations=[
          "All oracles synthetic, not real unknown natural phenomena.",
          "The learner assumes monotonicity for the efficient symbolic reconstruction, then tests rather than proves that assumption.",
          "The fixed rare exception is predeclared; adversarial posthoc completion is a theoretical indistinguishability witness, not an independent secret test.",
          "No number of nonexhaustive finite queries proves unrestricted monotonicity for arbitrary Boolean functions.",
          "The hidden oracle's source is public; practical blindness is via separate process only.",
          "C3 proves four small finite declared contracts, not universal monotonicity of 24-bit inputs.",
          "The 64 random audit probes are fixed before inspecting replies and have no assumption-free guarantee of finding rare exceptions.",
          "The zero unresolved count is conditional on structural monotonicity and cannot be claimed unconditionally."
        ])
    (out/"audit.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
    (out/"query_trace.json").write_text(json.dumps(dict(ordered_queries=audit_transcript,
         clean_answers=[clean.answers[x] for x in audit_transcript],
         obvious_answers=obvious_values,needle_answers=needle_values),indent=2)+"\n")
    print("HIDDEN_STRUCTURE_FINISHED",
        "ORIGINAL",len(original_queries),"TOTAL",nclean,
        "OBVIOUS_DETECTED",len(obvious_mismatches),
        "FIXED_NEEDLE_DETECTED",len(needle_mismatches),
        "LEAN_CERTS",len(receipts),flush=True)
    print("NO_UNCONDITIONAL_MONOTONICITY_PROOF",flush=True)

if __name__=="__main__":
    main(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_hidden_structure")
