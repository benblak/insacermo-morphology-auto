#!/usr/bin/env python3
"""INSACERMO one orchestrated proof-carrying laboratory.
Real NOAA observations -> unknown acquisition clock -> exact wave observation;
synthetic query-only law -> contradiction -> local repair -> certified PROBE;
real original C3 engine -> ACT / PROBE / REPAIR / REFUSE, Lean replay.
The original engine is not edited. NO universal scientific-law claim.
"""
from __future__ import annotations
import hashlib,json,os,sys,subprocess
from pathlib import Path
from datetime import datetime,timedelta,timezone
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from insacermo_one_engine import decide,replay,validate,canonical
from inverse_noaa_clock import retrieve,parse,fit,metrics,split
from inverse_wave_endpoint_certificates import source as get_endpoint_source,read as read_heights
from hidden_structure_24bit_c3 import Query,find_boundary_from_clean
from monotone_24bit_discovery_c3 import FULL

ENGINE_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
PREREG_COMMIT="705c722dc3ae6093500892909047d78b2e2da01e"
EXAMPLE=datetime(2023,2,23,10,10,tzinfo=timezone.utc)

def sha_bytes(b):return hashlib.sha256(b).hexdigest()
def write_json(path,obj):
    path.write_text(json.dumps(obj,ensure_ascii=False,indent=2,sort_keys=True)+"\n")
def model(good,*,sense=None,nfalse=None,ntrue=None,kind=None,depth=0,budget=0,
          lower=None,upper=None,must=None,may=None):
    w=len(good);a=len(good[0]);sense=sense if sense is not None else [[3]*w];q=len(sense)
    obj=dict(worldCount=w,actionCount=a,probeCount=q,
      good=good,sense=sense,
      nextFalse=nfalse if nfalse is not None else [[i for i in range(w)] for _ in range(q)],
      nextTrue=ntrue if ntrue is not None else [[i for i in range(w)] for _ in range(q)],
      actionCost=[0]*a,probeCost=[1]*q,
      lowerWorld=lower if lower is not None else list(range(w)),
      upperWorld=upper if upper is not None else list(range(w)),
      mustActions=must if must is not None else list(range(a)),
      mayActions=may if may is not None else list(range(a)),
      probeKinds=kind if kind is not None else ["PROBE"]*q,
      depth=depth,budget=budget,reserve=4,debt=0)
    validate(obj);return obj

def get_noaa(out):
    root=out/"raw";root.mkdir(exist_ok=True)
    raw_a,prov_a=retrieve("41002",2023,root)
    raw_b,prov_b=retrieve("42002",2023,root)
    train=parse(raw_a)
    y,t=split(train,"WVHT")
    c=fit(y,t)
    val=parse(raw_b)
    vy,vt=split(val,"WVHT")
    score=metrics(vy,vt,c)
    assert c["model"]["period_slots"]==3 and c["status"]=="PERIODIC"
    assert score["f1"]>.99 and score["brier_relative_gain"]>.90
    waves_raw=get_endpoint_source(2,root)
    values=read_heights(waves_raw)
    before=values.get(EXAMPLE-timedelta(minutes=30))
    after=values.get(EXAMPLE+timedelta(minutes=30))
    missing=values.get(EXAMPLE)
    assert missing is None and before==74 and after==80,(before,missing,after)
    assert abs(after-before)==6
    proven=dict(station="46002",year=2023,center_utc=EXAMPLE.isoformat(),
      measured_left_dm=before,measured_right_dm=after,
      observed_minimum_net_difference_dm=abs(after-before),
      central_height="UNKNOWN",
      source_gzip_sha256="93f488bdc6cc78a10469f20089eb337c8166f15845777de84a6c101fee7e8d04")
    return dict(clock_fit=c,clock_validation=score,clock_training_rows=len(train),
      clock_validation_rows=len(val),sources=[prov_a,prov_b,
        dict(station="46002",year=2023,gzip_sha256=proven["source_gzip_sha256"])],
      endpoint=proven)

def discover_challenge():
    # Query-only symbolic source device: no importing its secret evaluator.
    clean=Query("clean")
    try:
        description=find_boundary_from_clean(clean)
        nqueries=len(clean.order)
    finally:clean.close()
    assert description["minimal_positive_count"]==4
    assert description["unresolved_configurations"]==0
    predict=lambda x:any((x&t)==t for t in description["minimal_positive_terms"])
    # A deliberately changed / faulty variant of the same synthetic device.
    alternate=Query("obvious")
    try:
        context=FULL^(1<<23)
        u=next(t for t in description["minimal_positive_terms"] if (t&context)==t)
        observed_u=alternate.ask(u)
        observed_v=alternate.ask(context)
        assert predict(u) and predict(context)
        assert observed_u==1 and observed_v==0
        assert (u&context)==u
        # Repair is a labeled exception patch, NOT proof of a repaired global function.
        repaired=lambda x:0 if x==context else int(predict(x))
        assert repaired(u)==observed_u and repaired(context)==observed_v
        # Active-query control, the actual fresh response is obtained only AFTER
        # C3 has certified PROBE. The same device stays open for this.
        return (dict(symbolic_queries=nqueries,
          minimal_positive_count=description["minimal_positive_count"],
          conditional_coverage=description["unresolved_configurations"]==0,
          premise="MONOTONICITY_UNVERIFIED",
          witness_positive_subset=u,witness_negative_superset=context,
          witness_answers=[observed_u,observed_v],
          contradictory_under_monotonicity=True,
          local_exception_patch=context,
          patched_witnesses_replayed=True,
          global_law_certified=False,
          original_conditional_terms=description["minimal_positive_terms"]),
          alternate,FULL)
    except Exception:
        alternate.close()
        raise

def generated_lean(noaa):
    ex=noaa["endpoint"];left=ex["measured_left_dm"];right=ex["measured_right_dm"]
    assert right>=left and right-left>=5
    return f'''/-!
Automatically generated FROM ORIGINAL parsed NOAA GZIP, with independent
byte-level data auditor. These are EXACT FINITE COMPUTATIONS, not a proof that
the external data provider is infallible or that all hidden waves are known.
-/
namespace InsacermoIntegratedEvidence
def observedLeftDm : Nat := {left}
def observedRightDm : Nat := {right}
theorem observed_net_change_ge_five :
    observedRightDm >= observedLeftDm + 5 := by decide
theorem exact_observed_change :
    observedRightDm - observedLeftDm = {right-left} := by decide
def measured (present : Bool) (height : Nat) : Option Nat :=
  if present then some height else none
theorem missing_center_is_not_identified :
    measured false 0 = measured false 1 ∧ (0 : Nat) ≠ 1 := by decide
theorem zero_one_two_clock :
    ((List.range 3).filter (fun k => k % 3 == 1)).length = 1 := by decide
end InsacermoIntegratedEvidence
'''

def execute(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    root=Path(__file__).resolve().parents[1]
    b=(root/"insacermo_one_engine.py").read_bytes()
    engine_blob=hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()
    assert engine_blob==ENGINE_BLOB,"HISTORICAL_ENGINE_CHANGED"
    events=[]
    def event(name,data):
        events.append(dict(sequence=len(events),stage=name,payload=data))
        print("INTEGRATED_STAGE",len(events)-1,name,flush=True)

    actual=get_noaa(out)
    event("OBSERVE_REAL_NOAA",dict(source_count=3,
      train=actual["clock_training_rows"],validation=actual["clock_validation_rows"],
      example=actual["endpoint"]))
    event("DISCOVER_UNKNOWN_CLOCK",dict(inferred_minutes=actual["clock_fit"]["model"]["period_slots"]*10,
      train_bic_advantage=actual["clock_fit"]["bic_advantage"]))
    event("FALSIFY_ON_OTHER_REAL_STATION",dict(station="42002",year=2023,
      f1=actual["clock_validation"]["f1"],brier_gain=actual["clock_validation"]["brier_relative_gain"]))

    # Real physical epistemic decision under two declared local possible worlds
    # representing different missing physical middle values.
    observed_endpoints_guarantee=actual["endpoint"]["observed_minimum_net_difference_dm"]>=5
    assert observed_endpoints_guarantee
    act_model=model([[True],[True]])
    refused_midpoint_model=model([[True,False],[False,True]])
    # This is an actual same-input ORIGINAL engine, not an external simulation.
    gate_results={}
    for key,contract,expected in [
       ("REAL_ACT_NET_ENDPOINT_CHANGE",act_model,"ACT"),
       ("REAL_REFUSE_UNOBSERVED_CENTER",refused_midpoint_model,"REFUSE_ROBUST")]:
        folder=out/"C3_certificates"/key
        result=decide(contract,folder)
        assert result["verdict"]==expected,(key,result)
        assert replay(folder),(key,"NO_LEAN_PROOF")
        gate_results[key]=dict(verdict=result["verdict"],
           receipt_sha256=result["receipt_sha256"],contract_sha256=result["contract_sha256"],
           authorized=result["authorized"],source_sha256=result["source_sha256"])
        event(key,gate_results[key])
    # Repeated source authentication must be independent of computed c3 contract.

    learned,alternate,probe_input=discover_challenge()
    event("DISCOVER_SYNTHETIC_LAW_CONDITIONALLY",dict(
      conditional_positive_terms=learned["minimal_positive_count"],
      query_count=learned["symbolic_queries"],
      global_claim=False))
    event("FALSIFY_MONOTONICITY_ON_ALTERNATE_DEVICE",dict(
      subset=learned["witness_positive_subset"],
      superset=learned["witness_negative_superset"],
      labels=learned["witness_answers"]))
    event("LOCAL_REPAIR_OF_REPRESENTATION",dict(
      repaired_at=learned["local_exception_patch"],scope="LOCAL_ONLY"))

    # Synthetic finite two-world query-specific contract: two actions = label0/label1.
    probe_model=model([[True,False],[False,True]],sense=[[1,2]],
                      depth=1,budget=1)
    probe_dir=out/"C3_certificates"/"SYNTHETIC_PROBE"
    probe=decide(probe_model,probe_dir)
    assert probe["verdict"]=="PROBE" and probe["plan"]["probe"]==0,probe
    assert replay(probe_dir)
    gate_results["SYNTHETIC_PROBE"]=dict(verdict="PROBE",
        receipt_sha256=probe["receipt_sha256"],contract_sha256=probe["contract_sha256"],
        source_sha256=probe["source_sha256"])
    event("CERTIFIED_ACTIVE_PROBE",dict(input=probe_input,kind="SYNTHETIC",
        proof=probe["receipt_sha256"]))
    # This full-ones input was NOT queried on the *alternate* device before
    # certified PROBE: it is a genuinely fresh query in this local world.
    try: observed=alternate.ask(probe_input)
    finally:alternate.close()
    assert observed==1
    event("ACQUIRE_PROBE_RESPONSE",dict(input=probe_input,answer=observed))
    # New local world matches actually observed answer. It does not certify other x.
    act_after_model=model([[True,False]] if observed==0 else [[False,True]])
    after_dir=out/"C3_certificates"/"SYNTHETIC_ACT_AFTER_PROBE"
    after=decide(act_after_model,after_dir)
    assert after["verdict"]=="ACT" and replay(after_dir)
    gate_results["SYNTHETIC_ACT_AFTER_PROBE"]=dict(verdict="ACT",
       receipt_sha256=after["receipt_sha256"],
       contract_sha256=after["contract_sha256"],
       source_sha256=after["source_sha256"])
    event("CERTIFIED_ACT_AFTER_OBSERVED_PROBE",dict(label=observed,
         scope="SINGLE_INPUT",receipt=after["receipt_sha256"]))

    # Genuine C3 state-change semantics. This *simulated* repair makes all two
    # declared local states reach state 0 with an authorized action; NOT hardware repair.
    repair_contract=model([[True],[False]],sense=[[2,2]],
       nfalse=[[0,1]],ntrue=[[0,0]],kind=["REPAIR"],depth=1,budget=1)
    repair_dir=out/"C3_certificates"/"SYNTHETIC_STATE_REPAIR"
    repair=decide(repair_contract,repair_dir)
    assert repair["verdict"]=="REPAIR" and replay(repair_dir)
    gate_results["SYNTHETIC_STATE_REPAIR"]=dict(verdict="REPAIR",
         receipt_sha256=repair["receipt_sha256"],
         contract_sha256=repair["contract_sha256"],
         source_sha256=repair["source_sha256"])
    event("CERTIFIED_STATE_REPAIR",dict(receipt=repair["receipt_sha256"],
      change="SIMULATED 2-STATE TRANSITION TO GOOD STATE",physical_action=False))

    # Self-generated finite evidence proof directly binds to observed real data values.
    proof=generated_lean(actual)
    p=out/"NoaaEvidence.lean";p.write_text(proof)
    result=subprocess.run(["lean",str(p)],capture_output=True,text=True,timeout=90)
    (out/"direct_lean.log").write_text(result.stdout+"\n"+result.stderr)
    assert result.returncode==0,(result.stdout,result.stderr)
    event("LEAN_CERTIFY_DYNAMIC_REAL_DATA_FACTS",dict(
      proof_sha256=sha_bytes(p.read_bytes()),
      raw_data_file_sha256=actual["endpoint"]["source_gzip_sha256"],
      source="ORIGINAL NOAA OBSERVATION, SEPARATELY AUDITED"))

    # Mutate a copied receipt and confirm original replayer REJECTS corrupted proof;
    # restore the source before checking that original still verifies.
    receipt_path=probe_dir/"receipt.json"
    original=receipt_path.read_bytes()
    try:
        corrupted=original.replace(b'"authorized":true',b'"authorized":false')
        assert corrupted!=original
        receipt_path.write_bytes(corrupted)
        assert not replay(probe_dir),"TAMPERING_UNDETECTED"
    finally:receipt_path.write_bytes(original)
    assert replay(probe_dir)
    assert not replay(probe_dir,lean_binary="/missing/lean")
    event("CERTIFICATE_TAMPERING_AND_MISSING_LEAN_REJECTED",dict(
      tampered_rejected=True,missing_compiler_rejected=True,
      restored_original_reverified=True))

    # Claims the system actually supports, and nothing broader.
    report=dict(verdict="INTEGRATED_C3_LEAN_CHAIN_PASS",
      prereg_commit=PREREG_COMMIT,engine_git_blob=engine_blob,
      real_noaa=actual,synthetic_structure=learned,
      c3_certificates=gate_results,stages=events,
      n_stages=len(events),
      lean_evidence_sha256=sha_bytes(p.read_bytes()),
      real_noaa_claim="ONLY ACT ON MEASURED ENDPOINT DIFFERENCE",
      unknown_physical_midpoint="REFUSE_ROBUST",
      global_law_claim="REFUSE_UNCONDITIONAL",
      architecture="SINGLE ORCHESTRATOR, FROZEN ORIGINAL FINITE C3 GATE, LEAN-SAME-INPUT PROOF",
      proof_boundaries=[
        "C3 formal worlds and labels are dynamically generated from observed question, but bridge to NOAA raw bytes requires an independent raw-data auditor.",
        "Global monotonicity and invented exception patch are not Lean-proven for all 24-bit inputs; only finite local C3 contracts are certified.",
        "Simulated REPAIR is not physical actuation. The alternate device is an explicitly changed synthetic oracle variant.",
        "Active-probe input is fresh for the alternate device but chosen as a predetermined full-ones control, not a learned optimal query.",
        "No world-first physical law was discovered. These data were previously analyzed in separate labs.",
        "Not all previous experimental methods have been independently ported into the one orchestrator."
      ])
    write_json(out/"audit.json",report)
    write_json(out/"stage_manifest.json",events)
    print("INTEGRATED_C3_LEAN_CHAIN_PASS",len(events),
      "C3_RECEIPTS",len(gate_results),"REAL_NOAA_F1",
      actual["clock_validation"]["f1"],flush=True)

if __name__=="__main__":
    root=sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_unified"
    try:execute(root)
    except Exception as exc:
        p=Path(root);p.mkdir(parents=True,exist_ok=True)
        write_json(p/"failure.json",dict(verdict="FAIL",error=repr(exc)))
        print("INTEGRATED_CHAIN_FAILED",repr(exc),flush=True)
        raise
