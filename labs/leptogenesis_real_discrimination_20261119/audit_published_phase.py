"""Reproducible published-model PHASE discrimination laboratory.

Only the prediction intervals are sourced from scientific publications.
The ±error bound is a conditional instrument REQUIREMENT, NOT an
observed / published DUNE or Hyper-K capability, or a 3σ precision.
The frozen C3 kernel classifies a discrete abstraction, whose
physical meaning is conditional on the Lean angular-separation theorem.
"""
import hashlib,json,os
from pathlib import Path
from itertools import product
from insacermo_one_engine import decide,replay,solve

OUT=Path(os.environ.get("LEP_DISCRIMINATION_OUT","/tmp/insacermo-lep-discrimination"))
OUT.mkdir(parents=True,exist_ok=True)
ORIGINAL_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
RANGES_A=list(range(198,226))
RANGES_B=list(range(5,41))+list(range(320,356))

def dist(x,y):return min((x-y)%360,(y-x)%360)

def check_intervals():
    assert len(RANGES_A)==28 and len(RANGES_B)==72
    pairs=[(dist(a,b),a,b) for a,b in product(RANGES_A,RANGES_B)]
    gap,closest_a,closest_b=min(pairs)
    assert gap==95 and (closest_a,closest_b)==(225,320)
    results=[]
    for error in [0,20,40,47,48,50]:
        obsA={z for z in range(360) if any(dist(z,a)<=error for a in RANGES_A)}
        obsB={z for z in range(360) if any(dist(z,b)<=error for b in RANGES_B)}
        overlap=sorted(obsA&obsB)
        results.append({"error_bound_deg":error,
                        "compatible_measurement_overlap_count":len(overlap),
                        "first_overlapping_measurement":overlap[0] if overlap else None})
        if error<=47:assert not overlap,(error,overlap)
        if error>=48:assert overlap
    assert dist(225,272)==47 and dist(320,272)==48
    return gap,results

def c3_contract(with_rival=False,budget=1):
    # Worlds: A, B-low, B-high, optionally C-rival indistinguishable from A
    # The one-bit probe means "is observed angle in the expanded A interval".
    # Its deterministic assignments are entailed ONLY if one of A/B is true
    # AND the deterministic measurement error is bounded by <=47 degrees.
    good=[[True,False],[False,True],[False,True]]
    sense=[[2,1,1]]
    if with_rival:
        good=[row+[False] for row in good]
        good.append([False,False,True])
        sense=[[2,1,1,2]]
    n=len(good);actions=len(good[0])
    return {
      "worldCount":n,"actionCount":actions,"probeCount":1,
      "good":good,"sense":sense,
      "nextFalse":[list(range(n))],"nextTrue":[list(range(n))],
      "actionCost":[0]*actions,"probeCost":[1],
      "lowerWorld":list(range(n)),"upperWorld":list(range(n)),
      "mustActions":list(range(actions)),"mayActions":list(range(actions)),
      "probeKinds":["PROBE"],"depth":1,"budget":budget,
      "reserve":10,"debt":0
    }

def verify_proof_gate():
    original=Path("insacermo_one_engine.py").read_bytes()
    blob=hashlib.sha1(b"blob "+str(len(original)).encode()+b"\0"+original).hexdigest()
    assert blob==ORIGINAL_BLOB,blob
    cases=[
        ("NO_MEASUREMENT",c3_contract(budget=0),"REFUSE_ROBUST"),
        ("IDEAL_PHASE_PROBE_BOUND_47",c3_contract(budget=1),"PROBE"),
        ("NEW_RIVAL_SAME_PHASE_SIGNAL",c3_contract(with_rival=True,budget=1),"REFUSE_ROBUST")
    ]
    receipts=[]
    for label,m,expected in cases:
        r=decide(m,OUT/label)
        assert r["verdict"]==expected,(label,r)
        assert replay(OUT/label)
        receipts.append({"case":label,"verdict":expected,"replayed":True,
                         "contract_sha256":r["contract_sha256"],
                         "proof_source_sha256":r["source_sha256"]})
    # Independently check reachability with all outcomes.
    assert solve(cases[0][1],range(3),[0,1],1,0) is None
    assert solve(cases[1][1],range(3),[0,1],1,1) is not None
    assert solve(cases[2][1],range(4),[0,1,2],1,1) is None
    nolean=decide(c3_contract(),OUT/"MISSING_LEAN",lean_binary="/no/lean")
    assert nolean["verdict"]=="REFUSE_CERTIFICATE_MISSING"
    assert nolean["authorized"] is False
    return receipts

def main():
    gap,errors=check_intervals()
    receipts=verify_proof_gate()
    out={
      "kind":"published prediction intervals + conditionally hypothetical error model",
      "published_model_A_CP_phase_deg":[198,225],
      "published_model_B_CP_phase_deg":[[5,40],[320,355]],
      "smallest_angular_gap_deg":gap,
      "maximum_closed_integer_error_bound_for_guaranteed_discrimination_deg":47,
      "counterexample_at_48_deg":{"true_A_deg":225,"true_B_deg":320,"measurement_deg":272},
      "uncertainty_scope":"Worst-case bounded cyclic angle error, not a statistical uncertainty or a real detector projection",
      "source_scope":"2018 and 2021 model predictions; current global-fit 3sigma region overlaps both A and B-high",
      "instrument_scope":"DUNE/Hyper-K can study CP but no forecast of these guaranteed bounded errors is implied",
      "synthetic_C3_abstraction_scope":"C3 sees 3 family worlds (A,B-low,B-high); extra adversarial rival is hypothetical, not a discovered physical mechanism",
      "error_sweep":errors,"C3_original_lean_receipts":receipts,
      "C3_original_blob":ORIGINAL_BLOB
    }
    (OUT/"PUBLISHED_PHASE_SEPARATION_REPORT.json").write_text(json.dumps(out,indent=2,ensure_ascii=False)+"\n")
    print(json.dumps(out,indent=2,ensure_ascii=False))
    print("PUBLISHED_CP_PHASE_C3_LEAN_AUDIT_SUCCESS")

if __name__=="__main__":main()
