"""INSACERMO antimatter: finite synthetic observational obstruction laboratory.

IMPORTANT: Physical eta/eEDM anchors are literature measurements, but ALL
mechanism-specific predicted outcomes in benchmarks_synthetiques.json
are deliberately invented. No physical baryogenesis model is selected.
The original C3 module remains unchanged.
"""
from __future__ import annotations
from collections import defaultdict
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import hashlib, json, os, math

from insacermo_one_engine import decide, replay, solve

HERE=Path(__file__).resolve().parent
OUT=Path(os.environ.get("ANTIMATTER_OUT","/tmp/insacermo-antimatter"))
B=json.loads((HERE/"benchmarks_synthetiques.json").read_text())
OBS=json.loads((HERE/"observations_publiques.json").read_text())
ROWS=B["benchmarks"]
OLD_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"

def git_blob(path):
    raw=Path(path).read_bytes()
    return hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\\0"+raw).hexdigest()

def verify_input_separation():
    assert "SYNTHETIC" in B["declaration"]
    assert len(ROWS)==8 and len(B["probes"])==5
    assert len({x["id"] for x in ROWS})==len(ROWS)
    for r in ROWS:
        assert len(r["outcomes"])==5
        assert all(type(x)==int and x in (0,1) for x in r["outcomes"])
    assert ROWS[0]["outcomes"][:4]==ROWS[6]["outcomes"][:4]
    assert ROWS[0]["outcomes"][4]!=ROWS[6]["outcomes"][4]
    assert ROWS[0]["family"]!=ROWS[6]["family"]
    anchor=OBS["eta10_CMB"]
    for w in B["closed_panel"]+ [6]:
        assert abs(ROWS[w]["eta10"]-anchor["mean"])<=anchor["reported_uncertainty"]+1e-9
        assert ROWS[w]["eEDM_abs_units_1e30"] < OBS["electron_edm"]["upper_abs"]
    assert ROWS[7]["eEDM_abs_units_1e30"]>OBS["electron_edm"]["upper_abs"]
    # This screening is only an illustration of accepting/rejecting
    # synthetic numerical fixtures. The PDG 1-sigma error and a 90% CL
    # EDM constraint are NOT hard exclusion cuts on physical models.
    return True

def fibres(ids,probes):
    d=defaultdict(list)
    for w in ids:
        d[tuple(ROWS[w]["outcomes"][q] for q in probes)].append(w)
    return dict(d)

def family_safe(ids,probes):
    return all(len({ROWS[w]["family"] for w in group})==1
               for group in fibres(ids,probes).values())

def exhaustive_fixed(ids,allowed):
    for k in range(len(allowed)+1):
        choices=[sel for sel in combinations(allowed,k) if family_safe(ids,sel)]
        if choices:return {"minimum":k,"sets":[list(t) for t in choices]}
    return {"minimum":None,"sets":[]}

def exhaustive_adaptive(ids,allowed):
    @lru_cache(None)
    def rec(worlds,probes):
        if len({ROWS[w]["family"] for w in worlds})==1:
            return 0,{"act":ROWS[worlds[0]]["family"]}
        candidates=[]
        for q in probes:
            no=tuple(w for w in worlds if ROWS[w]["outcomes"][q]==0)
            yes=tuple(w for w in worlds if ROWS[w]["outcomes"][q]==1)
            if not no or not yes:continue
            tail=tuple(t for t in probes if t!=q)
            nd,nt=rec(no,tail)
            yd,yt=rec(yes,tail)
            if nd is not None and yd is not None:
                candidates.append((1+max(nd,yd),q,{"probe":q,"no":nt,"yes":yt}))
        if not candidates:return None,None
        depth,q,tree=min(candidates,key=lambda x:(x[0],x[1]))
        return depth,tree
    d,t=rec(tuple(ids),tuple(allowed))
    return {"minimum_worst_case_depth":d,"tree":t}

def first_obstruction(ids,allowed):
    for group in fibres(ids,allowed).values():
        if len({ROWS[w]["family"] for w in group})>1:
            a,b=next((a,b) for a in group for b in group
                     if ROWS[a]["family"]!=ROWS[b]["family"])
            return {"worlds":[ROWS[a]["id"],ROWS[b]["id"]],
                    "same_observation":[ROWS[a]["outcomes"][q] for q in allowed],
                    "different_families":[ROWS[a]["family"],ROWS[b]["family"]]}
    return None

def c3_model(ids,allowed,budget,depth=4,lower=None,upper=None):
    ids=list(ids)
    assert 1<=len(ids)<=8
    allowed=list(allowed)
    assert allowed
    cats=sorted({ROWS[w]["family"] for w in ids})
    cat_id={c:i for i,c in enumerate(cats)}
    good=[[cat_id[ROWS[w]["family"]]==a for a in range(len(cats))] for w in ids]
    qs=[[1 if ROWS[w]["outcomes"][q]==0 else 2 for w in ids] for q in allowed]
    nq=[list(range(len(ids))) for _ in qs]
    m=dict(worldCount=len(ids),actionCount=len(cats),probeCount=len(qs),
        good=good,sense=qs,nextFalse=nq,nextTrue=nq,
        actionCost=[0]*len(cats),probeCost=[1]*len(qs),
        lowerWorld=list(range(len(ids))) if lower is None else lower,
        upperWorld=list(range(len(ids))) if upper is None else upper,
        mustActions=list(range(len(cats))),mayActions=list(range(len(cats))),
        probeKinds=["PROBE"]*len(qs),depth=depth,budget=budget,reserve=20,debt=0)
    return m

def check_oracle_vs_c3():
    # All 2^6 nonempty or partial subsets on the six-world closed panel,
    # all 16 probe subsets, budgets 0..4. Avoid empty subsets.
    checks=0
    for mask in range(1,1<<6):
        ids=[w for w in range(6) if mask&(1<<w)]
        for pmask in range(16):
            allowed=[q for q in range(4) if pmask&(1<<q)]
            for budget in range(5):
                oracle=exhaustive_adaptive(ids,allowed)
                expected=(oracle["minimum_worst_case_depth"] is not None
                          and oracle["minimum_worst_case_depth"]<=budget)
                # Original C3 formally requires >=1 probe, so use a dummy
                # with zero budget when the allowed set is empty.
                if not allowed:
                    if budget!=0:continue
                    allowed_=[0]  # C3 could use this with positive budget; here budget 0
                else:allowed_=allowed
                m=c3_model(ids,allowed_,budget,depth=4)
                t=solve(m,m["upperWorld"],m["mustActions"],m["depth"],budget)
                if (t is not None)!=expected:
                    raise AssertionError((ids,allowed,budget,oracle,t))
                checks+=1
    return checks

def certify():
    all6=B["closed_panel"];all7=B["adversarial_panel"]
    fixtures=[
       ("ACT_SINGLE",c3_model(all6,[0],0,upper=[0],lower=[0]),"ACT"),
       ("REFUSE_CLOSED_DEPTH2",c3_model(all6,[0,1,2,3],2),"REFUSE_ROBUST"),
       ("PROBE_CLOSED_DEPTH3",c3_model(all6,[0,1,2,3],3),"PROBE"),
       ("REFUSE_COLLISION_4_PROBES",c3_model(all7,[0,1,2,3],4),"REFUSE_ROBUST"),
       ("PROBE_IDEAL_FIFTH",c3_model(all7,[0,1,2,3,4],4),"PROBE"),
       ("OPEN_UNCERTAIN_ENVELOPE",c3_model(all7,[0,1,2,3],4,lower=[0]),"EPISTEMIC_OPEN"),
       ("REFUSE_ONE_PROBE",c3_model(all6,[0],1),"REFUSE_ROBUST"),
    ]
    receipts=[]
    for name,m,expected in fixtures:
        folder=OUT/name
        r=decide(m,folder)
        assert r["verdict"]==expected,(name,r)
        assert r["authorized"] == (expected in ("ACT","PROBE","REPAIR")),(name,r)
        assert replay(folder),name
        receipts.append({"case":name,"verdict":r["verdict"],
                         "receipt_sha256":r["receipt_sha256"],"replay":True})
    # Require receipt mismatch detection and fail-closed if Lean cannot execute.
    p=OUT/"ACT_SINGLE"/"receipt.json"
    original=p.read_bytes()
    j=json.loads(original)
    j["authorized"]=False
    p.write_text(json.dumps(j))
    assert not replay(p.parent)
    p.write_bytes(original)
    assert replay(p.parent)
    fail=decide(fixtures[0][1],OUT/"MISSING_LEAN",
                lean_binary="/deliberately/not/installed/lean")
    assert fail["verdict"]=="REFUSE_CERTIFICATE_MISSING" and not fail["authorized"]
    return receipts

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    assert git_blob(Path("insacermo_one_engine.py"))==OLD_BLOB
    verify_input_separation()
    closed=B["closed_panel"];adv=B["adversarial_panel"]
    report={
      "status":"formal model laboratory only, NOT cosmological discovery",
      "historic_C3_git_blob":OLD_BLOB,
      "public_measurement_anchors":OBS,
      "synthetic_prediction_warning":B["declaration"],
      "closed_panel":{"fixed":exhaustive_fixed(closed,range(4)),
                      "adaptive":exhaustive_adaptive(closed,range(4))},
      "adversarial_no_new_instrument":{
          "fixed":exhaustive_fixed(adv,range(4)),
          "adaptive":exhaustive_adaptive(adv,range(4)),
          "collision":first_obstruction(adv,range(4))},
      "adversarial_with_ideal_probe":{
          "fixed":exhaustive_fixed(adv,range(5)),
          "adaptive":exhaustive_adaptive(adv,range(5))},
      "oracle_C3_crosschecks":check_oracle_vs_c3(),
      "C3_lean_replay_receipts":certify(),
    }
    (OUT/"RESULTS.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\\n")
    print(json.dumps({k:v for k,v in report.items() if k not in ("public_measurement_anchors",)},
                     indent=2,ensure_ascii=False))
    print("ANTIMATTER_C3_LEAN_LAB_SUCCESS")

if __name__=="__main__":main()
