#!/usr/bin/env python3
"""INSACERMO finite actionability on *measured* UCI NOx emissions.

FROZEN original C3, no modifications. Two kinds of results:
(1) Within declared real-world samples, a decision contract (NOx >=70) can
    need fewer questions than identifying the individual observation.
(2) Observationally identical eight-bit sensor profiles can have different
    outcomes; C3 correctly REFUSE_ROBUST.
(3) Transfer of 2011 profile purity to 2015 is quantitatively falsified.
    Strictly retrospective audit; not prospectively blind since 2015 labels
    were seen in an earlier experiment.

No claim of physical law discovery, of probabilistic validity from Lean, or
of universal safety of emissions decisions.
"""
from __future__ import annotations
import csv,hashlib,io,json,itertools,math,urllib.request
from collections import defaultdict
from functools import lru_cache
from pathlib import Path
from insacermo_one_engine import decide,replay,validate

REPO="https://raw.githubusercontent.com/MarkLee7925/Gas-Turbine-Emissions/cb411da49edabfe1cbf8cb43650e612b1c88695c/data/"
DATA_BLOB={2011:"403de0df000bedaffa99eae75b496b646200d953",2015:"654a113d7721faf087a50bb1101002ccd3d2a7a5"}
C3_SOURCE_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
COLS=["AT","AP","AH","AFDP","GTEP","TIT","TAT","TEY","CDP","CO","NOX"]
SENSOR_COLS=tuple(range(8))
NOX_THRESHOLD=70.

def blob(v):
    return hashlib.sha1(b"blob "+str(len(v)).encode()+bytes([0])+v).hexdigest()

def get_data():
    out={}
    for year in (2011,2015):
        req=urllib.request.Request(REPO+f"gt_{year}.csv",
          headers={"User-Agent":"INSACERMO-C3-boundary-science/1.0"})
        with urllib.request.urlopen(req,timeout=90) as res:raw=res.read()
        assert blob(raw)==DATA_BLOB[year],("SOURCE_CHANGED",year)
        obj=list(csv.DictReader(io.StringIO(raw.decode("utf-8-sig"))))
        assert list(obj[0])==COLS
        rows=[tuple(float(r[k]) for k in COLS) for r in obj]
        assert len(rows)==({2011:7411,2015:7384}[year])
        out[year]=rows
    return out

def median(v):
    s=sorted(v);return s[len(s)//2]

def sensors(row,thresholds):
    return tuple(int(row[k]>=thresholds[k]) for k in SENSOR_COLS)

def signature_stats(rows,thresholds):
    groups=defaultdict(list)
    for idx,row in enumerate(rows):groups[sensors(row,thresholds)].append((idx,row))
    classes=dict()
    for k,group in groups.items():
        outcomes=[int(row[10]>=NOX_THRESHOLD) for _,row in group]
        classes[k]=dict(count=len(group),low=outcomes.count(0),high=outcomes.count(1))
    return groups,classes

def make_model(rows,thresholds,kind="threshold",probe_indices=None,depth=1):
    qs=list(SENSOR_COLS if probe_indices is None else probe_indices)
    assert rows and len(rows)<=8 and qs and len(qs)<=8 and depth<=4
    if kind=="threshold":
        labels=[int(row[10]>=NOX_THRESHOLD) for row in rows]
        acts=2
    elif kind=="identity":
        labels=list(range(len(rows)));acts=len(rows)
    else:raise ValueError(kind)
    signature=[sensors(row,thresholds) for row in rows]
    n=len(rows)
    m=dict(worldCount=n,actionCount=acts,probeCount=len(qs),
       good=[[labels[w]==a for a in range(acts)] for w in range(n)],
       sense=[[2 if signature[w][q] else 1 for w in range(n)] for q in qs],
       nextFalse=[list(range(n)) for _ in qs],
       nextTrue=[list(range(n)) for _ in qs],
       actionCost=[0]*acts,probeCost=[1]*len(qs),
       lowerWorld=list(range(n)),upperWorld=list(range(n)),
       mustActions=list(range(acts)),mayActions=list(range(acts)),
       probeKinds=["PROBE"]*len(qs),
       depth=depth,budget=depth,reserve=8,debt=0)
    validate(m)
    return m

def independent_min_queries(rows,thresholds,kind,qs):
    labels=[int(r[10]>=NOX_THRESHOLD) for r in rows] if kind=="threshold" else list(range(len(rows)))
    sig=[sensors(r,thresholds) for r in rows]
    @lru_cache(None)
    def rec(worlds,available):
        if len({labels[w] for w in worlds})<=1:return 0
        best=float("inf")
        for q in available:
            a=tuple(w for w in worlds if sig[w][q]==0)
            b=tuple(w for w in worlds if sig[w][q]==1)
            if not a or not b:continue
            remaining=tuple(i for i in available if i!=q)
            c=1+max(rec(a,remaining),rec(b,remaining))
            best=min(best,c)
        return best
    return rec(tuple(range(len(rows))),tuple(qs))

def case(out,title,rows,th,kind,qs,depth,expected,chosen_q=None):
    folder=out/"Lean_contracts"/title
    model=make_model(rows,th,kind,qs,depth)
    res=decide(model,folder)
    assert res["verdict"]==expected,(title,res)
    assert replay(folder),(title,"LEAN_REPLAY_FAILED")
    independent=independent_min_queries(rows,th,kind,qs)
    assert (independent<=depth)==(expected!="REFUSE_ROBUST"),(title,independent,expected)
    if chosen_q is not None:
        assert res["verdict"]=="PROBE" and qs[res["plan"]["probe"]]==chosen_q,(title,res)
    return dict(name=title,worlds=len(rows),contract=kind,
        allowed_probes=list(qs),depth=depth,independent_min_depth=(
          independent if math.isfinite(independent) else None),
        verdict=res["verdict"],chosen_global_probe=(
           qs[res["plan"]["probe"]] if isinstance(res.get("plan"),dict) and "probe" in res["plan"] else None),
        certificate_hash=res["receipt_sha256"])

def select_contract_example(rows,th):
    # Explicitly constructed diagnostic sample; select four true-low-NOx and
    # four true-high-NOx with DISTINCT full signatures, separable by AT.
    # NO claim this is representative of the whole turbine sample.
    picked=[];already=set()
    for desired_label,at in ((1,0),(0,1)):
        candidates=sorted((r for r in rows if int(r[10]>=NOX_THRESHOLD)==desired_label
              and sensors(r,th)[0]==at),key=lambda r:tuple(sensors(r,th)))
        n=0
        for r in candidates:
            sig=sensors(r,th)
            if sig in already:continue
            picked.append(r);already.add(sig);n+=1
            if n==4:break
        assert n==4
    assert len(picked)==8 and len(already)==8
    return picked

def find_opposing_pairs(groups):
    pairs=[]
    for sig,items in sorted(groups.items()):
        good=next((r for _,r in items if r[10]<NOX_THRESHOLD),None)
        bad=next((r for _,r in items if r[10]>=NOX_THRESHOLD),None)
        if good is not None and bad is not None:
            pairs.append((sig,good,bad))
        if len(pairs)==4:break
    assert len(pairs)==4
    return pairs

def run(root):
    root=Path(root);root.mkdir(parents=True,exist_ok=True)
    engine=(Path(__file__).resolve().parents[1]/"insacermo_one_engine.py").read_bytes()
    assert blob(engine)==C3_SOURCE_BLOB,"C3_FROZEN_ENGINE_CHANGED"
    data=get_data()
    th={i:median(r[i] for r in data[2011]) for i in SENSOR_COLS}
    groups,profile=signature_stats(data[2011],th)
    assert len(groups)==148
    mixed=sum(d["low"]>0 and d["high"]>0 for d in profile.values())
    pure=sum(d["low"]==0 or d["high"]==0 for d in profile.values())
    assert (mixed,pure)==(77,71)
    model2011={k:(1 if d["low"]==0 else 0)
       for k,d in profile.items() if (d["low"]==0 or d["high"]==0)}
    found=0;errors=[];correct=[];uncovered=0
    for i,r in enumerate(data[2015]):
        k=sensors(r,th)
        if k not in model2011:
            uncovered+=1;continue
        found+=1
        if model2011[k]==int(r[10]>=NOX_THRESHOLD):correct.append(i)
        else:errors.append(i)
    assert (found,len(errors))==(1058,240),(found,len(errors))
    # Formal finite selected-example demonstration
    selected=select_contract_example(data[2011],th)
    dmin=independent_min_queries(selected,th,"threshold",tuple(range(8)))
    imin=independent_min_queries(selected,th,"identity",tuple(range(8)))
    assert dmin==1 and imin>=3 and math.isfinite(imin),(dmin,imin)
    audit=[]
    audit.append(case(root,"real_8_worlds_action_AT",selected,th,
      "threshold",list(range(8)),1,"PROBE",chosen_q=0))
    audit.append(case(root,"real_8_worlds_action_without_AT",selected,th,
      "threshold",[0],1,"PROBE",chosen_q=0))
    audit.append(case(root,"real_8_worlds_identity_1_probe",selected,th,
      "identity",list(range(8)),1,"REFUSE_ROBUST"))
    audit.append(case(root,"real_8_worlds_identity_min_depth",selected,th,
      "identity",list(range(8)),imin,"PROBE"))
    # Four real conflicting indistinguishable pairs -> robust refusal,
    # independently of which of the eight binary sensors is consulted.
    pairs=find_opposing_pairs(groups)
    for i,(sig,good,bad) in enumerate(pairs):
        audit.append(case(root,f"real_same_bits_opposite_outcome_pair_{i}",
         [good,bad],th,"threshold",list(range(8)),4,"REFUSE_ROBUST"))
    # Positive C3 control: a pure profile with eight real observations.
    safe_cells=[(k,items) for k,items in groups.items() if len(items)>=8
                and all(r[10]<NOX_THRESHOLD for _,r in items)]
    assert safe_cells
    sig,items=sorted(safe_cells,key=lambda v: -len(v[1]))[0]
    audit.append(case(root,"real_pure_cell_action",[r for _,r in items[:8]],th,
      "threshold",list(range(8)),0,"ACT"))
    assert len(audit)==9
    receipt=root/"Lean_contracts"/"real_8_worlds_action_AT"
    assert not replay(receipt,lean_binary="/missing-lean")
    p=receipt/"receipt.json";original=p.read_bytes()
    manipulated=original.replace(b'"authorized":true',b'"authorized":false')
    assert manipulated!=original
    try:
        p.write_bytes(manipulated)
        assert not replay(receipt)
    finally:p.write_bytes(original)
    assert replay(receipt)
    record=dict(
        experiment="INSACERMO contract sufficiency vs full state identification and future transfer",
        source="UCI 2011 and 2015 gas turbine measured NOX",
        data_git_blobs=DATA_BLOB,engine_git_blob=C3_SOURCE_BLOB,
        data_counts={"2011":len(data[2011]),"2015":len(data[2015])},
        threshold_nox_mg_m3=NOX_THRESHOLD,
        sensor_thresholds={COLS[k]:th[k] for k in SENSOR_COLS},
        sensor_bits=8,
        profiles_2011=len(groups),mixed_profiles_2011=mixed,pure_profiles_2011=pure,
        finite_example=dict(eight_selected_real_measurements=[dict(
          sensor_bits=list(sensors(r,th)),measured_nox=r[10],
          high_nox=bool(r[10]>=NOX_THRESHOLD)) for r in selected],
          min_decision_queries=dmin,min_identity_queries=imin),
        transfer_2015=dict(
          technique="2011 pure signature mapping, with NOx threshold; absent or mixed profiles refuse",
          total=len(data[2015]),acted=found,refused=uncovered,
          wrong= len(errors),correct=len(correct),error_rate_on_act= len(errors)/found,
          coverage=found/len(data[2015]),
          warning="retrospective, NOT a certified 2015 safety rate",
          first_10_violating_2015_indices=errors[:10]),
        formal_C3_certificates=audit,
        Lean_replayed=len(audit),
        integrity_controls=["tampered_receipt_refused","Lean_missing_refused"],
        limitations=[
          "2015 results have been inspected in an earlier November run, so this is NOT a new blind holdout",
          "Threshold 70 and eight median-based probes are explicitly specified; results conditional on this experiment",
          "Selected 8-row example demonstrates possibility, not prevalence of low-cost decision",
          "Real labels are NOx emissions, not labels of safe operation; 70 mg/m3 is an illustrative research threshold, NOT regulatory limit",
          "2011 pure profile inference does not generalize automatically to 2015; 240 violations documented",
          "Lean verifies only posthoc declared finite C3 world models, not the 2015 empirical generalization or every row",
          "The independent minimal-depth oracle is Python DP and is checked against the C3 outcomes",
          "This distinction between identification and decision is known in information theory; no historical originality claimed"
        ])
    (root/"audit.json").write_text(json.dumps(record,indent=2,ensure_ascii=False)+"\n")
    print("CONTRACT_2011_REAL",len(data[2011]),"PROFILES",len(groups),
          "PURE",pure,"MIXED",mixed,flush=True)
    print("REAL_DECISION_VS_IDENTITY_COST",dmin,imin,flush=True)
    print("TRANSFER_2015_REAL","ACT",found,"REFUSE",uncovered,
          "WRONG",len(errors),"ERROR_RATE",len(errors)/found,flush=True)
    print("FROZEN_C3_CONTRACT_INFORMATION_PASS",len(audit),flush=True)
    return record

if __name__=="__main__":
    import sys
    run(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_actionability_industry")
