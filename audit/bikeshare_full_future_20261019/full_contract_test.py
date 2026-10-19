#!/usr/bin/env python3
"""INSACERMO complete FUTURE/CAPABILITY/REPAIR/PROBE/REFUSE witness, Oct 2026.
REAL source: UCI Bike Sharing hourly rental records (2011-2012).
SIMULATED contract: abstract inventory reserve units, action permissions and repairs.
Neither actual station inventory nor interventions nor future safety is observed.
Three baselines: greedy-now, complete classical AND/OR (same model), frozen C3+Lean.
Temporal holdout is archival, not prospective data collected after protocol lock.
No claim of novelty, speedup, or superiority over full-horizon shield.
"""
import csv,io,zipfile,urllib.request,json,hashlib,statistics,sys
from collections import defaultdict,Counter
from functools import lru_cache
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from insacermo_one_engine import decide,replay
OUT=ROOT/"audit/bikeshare_full_future_20261019/evidence"
OUT.mkdir(parents=True,exist_ok=True)
SOURCE="https://archive.ics.uci.edu/static/public/275/bike+sharing+dataset.zip"
with urllib.request.urlopen(SOURCE,timeout=90) as r:raw=r.read()
shasum=hashlib.sha256(raw).hexdigest()
with zipfile.ZipFile(io.BytesIO(raw)) as z:
    hr=[x for x in z.namelist() if x.endswith("hour.csv")]
    assert len(hr)==1,hr
    rows=list(csv.DictReader(io.TextIOWrapper(z.open(hr[0]),encoding="utf-8-sig")))
assert len(rows)==17379,len(rows)
days=defaultdict(dict)
for row in rows:
    day=row["dteday"];hour=int(row["hr"]);count=int(row["cnt"])
    assert 0<=hour<=23 and count>=0 and hour not in days[day],(day,hour)
    assert count==int(row["casual"])+int(row["registered"])
    days[day][hour]=count
# Only days with all 6 hourly readings in each observation and future window.
windows=[]
for day,counts in sorted(days.items()):
    if not all(set(range(start,start+6))<=set(counts) for start in (6,12,18)):continue
    windows.append((day,tuple(sum(counts[h] for h in range(start,start+6)) for start in (6,12,18))))
assert len(windows)>=700,len(windows)
split=int(len(windows)*0.75)
train=windows[:split];hold=windows[split:]
assert train[-1][0]<hold[0][0]
def quantile(data,fraction):
    s=sorted(data)
    idx=(len(s)-1)*fraction;lo=int(idx);hi=min(lo+1,len(s)-1)
    return s[lo]*(hi-idx)+s[hi]*(idx-lo) if lo!=hi else s[lo]
T0=quantile([w[1][0] for w in train],0.5)
T1=quantile([w[1][1] for w in train],0.5)
T2=quantile([w[1][2] for w in train],0.75)
def sig(c):return (int(c[0]>T0),int(c[1]>T1))
def high(c):return int(c[2]>T2)
training=defaultdict(Counter)
for date,c in train:training[sig(c)][high(c)]+=1
evidence=Counter()
examples=[]
for date,c in hold:
    label=high(c);s=sig(c)
    baseline=(1 if training[s][1]>training[s][0] else 0) if s in training else 0
    # Contract only permits risky action if its training support excludes HIGH.
    # This is a train-derived IN-SAMPLE claim; monitor factual test failures.
    permit_fast=(s in training and training[s][1]==0)
    action="FAST" if permit_fast else "PRESERVE"
    evidence["holdout_days"]+=1
    evidence["actual_high"]+=label
    evidence["majority_errors"]+=int(baseline!=label)
    evidence["greedy_future_violation"]+=label
    evidence["fast_permitted"]+=permit_fast
    evidence["training_derived_violations"]+=int(permit_fast and label)
    evidence["future_preserved"]+=int(not permit_fast)
    # Full-uncertainty safety shield is ALWAYS preserve, because both future
    # outcomes are possible without further trustworthy information.
    evidence["full_shield_future_violations"]+=0
    evidence["oracle_if_future_known_fast"]+=int(not label)
    if permit_fast and label:examples.append(date)
# Four declared states: future low/high x reserve capacity 2/3.
# Release-now (FAST) consumes 1 unit; evening obligation requires 1 or 2.
# Preserve-now consumes 0. REPAIR increases reserve from 2 to 3 for unit cost.
# THESE ARE INVENTED RESOURCE UNITS, NOT OBSERVED BIKE FLEET CAPACITY.
worlds=[(lowhigh,capacity) for capacity in (2,3) for lowhigh in (0,1)]
assert worlds==[(0,2),(1,2),(0,3),(1,3)]
good=[[capacity-1 >= (1+ev),capacity >= (1+ev)] for ev,capacity in worlds]
def contract(actions=(0,1),depth=0,repair=False,lower=(0,1),budget=1, debt=0):
    return dict(worldCount=4,actionCount=2,probeCount=1,
        good=good,
        sense=[[2,2,2,2] if repair else [1,1,1,1]],
        nextFalse=[list(range(4))],
        nextTrue=[[2,3,2,3] if repair else list(range(4))],
        actionCost=[0,0],probeCost=[1],
        lowerWorld=list(lower),upperWorld=[0,1],
        mustActions=list(actions),mayActions=list(actions),
        probeKinds=["REPAIR" if repair else "PROBE"],
        depth=depth,budget=budget,reserve=3,debt=debt)
# Sensor forecasts the future perfectly ONLY BY ASSUMPTION; exercise PROBE
# without falsely claiming morning traffic can predict evening demand.
def info_contract(noisy=False):
    m=contract(actions=(0,1),depth=1,repair=False)
    m["good"]=[[ev==0,ev==1] for ev,capacity in worlds]
    m["sense"]=[[3 if noisy and i==0 else (1 if ev==0 else 2)
                 for i,(ev,capacity) in enumerate(worlds)]]
    return m
specimens={
    "FUTURE_PRESERVE":(contract(),"ACT"),
    "SELL_CAPABILITY_REFUSE":(contract(actions=(0,),depth=0),"REFUSE_ROBUST"),
    "REPAIR_CAPABILITY":(contract(actions=(0,),depth=1,repair=True),"REPAIR"),
    "EPISTEMIC_UNKNOWN_FUTURE":(contract(actions=(0,),depth=0,lower=(0,)),"EPISTEMIC_OPEN"),
    "HYPOTHETICAL_PERFECT_FUTURE_SENSOR":(info_contract(False),"PROBE"),
    "NOISY_FUTURE_SENSOR":(info_contract(True),"REFUSE_ROBUST"),
    "DEBT_BLOCKS_REPAIR":(contract(actions=(0,),depth=1,repair=True,debt=2),"REFUSE_ROBUST")
}
def classic(m,subset,allowed,depth,budget):
    @lru_cache(None)
    def win(ws,d,b):
        if any(m["actionCost"][a]<=b and all(m["good"][w][a] for w in ws) for a in allowed):return True
        if d==0:return False
        for q,c in enumerate(m["probeCost"]):
            if c>b:continue
            branches=[]
            for bit,key in ((1,"nextFalse"),(2,"nextTrue")):
                nexts=tuple(sorted({m[key][q][w] for w in ws if m["sense"][q][w]&bit}))
                branches.append(win(nexts,d-1,b-c))
            if all(branches):return True
        return False
    return win(tuple(sorted(subset)),depth,budget)
def classic_verdict(m):
    b=min(m["budget"],m["reserve"]-m["debt"]-1)
    upper=m["upperWorld"]
    if classic(m,upper,tuple(m["mustActions"]),m["depth"],b):
        if any(m["actionCost"][a]<=b and all(m["good"][w][a] for w in upper)
               for a in m["mustActions"]):return "ACT"
        for q,c in enumerate(m["probeCost"]):
            if c>b:continue
            successors=[sorted({m[key][q][w] for w in upper if m["sense"][q][w]&bit})
                for bit,key in ((1,"nextFalse"),(2,"nextTrue"))]
            if all(classic(m,nxt,tuple(m["mustActions"]),m["depth"]-1,b-c) for nxt in successors):
                return m["probeKinds"][q]
        raise AssertionError("No winning first step")
    return "EPISTEMIC_OPEN" if classic(m,m["lowerWorld"],tuple(m["mayActions"]),m["depth"],b) else "REFUSE_ROBUST"
verified={}
for case,(m,expected) in specimens.items():
    conventional=classic_verdict(m)
    assert conventional==expected,(case,"CLASSICAL",conventional,expected)
    result=decide(m,OUT/case)
    assert result["verdict"]==conventional,(case,"C3",result)
    assert replay(OUT/case),("REPLAY_ERROR",case)
    verified[case]=dict(verdict=result["verdict"],same_as_classic=True,
        replay_lean=True,source_sha256=result["source_sha256"],
        contract_sha256=result["contract_sha256"],plan=result["plan"])
    print("BIKE_FUTURE_C3_LEAN",case,result["verdict"],flush=True)
report=dict(source_url=SOURCE,source_zip_sha256=shasum,
    source="UCI Bike Sharing Dataset; Fanaee-T & Gama, 2013; doi:10.24432/C5W894",
    original_hourly_rows=len(rows),available_dates=len(days),window_complete_dates=len(windows),
    training_days=len(train),holdout_days=len(hold),
    training_last_day=train[-1][0],holdout_first_day=hold[0][0],
    locked_thresholds=dict(morning_rentals_median=T0,afternoon_rentals_median=T1,
                           evening_rentals_q75=T2),
    training_signature_support={str(x):dict(cc) for x,cc in training.items()},
    empirical=dict(evidence),train_pure_low_holdout_violations=examples,
    c3_original_finite_certificates=verified,
    comparison="Greedy ignoring future vs exact classical AND/OR knowing same finite future contracts vs frozen INSACERMO C3 with Lean",
    theoretical_warning="Complete classical AND/OR with identical contract agrees with C3 by design. Certified planning, not novel predictive physics.",
    important_limits=[
        "Actual bike station inventory/rebalancing costs were NOT observed. All reserves and actions are explicitly invented abstractions.",
        "The rental figures are real; the future 'need' is defined by a threshold learned only on past days.",
        "Safety of PRESERVE in finite model is tautological: it follows from the declared abstract capacity, not empirical proof about operations.",
        "The perfect future sensor is hypothetical, NOT observed available hardware.",
        "Historical chronological holdout, not newly collected prospective observations.",
        "Only 4 declared abstract worlds in certified contracts; Lean did not verify all individual rides/days.",
        "The train-derived policy can fail under dataset shift, reported honestly, without universal claim.",
        "An equivalent classical shield or fully-informed planner makes the same decisions.",
        "No uniqueness or scientific priority proven by this single dataset."])
(OUT/"FULL_REPORT.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
print("BIKESHARE_FUTURE_AUDIT_OK",json.dumps(
    {k:report[k] for k in ["original_hourly_rows","window_complete_dates","training_days",
       "holdout_days","locked_thresholds","empirical"]},sort_keys=True),flush=True)
