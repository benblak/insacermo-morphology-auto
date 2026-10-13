#!/usr/bin/env python3
"""Independent electric-usage time-series challenge for the FROZEN C3 engine.

Source: UCI Individual Household Electric Power Consumption (Sceaux, France).
DOI 10.24432/C58K54. Actual historical meter readings; obligations are
EXPERIMENTALLY DECLARED, not the homeowner's actual decisions.
Protocol PRECOMMITTED in this script, prior to accessing the ZIP:
- timestamp-ordered 75/25 train/test; no random temporal leakage
- per day measurements: average active kW 06-12 (morning), 12-18 (afternoon)
- future event: average active kW 18-24 > training q75
- observations are only morning and afternoon threshold bits (training medians)
- contract worlds: exact quotient of (morning bit, afternoon bit, evening event)
  on training only; at most 8 Boolean states, not 8 physical days
- two mutually exclusive actions, event vs no event; no future data to engine
- compare majority lookup trained only on past, and a selective exact rule
- compare independent strong AND/OR semantics with frozen C3+Lean
- abstract costly third safety action in a SEPARATE contract, not real hardware
- no claim of novelty, future prediction guarantee, or better full information planner.
"""
import io,zipfile,urllib.request,hashlib,json,datetime,statistics,sys
from pathlib import Path
from collections import Counter,defaultdict
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from insacermo_one_engine import decide,replay

OUT=ROOT/"audit/energy_uci_temporal_20261013/evidence";OUT.mkdir(parents=True,exist_ok=True)
URL="https://archive.ics.uci.edu/static/public/235/individual+household+electric+power+consumption.zip"
with urllib.request.urlopen(URL,timeout=100) as q: raw=q.read()
archive_sha=hashlib.sha256(raw).hexdigest()
print("ENERGY_ARCHIVE_SHA256",archive_sha,"BYTES",len(raw),flush=True)
with zipfile.ZipFile(io.BytesIO(raw)) as z:
    files=[n for n in z.namelist() if n.endswith(".txt") and "household" in n.lower()]
    assert len(files)==1,files
    # streaming decoded raw data; account for all rows incl missing
    stream=io.TextIOWrapper(z.open(files[0]),encoding="utf-8-sig")
    header=stream.readline().strip().split(";")
    assert header[:3]==["Date","Time","Global_active_power"],header

    day={};total=0;valid=0;missing=0
    # arbitrary consistent time windows same day, not next-day prediction.
    for line in stream:
        total+=1
        vals=line.rstrip("\r\n").split(";")
        if len(vals)<3 or vals[2] in ("?","", "NA"):
            missing+=1;continue
        try:v=float(vals[2])
        except ValueError:
            missing+=1;continue
        if v<0:continue
        valid+=1
        hour=int(vals[1][:2])
        bucket=0 if 6<=hour<12 else (1 if 12<=hour<18 else (2 if 18<=hour<24 else None))
        if bucket is None:continue
        x=day.setdefault(vals[0],[0.0,0,0.0,0,0.0,0])
        x[bucket*2]+=v;x[bucket*2+1]+=1
print("UCI_SOURCE_READINGS",total,"VALID",valid,"MISSING",missing,flush=True)
pairs=[]
for ds,z in day.items():
    if min(z[1],z[3],z[5])<300:continue
    dt=datetime.datetime.strptime(ds,"%d/%m/%Y").date()
    pairs.append((dt,z[0]/z[1],z[2]/z[3],z[4]/z[5]))
pairs.sort()
assert len(pairs)>1000,len(pairs)
ntrain=int(len(pairs)*0.75)
train=pairs[:ntrain];holdout=pairs[ntrain:]
assert train[-1][0]<holdout[0][0]
def quantile(xs,frac):
    ys=sorted(xs)
    idx=(len(ys)-1)*frac;lo=int(idx);hi=min(lo+1,len(ys)-1)
    return ys[lo]*(1-(idx-lo))+ys[hi]*(idx-lo)
t_morning=quantile([x[1] for x in train],0.50)
t_afternoon=quantile([x[2] for x in train],0.50)
t_evening=quantile([x[3] for x in train],0.75)
def encode(x):
    return (int(x[1]>t_morning),int(x[2]>t_afternoon),int(x[3]>t_evening))
train_state=Counter(encode(x) for x in train)
test_state=Counter(encode(x) for x in holdout)
# The 3 observable/event bits produce max eight QUOTIENT worlds.
worlds=sorted(train_state)
assert len(worlds)<=8
sense=[[2 if v[j] else 1 for v in worlds] for j in (0,1)]
good=[[v[2]==0,v[2]==1] for v in worlds]
n=len(worlds)
model=dict(worldCount=n,actionCount=2,probeCount=2,good=good,sense=sense,
           nextFalse=[list(range(n)) for _ in range(2)],
           nextTrue=[list(range(n)) for _ in range(2)],
           actionCost=[0,0],probeCost=[1,1],lowerWorld=list(range(n)),
           upperWorld=list(range(n)),mustActions=[0,1],mayActions=[0,1],
           probeKinds=["PROBE","PROBE"],depth=2,budget=2,reserve=4,debt=0)
# EPISTEMIC_OPEN: lower hypothesis restricted to a single normal case,
# upper envelope unchanged; lower only is an explicit synthetic envelope.
open_model=dict(model,lowerWorld=[next(i for i,z in enumerate(worlds) if z[2]==0)])
safe_model=dict(model,actionCount=3,good=[row+[True] for row in good],
                actionCost=[0,0,2],mustActions=[0,1,2],mayActions=[0,1,2])

def classic_safe(m,ws,actions,depth,budget):
    for a in actions:
        if m["actionCost"][a]<=budget and all(m["good"][w][a] for w in ws):
            return True
    if depth==0:return False
    for q in range(m["probeCount"]):
        if m["probeCost"][q]>budget:continue
        children=[sorted({m["nextFalse"][q][w] for w in ws if m["sense"][q][w]&1}),
                  sorted({m["nextTrue"][q][w] for w in ws if m["sense"][q][w]&2})]
        if all(classic_safe(m,ss,actions,depth-1,budget-m["probeCost"][q]) for ss in children):
            return True
    return False
def classical_verdict(m):
    b=min(m["budget"],m["reserve"]-m["debt"]-1)
    u=m["upperWorld"];l=m["lowerWorld"]
    has_act=any(m["actionCost"][a]<=b and all(m["good"][w][a] for w in u) for a in m["mustActions"])
    if has_act:return "ACT"
    if classic_safe(m,u,m["mustActions"],m["depth"],b):return "PROBE"
    return "EPISTEMIC_OPEN" if classic_safe(m,l,m["mayActions"],m["depth"],b) else "REFUSE_ROBUST"

certificates={}
for name,m in [("STRICT_ENERGY",model),("OPEN_ENVELOPE",open_model),("COSTLY_SAFETY_ACTION",safe_model)]:
    result=decide(m,OUT/name)
    expected=classical_verdict(m)
    assert result["verdict"]==expected,(name,expected,result)
    assert replay(OUT/name)
    certificates[name]=dict(verdict=result["verdict"],replay_Lean=True,
                            scope="Only training-derived 3-bit quotient worlds",
                            contract_sha256=result["contract_sha256"])
    print("ORIGINAL_C3_LEAN",name,result["verdict"],flush=True)

# Strictly TRAIN-ONLY empirical forecast baselines on future heldout days.
# A "naive" baseline is included for illustration, NOT a fair full-horizon
# controller; an independent full-horizon AND/OR reference is given above.
by_signature=defaultdict(Counter)
for z,count in train_state.items():
    by_signature[z[:2]][z[2]]+=count
lookup={s: (0 if cc[0]>=cc[1] else 1) for s,cc in by_signature.items()}
pure_lookup={s: (0 if cc[1]==0 else 1 if cc[0]==0 else None) for s,cc in by_signature.items()}
res=Counter()
for x in holdout:
    z=encode(x);s=z[:2];correct=z[2]
    naive=lookup.get(s)
    strict=pure_lookup.get(s)
    if naive is None:res["naive_refuse"]+=1
    elif naive==correct:res["naive_correct"]+=1
    else:res["naive_wrong"]+=1
    if strict is None:res["strict_refuse"]+=1
    elif strict==correct:res["strict_correct"]+=1
    else:res["strict_wrong"]+=1
    res["test_event"]+=correct
unseen_signatures=[str(k) for k in test_state if k not in train_state]
out=dict(dataset="UCI Individual Household Electric Power Consumption, Sceaux",
    doi="10.24432/C58K54",url=URL,archive_sha256=archive_sha,
    record_count=total,valid_count=valid,missing_count=missing,
    daily_complete=len(pairs),train_days=len(train),holdout_days=len(holdout),
    train_last_day=str(train[-1][0]),holdout_first_day=str(holdout[0][0]),
    train_only_thresholds_kw=dict(morning_median=t_morning,afternoon_median=t_afternoon,
                                  evening_75p=t_evening),
    world_count=n,train_world_counts={str(k):v for k,v in train_state.items()},
    holdout_world_counts={str(k):v for k,v in test_state.items()},
    test_worlds_not_in_train=unseen_signatures,
    holdout_evaluation=dict(res),
    c3_lean=certificates,
    statuses=["RETROSPECTIVE_TEMPORAL_HOLDOUT","SYNTHETIC_OPERATIONAL_CONTRACT"],
    limits=["The physical measurements are real, but alert actions and reserve costs are synthetic",
       "The holdout is chronologically withheld FROM THRESHOLD CHOICE, but the dataset is historical and public",
       "Classical contingent planning with full future constraints and same inputs yields same verdict",
       "C3 Lean proof proves only encoded training quotient, not real external validity",
       "These data do not establish a new physical law or scientific originality of the architecture",
       "Real battery hardware, reserve price, intervention, causal effects, etc. are not modeled",
       "All performance denominators explicitly count refusals and errors"])
(OUT/"REPORT.json").write_text(json.dumps(out,indent=2,ensure_ascii=False)+"\n")
print("ENERGY_TEMPORAL_HOLDOUT_COMPLETED",json.dumps(
 {k:out[k] for k in ("record_count","daily_complete","train_days","holdout_days",
 "world_count","train_only_thresholds_kw","test_worlds_not_in_train","holdout_evaluation",
 "c3_lean")},ensure_ascii=False),flush=True)
