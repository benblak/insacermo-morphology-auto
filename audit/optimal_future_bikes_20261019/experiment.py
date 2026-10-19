#!/usr/bin/env python3
"""INSACERMO disclosure audit: preserving enough of the future to still act.
Source = real UCI bike rentals. Capacity, actions and safety are a SYNTHETIC
operational scenario; NO bike stations, physical repairs, batteries or actual
resource inventories are present in the source data.

Preserve original C3, Lean, and MAX TOTAL. C3 tests FINITE DECLARED MODELS.
Core question: does original C3 optimize safe action throughput on its own?
Explicit opposing policies: MYOPIC FAST, ALWAYS PRESERVE, FULL CLASSICAL
CONTINGENT (safety + reward), ORIGINAL C3 feasibility alone, C3 with
externally authored throughput obligation. Same worlds/costs in full comparator.

Warning: bike holdout has been inspected in earlier experiments. Results
are exploratory retrospective comparisons, NOT a new prospectively blind test.
"""
import csv,hashlib,io,json,statistics,sys,urllib.request,zipfile
from collections import Counter,defaultdict
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from insacermo_one_engine import decide,replay
OUT=ROOT/"audit/optimal_future_bikes_20261019/evidence"
OUT.mkdir(parents=True,exist_ok=True)
URL="https://archive.ics.uci.edu/static/public/275/bike+sharing+dataset.zip"
with urllib.request.urlopen(URL,timeout=90) as h:source=h.read()
digest=hashlib.sha256(source).hexdigest()
with zipfile.ZipFile(io.BytesIO(source)) as z:
    names=[p for p in z.namelist() if p.endswith("hour.csv")]
    assert len(names)==1
    records=list(csv.DictReader(io.TextIOWrapper(z.open(names[0]),encoding="utf-8-sig")))
assert len(records)==17379
readings=defaultdict(dict)
for r in records:
    date=r["dteday"];hour=int(r["hr"]);val=int(r["cnt"])
    assert val>=0 and val==int(r["registered"])+int(r["casual"]) and hour not in readings[date]
    readings[date][hour]=val
daily=[]
for date,rr in sorted(readings.items()):
    if all(all(h in rr for h in range(start,start+6)) for start in (6,12,18)):
        daily.append((date,tuple(sum(rr[h] for h in range(start,start+6)) for start in (6,12,18))))
assert len(daily)==723,len(daily)
index=int(len(daily)*0.75)
train=daily[:index];hold=daily[index:]
assert len(train)==542 and len(hold)==181
def quantile(v,q):
    v=sorted(v);ix=(len(v)-1)*q;lo=int(ix);hi=min(lo+1,len(v)-1)
    return v[lo]*(1-(ix-lo))+v[hi]*(ix-lo)
morning_med=quantile([c[0] for _,c in train],0.5)
evening_p75=quantile([c[2] for _,c in train],0.75)
# Synthetic operational contract. Morning demand observed by decision time:
# lower morning demand => assume a *hypothetical* 3-unit endowment,
# higher => assume 2 units. This is NOT a measured real bicycle inventory.
# Evening requirement is 1 or 2 invented units according to real rentals.
def endowment(c):return 3 if c[0]<=morning_med else 2
def future_required(c):return 2 if c[2]>evening_p75 else 1
def is_safe(policy,c):
    cap=endowment(c)
    chosen="FAST" if policy=="FAST" or (policy=="OBSERVE_CAPACITY" and cap==3) else "PRESERVE"
    remainder=cap-(1 if chosen=="FAST" else 0)
    return chosen,remainder>=future_required(c)
evals=Counter()
by_capacity={2:Counter(),3:Counter()}
daily_controls=[]
for day,c in hold:
    e=endowment(c);high=int(future_required(c)==2)
    strategies={}
    for name in ("FAST","PRESERVE","OBSERVE_CAPACITY"):
        act,safe=is_safe(name,c)
        strategies[name]=(act,safe)
        evals[name+"_fast"]+=int(act=="FAST")
        evals[name+"_violation"]+=int(not safe)
    evals["high_evening"]+=high
    by_capacity[e]["days"]+=1
    by_capacity[e]["high_evening"]+=high
    daily_controls.append(dict(day=day,endowment=e,evening_high=high,
                               myopic_safe=strategies["FAST"][1],
                               gated_action=strategies["OBSERVE_CAPACITY"][0]))
assert sum(by_capacity[cap]["days"] for cap in (2,3))==len(hold)
assert evals["PRESERVE_violation"]==evals["OBSERVE_CAPACITY_violation"]==0
assert evals["OBSERVE_CAPACITY_fast"]==by_capacity[3]["days"]
assert evals["FAST_violation"]==by_capacity[2]["high_evening"]

# Both branches are robust against unknown event {low,high} because
# the future requirement is bounded by two abstract units.
worlds=[(2,0),(2,1),(3,0),(3,1)]
sense=[[1,1,2,2]] # hypothetical truthful reading of endowment class
good_safety=[[cap-1 >= 1+high,cap >= 1+high] for cap,high in worlds]
good_throughput=[[cap==3,cap==2] for cap,high in worlds]
assert good_safety==[[True,True],[False,True],[True,True],[True,True]]
# NOTE the first row is cap2 + low future: FAST safe but not robust to high.
# External throughput obligation: MUST use available extra safe capacity
# on high-endowment worlds, MUST preserve on low-endowment worlds.
def model(good, *,kind="PROBE",mask=None,budget=1,depth=1,debt=0):
    return dict(worldCount=4,actionCount=2,probeCount=1,
      good=good,sense=[mask or sense[0]],
      nextFalse=[list(range(4))],nextTrue=[list(range(4))],
      actionCost=[0,0],probeCost=[1],probeKinds=[kind],
      lowerWorld=list(range(4)),upperWorld=list(range(4)),
      mustActions=[0,1],mayActions=[0,1],
      depth=depth,budget=budget,reserve=3,debt=debt)
models={
  "SAFETY_ONLY":(model(good_safety),"ACT"),
  "THROUGHPUT_CONTRACT":(model(good_throughput),"PROBE"),
  "THROUGHPUT_WITH_AMBIGUOUS_MEASURE":(
      model(good_throughput,mask=[1,3,2,2]),"REFUSE_ROBUST"),
  "THROUGHPUT_WITH_NO_OBSERVATION_BUDGET":(
      model(good_throughput,depth=0,budget=0),"REFUSE_ROBUST"),
  "THROUGHPUT_WITH_DEBT":(
      model(good_throughput,debt=2),"REFUSE_ROBUST")
}
# Additional model: REPAIR increases endowment 2->3 and enables FAST across
# all future outcomes in the assumed universe. It is a hypothetical action.
repair_model=dict(model([[cap==3,False] for cap,high in worlds],kind="REPAIR",
                         mask=[2,2,2,2]),
    nextTrue=[[2,3,2,3]])
# Need inactive "PRESERVE" action to force repair? action1 universally False.
models["HYPOTHETICAL_REPAIR_TO_ENABLE_FAST"]=(repair_model,"REPAIR")

# Independently written classical strong contingency winner. Same finite
# planning grammar, costs, transition and worlds (not just greedy heuristic).
from functools import lru_cache
def reference(m,X,allowed,depth,budget):
    @lru_cache(None)
    def rec(states,d,b):
        for a in allowed:
            if m["actionCost"][a]<=b and all(m["good"][w][a] for w in states):
                return ("ACT",a)
        if d==0:return None
        for q,cost in enumerate(m["probeCost"]):
            if cost>b:continue
            children=[]
            for bit,nxt in ((1,"nextFalse"),(2,"nextTrue")):
                targets=tuple(sorted({m[nxt][q][w] for w in states if m["sense"][q][w]&bit}))
                children.append(rec(targets,d-1,b-cost))
            if all(z is not None for z in children):
                return (m["probeKinds"][q],q)
        return None
    return rec(tuple(sorted(set(X))),depth,budget)
def reference_verdict(m):
    b=min(m["budget"],m["reserve"]-m["debt"]-1)
    r=reference(m,m["upperWorld"],m["mustActions"],m["depth"],b)
    if r is not None:return r[0]
    return ("EPISTEMIC_OPEN" if
        reference(m,m["lowerWorld"],m["mayActions"],m["depth"],b) is not None
        else "REFUSE_ROBUST")
verified={}
for name,(m,expected) in models.items():
    base=reference_verdict(m)
    assert base==expected,(name,base,expected)
    result=decide(m,OUT/name)
    assert result["verdict"]==expected,(name,result)
    assert replay(OUT/name),name
    verified[name]=dict(verdict=result["verdict"],
      same_as_classical=True,lean_replay=True,
      contract_sha256=result["contract_sha256"],
      plan=result["plan"])
    print("OPTIMAL_FUTURE_C3_LEAN",name,expected,flush=True)

# An independently enumerated optimizer over the AVAILABLE three policies.
# Safety is absolute over declared 4 worlds. Utility = number of permitted FAST
# on observed holdout days; reading cost is an ABSTRACT parameter only.
reward_per_fast=1.
read_cost=.1
def policy_robust(name):
    for cap,high in worlds:
        choice="FAST" if name=="FAST" or (name=="OBSERVE_CAPACITY" and cap==3) else "PRESERVE"
        if cap-int(choice=="FAST")<1+high:return False
    return True
allowed=[p for p in ("FAST","PRESERVE","OBSERVE_CAPACITY") if policy_robust(p)]
assert allowed==["PRESERVE","OBSERVE_CAPACITY"]
utility={
 p:evals[p+"_fast"]*reward_per_fast-(len(hold)*read_cost if p=="OBSERVE_CAPACITY" else 0)
 for p in allowed
}
best=max(allowed,key=lambda p:utility[p])
assert best=="OBSERVE_CAPACITY"
# An informed classical planner with the SAME safety contract and throughput
# objective selects the exact same observation-then-act policy.
report=dict(status="COMPLETED_C3_OPTIMALITY_SCOPE_DIAGNOSIS",
    source=URL,archive_sha256=digest,hourly_readings=len(records),
    complete_days=len(daily),train_days=len(train),holdout_days=len(hold),
    training_end_date=train[-1][0],holdout_start_date=hold[0][0],
    train_frozen_thresholds=dict(morning_median=morning_med,evening_p75=evening_p75),
    synthetic_endowment="capacity=3 if morning <= training morning median; else 2",
    synthetic_future_requirement="1+I(evening rentals > training q75)",
    policy_results=dict(evals),capacity_breakdown={str(k):dict(v) for k,v in by_capacity.items()},
    policies_robust_under_declared_two_future_worlds=allowed,
    utility_contract=dict(reward_per_fast=reward_per_fast,observation_cost=read_cost,
                          expected_or_heldout_score=utility,best=best),
    c3_with_lean=verified,
    key_conclusion="On safety-only input, original frozen C3 returns ACT PRESERVE, not reward-optimal PROBE. The throughput constraint must be encoded to make C3 PROBE. Standard classical AND/OR agrees on all cases.",
    daily_holdout_results=daily_controls,
    limitations=[
      "Observations and demand are real, but resource endowment and actual ability to intervene are entirely hypothetical.",
      "This holdout period was previously examined in the earlier bikeshare pilot: no genuine new blind validation.",
      "Zero robust-policy violations are a tautology from the two-unit synthetic demand ceiling, not evidence of a real-world operating safety guarantee.",
      "The performance contract forcing PROBE was supplied externally, not automatically discovered by C3.",
      "C3 search returns the first feasible safe action, not a maximum-throughput or reward-optimal policy.",
      "The classical full-horizon optimizer can solve the same problem when given the same model and objective.",
      "Utility of FAST=1, PROBE read cost=0.1 are synthetic utility units, not dollars or physical measurement cost.",
      "The 4-world C3 proof does not certify 17,379 rides, nor predictions about tomorrow.",
      "No proof of novel scientific phenomenon, architecture uniqueness or industrial deployment."
    ])
(OUT/"EXPERIMENT.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
print("INSACERMO_FUTURE_NONTRIVIAL_TEST",json.dumps({
  "holdout_days":len(hold),
  "experimental_policies":{p:{"fast":evals[p+"_fast"],"violations":evals[p+"_violation"]} for p in
         ("FAST","PRESERVE","OBSERVE_CAPACITY")},
  "best_robust_policy":best,
  "classical_agrees":True,
  "lean_contracts":len(verified),
  "c3_safety_only":verified["SAFETY_ONLY"]["verdict"],
  "c3_throughput":verified["THROUGHPUT_CONTRACT"]["verdict"]
},sort_keys=True),flush=True)
