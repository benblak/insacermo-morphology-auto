#!/usr/bin/env python3
"""External exact optimizer + FROZEN C3 Lean receipts, on archival UCI Bike.
No modified core, source real; capacity/repairs/costs are EXPLICITLY SYNTHETIC.
Data already examined in older pilots, so this is NOT a new blind test.
Question: can paying for information preserve the future and maximize net
present opportunities? Does optimality transfer under chronological shift?

UNIVERSE: morning-dependent synthetic resource capacity 2 or 3; unknown
future evening obligation 1 or 2; robustly safe FAST requires capacity>=3.
Actions PRESERVE (0 reward); FAST (20 gross); REPAIR+FAST (cost 10);
observation of resource capacity (cost 2).
All scores are abstract integer utility units, not dollars/euros.
Complete strategy grammar: no-probe {PRESERVE,REPAIR_FAST} or
capacity-probe then {PRESERVE,REPAIR_FAST} for cap2 and
{PRESERVE,FAST,REPAIR_FAST} for cap3. => exactly 8 robust deterministic
policy skeletons, independently enumerated and checked by Lean.
We deliberately disallow mixed randomization and unlimited actions.
"""
import csv,io,zipfile,urllib.request,json,hashlib,sys
from collections import Counter,defaultdict
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from insacermo_one_engine import decide,replay
OUT=ROOT/"audit/exact_information_price_20261019/evidence";OUT.mkdir(parents=True,exist_ok=True)
URL="https://archive.ics.uci.edu/static/public/275/bike+sharing+dataset.zip"
with urllib.request.urlopen(URL,timeout=90) as u:source=u.read()
digest=hashlib.sha256(source).hexdigest()
with zipfile.ZipFile(io.BytesIO(source)) as z:
    files=[f for f in z.namelist() if f.endswith("hour.csv")]
    assert len(files)==1
    rows=list(csv.DictReader(io.TextIOWrapper(z.open(files[0]),encoding="utf-8-sig")))
assert len(rows)==17379
hours=defaultdict(dict)
for r in rows:
    day=r["dteday"];hr=int(r["hr"]);cnt=int(r["cnt"])
    assert cnt>=0 and cnt==int(r["casual"])+int(r["registered"])
    assert hr not in hours[day]
    hours[day][hr]=cnt
daily=[]
for date,z in sorted(hours.items()):
    if all(all(hr in z for hr in range(st,st+6)) for st in (6,12,18)):
        daily.append((date,tuple(sum(z[hr] for hr in range(st,st+6)) for st in (6,12,18))))
assert len(daily)==723
train=daily[:int(len(daily)*.75)]
test=daily[int(len(daily)*.75):]
assert len(train)==542 and len(test)==181 and train[-1][0]<test[0][0]
def median(values):
    s=sorted(values);n=len(s)
    return (s[n//2-1]+s[n//2])/2 if n%2==0 else s[n//2]
threshold=median([z[0] for _,z in train])
# Synthetic capacity derived from real morning demand; this is not
# physical bicycle availability measured in the UCI source.
def capacity(row):return 3 if row[0]<=threshold else 2
def summarize(v):
    cc=Counter(capacity(c) for _,c in v)
    assert cc[2]+cc[3]==len(v)
    return dict(days=len(v),cap2=cc[2],cap3=cc[3])
tr=summarize(train);te=summarize(test)
assert tr["cap3"]>0 and te["cap3"]>0
REWARD=20;REPAIR_COST=10;SENSE_COST=2
# Every allowed policy is robustly safe for both future demand levels
# (requires reserve 1 or 2). 8 exact skeletons.
def policies():
    ans=[
      dict(name="NO_OBSERVE_PRESERVE",observe=False,low="PRESERVE",high="PRESERVE"),
      dict(name="NO_OBSERVE_REPAIR_FAST",observe=False,low="REPAIR_FAST",high="REPAIR_FAST")
    ]
    for low in ("PRESERVE","REPAIR_FAST"):
        for high in ("PRESERVE","FAST","REPAIR_FAST"):
            ans.append(dict(name="OBSERVE_"+low+"__"+high,observe=True,low=low,high=high))
    assert len(ans)==8
    return ans
def safe(cap,decision,evening_need):
    after=cap
    if decision=="FAST":after-=1
    if decision=="REPAIR_FAST":after=max(after,3)-1
    assert decision in ("FAST","PRESERVE","REPAIR_FAST")
    return after>=evening_need
def score_policy(p,subset):
    utility=0;fast_count=repair_count=obs_count=0
    for date,c in subset:
        cap=capacity(c)
        action=p["low" if cap==2 else "high"]
        assert all(safe(cap,action,need) for need in (1,2)),(p,cap,action)
        score=(REWARD if action in ("FAST","REPAIR_FAST") else 0)
        score-=REPAIR_COST if action=="REPAIR_FAST" else 0
        score-=SENSE_COST if p["observe"] else 0
        utility+=score
        fast_count+=action in ("FAST","REPAIR_FAST")
        repair_count+=action=="REPAIR_FAST"
        obs_count+=p["observe"]
    return dict(total_utility=utility,fast=int(fast_count),repairs=int(repair_count),
                observations=int(obs_count),robust_violations=0)
p_list=policies()
train_results={p["name"]:score_policy(p,train) for p in p_list}
test_results={p["name"]:score_policy(p,test) for p in p_list}
rank=lambda d: sorted(d,key=lambda k:(-d[k]["total_utility"],k))
train_choice=rank(train_results)[0]
test_oracle=rank(test_results)[0]
assert train_choice=="OBSERVE_REPAIR_FAST__FAST",(train_choice,tr,train_results)
assert test_oracle=="NO_OBSERVE_REPAIR_FAST",(test_oracle,te,test_results)
# Train optimum comes from exact enumeration only; original C3 has neither
# expected-value prior nor preference objective in its current input interface.
# An independent closed-form test: observation worthwhile iff
# SENSE_COST*N < REPAIR_COST * count(capacity=3).
assert SENSE_COST*tr["days"]<REPAIR_COST*tr["cap3"]
assert SENSE_COST*te["days"]>REPAIR_COST*te["cap3"]
def exact_scores(counts):
    L,H=counts["cap2"],counts["cap3"]
    return [
       0,10*(L+H),
       -2*(L+H),10*H-2*(L+H),20*H-2*(L+H),
       10*L-2*(L+H),10*(L+H)-2*(L+H),
       10*L+20*H-2*(L+H)
    ]
for counts,result in ((tr,train_results),(te,test_results)):
    assert sorted(x["total_utility"] for x in result.values())==sorted(exact_scores(counts))
# C3 four-world abstraction. The true evening outcome is still unknown.
# fast action succeeds after capacity reaches 3 under either future outcome.
worlds=[(2,1),(2,2),(3,1),(3,2)]
def base_model(include_preserve=False,budget=12,debt=0):
    good=[[cap>=need+1] for cap,need in worlds]
    if include_preserve:
        good=[g+[True] for g in good]
    return dict(worldCount=4,actionCount=2 if include_preserve else 1,
      probeCount=2,good=good,
      sense=[[1,1,2,2],[2,2,2,2]],
      nextFalse=[list(range(4)),list(range(4))],
      nextTrue=[list(range(4)),[2,3,2,3]],
      actionCost=[0,0] if include_preserve else [0],
      probeCost=[2,10],probeKinds=["PROBE","REPAIR"],
      lowerWorld=list(range(4)),upperWorld=list(range(4)),
      mustActions=[0,1] if include_preserve else [0],
      mayActions=[0,1] if include_preserve else [0],
      depth=2,budget=budget,reserve=20,debt=debt)
cases={
   "SAFETY_ONLY_FIRST_SAFE_PRESERVE":(base_model(include_preserve=True),"ACT"),
   "FAST_CONTRACT_PROBE_THEN_REPAIR":(base_model(),"PROBE"),
   "FAST_CONTRACT_LOW_BUDGET_DIRECT_REPAIR":(base_model(budget=10),"REPAIR"),
   "FAST_CONTRACT_INSUFFICIENT_BUDGET":(base_model(budget=9),"REFUSE_ROBUST"),
   "FAST_CONTRACT_RESERVE_DEBT_REFUSE":(base_model(debt=11),"REFUSE_ROBUST")
}
def independent_win(m,states,actions,depth,budget):
    from functools import lru_cache
    @lru_cache(None)
    def go(ws,d,b):
        if any(m["actionCost"][a]<=b and all(m["good"][w][a] for w in ws) for a in actions):
            return True
        if not d:return False
        for q,c in enumerate(m["probeCost"]):
            if c>b:continue
            branches=[]
            for bit,key in ((1,"nextFalse"),(2,"nextTrue")):
                dest=tuple(sorted(set(m[key][q][w] for w in ws if m["sense"][q][w]&bit)))
                branches.append(go(dest,d-1,b-c))
            if all(branches):return True
        return False
    return go(tuple(sorted(states)),depth,budget)
def independent_verdict(m):
    b=min(m["budget"],m["reserve"]-m["debt"]-1)
    if independent_win(m,m["upperWorld"],m["mustActions"],m["depth"],b):
        if any(m["actionCost"][a]<=b and all(m["good"][w][a] for w in m["upperWorld"]) for a in m["mustActions"]):
            return "ACT"
        for q,c in enumerate(m["probeCost"]):
            if c>b:continue
            targets=[
                sorted(set(m[k][q][w] for w in m["upperWorld"] if m["sense"][q][w]&bit))
                for bit,k in ((1,"nextFalse"),(2,"nextTrue"))]
            if all(independent_win(m,t,m["mustActions"],m["depth"]-1,b-c) for t in targets):
                return m["probeKinds"][q]
        raise AssertionError("independent winning plan has no root")
    return "EPISTEMIC_OPEN" if independent_win(m,m["lowerWorld"],m["mayActions"],m["depth"],b) else "REFUSE_ROBUST"
certificates={}
for name,(m,exp) in cases.items():
    assert independent_verdict(m)==exp,(name,independent_verdict(m),exp)
    res=decide(m,OUT/name)
    assert res["verdict"]==exp,(name,res)
    assert replay(OUT/name),("LEAN_REPLAY",name)
    if name=="FAST_CONTRACT_PROBE_THEN_REPAIR":
        assert res["plan"]["probe"]==0
        assert res["plan"]["no"]["probe"]==1
        assert res["plan"]["yes"]["act"]==0
    certificates[name]=dict(verdict=exp,lean_replayed=True,
        contract_sha256=res["contract_sha256"],plan=res["plan"])
    print("EXACT_PRICE_ORIGINAL_C3_LEAN",name,exp,flush=True)
# Generate an independently executable Lean arithmetic proof verifying the
# COMPLETE enumeration of 8 safe policy scores at the actual train/test counts.
# This does not assert that Lean proved the provenance or representativeness.
lean_src=f'''import Init
namespace InsacermoInformationPriceAudit
def probeScore (low high lowReward highReward : Int) : Int :=
  low * lowReward + high * highReward - 2 * (low+high)
def allScores (low high : Int) : List Int :=
  [0, 10*(low+high),
   probeScore low high 0 0,
   probeScore low high 0 10,
   probeScore low high 0 20,
   probeScore low high 10 0,
   probeScore low high 10 10,
   probeScore low high 10 20]
def trainLow : Int := {tr["cap2"]}
def trainHigh : Int := {tr["cap3"]}
def testLow : Int := {te["cap2"]}
def testHigh : Int := {te["cap3"]}
def trainCandidate : Int := probeScore trainLow trainHigh 10 20
def testCandidate : Int := 10*(testLow+testHigh)
theorem all_eight_train_scores_below_chosen :
  (allScores trainLow trainHigh).all (fun s => decide (s ≤ trainCandidate)) = true := by decide
theorem all_eight_test_scores_below_chosen :
  (allScores testLow testHigh).all (fun s => decide (s ≤ testCandidate)) = true := by decide
theorem training_observation_worth_cost :
  2 * (trainLow+trainHigh) < 10*trainHigh := by decide
theorem test_observation_cost_exceeds_saving :
  2 * (testLow+testHigh) > 10*testHigh := by decide
end InsacermoInformationPriceAudit
'''
(OUT/"ExactInformationPrice.lean").write_text(lean_src)
import subprocess,os
env=dict(os.environ,LEAN_PATH=".:lean")
proof=subprocess.run(["lean",str((OUT/"ExactInformationPrice.lean").resolve())],
    cwd=ROOT,capture_output=True,text=True,env=env,timeout=120)
assert proof.returncode==0,(proof.stdout+proof.stderr)[-3000:]
assert "sorryAx" not in proof.stdout
print("LEAN_EXHAUSTIVE_8_POLICY_PRICE_OPTIMUM_OK",
    "train_best",train_choice,"test_best",test_oracle,flush=True)
report=dict(status="EXACT_FINITE_OPTIMALITY_AUDIT_PASS",
    source_url=URL,source_sha256=digest,hourly_rows=len(rows),complete_days=len(daily),
    train_end=train[-1][0],test_start=test[0][0],
    training=tr,testing=te,train_morning_median_threshold=threshold,
    utility_scale=dict(reward_fast=REWARD,repair_cost=REPAIR_COST,
        observation_cost=SENSE_COST,units="fictitious utility points"),
    robust_policies_enumerated=8,train_best=train_choice,test_best_ex_post=test_oracle,
    train_policies=train_results,test_policies=test_results,
    chosen_on_training_test_performance=test_results[train_choice],
    full_information_ex_post_test_best=test_results[test_oracle],
    information_use_threshold="Observation preferred iff cost_probe < P(cap3)*cost_repair",
    c3_original_certificates=certificates,
    independent_lean_8_policy_optimality=True,
    conclusions=[
     "Frozen original C3's safety-only case returns immediate ACT/PRESERVE",
     "When future guaranteed FAST is declared, C3 returns PROBE with a low-capacity REPAIR branch",
     "At a smaller budget original C3 picks REPAIR instead of PROBE",
     "Exact external optimizer over eight robust policy skeletons picks capacity observation on historical training",
     "Chronological holdout distribution shift reverses net-optimal policy to unconditional repair",
     "Classical full-horizon AND/OR given the same model obtains identical feasible decisions",
     "This is a scope-limited negative control on economic transfer, not a scientific novelty claim"],
    limitations=[
     "Original bike dataset is archival and the test period has been previously seen in earlier experiments",
     "Capacities, rewards, repair availability and costs are entirely hypothetical",
     "The two possible future requirements are a constructed robustness bound, not an independently estimated physical bound",
     "An actual observation of capacity may be cheap/free or expensive; utility units do not measure real lab or operations expenditure",
     "Eight-policy exhaustive proof applies only to the declared finite deterministic grammar, no adaptive multi-day real-world constraints",
     "The generated Lean optimizer theorem checks fixed integer scores, not data provenance, full Python code or a universal theorem",
     "Original C3 certifies plans under finite contracts; it does not infer reward optimality without an external objective",
     "Distribution shift explains payoff reversal under given synthetic costs, not a discovered physical law",
     "No claim of superiority to classical robust optimisation with equal inputs/objectives"])
(OUT/"RESULT.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
print("EXACT_PRICE_AUDIT_RESULT",json.dumps({
 "source_sha256":digest,"train":tr,"test":te,"train_best":train_choice,
 "test_ex_post_best":test_oracle,"on_test_train_plan":test_results[train_choice],
 "on_test_repair_plan":test_results[test_oracle],"lean_c3_certificates":len(certificates),
 "lean_exact_policy_proof":True},sort_keys=True),flush=True)
