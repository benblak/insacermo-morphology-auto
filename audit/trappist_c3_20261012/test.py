#!/usr/bin/env python3
"""TRAPPIST-1: descriptive NASA orbital periods -> declared hypothetical observing policy.

Scientific limits: NASA values are public catalog approximations. Hypothetical probes
perfectly reveal period-class predicates; they are not validated telescope sensors.
This is a research illustration, not an astronomy discovery.
"""
import json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from insacermo_one_engine import decide
PLANETS=[
 ("TRAPPIST-1 b",1.51),("TRAPPIST-1 c",2.42),("TRAPPIST-1 d",4.05),
 ("TRAPPIST-1 e",6.10),("TRAPPIST-1 f",9.21),("TRAPPIST-1 g",12.35),("TRAPPIST-1 h",18.77)
]
# Data source: NASA Exoplanet Archive overview, publicly reported orbital periods:
# https://exoplanetarchive.ipac.caltech.edu/overview/TRAPPIST-1e
# The hypothetical three protocols are only labels for period regimes.
classes=[0 if period<=5 else (1 if period<=10 else 2) for _,period in PLANETS]
good=[[k==a for a in range(3)] for k in classes]
m=dict(worldCount=7,actionCount=3,probeCount=2,good=good,
       # q0 reveals P<=5d; q1 reveals P<=10d. 1=false; 2=true.
       sense=[[2 if period<=5 else 1 for _,period in PLANETS],
              [2 if period<=10 else 1 for _,period in PLANETS]],
       nextFalse=[list(range(7)),list(range(7))],
       nextTrue=[list(range(7)),list(range(7))],
       actionCost=[0,0,0],probeCost=[1,1],
       lowerWorld=list(range(7)),upperWorld=list(range(7)),
       mustActions=[0,1,2],mayActions=[0,1,2],
       probeKinds=["PROBE","PROBE"],depth=2,budget=2,reserve=4,debt=0)
output=ROOT/"audit/trappist_c3_20261012/output"
output.mkdir(parents=True,exist_ok=True)
def check_plan(t, worlds):
    if "act" in t:
        return len(worlds)>0 and all(good[w][t["act"]] for w in worlds)
    q=t["probe"]
    no=[w for w in worlds if m["sense"][q][w]&1]
    yes=[w for w in worlds if m["sense"][q][w]&2]
    return check_plan(t["no"],no) and check_plan(t["yes"],yes)
# Only the first case invokes genuine Lean to avoid restaging extensive old audits.
result=decide(m,output/"original_decision")
assert result["verdict"]=="PROBE" and result["authorized"],result
assert check_plan(result["plan"],list(range(7))),result
# Baseline analytical feasibility (independent exhaustive partitions, not ML)
assert len(set(classes))==3
assert len(set(classes))>2 # one binary query cannot separate all three required actions
rows=[]
for i,(name,period) in enumerate(PLANETS):
    rows.append({"planet":name,"period_days":period,"declared_action":["short","medium","long"][classes[i]]})
(output/"planets_and_actions.json").write_text(json.dumps(rows,indent=2)+"\n")
(output/"declared_contract.json").write_text(json.dumps(m,indent=2)+"\n")
(output/"RESULT.json").write_text(json.dumps({
 "source":"https://exoplanetarchive.ipac.caltech.edu/overview/TRAPPIST-1e",
 "note":"Catalog rounded periods; synthetic mission thresholds, perfect class queries, no telescope hardware model",
 "orbits_days":[x[1] for x in PLANETS],"period_classes":[x["declared_action"] for x in rows],
 "verdict":result["verdict"],"plan":result["plan"],
 "authorized":result["authorized"],"contract_sha256":result["contract_sha256"],
 "lean_source_sha256":result["source_sha256"],
 "two_question_plan_safe_under_declared_model":True,
 "single_binary_question_cannot_separate_three_classes":True},indent=2)+"\n")
print("TRAPPIST_C3_ORIGINAL_LEAN_DECISION_OK",result["verdict"],"7_PLANETS_3_PROTOCOLS_2_QUERY_LEVELS",flush=True)
print("PLAN",json.dumps(result["plan"],sort_keys=True),flush=True)
