#!/usr/bin/env python3
"""Method comparison: C3 original vs independently written AND/OR strong planner.

Same FINITE declared model, action availability, no/yes sensor outcomes,
transition and probe/action cost, max depth, budget, strict reserve/debt.
Original kernel/Lean untouched. First-party baseline is a REFERENCE
IMPLEMENTATION of standard contingent AND/OR planning, NOT an external
third-party planning system. No claim of runtime speedup or novelty from
semantic equivalence. 200 deterministic randomly generated finite contracts,
seven curated witness contracts with real C3/Lean full replay.
"""
import json,random,sys,statistics,time
from pathlib import Path
from functools import lru_cache
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from insacermo_one_engine import decide,replay,solve as c3_solve

OUT=Path(__file__).resolve().parent/"evidence"
OUT.mkdir(parents=True,exist_ok=True)

# A separately written classical AND/OR backward reachability solver:
# V_d^b(B)= [exists one universally good allowed terminal action] OR
#           [exists affordable probe with both observation successors winning].
# This is the standard strong contingent planning recurrence.
def classical_winning(m,worlds,actions,d,b):
    @lru_cache(None)
    def win(B,depth,budget):
        terminal=any(m["actionCost"][a]<=budget and all(m["good"][w][a] for w in B) for a in actions)
        if terminal:return True
        if depth<=0:return False
        for q,cost in enumerate(m["probeCost"]):
            if cost>budget:continue
            successor=[]
            for observed_bit,next_key in ((1,"nextFalse"),(2,"nextTrue")):
                ss=set()
                for w in B:
                    if m["sense"][q][w] & observed_bit:
                        ss.add(m[next_key][q][w])
                successor.append(tuple(sorted(ss)))
            if all(win(x,depth-1,budget-cost) for x in successor):
                return True
        return False
    return win(tuple(sorted(set(worlds))),d,b)
def classical_verdict(m):
    allowed_budget=min(m["budget"],m["reserve"]-m["debt"]-1)
    if classical_winning(m,m["upperWorld"],tuple(m["mustActions"]),m["depth"],allowed_budget):
        has_now=any(m["actionCost"][a]<=allowed_budget and
                all(m["good"][w][a] for w in m["upperWorld"]) for a in m["mustActions"])
        if has_now:return "ACT"
        # Priority among available cost-feasible declared probes consistent
        # with original C3: first root query with winning branches.
        for q,cost in enumerate(m["probeCost"]):
            if cost>allowed_budget:continue
            parts=[]
            for bit,next_key in ((1,"nextFalse"),(2,"nextTrue")):
                dest=sorted({m[next_key][q][w] for w in m["upperWorld"] if m["sense"][q][w]&bit})
                parts.append(classical_winning(m,dest,tuple(m["mustActions"]),m["depth"]-1,allowed_budget-cost))
            if all(parts):return m["probeKinds"][q]
        raise AssertionError("Strong planner says reachable but no root move")
    if classical_winning(m,m["lowerWorld"],tuple(m["mayActions"]),m["depth"],allowed_budget):
        return "EPISTEMIC_OPEN"
    return "REFUSE_ROBUST"

def basic_model(W=8,A=2,mask=None,probe_kind="PROBE",depth=1,budget=1):
    # Record correspondence: abstract glass laboratory eight-pane contract
    # 4 same-source type A, four type B, order fixed; no claim of a new
    # extraction from data here. Authentic source-to-model conversion is in
    # separately audited GitHub run 38355645225.
    if mask is None:mask=[1,1,1,1,2,2,2,2]
    return dict(worldCount=W,actionCount=A,probeCount=1,
       good=[[w<4,w>=4] for w in range(W)],
       sense=[mask],
       nextFalse=[list(range(W))],nextTrue=[list(range(W))],
       actionCost=[0,0],probeCost=[1],
       lowerWorld=list(range(W)),upperWorld=list(range(W)),
       mustActions=[0,1],mayActions=[0,1],
       probeKinds=[probe_kind],depth=depth,budget=budget,reserve=3,debt=0)

glass=basic_model()
bad=basic_model(depth=0,budget=0)
op=basic_model(depth=0,budget=0);op["lowerWorld"]=[0,1,2,3]
act=basic_model(depth=0,budget=0);act["lowerWorld"]=act["upperWorld"]=[0,1,2,3]
noisy=basic_model(mask=[3,1,1,1,2,2,2,2])
# Repair must actually transform a world (not disguise a probe).
repair=dict(worldCount=2,actionCount=1,probeCount=1,
  good=[[True],[False]],sense=[[1,2]],
  nextFalse=[[0,1]],nextTrue=[[0,0]],
  actionCost=[0],probeCost=[1],
  lowerWorld=[0,1],upperWorld=[0,1],
  mustActions=[0],mayActions=[0],probeKinds=["REPAIR"],
  depth=1,budget=1,reserve=3,debt=0)
# Enforced reserve/debt: probe costs >= 1 but effective budget becomes zero.
debt=basic_model();debt["reserve"]=3;debt["debt"]=2
fixtures={"glass_PROBE":glass,"no_probe_REFUSE":bad,
          "epistemic_OPEN":op,"known_ACT":act,
          "noisy_REFUSE":noisy,"repair_REPAIR":repair,
          "reserve_REFUSE":debt}
for k,m in fixtures.items():
    assert classical_verdict(m)=={
       "glass_PROBE":"PROBE","no_probe_REFUSE":"REFUSE_ROBUST",
       "epistemic_OPEN":"EPISTEMIC_OPEN","known_ACT":"ACT",
       "noisy_REFUSE":"REFUSE_ROBUST","repair_REPAIR":"REPAIR",
       "reserve_REFUSE":"REFUSE_ROBUST"}[k],(k,classical_verdict(m))

def make_random(rng):
    W=rng.randint(2,6);A=rng.randint(1,4);Q=rng.randint(1,3)
    good=[[rng.random()<rng.uniform(.3,.8) for _ in range(A)] for _ in range(W)]
    sense=[[rng.choice((1,2,3)) for _ in range(W)] for _ in range(Q)]
    nfalse=[list(range(W)) for _ in range(Q)]
    ntrue=[list(range(W)) for _ in range(Q)]
    for q in range(Q):
        for w in range(W):
            if rng.random()<.22:nfalse[q][w]=rng.randrange(W)
            if rng.random()<.22:ntrue[q][w]=rng.randrange(W)
    kinds=[]
    for q in range(Q):
        actual=any(((sense[q][w]&1) and nfalse[q][w]!=w) or
                   ((sense[q][w]&2) and ntrue[q][w]!=w)
                   for w in range(W))
        kinds.append("REPAIR" if actual and rng.random()<.25 else "PROBE")
    upper=sorted(w for w in range(W) if rng.random()<.83)
    if not upper:upper=[rng.randrange(W)]
    lower=sorted(w for w in upper if rng.random()<.7)
    if not lower:lower=[rng.choice(upper)]
    may=sorted(a for a in range(A) if rng.random()<.82)
    must=sorted(a for a in may if rng.random()<.80)
    dep=rng.randint(0,3);reserve=rng.randint(dep+1,7)
    budget=rng.randint(0,4)
    return dict(worldCount=W,actionCount=A,probeCount=Q,
      good=good,sense=sense,nextFalse=nfalse,nextTrue=ntrue,
      actionCost=[rng.randint(0,2) for _ in range(A)],
      probeCost=[rng.randint(1,2) for _ in range(Q)],
      lowerWorld=lower,upperWorld=upper,mustActions=must,mayActions=may,
      probeKinds=kinds,depth=rng.randint(0,3),
      budget=budget,reserve=reserve,debt=dep)
rng=random.Random(20261013)
random_models=[make_random(rng) for _ in range(200)]
verdict_counts={}
for i,m in enumerate(random_models):
    b=min(m["budget"],m["reserve"]-m["debt"]-1)
    must=c3_solve(m,m["upperWorld"],m["mustActions"],m["depth"],b)
    may=c3_solve(m,m["lowerWorld"],m["mayActions"],m["depth"],b)
    candidate=("ACT" if "act" in must else m["probeKinds"][must["probe"]]) if must is not None else ("EPISTEMIC_OPEN" if may is not None else "REFUSE_ROBUST")
    reference=classical_verdict(m)
    assert reference==candidate,(i,reference,candidate,m)
    verdict_counts[reference]=verdict_counts.get(reference,0)+1
print("AND_OR_BASELINE_200_MODELS_MATCH_ORIGINAL_C3_SOLVER",json.dumps(verdict_counts,sort_keys=True),flush=True)

# Compare *complete original Lean-gated interface* for seven preset inputs
# against the independent classical planner, using exactly same finite model.
cases={}
for name,m in fixtures.items():
    t0=time.perf_counter()
    conventional=classical_verdict(m)
    classical_ms=(time.perf_counter()-t0)*1000
    t0=time.perf_counter()
    certified=decide(m,OUT/name)
    c3_ms=(time.perf_counter()-t0)*1000
    assert certified["verdict"]==conventional,(name,conventional,certified)
    assert replay(OUT/name),(name,"ORIGINAL_LEAN_REPLAY_FAILED")
    cases[name]=dict(baseline=conventional,insacermo=certified["verdict"],
        baseline_ms=classical_ms,c3_with_lean_ms=c3_ms,
        replay_accepted=True,certified_contract_sha256=certified["contract_sha256"])
    print("REAL_C3_LEAN_CLASSICAL_BASELINE_AGREE",name,conventional,
        "baseline_ms",round(classical_ms,4),"c3_lean_ms",round(c3_ms,4),flush=True)
report=dict(status="ALL_CONTROLS_PASS",
    comparison="Independent reference dynamic AND/OR strong contingent planner vs frozen finite INSACERMO C3",
    semantic_equivalence_evidence="200 random finite compatible contracts plus 7 genuine Lean-gated contracts",
    random_contracts=200,verdict_counts=verdict_counts,
    curated_cases=cases,lean_receipts=7,
    cautions=[
      "AND/OR baseline is independently written for THIS AUDIT, not a third-party optimized planner",
      "Same finite decision problem and same declared transitions; no advantage in solution power expected",
      "Timing includes Lean compilation for C3 and does not for baseline; the result is an end-to-end latency comparison, not search algorithm speed alone",
      "No claim of speedup, novelty, universality, or correctness under unspecified laws",
      "The eight-pane baseline fixture is a hand-transcribed abstraction from previously authenticated real-glass contract, not data independently parsed in this audit",
      "No nonmonotone or continuous models; max depth here 3, worldCount<=8 and probes<=3",
      "Explicit physical source authenticity, external test validity, future preservation, and ability to scale are outside this reference baseline"
    ])
(OUT/"COMPARISON.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
print("FAIR_BASELINE_AUDIT_COMPLETE",json.dumps({"random_contracts":200,"lean_certificates":7,
"verdicts":verdict_counts,"one_example":cases["glass_PROBE"]}),flush=True)
