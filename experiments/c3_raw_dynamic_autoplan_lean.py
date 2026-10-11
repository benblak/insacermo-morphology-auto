#!/usr/bin/env python3
"""INSACERMO: raw finite dynamic contract -> real C3 policy tree -> Lean proof.

No ML, no oracle, no supplied policy. Finite exact enumeration of recipe
numerators and declared probes; transformations can CREATE future capability.
One stable Lean kernel validates every branch after state transitions.
The third verdict UNKNOWN_BOUNDED is NOT a global mathematical refusal.
"""
from __future__ import annotations
from functools import lru_cache
from pathlib import Path
import json,sys

def require(c):
    W=len(c["future_worlds"]); assert 1<=W<=8
    N=len(c["future_worlds"][0]);assert 1<=N<=6
    assert all(len(x)==N and all(type(v)==bool for v in x) for x in c["future_worlds"])
    M=len(c["b"]);assert 1<=M<=6 and len(c["A"])==M
    assert all(len(row)==N and all(type(x)==int and x>=0 for x in row) for row in c["A"])
    assert all(type(b)==int and b>=0 for b in c["b"])
    assert c["annual_limit"]==40 and c["annual_days"]==365 and c["scale"]==10
    initial=c["initial"];assert initial and all(type(w)==int and 0<=w<W for w in initial)
    probes=c["probes"]; assert len(probes)<=4
    O=c["outcomes"];assert 2<=O<=3
    for p in probes:
        assert type(p["price"])==int and p["price"]>=0
        assert len(p["observation"])==W and all(type(o)==int and 0<=o<O for o in p["observation"])
        assert len(p["transition"])==O and all(len(row)==W for row in p["transition"])
        assert all(type(t)==int and 0<=t<W for row in p["transition"] for t in row)
    for k in ["depth","probe_budget","rho","debt","denominator","max_units"]:
        assert type(c[k])==int and c[k]>=0
    assert c["denominator"]>0 and c["denominator"]<=365
    assert c["max_units"]<=40 and c["depth"]<=4
    assert c["debt"]<=c["rho"]

def robust_recipe(c,belief):
    N=len(c["future_worlds"][0]);D=c["denominator"]
    if not belief: return tuple([0]*N)
    usable=[all(c["future_worlds"][w][j] for w in belief) for j in range(N)]
    cap=min(c["max_units"],(40*D)//365)
    x=[0]*N
    def dfs(j,left):
        if j==N:
            if all(sum(c["A"][i][k]*x[k] for k in range(N))>=c["b"][i]*D
                   for i in range(len(c["b"]))):return tuple(x)
            return None
        for amount in range(left+1):
            if amount and not usable[j]:continue
            x[j]=amount
            hit=dfs(j+1,left-amount)
            if hit is not None:return hit
        x[j]=0
        return None
    return dfs(0,cap)

def dual_impossible(c):
    # Sufficient global LP impossibility (independent of any future worlds).
    # Therefore applies to ALL transformations and C3 probe policies.
    M=len(c["b"]);N=len(c["future_worlds"][0])
    for i in range(M):
        E=max([c["A"][i][j] for j in range(N)] or [0])
        E=max(E,1);y=[0]*M;y[i]=10
        if all(sum(c["A"][k][j]*y[k] for k in range(M))<=10*E for j in range(N)) and (
            40*10*E<365*sum(c["b"][k]*y[k] for k in range(M))):
            return {"y":y,"E":E}
    return None

def synth(c):
    require(c)
    probes=c["probes"];O=c["outcomes"];rho=c["rho"];debt=c["debt"]
    initial=tuple(sorted(set(c["initial"])))
    @lru_cache(None)
    def recurse(worlds,depth,budget,spent):
        x=robust_recipe(c,worlds)
        if x is not None:return {"kind":"act","x":list(x)},0
        if depth==0:return None
        for q,p in enumerate(probes):
            price=p["price"]
            if price>budget or debt+spent+price>=rho:continue
            children=[];costs=[]
            for o in range(O):
                after=tuple(sorted({p["transition"][o][w] for w in worlds
                                    if p["observation"][w]==o}))
                sub=recurse(after,depth-1,budget-price,spent+price)
                if sub is None:break
                children.append(sub[0]);costs.append(sub[1])
            if len(children)==O:
                return {"kind":"probe","q":q,"children":children},price+max(costs)
        return None
    tree=recurse(initial,c["depth"],c["probe_budget"],0)
    if tree is not None:return {"verdict":"ACT","tree":tree[0],"ceiling":tree[1]}
    witness=dual_impossible(c)
    if witness is not None:return {"verdict":"REFUSE_PROVEN","witness":witness}
    return {"verdict":"UNKNOWN_BOUNDED"}

def lst(items):return "["+",".join(map(str,items))+"]"
def mat(items):return lst([lst(row) for row in items])
def bools(items):return "["+",".join("true" if x else "false" for x in items)+"]"
def boolmat(items):return lst([bools(row) for row in items])

def emit(c,r,k):
    W=len(c["future_worlds"]);N=len(c["future_worlds"][0]);M=len(c["b"])
    Q=len(c["probes"]);O=c["outcomes"]
    ns=f"DynamicCase{k}"
    obs=[p["observation"] for p in c["probes"]]
    trans=[p["transition"] for p in c["probes"]]
    prices=[p["price"] for p in c["probes"]]
    code=f"""import C3.TotalHistoricalMultiProbeIntegrationV1
namespace {ns}
open InsacermoExactRepair INSACERMO.TotalHistoricalMulti
open INSACERMO.TotalRepairFuture INSACERMO.LegacyC3Repair
open INSACERMO.RecursiveC3 INSACERMO.C3PP
open InsacermoMultiProbeBudget

def rows : List (List Nat) := {mat(c['A'])}
def rhs : List Nat := {lst(c['b'])}
def futureFlags : List (List Bool) := {boolmat(c['future_worlds'])}
def obs : List (List Nat) := {mat(obs)}
def trans : List (List (List Nat)) := {lst([mat(p) for p in trans])}
def prices : List Nat := {lst(prices)}
def start : List Nat := {lst(sorted(set(c['initial'])))}
def a : Nat → Nat → Nat := fun i j => (((rows[i]?).getD [])[j]?).getD 0
def req : Nat → Nat := fun i => (rhs[i]?).getD 0
def initial : Fin {W} → Prop := fun s => s.val ∈ start
def observation : Fin {Q} → Fin {W} → Fin {O} → Prop :=
  fun q s o => ((((obs[q.val]?).getD [])[s.val]?).getD 0) = o.val
def transition : Fin {Q} → Fin {O} → Fin {W} → Fin {W} :=
  fun q o s =>
    let xs := (((trans[q.val]?).getD [])[o.val]?).getD []
    let idx := (xs[s.val]?).getD 0
    ⟨idx % {W}, Nat.mod_lt _ (by decide)⟩
def price : Fin {Q} → Nat := fun q => (prices[q.val]?).getD 0

def bad0 : Bool → Prop := fun x => x = true
def dist (x y : Bool) : Nat := if x == y then 0 else 2
def state (s : Fin {W}) (p : Recipe) : Bool :=
  (List.range {N}).any (fun j =>
    decide (p.amount j ≠ 0) &&
      !((((futureFlags[s.val]?).getD [])[j]?).getD false))
def model : DynamicProblem (Fin {W}) Recipe (Fin {Q}) (Fin {O}) :=
  repairModel {M} {N} a req (fun _ => true)
    (HistoricalFuture bad0 dist 0 state)
    (fun _ => True) price observation transition
set_option maxRecDepth 8192
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
"""
    if r["verdict"]=="ACT":
        recipe_defs=[]
        memo={}
        def expr(t):
            if t["kind"]=="act":
                tup=tuple(t["x"])
                if tup not in memo:
                    name=f"recipe{len(memo)}"
                    memo[tup]=name
                    recipe_defs.append(f"def {name}v : List Nat := {lst(tup)}\ndef {name} : Recipe := ⟨(fun j => ({name}v[j]?).getD 0), {c['denominator']}⟩\n")
                return f"(.act {memo[tup]})"
            children=[expr(ch) for ch in t["children"]]
            result=children[-1]
            for o in range(len(children)-2,-1,-1):
                result=f"(if o.val == {o} then {children[o]} else {result})"
            return f"(.probe ⟨{t['q']}, by decide⟩ (fun o => {result}))"
        tree=expr(r["tree"])
        code+="".join(recipe_defs)
        code+=f"""def plan : Plan Recipe (Fin {Q}) (Fin {O}) := {tree}
theorem tree_valid : PlanValid model {c['depth']} {c['probe_budget']} initial plan := by
  unfold plan
  simp only [PlanValid, model, repairModel, Total, AfterDynamic]
  decide +kernel
theorem price_envelope : PriceEnvelope model {c['depth']} initial plan {r['ceiling']} := by
  unfold plan
  simp only [PriceEnvelope, model, repairModel, AfterDynamic]
  decide +kernel
theorem strict_reserve : PlanAffordable {c['rho']} {c['debt']} [{r['ceiling']}] := by
  simp [PlanAffordable, debtAfterPlan]
theorem CERTIFIED_C3_DYNAMIC : CanDynamic model {c['depth']} {c['probe_budget']} initial :=
  (can_iff_verified_plan model {c['depth']} {c['probe_budget']} initial).mpr
    ⟨plan, tree_valid⟩
theorem FUTURE_SAFE_AND_RESERVE :
    NoBadAtLeaves model bad0 state {c['depth']} initial plan ∧
    StrictTraceReserve model {c['rho']} {c['depth']} initial {c['debt']} plan := by
  exact ALL_BRANCHES_FUTURE_AND_RESERVE
    {M} {N} a req (fun _ => true)
    (fun _ => True) price observation transition
    bad0 bad0 dist 0 0 state
    (by intro b hb; exact ⟨b, hb, by simp [dist]⟩)
    (by decide)
    {c['rho']} {c['debt']} {r['ceiling']} {c['depth']} {c['probe_budget']} initial plan
    tree_valid price_envelope strict_reserve
"""
    elif r["verdict"]=="REFUSE_PROVEN":
        y=r["witness"]["y"];E=r["witness"]["E"]
        code+=f"""def yv : List Nat := {lst(y)}
def y : Nat → Nat := fun i => (yv[i]?).getD 0
theorem dual_check : checkDual {M} {N} a (fun _ => true) y {E} = true := by
  decide +kernel
theorem budget_gap : 40 * (10 * {E}) <
    365 * sumN {M} (fun i => req i * y i) := by
  decide +kernel
theorem CERTIFIED_NO_C3_PLAN :
    ¬ CanDynamic model {c['depth']} {c['probe_budget']} initial := by
  exact dual_certificate_blocks_every_dynamic_plan
    {M} {N} a req (fun _ => true) (HistoricalFuture bad0 dist 0 state)
    (fun _ => True) price observation transition
    y {E} dual_check budget_gap {c['depth']}
    {c['probe_budget']} initial
    ⟨⟨{c['initial'][0]}, by decide⟩, by decide⟩
"""
    return code+f"end {ns}\n"

def main():
    raw=json.loads(Path(sys.argv[1]).read_text())
    out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
    results=[]
    for k,c in enumerate(raw):
        res=synth(c);v=res["verdict"]
        if v!="UNKNOWN_BOUNDED":
            (out/f"DynamicCase{k}.lean").write_text(emit(c,res,k))
        results.append({"case":k,**res})
    (out/"result.json").write_text(json.dumps(results,indent=2))
    print(json.dumps([{"case":r["case"],"verdict":r["verdict"],
        "ceiling":r.get("ceiling")} for r in results]))
if __name__=="__main__":main()
