"""INSACERMO ONE ENGINE: finite C3 Must/May with exact Lean decision gate.

This is the central *bounded finite* interface over pre-existing PortableC3.
It does not supersede historical MAX TOTAL or imply physical law discovery.
Two world envelopes L subset U, two policy grammars must subset may, and
unmodified transitions. Numeric budget includes strict debt reserve.
"""
from __future__ import annotations
import hashlib,json,subprocess,os
from pathlib import Path
from functools import lru_cache

VERSION="INSACERMO_C3_FINITE_ONE_ENGINE_V1"
def canonical(x):return json.dumps(x,sort_keys=True,separators=(",",":")).encode()
def sha(x):return hashlib.sha256(x).hexdigest()
def validate(m):
    W=m["worldCount"];A=m["actionCount"];Q=m["probeCount"]
    assert type(W)==int and 1<=W<=8 and type(A)==int and 1<=A<=12 and type(Q)==int and 1<=Q<=8
    for key,n,k,allowed in [("good",W,A,(False,True)),("sense",Q,W,(1,2,3)),
            ("nextFalse",Q,W,range(W)),("nextTrue",Q,W,range(W))]:
        v=m[key];assert len(v)==n and all(len(row)==k for row in v)
        assert all(type(x)==(bool if key=="good" else int) and x in allowed for row in v for x in row)
    for key,n in (("actionCost",A),("probeCost",Q)):
        assert len(m[key])==n and all(type(x)==int and 0<=x<=100 for x in m[key])
    L=m["lowerWorld"];U=m["upperWorld"]
    assert L and U and all(type(x)==int and 0<=x<W for x in L+U)
    assert len(L)==len(set(L)) and len(U)==len(set(U)) and set(L)<=set(U)
    Must=m["mustActions"];May=m["mayActions"]
    assert all(type(x)==int and 0<=x<A for x in Must+May)
    assert len(Must)==len(set(Must)) and len(May)==len(set(May)) and set(Must)<=set(May)
    for k in ("depth","budget","reserve","debt"):
        assert type(m[k])==int and 0<=m[k]<=100
    assert m["depth"]<=4 and m["debt"]<m["reserve"]

def solve(m,X,action_allowed,depth,budget):
    @lru_cache(None)
    def rec(worlds,n,b):
        for a in action_allowed:
            if m["actionCost"][a]<=b and all(m["good"][w][a] for w in worlds):
                return {"act":a}
        if n==0:return None
        for q in range(m["probeCount"]):
            cost=m["probeCost"][q]
            if cost>b:continue
            no=[];yes=[]
            for w in worlds:
                mask=m["sense"][q][w]
                if mask&1:no.append(m["nextFalse"][q][w])
                if mask&2:yes.append(m["nextTrue"][q][w])
            l=rec(tuple(sorted(set(no))),n-1,b-cost)
            r=rec(tuple(sorted(set(yes))),n-1,b-cost)
            if l is not None and r is not None:
                return {"probe":q,"no":l,"yes":r}
        return None
    return rec(tuple(sorted(X)),depth,budget)

def lean(m,mode,tree,budget):
    def nat(x):return "["+",".join(str(v) for v in x)+"]"
    def bools(x):return "["+",".join(str(v).lower() for v in x)+"]"
    def matrix(xs,bo=False):return "["+",".join(bools(x) if bo else nat(x) for x in xs)+"]"
    def tree_l(t):
        if "act" in t:return f"(Tree.act {t['act']})"
        return f"(Tree.probe {t['probe']} {tree_l(t['no'])} {tree_l(t['yes'])})"
    assert mode in ("ACT","REFUSE_ROBUST","EPISTEMIC_OPEN")
    # For robust ACT, non-MUST actions are deliberately blocked in Lean.
    action_flags=[a in (m["mustActions"] if mode=="ACT" else m["mayActions"]) for a in range(m["actionCount"])]
    actions=[[(x if action_flags[j] else False) for j,x in enumerate(row)] for row in m["good"]]
    worlds=m["upperWorld"] if mode=="ACT" else m["lowerWorld"]
    lines=["import C3.PortableExactSearchV1","namespace INSACERMO.C3OneDecision","open PortableC3"]
    lines+=["def mm : Model := {",
        f" worldCount := {m['worldCount']}",
        f" actionCount := {m['actionCount']}",
        f" probeCount := {m['probeCount']}",
        f" good := {matrix(actions,True)}",
        f" sense := {matrix(m['sense'])}",
        f" nextFalse := {matrix(m['nextFalse'])}",
        f" nextTrue := {matrix(m['nextTrue'])}",
        f" actionCost := {nat(m['actionCost'])}",
        f" probeCost := {nat(m['probeCost'])}","}",
        f"def start : List Nat := {nat(worlds)}",
        "set_option maxRecDepth 8192","set_option maxHeartbeats 20000000",
        "theorem input_ok : wellFormed mm start = true := by decide +kernel"]
    if mode=="ACT":
        lines.extend([f"def choice : Tree := {tree_l(tree)}",
            f"theorem decision_verified : checkTree mm {m['depth']} {budget} start choice = true := by decide +kernel",
            f"theorem all_branches_safe : Safe mm {m['depth']} {budget} start choice :=",
            f"  accepted_certificate_sound mm {m['depth']} {budget} start choice decision_verified"])
    else:
        lines.extend([f"theorem no_plan_in_declared_grammar : canFinite mm {m['depth']} {budget} start = false := by decide +kernel",
            f"theorem no_checked_strategy (t : Tree) : checkTree mm {m['depth']} {budget} start t = false :=",
            f"  impossible_budget_rejects_every_plan mm {m['depth']} {budget} start no_plan_in_declared_grammar t"])
    lines.append("end INSACERMO.C3OneDecision")
    return "\n".join(lines)+"\n"

def decide(model,folder,*,lean_binary="lean"):
    try:validate(model)
    except (AssertionError,KeyError,TypeError,ValueError):
        return {"verdict":"REFUSE_INVALID_MODEL","authorized":False}
    h=sha(canonical(model))
    budget=min(model["budget"],model["reserve"]-model["debt"]-1)
    if budget<0:return {"verdict":"REFUSE_INVALID_MODEL","authorized":False}
    must=solve(model,model["upperWorld"],model["mustActions"],model["depth"],budget)
    may=solve(model,model["lowerWorld"],model["mayActions"],model["depth"],budget)
    if must is not None:mode="ACT";plan=must
    elif may is None:mode="REFUSE_ROBUST";plan=None
    else:mode="EPISTEMIC_OPEN";plan=may
    # No positive authorization until *same-input* Lean acceptance.
    proof=lean(model,mode,plan,budget)
    folder=Path(folder);folder.mkdir(parents=True,exist_ok=True)
    (folder/"C3Decision.lean").write_text(proof)
    (folder/"contract.json").write_bytes(canonical(model))
    (folder/"candidate.json").write_bytes(canonical({"verdict":mode,"plan":plan,"budget":budget}))
    env=dict(os.environ,LEAN_PATH=".:lean")
    try:
        completed=subprocess.run([lean_binary,str((folder/"C3Decision.lean").resolve())],
            cwd=Path(__file__).resolve().parent,env=env,capture_output=True,text=True,timeout=120)
        ok=(completed.returncode==0 and "sorryAx" not in completed.stdout)
    except (OSError,subprocess.TimeoutExpired):
        ok=False
    if not ok:return {"verdict":"REFUSE_CERTIFICATE_MISSING","authorized":False,"contract_sha256":h}
    result={"verdict":mode,"authorized":mode=="ACT","plan":plan,
        "probe_or_repair_required":bool(plan and "probe" in plan),
        "contract_sha256":h,"source_sha256":sha(proof.encode()),"budget":budget,
        "scope":"EXACT FINITE C3 ENVELOPES AND DECLARED PROBE/REPAIR GRAMMAR"}
    result["receipt_sha256"]=sha(canonical(result))
    (folder/"receipt.json").write_bytes(canonical(result))
    return result
