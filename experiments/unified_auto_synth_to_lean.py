#!/usr/bin/env python3
"""Raw contract -> synthesis -> Lean certificate. Bounded exact enumeration.
No oracle and no solution embedded in the input. REFUSE_UNPROVEN is fail-closed.
"""
import json,sys
from pathlib import Path
from fractions import Fraction

def vector(z): return "["+",".join(map(str,z))+"]"
def booleans(z):return "["+",".join(str(v).lower() for v in z)+"]"

def synth(c):
    A=c["A"];b=c["b"]; worlds=c["future_worlds"]
    n=len(worlds[0]);m=len(b)
    assert n>0 and m>0 and all(len(row)==n for row in A)
    assert len(A)==m and all(len(w)==n for w in worlds) and len(worlds)>0
    assert all(type(t) is bool for w in worlds for t in w)
    assert all(type(t) is int and t>=0 for row in A for t in row)
    assert all(type(t) is int and t>=0 for t in b)
    assert c.get("annual_limit")==40 and c.get("annual_days")==365 and c.get("scale")==10
    denom=c.get("denominator",365)
    maximum=c.get("max_units",40)
    assert type(denom) is int and 1<=denom<=1000
    assert type(maximum) is int and 0<=maximum<=100
    allowed=[all(w[j] for w in worlds) for j in range(n)]
    x=[0]*n
    limit=(40*denom)//365
    limit=min(limit,maximum)
    # full rational numerator enumeration under budget, no numerical approximations
    def search(j,left):
        if j==n:
            if all(sum(A[i][k]*x[k] for k in range(n)) >= b[i]*denom for i in range(m)):
                return x[:]
            return None
        if not allowed[j]:return search(j+1,left)
        for v in range(left+1):
            x[j]=v
            found=search(j+1,left-v)
            if found is not None:return found
        x[j]=0
        return None
    found=search(0,limit)
    if found is not None:return {"verdict":"ACT","x":found,"D":denom,"allowed":allowed}
    # Exact elementary dual: a single unmet nutrient lower bound even at
    # total budget. Does not cover all LP obstructions.
    for i in range(m):
        maxcoef=max([A[i][j] for j in range(n) if allowed[j]] or [0])
        if 365*b[i]>40*maxcoef:
            y=[0]*m;y[i]=10
            E=maxcoef
            if E==0:E=1
            # Aij*y_i <= 10E; strict inequality then check explicitly
            if 40*10*E < 365*sum(b[k]*y[k] for k in range(m)):
                return {"verdict":"REFUSE_PROVEN","y":y,"E":E,"allowed":allowed}
    return {"verdict":"REFUSE_UNPROVEN","allowed":allowed}

def lean(c,res,name):
    A=c["A"];b=c["b"];worlds=c["future_worlds"]
    m=len(b);n=len(worlds[0])
    head=f"""import UnifiedAutoSynthCertificateV1
namespace {name}
open InsacermoExactRepair INSACERMO.AutoSynthCert
def rows : List (List Nat) := {vector([vector(row) for row in A])}
def requirements : List Nat := {vector(b)}
def futures : List (List Bool) := {vector([booleans(w) for w in worlds])}
def flags : List Bool := {booleans(res['allowed'])}
def a : Nat → Nat → Nat := fun i j => (((rows[i]?).getD [])[j]?).getD 0
def b : Nat → Nat := fun i => (requirements[i]?).getD 0
def allowed : Nat → Bool := fun j => (flags[j]?).getD false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
"""
    if res["verdict"]=="ACT":
        head+=f"""def xv : List Nat := {vector(res['x'])}
def x : Nat → Nat := fun j => (xv[j]?).getD 0
theorem primal_check : checkPrimal {m} {n} a b allowed x {res['D']} = true := by decide +kernel
theorem future_check : checkFuture {n} futures x = true := by decide +kernel
theorem within_budget : 365 * sumN {n} x ≤ 40 * {res['D']} := by decide +kernel
theorem CERTIFIED_ACT :
    PrimalValid (m := {m}) (n := {n}) a b allowed x {res['D']} ∧
    (∀ w, w < futures.length → ∀ j, j < {n} →
      x j ≠ 0 → worldAllowed futures w j = true) ∧
    365 * sumN {n} x ≤ 40 * {res['D']} :=
  certified_future_construction {m} {n} a b allowed futures x {res['D']}
    primal_check future_check within_budget
"""
    elif res["verdict"]=="REFUSE_PROVEN":
        head+=f"""def yv : List Nat := {vector(res['y'])}
def y : Nat → Nat := fun i => (yv[i]?).getD 0
theorem dual_check : checkDual {m} {n} a allowed y {res['E']} = true := by decide +kernel
theorem budget_gap : 40 * (10 * {res['E']}) < 365 * sumN {m} (fun i => b i * y i) := by decide +kernel
theorem CERTIFIED_REFUSE :
    ∀ D, D > 0 → ∀ x,
      PrimalValid (m := {m}) (n := {n}) a b allowed x D →
      ¬ (365 * sumN {n} x ≤ 40 * D) :=
  certified_no_robust_single_construction {m} {n} a b allowed y {res['E']}
    dual_check budget_gap
"""
    return head+f"end {name}\n"

def main():
    inp=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
    data=json.loads(inp.read_text())
    results=[]
    for k,c in enumerate(data):
        r=synth(c);name=f"AutoCase{k}"
        if r["verdict"]!="REFUSE_UNPROVEN":
            (out/f"{name}.lean").write_text(lean(c,r,name))
        results.append({"case":name,"verdict":r["verdict"],"result":r})
    (out/"result.json").write_text(json.dumps(results,indent=2))
    print(json.dumps([{"case":r["case"],"verdict":r["verdict"]} for r in results]))
if __name__=="__main__":main()
