#!/usr/bin/env python3
"""Data-to-Lean emitter, independent of mathematical Lean kernel.
Takes JSON instances. NEVER patches the proof kernel.
"""
import json, re, sys
from pathlib import Path

def render(case):
    name=case["case_id"]
    assert re.fullmatch(r"[a-z][a-z0-9_]*", name)
    A=case["A"];b=case["b"];allowed=case["allowed"];x=case["x"]
    D=case["D"];y=case["y"];E=case["E"]
    m=len(b); n=len(allowed)
    assert m>0 and n>0 and len(A)==m and all(len(row)==n for row in A)
    assert len(x)==n and len(y)==m and D>0 and E>0
    for seq in [b,x,y,*A]:
        assert all(type(v) is int and v>=0 for v in seq)
    assert all(type(t) is bool for t in allowed)
    assert case["expected"] in ("infeasible40","feasible40")
    S=lambda xs:"["+",".join(map(str,xs))+"]"
    Bt=lambda xs:"["+",".join(str(x).lower() for x in xs)+"]"
    p=f'''import ExactRepairCheckerV1
namespace Generated_{name}
open InsacermoExactRepair

def matrix : List (List Nat) := {S([S(row) for row in A])}
def limits : List Nat := {S(b)}
def admissions : List Bool := {Bt(allowed)}
def xvals : List Nat := {S(x)}
def yvals : List Nat := {S(y)}
def a : Nat → Nat → Nat := fun i j => ((matrix[i]?).getD [])[j]?.getD 0
def req : Nat → Nat := fun i => (limits[i]?).getD 0
def allowed : Nat → Bool := fun j => (admissions[j]?).getD false
def x : Nat → Nat := fun j => (xvals[j]?).getD 0
def y : Nat → Nat := fun i => (yvals[i]?).getD 0
def denominator : Nat := {D}
def dualDenominator : Nat := {E}

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

theorem input_dimensions_verified :
    matrix.length = {m} ∧ limits.length = {m} ∧ admissions.length = {n} ∧
    xvals.length = {n} ∧ yvals.length = {m} ∧
    matrix.all (fun row => row.length == {n}) = true := by
  decide +kernel

'''
    if case["expected"]=="infeasible40":
        p+=f'''theorem dual_certificate_accepted :
    checkDual {m} {n} a allowed y dualDenominator = true := by
  decide +kernel

theorem exceeds_annual_budget :
    40 * (10 * dualDenominator) <
    365 * sumN {m} (fun i => req i * y i) := by
  decide +kernel

theorem NO_ADMISSIBLE_CONSTRUCTION_UNDER_40
    (D : Nat) (hD : D > 0) (solution : Nat → Nat)
    (hp : PrimalValid (m := {m}) (n := {n}) a req allowed solution D) :
    ¬ (365 * sumN {n} solution ≤ 40 * D) :=
  checked_budget_impossible {m} {n} a req allowed y dualDenominator
    dual_certificate_accepted exceeds_annual_budget D hD solution hp

'''
    else:
        p+=f'''theorem primal_certificate_accepted :
    checkPrimal {m} {n} a req allowed x denominator = true := by
  decide +kernel

theorem within_annual_budget :
    365 * sumN {n} x ≤ 40 * denominator := by
  decide +kernel

theorem EXISTING_CONSTRUCTION_UNDER_40 :
    PrimalValid (m := {m}) (n := {n}) a req allowed x denominator ∧
    365 * sumN {n} x ≤ 40 * denominator :=
  ⟨checked_primal_sound {m} {n} a req allowed x denominator
      primal_certificate_accepted, within_annual_budget⟩

'''
    p+=f'end Generated_{name}\n'
    return p

def main():
    inputs=json.loads(Path(sys.argv[1]).read_text())
    dest=Path(sys.argv[2]); dest.mkdir(parents=True,exist_ok=True)
    assert len(set(c["case_id"] for c in inputs))==len(inputs)
    for case in inputs:
        out=dest/("Generated_"+case["case_id"]+".lean")
        out.write_text(render(case))
        print(f"EMITTED {out} ({case['expected']})")
if __name__=="__main__":main()
