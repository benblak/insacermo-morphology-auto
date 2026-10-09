import Std
namespace INSACERMO.RuntimeVerdictProjection
inductive Verdict where
  | act | probe | repair | refuse
  deriving DecidableEq, Repr
structure FiniteCase where
  valid : Bool
  good : List (List Bool)
  probes : List (List Nat)
  repairs : List (List Bool)
  depth : Nat
  deriving Repr
def atBool (xs : List Bool) (i : Nat) : Bool := (xs[i]?).getD false
def atNat (xs : List Nat) (i : Nat) : Nat := (xs[i]?).getD 0
def goodAt (c : FiniteCase) (w a : Nat) : Bool :=
  atBool ((c.good[w]?).getD []) a
def actionCount (c : FiniteCase) : Nat :=
  ((c.good[0]?).getD []).length
def commonAction (c : FiniteCase) (belief : List Nat) : Bool :=
  (List.range (actionCount c)).any fun a => belief.all fun w => goodAt c w a
def probePossible (c : FiniteCase) : Bool :=
  decide (c.depth > 0) &&
  commonAction c [0] && commonAction c [1] &&
  c.probes.any (fun p => atNat p 0 != atNat p 1)
def repairPossible (c : FiniteCase) : Bool :=
  c.repairs.any (fun r => atBool r 0 && atBool r 1)
def wellFormed (c : FiniteCase) : Bool :=
  c.good.length == 2 &&
  c.good.all (fun row => row.length == actionCount c) &&
  c.probes.all (fun row => row.length == 2) &&
  c.repairs.all (fun row => row.length == 2)
def computed (c : FiniteCase) : Verdict :=
  if !c.valid || !wellFormed c then .refuse
  else if commonAction c [0,1] then .act
  else if probePossible c then .probe
  else if repairPossible c then .repair
  else .refuse
end INSACERMO.RuntimeVerdictProjection
