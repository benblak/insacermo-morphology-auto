import Std

/-!
INSACERMO C3 TOTAL — generic finite model / portable certificate checker.
All data is declared, and no physical law is inferred. The model supports
ambiguous observations (bitmask 3) and state-changing sensing branches.
All terminal actions, probes and numeric costs are enumerated from the model.
This verifier is reusable without editing its source for each new instance.
-/
namespace PortableC3

structure Model where
  worldCount : Nat
  actionCount : Nat
  probeCount : Nat
  good : List (List Bool)
  sense : List (List Nat)
  nextFalse : List (List Nat)
  nextTrue : List (List Nat)
  actionCost : List Nat
  probeCost : List Nat
  deriving Repr

inductive Tree where
  | act : Nat → Tree
  | probe : Nat → Tree → Tree → Tree
  deriving Repr

def boolAt (xs : List Bool) (i : Nat) : Bool := (xs[i]?).getD false
def natAt (xs : List Nat) (i : Nat) : Nat := (xs[i]?).getD 0

def goodAt (m : Model) (w a : Nat) : Bool :=
  boolAt ((m.good[w]?).getD []) a

def senseAt (m : Model) (q w : Nat) : Nat :=
  natAt ((m.sense[q]?).getD []) w

def priceAction (m : Model) (a : Nat) : Nat := natAt m.actionCost a
def priceProbe (m : Model) (q : Nat) : Nat := natAt m.probeCost q

def nextAt (m : Model) (q w : Nat) (o : Bool) : Nat :=
  natAt (((if o then m.nextTrue else m.nextFalse)[q]?).getD []) w

def permits (mask : Nat) (o : Bool) : Bool :=
  if o then mask == 2 || mask == 3 else mask == 1 || mask == 3

def after (m : Model) (X : List Nat) (q : Nat) (o : Bool) : List Nat :=
  (X.filter (fun w => permits (senseAt m q w) o)).map (fun w => nextAt m q w o)

def sensorTotal (m : Model) (X : List Nat) (q : Nat) : Bool :=
  X.all (fun w => senseAt m q w != 0)

def wellFormed (m : Model) (start : List Nat) : Bool :=
  m.worldCount > 0 && m.actionCount > 0 && m.probeCount > 0 &&
  !start.isEmpty && start.all (fun w => w < m.worldCount) &&
  m.good.length == m.worldCount &&
  m.good.all (fun row => row.length == m.actionCount) &&
  m.sense.length == m.probeCount &&
  m.sense.all (fun row => row.length == m.worldCount &&
    row.all (fun mask => mask == 1 || mask == 2 || mask == 3)) &&
  m.nextFalse.length == m.probeCount &&
  m.nextTrue.length == m.probeCount &&
  m.nextFalse.all (fun row => row.length == m.worldCount &&
    row.all (fun w => w < m.worldCount)) &&
  m.nextTrue.all (fun row => row.length == m.worldCount &&
    row.all (fun w => w < m.worldCount)) &&
  m.actionCost.length == m.actionCount &&
  m.probeCost.length == m.probeCount

def direct (m : Model) (budget : Nat) (X : List Nat) : Bool :=
  (List.range m.actionCount).any (fun a =>
    decide (priceAction m a ≤ budget) && X.all (fun w => goodAt m w a))

def canFinite (m : Model) : Nat → Nat → List Nat → Bool
  | 0, b, X => direct m b X
  | n + 1, b, X =>
      direct m b X || (List.range m.probeCount).any (fun q =>
        decide (priceProbe m q ≤ b) && sensorTotal m X q &&
        canFinite m n (b - priceProbe m q) (after m X q false) &&
        canFinite m n (b - priceProbe m q) (after m X q true))

def checkTree (m : Model) (depth budget : Nat) (X : List Nat) : Tree → Bool
  | .act a =>
      decide (a < m.actionCount) && decide (priceAction m a ≤ budget) &&
      X.all (fun w => goodAt m w a)
  | .probe q no yes =>
      decide (depth > 0) && decide (q < m.probeCount) &&
      decide (priceProbe m q ≤ budget) && sensorTotal m X q &&
      checkTree m (depth - 1) (budget - priceProbe m q) (after m X q false) no &&
      checkTree m (depth - 1) (budget - priceProbe m q) (after m X q true) yes

/-- Declarative meaning of the tree checker. -/
def Safe (m : Model) (depth budget : Nat) (X : List Nat) : Tree → Prop
  | .act a => a < m.actionCount ∧ priceAction m a ≤ budget ∧
      ∀ w, w ∈ X → goodAt m w a = true
  | .probe q no yes =>
      depth > 0 ∧ q < m.probeCount ∧ priceProbe m q ≤ budget ∧
      (∀ w, w ∈ X → senseAt m q w != 0) ∧
      Safe m (depth-1) (budget-priceProbe m q) (after m X q false) no ∧
      Safe m (depth-1) (budget-priceProbe m q) (after m X q true) yes

end PortableC3
