import Std

/-!
Independent finite policy checker, no ML. Exactly one link outage in 4 critical
links, or OTHER, with perfect Boolean OR probes and singleton repairs.
The proof DOES NOT cover the raw OpenFlights file or arbitrary INSACERMO inputs.
-/
namespace INSACERMO.FiniteCertV2

structure Operator where
  kind : Nat
  mask : Nat
  price : Nat
  deriving DecidableEq, BEq, Repr

inductive Policy where
  | act
  | refuse
  | probe (mask price : Nat) (onDown onUp : Policy)
  | repair (mask price : Nat) (next : Policy)
  deriving Repr

structure Contract where
  worlds : Nat
  critical : Nat
  reserve : Nat
  debt : Nat
  validEnvelope : Bool
  kind : String
  deriving Repr

structure Trace where
  repaired : Nat
  cost : Nat
  didAct : Bool
  deriving Repr

def grammarValid (allowed : List Operator) : Policy → Bool
  | .act => true
  | .refuse => true
  | .probe mask price yes no =>
      allowed.contains ⟨0, mask, price⟩ &&
      decide (mask > 0 ∧ mask < 16 ∧ price > 0) &&
      grammarValid allowed yes && grammarValid allowed no
  | .repair mask price next =>
      allowed.contains ⟨1, mask, price⟩ &&
      (mask == 1 || mask == 2 || mask == 4 || mask == 8) &&
      decide (price > 0) &&
      grammarValid allowed next

def replay (world repaired : Nat) : Policy → Trace
  | .act => ⟨repaired, 0, true⟩
  | .refuse => ⟨repaired, 0, false⟩
  | .probe mask price onDown onUp =>
      let down := world < 4 && !(repaired.testBit world) && mask.testBit world
      let r := if down then replay world repaired onDown else replay world repaired onUp
      ⟨r.repaired, price + r.cost, r.didAct⟩
  | .repair mask price next =>
      let r := replay world (Nat.lor repaired mask) next
      ⟨r.repaired, price + r.cost, r.didAct⟩

def accepts (c : Contract) (allowed : List Operator) (plan : Policy) : Bool :=
  c.kind == "REACHABILITY_ONE_OUTAGE" &&
  c.worlds == 5 && c.critical == 4 && c.validEnvelope &&
  grammarValid allowed plan &&
  (List.range c.worlds).all (fun w =>
    let trace := replay w 0 plan
    trace.didAct &&
    (w == 4 || trace.repaired.testBit w) &&
    decide (trace.cost + c.debt < c.reserve))

def worstCost (worlds : Nat) (plan : Policy) : Nat :=
  (List.range worlds).foldl (fun maxCost w =>
    max maxCost (replay w 0 plan).cost) 0

def referenceGrammar : List Operator :=
  (List.range 15).map (fun i => ⟨0, i+1, 1⟩) ++
  (List.range 4).map (fun i => ⟨1, 2^i, 2⟩)

end INSACERMO.FiniteCertV2
