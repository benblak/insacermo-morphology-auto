import MaxExactOperatorOptimumV1
import Std

/-!
INSACERMO portable policy certificate V1.

The plan below was emitted by the *previously frozen* finite operator
synthesizer for the five-world, exactly-one-failure model with:
  four critical failure edges plus OTHER;
  all nonempty OR probes on the 4 critical edges at cost 1;
  each single-edge repair at cost 2.

This checker is separate from the synthesizer. No use of python,
unverified oracle, labels, statistical learning, sorry, admit or axioms.

Soundness is deliberately model-relative: this theorem says nothing about
a real deployed grouped sensor, physical cost, OpenFlights data integrity,
or a full operational MAX TOTAL runtime execution.
-/

namespace INSACERMO.Portable

inductive Policy where
  | act
  | probe (mask : Nat) (onDown onUp : Policy)
  | repair (mask : Nat) (next : Policy)
deriving Repr

/-- The independently auditable finite policy serialized as Lean data. -/
def emittedPlan : Policy :=
  .probe 3
    (.probe 1
      (.repair 1 .act)
      (.repair 2 .act))
    (.probe 4
      (.repair 4 .act)
      (.repair 8 .act))

/-- Restrict the certificate to its declared operator grammar:
  every nonempty subset can be probed at unit cost,
  repairs can touch exactly one individual critical edge. -/
def grammarValid : Policy → Bool
  | .act => true
  | .probe mask yes no =>
      decide (0 < mask ∧ mask < 16) && grammarValid yes && grammarValid no
  | .repair mask next =>
      (mask == 1 || mask == 2 || mask == 4 || mask == 8) && grammarValid next

/-- Deterministic interpreter, independent of the optimizer.
    The irrelevant world has index 4. -/
def runWorld (world repaired : Nat) : Policy → Nat × Nat
  | .act => (repaired, 0)
  | .probe mask yes no =>
      let down := world < 4 && !(repaired.testBit world) && mask.testBit world
      let r := runWorld world repaired (if down then yes else no)
      (r.1, r.2 + 1)
  | .repair mask next =>
      let r := runWorld world (Nat.lor repaired mask) next
      (r.1, r.2 + 2)

def validInEveryWorld : Bool :=
  grammarValid emittedPlan &&
    (List.range 5).all (fun w =>
      let result := runWorld w 0 emittedPlan
      decide (result.2 ≤ 4) && (w == 4 || result.1.testBit w))

def reachesWorstCostFour : Bool :=
  (List.range 5).any (fun w =>
    (runWorld w 0 emittedPlan).2 == 4)

theorem emitted_plan_passes_all_worlds :
    validInEveryWorld = true := by
  decide +kernel

theorem witness_attains_cost_four :
    reachesWorstCostFour = true := by
  decide +kernel

/-- Combined certificate:
  the serialized operator tree is a valid worst-case-4 policy;
  the independently checked exhaustive finite feasibility theorem
  rules out every policy with worst-case budget 3 in the same grammar. -/
theorem emitted_plan_exact_minimax :
    validInEveryWorld = true ∧
    reachesWorstCostFour = true ∧
    MaxExact.feasible 3 MaxExact.allBelief 0 = false :=
  ⟨emitted_plan_passes_all_worlds,
    witness_attains_cost_four,
    MaxExact.three_insufficient⟩

end INSACERMO.Portable
