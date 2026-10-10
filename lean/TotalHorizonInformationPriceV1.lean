import Std

/-!
A finite rational-scaled witness for information value under future obligations.
This Lean theorem verifies an exact example, not a general LP solver.
-/
namespace InsacermoTotalHorizon

/-- Without branch distinction, both worlds must use the same post-observation controls.
These four inequalities are the distilled coupled service and future-reserve
constraints after eliminating state variables. -/
def BlindFeasible (presentFast presentRepair futureFast futureRepair : Nat) : Prop :=
  2 ≤ presentFast + presentRepair ∧
  presentRepair ≤ 1 ∧
  2 ≤ presentRepair + futureRepair ∧
  3 ≤ presentRepair + futureRepair ∧
  2 ≤ presentFast + presentRepair + futureFast + futureRepair

/-- Model price of a non-adaptive controller. -/
def BlindCost (presentFast presentRepair futureFast futureRepair : Nat) : Nat :=
  presentFast + 3*presentRepair + futureFast + 3*futureRepair

/-- Under the stronger future requirement, an admissible blind plan needs cost at least 7. -/
theorem blind_cost_lower_bound (a b c d : Nat)
    (h : BlindFeasible a b c d) : 7 ≤ BlindCost a b c d := by
  dsimp [BlindFeasible] at h
  dsimp [BlindCost]
  omega

theorem blind_cost_witness : BlindFeasible 1 1 0 2 ∧ BlindCost 1 1 0 2 = 10 := by
  constructor
  · dsimp [BlindFeasible]
    omega
  · dsimp [BlindCost]

end InsacermoTotalHorizon
