import Std
import CostlyProbeMinimal
import SafeProbeTheorem

/-!
INSACERMO — Probe Repair Kernel V1

Structural theorem for repairing an unsafe observation fiber.

For a fixed observation value o and candidate action a, define the worlds in that fiber
that currently lack action a. That set is exactly the minimal repair set required if the
repair operation consists of adding feasibility of a to selected worlds.

This theorem is qualitative/structural. A numerical "price of information" comes later,
once a cost model on repairs is supplied.
-/

namespace InsacermoProbeRepair

/-- Repair set for candidate action a on observation fiber o. -/
def RepairSet {W A O : Type} [DecidableEq O]
    (feasible : W → A → Prop)
    (observe : W → O)
    (o : O)
    (a : A) : W → Prop :=
  fun w => observe w = o ∧ ¬ feasible w a

/-- After repairing candidate action a on exactly R, a world has a whenever it had it already or is in R. -/
def RepairedFeasible {W A : Type}
    (feasible : W → A → Prop)
    (R : W → Prop)
    (aRepair : A)
    (w : W)
    (a : A) : Prop :=
  feasible w a ∨ (a = aRepair ∧ R w)

/--
Exactness: repairing precisely RepairSet makes a common action available on the whole fiber.
-/
theorem repairset_suffices
    {W A O : Type} [DecidableEq O]
    (feasible : W → A → Prop)
    (observe : W → O)
    (o : O)
    (a : A) :
    ∀ w : W, observe w = o →
      RepairedFeasible feasible (RepairSet feasible observe o a) a w a := by
  intro w hw
  by_cases hfa : feasible w a
  · exact Or.inl hfa
  · exact Or.inr ⟨rfl, ⟨hw, hfa⟩⟩

/--
Minimality: any repair predicate R that makes candidate action a feasible throughout the fiber
must contain every world in RepairSet.
-/
theorem repairset_is_minimal
    {W A O : Type} [DecidableEq O]
    (feasible : W → A → Prop)
    (observe : W → O)
    (o : O)
    (a : A)
    (R : W → Prop)
    (hR : ∀ w : W, observe w = o →
      RepairedFeasible feasible R a w a) :
    ∀ w : W, RepairSet feasible observe o a w → R w := by
  intro w hbad
  rcases hbad with ⟨hw, hnot⟩
  have h := hR w hw
  rcases h with hfa | hrep
  · exact False.elim (hnot hfa)
  · exact hrep.2

/--
Characterization: a repair predicate is sufficient for candidate action a on fiber o
iff it contains the exact RepairSet.
-/
theorem repair_sufficient_iff_contains_repairset
    {W A O : Type} [DecidableEq O]
    (feasible : W → A → Prop)
    (observe : W → O)
    (o : O)
    (a : A)
    (R : W → Prop) :
    (∀ w : W, observe w = o →
      RepairedFeasible feasible R a w a)
    ↔
    (∀ w : W, RepairSet feasible observe o a w → R w) := by
  constructor
  · intro hs
    exact repairset_is_minimal feasible observe o a R hs
  · intro hcontains
    intro w hw
    by_cases hfa : feasible w a
    · exact Or.inl hfa
    · exact Or.inr ⟨rfl, hcontains w ⟨hw, hfa⟩⟩

/--
If a fiber is already safe for action a, its repair set is empty.
-/
theorem repairset_empty_when_common
    {W A O : Type} [DecidableEq O]
    (feasible : W → A → Prop)
    (observe : W → O)
    (o : O)
    (a : A)
    (hcommon : ∀ w : W, observe w = o → feasible w a) :
    ∀ w : W, ¬ RepairSet feasible observe o a w := by
  intro w h
  exact h.2 (hcommon w h.1)

/--
The minimal 3×2 witness has a nonempty repair set for either candidate action
on the bad false-observation fiber.
-/
theorem minimal_witness_repair_false_for_action_false :
    RepairSet
      InsacermoCostlyProbeMinimal.afterFeasible
      InsacermoCostlyProbeMinimal.probeObservation
      false
      false
      (2 : InsacermoCostlyProbeMinimal.World) := by
  constructor <;> decide

theorem minimal_witness_repair_false_for_action_true :
    RepairSet
      InsacermoCostlyProbeMinimal.afterFeasible
      InsacermoCostlyProbeMinimal.probeObservation
      false
      true
      (0 : InsacermoCostlyProbeMinimal.World) := by
  constructor <;> decide

#print axioms repairset_suffices
#print axioms repairset_is_minimal
#print axioms repair_sufficient_iff_contains_repairset
#print axioms repairset_empty_when_common
#print axioms minimal_witness_repair_false_for_action_false
#print axioms minimal_witness_repair_false_for_action_true

end InsacermoProbeRepair
