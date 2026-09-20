import InsacermoActionabilityInformation.RepairDiversityThreshold

namespace InsacermoActionabilityInformation
namespace RepairDiversityDimension

open FractureObstructionRepairBound
open RepairDiversityThreshold

/-- Every repair atom in A has its own exclusive fracture obstruction. -/
def ExclusiveRepairAlphabet
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    (canResolve : Finset Q → Finset I)
    (A : Finset I) : Prop :=
  ∀ a, a ∈ A → ExclusiveRepairWitness family canResolve a

/-- Every certified fracture obstruction can be repaired by at least one atom
from A, and no repair atom outside A is declared for that obstruction. -/
def RepairAlphabetComplete
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    (canResolve : Finset Q → Finset I)
    (A : Finset I) : Prop :=
  ∀ F, F ∈ family.obstructions →
    (canResolve F).Nonempty ∧ canResolve F ⊆ A

/-- Any transversal of the fracture family must contain every atom that has an
exclusive obstruction witness. -/
theorem every_hit_contains_exclusive_alphabet
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    {family : CertifiedFractureFamily before after target}
    {canResolve : Finset Q → Finset I}
    {A H : Finset I}
    (hexclusive : ExclusiveRepairAlphabet family canResolve A)
    (hhit : HitsFractureFamily family canResolve H) :
    A ⊆ H := by
  intro a ha
  rcases hexclusive a ha with ⟨F, hF, hcap⟩
  rcases hhit F hF with ⟨i, hiH, hiCap⟩
  have hia : i = a := by
    simpa [hcap] using hiCap
  simpa [hia] using hiH

/-- If every obstruction has a nonempty repair set contained in A, then A
itself is a transversal. -/
theorem alphabet_hits_of_complete
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    {family : CertifiedFractureFamily before after target}
    {canResolve : Finset Q → Finset I}
    {A : Finset I}
    (hcomplete : RepairAlphabetComplete family canResolve A) :
    HitsFractureFamily family canResolve A := by
  intro F hF
  rcases hcomplete F hF with ⟨hne, hsub⟩
  rcases hne with ⟨a, ha⟩
  exact ⟨a, hsub ha, ha⟩

/-- Under unit atom cost, every transversal has cost at least the cardinality
of an exclusive repair alphabet. -/
theorem unit_cost_lower_bound_of_exclusive_alphabet
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    {family : CertifiedFractureFamily before after target}
    {canResolve : Finset Q → Finset I}
    {A H : Finset I}
    (hexclusive : ExclusiveRepairAlphabet family canResolve A)
    (hhit : HitsFractureFamily family canResolve H) :
    A.card ≤ SelectionCost (fun _ : I => 1) H := by
  have hsub : A ⊆ H :=
    every_hit_contains_exclusive_alphabet hexclusive hhit
  have hcard : A.card ≤ H.card := Finset.card_le_card hsub
  simpa [RepairDiversityThreshold.unitSelectionCost_eq_card] using hcard

/-- Completeness of A gives a unit-cost transversal with budget |A|. -/
theorem complete_alphabet_gives_unit_transversal
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    {family : CertifiedFractureFamily before after target}
    {canResolve : Finset Q → Finset I}
    {A : Finset I}
    (hcomplete : RepairAlphabetComplete family canResolve A) :
    FractureTransversalWithinBudget
      family canResolve (fun _ : I => 1) A.card := by
  refine ⟨A, ?_, alphabet_hits_of_complete hcomplete⟩
  simp [SelectionCost]

/-- The unit-cost obstruction-transversal price, viewed as a repair-diversity
dimension of the fracture family. -/
noncomputable def RepairDiversityDimension
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    (canResolve : Finset Q → Finset I)
    (htrans : HasFractureTransversal family canResolve (fun _ : I => 1)) : Nat :=
  FractureTransversalPrice family canResolve (fun _ : I => 1) htrans

/-- GENERAL REPAIR-DIVERSITY THEOREM.
If A is a complete repair alphabet and each atom of A has at least one
exclusive fracture obstruction, then the exact unit-cost transversal price,
hence the repair-diversity dimension, is exactly |A|. -/
theorem repairDiversityDimension_eq_card
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    {family : CertifiedFractureFamily before after target}
    {canResolve : Finset Q → Finset I}
    {A : Finset I}
    (hcomplete : RepairAlphabetComplete family canResolve A)
    (hexclusive : ExclusiveRepairAlphabet family canResolve A)
    (htrans : HasFractureTransversal family canResolve (fun _ : I => 1)) :
    RepairDiversityDimension family canResolve htrans = A.card := by
  unfold RepairDiversityDimension
  apply Nat.le_antisymm
  · apply fractureTransversalPrice_minimal
    exact complete_alphabet_gives_unit_transversal hcomplete
  ·
    rcases fractureTransversalPrice_spec
      family canResolve (fun _ : I => 1) htrans with ⟨H, hcost, hhit⟩
    exact Nat.le_trans
      (unit_cost_lower_bound_of_exclusive_alphabet hexclusive hhit)
      hcost

/-- Lower-bound form without completeness: every exclusive repair alphabet A
forces diversity dimension at least |A|. -/
theorem repairDiversityDimension_ge_card_exclusive
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    {family : CertifiedFractureFamily before after target}
    {canResolve : Finset Q → Finset I}
    {A : Finset I}
    (hexclusive : ExclusiveRepairAlphabet family canResolve A)
    (htrans : HasFractureTransversal family canResolve (fun _ : I => 1)) :
    A.card ≤ RepairDiversityDimension family canResolve htrans := by
  unfold RepairDiversityDimension
  rcases fractureTransversalPrice_spec
    family canResolve (fun _ : I => 1) htrans with ⟨H, hcost, hhit⟩
  exact Nat.le_trans
    (unit_cost_lower_bound_of_exclusive_alphabet hexclusive hhit)
    hcost

end RepairDiversityDimension
end InsacermoActionabilityInformation
