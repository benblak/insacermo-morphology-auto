import InsacermoActionabilityInformation.FractureObstructionRepairBound

namespace InsacermoActionabilityInformation
namespace RepairDiversityThreshold

open FractureObstructionRepairBound

/-- One fracture obstruction can be repaired only by atom `a`. -/
def ExclusiveRepairWitness
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    (canResolve : Finset Q → Finset I)
    (a : I) : Prop :=
  ∃ F, F ∈ family.obstructions ∧ canResolve F = {a}

/-- Every certified obstruction has at least one repair atom, and every such
atom belongs to the two-class alphabet {a,b}. -/
def TwoAtomComplete
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    (canResolve : Finset Q → Finset I)
    (a b : I) : Prop :=
  ∀ F, F ∈ family.obstructions →
    (canResolve F).Nonempty ∧ canResolve F ⊆ ({a,b} : Finset I)

/-- Under two-atom completeness, selecting both atoms always hits the fracture family. -/
theorem pair_hits_of_twoAtomComplete
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    {family : CertifiedFractureFamily before after target}
    {canResolve : Finset Q → Finset I}
    {a b : I}
    (hcomplete : TwoAtomComplete family canResolve a b) :
    HitsFractureFamily family canResolve ({a,b} : Finset I) := by
  intro F hF
  rcases hcomplete F hF with ⟨hne, hsub⟩
  rcases hne with ⟨i, hi⟩
  exact ⟨i, hsub hi, hi⟩

/-- If one obstruction is exclusively A-repairable and another is exclusively
B-repairable, every hitting repair support must contain both atoms. -/
theorem every_hit_contains_both_of_exclusive_witnesses
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    {family : CertifiedFractureFamily before after target}
    {canResolve : Finset Q → Finset I}
    {a b : I}
    (ha : ExclusiveRepairWitness family canResolve a)
    (hb : ExclusiveRepairWitness family canResolve b)
    {H : Finset I}
    (hhit : HitsFractureFamily family canResolve H) :
    a ∈ H ∧ b ∈ H := by
  rcases ha with ⟨Fa, hFa, hcapA⟩
  rcases hb with ⟨Fb, hFb, hcapB⟩
  rcases hhit Fa hFa with ⟨i, hiH, hiCap⟩
  rcases hhit Fb hFb with ⟨j, hjH, hjCap⟩
  have hia : i = a := by
    simpa [hcapA] using hiCap
  have hjb : j = b := by
    simpa [hcapB] using hjCap
  subst i
  subst j
  exact ⟨hiH, hjH⟩

/-- Unit-cost support cost is exactly support cardinality. -/
theorem unitSelectionCost_eq_card
    {I : Type*} [DecidableEq I]
    (H : Finset I) :
    SelectionCost (fun _ : I => 1) H = H.card := by
  simp [SelectionCost]

/-- Two distinct exclusive repair witnesses force every hitting support to have
unit cost at least two. -/
theorem unit_cost_at_least_two_of_exclusive_witnesses
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    {family : CertifiedFractureFamily before after target}
    {canResolve : Finset Q → Finset I}
    {a b : I}
    (hab : a ≠ b)
    (ha : ExclusiveRepairWitness family canResolve a)
    (hb : ExclusiveRepairWitness family canResolve b)
    {H : Finset I}
    (hhit : HitsFractureFamily family canResolve H) :
    2 ≤ SelectionCost (fun _ : I => 1) H := by
  rcases every_hit_contains_both_of_exclusive_witnesses ha hb hhit with ⟨haH, hbH⟩
  have hsub : ({a,b} : Finset I) ⊆ H := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hxa | hxb
    · simpa [hxa] using haH
    · simpa [hxb] using hbH
  have hcard : 2 ≤ H.card := by
    have := Finset.card_le_card hsub
    simpa [hab] using this
  simpa [unitSelectionCost_eq_card] using hcard

/-- The two selected repair atoms provide a feasible unit-cost transversal of budget 2. -/
theorem two_atom_unit_transversal_within_two
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    {family : CertifiedFractureFamily before after target}
    {canResolve : Finset Q → Finset I}
    {a b : I}
    (hab : a ≠ b)
    (hcomplete : TwoAtomComplete family canResolve a b) :
    FractureTransversalWithinBudget
      family canResolve (fun _ : I => 1) 2 := by
  refine ⟨({a,b} : Finset I), ?_, pair_hits_of_twoAtomComplete hcomplete⟩
  simp [SelectionCost, hab]

/-- REPAIR DIVERSITY THRESHOLD.
For two distinct unit-cost repair classes, if every obstruction is repairable
by at least one of them and the fracture family contains one obstruction
exclusive to each class, then the exact obstruction-transversal price is 2.

Thus the strict gap over the trivial one-atom bound is characterized by repair
diversity inside the obstruction family, not merely by the existence of damage.
-/
theorem exact_two_of_two_exclusive_repair_classes
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    {family : CertifiedFractureFamily before after target}
    {canResolve : Finset Q → Finset I}
    {a b : I}
    (hab : a ≠ b)
    (hcomplete : TwoAtomComplete family canResolve a b)
    (ha : ExclusiveRepairWitness family canResolve a)
    (hb : ExclusiveRepairWitness family canResolve b)
    (htrans :
      HasFractureTransversal family canResolve (fun _ : I => 1)) :
    FractureTransversalPrice
      family canResolve (fun _ : I => 1) htrans = 2 := by
  apply Nat.le_antisymm
  · apply fractureTransversalPrice_minimal
    exact two_atom_unit_transversal_within_two hab hcomplete
  ·
    rcases fractureTransversalPrice_spec
      family canResolve (fun _ : I => 1) htrans with ⟨H, hcost, hhit⟩
    exact Nat.le_trans
      (unit_cost_at_least_two_of_exclusive_witnesses hab ha hb hhit)
      hcost

/-- London-type collapse: if one atom is present in the repair capability of
every obstruction, the family has a unit-cost transversal at budget 1. -/
theorem universal_atom_gives_unit_transversal
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : FutureRobustness.ContractComplex Q}
    {target : Finset Q}
    {family : CertifiedFractureFamily before after target}
    {canResolve : Finset Q → Finset I}
    {a : I}
    (huniv : ∀ F, F ∈ family.obstructions → a ∈ canResolve F) :
    FractureTransversalWithinBudget
      family canResolve (fun _ : I => 1) 1 := by
  refine ⟨({a} : Finset I), ?_, ?_⟩
  · simp [SelectionCost]
  · intro F hF
    exact ⟨a, by simp, huniv F hF⟩

end RepairDiversityThreshold
end InsacermoActionabilityInformation
