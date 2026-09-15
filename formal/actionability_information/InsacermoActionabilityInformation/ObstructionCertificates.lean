import InsacermoActionabilityInformation.BiMonotone

namespace InsacermoActionabilityInformation

/-- Safety implies that every world in the ambiguity set has at least one
currently available Good action. -/
theorem safeRep_implies_world_actionable
    {S A Y : Type*}
    {Good : S → A → Prop} {B : Set S} {C : Set A} {h : S → Y}
    (hsafe : SafeRep Good B C h)
    {s : S} (hsB : s ∈ B) :
    ∃ a, a ∈ C ∧ Good s a := by
  have hreal : ∃ t, t ∈ B ∧ h t = h s := ⟨s, hsB, rfl⟩
  rcases hsafe (h s) hreal with ⟨a, haC, hgood⟩
  exact ⟨a, haC, hgood s hsB rfl⟩

/-- Capability-hole certificate: if one admissible world has no Good action
in the current capability set, then no representation can be safe. -/
theorem capabilityHole_blocks_safeRep
    {S A Y : Type*}
    {Good : S → A → Prop} {B : Set S} {C : Set A} {h : S → Y}
    {s : S} (hsB : s ∈ B)
    (hno : ∀ a, a ∈ C → ¬ Good s a) :
    ¬ SafeRep Good B C h := by
  intro hsafe
  rcases safeRep_implies_world_actionable hsafe hsB with ⟨a, haC, hgood⟩
  exact (hno a haC) hgood

/-- If two admissible worlds receive the same code under a safe
representation, they must share at least one currently available Good action. -/
theorem safeRep_implies_aliased_pair_compatible
    {S A Y : Type*}
    {Good : S → A → Prop} {B : Set S} {C : Set A} {h : S → Y}
    (hsafe : SafeRep Good B C h)
    {s t : S} (hsB : s ∈ B) (htB : t ∈ B)
    (halias : h s = h t) :
    ∃ a, a ∈ C ∧ Good s a ∧ Good t a := by
  have hreal : ∃ u, u ∈ B ∧ h u = h s := ⟨s, hsB, rfl⟩
  rcases hsafe (h s) hreal with ⟨a, haC, hgood⟩
  refine ⟨a, haC, hgood s hsB rfl, ?_⟩
  exact hgood t htB halias.symm

/-- Aliasing certificate: two admissible worlds with the same code and no
common available Good action make that representation unsafe. -/
theorem aliasedIncompatiblePair_blocks_safeRep
    {S A Y : Type*}
    {Good : S → A → Prop} {B : Set S} {C : Set A} {h : S → Y}
    {s t : S} (hsB : s ∈ B) (htB : t ∈ B)
    (halias : h s = h t)
    (hincompat : ∀ a, a ∈ C → ¬ (Good s a ∧ Good t a)) :
    ¬ SafeRep Good B C h := by
  intro hsafe
  rcases safeRep_implies_aliased_pair_compatible hsafe hsB htB halias with
    ⟨a, haC, hgs, hgt⟩
  exact (hincompat a haC) ⟨hgs, hgt⟩

/-- Contrapositive of information monotonicity: if a finer representation is
already unsafe, every representation it refines is unsafe as well. -/
theorem unsafeFine_blocks_coarsening
    {S A YFine YCoarse : Type*}
    {Good : S → A → Prop} {B : Set S} {C : Set A}
    {fine : S → YFine} {coarse : S → YCoarse}
    (hunsafe : ¬ SafeRep Good B C fine)
    (href : Refines fine coarse) :
    ¬ SafeRep Good B C coarse := by
  intro hcoarse
  exact hunsafe (safeRep_information_mono hcoarse href)

/-- Full-probe obstruction certificate. If the finest allowed observation map
aliases one incompatible pair, then every allowed representation obtained by
coarsening that full observation map is unsafe. -/
theorem fullProbeAlias_blocks_all_coarsenings
    {S A YFull YCoarse : Type*}
    {Good : S → A → Prop} {B : Set S} {C : Set A}
    {full : S → YFull} {coarse : S → YCoarse}
    {s t : S} (hsB : s ∈ B) (htB : t ∈ B)
    (halias : full s = full t)
    (hincompat : ∀ a, a ∈ C → ¬ (Good s a ∧ Good t a))
    (href : Refines full coarse) :
    ¬ SafeRep Good B C coarse := by
  apply unsafeFine_blocks_coarsening
  · exact aliasedIncompatiblePair_blocks_safeRep hsB htB halias hincompat
  · exact href

end InsacermoActionabilityInformation
