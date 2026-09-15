import InsacermoActionabilityInformation.ObstructionCertificates

namespace InsacermoActionabilityInformation

/-- Deterministic contract: each world has exactly one Good action, namely
`label s`. -/
def DeterministicGood {S A : Type*} (label : S → A) : S → A → Prop :=
  fun s a => a = label s

/-- Exact criterion for deterministic contracts. Assuming every required
label is actually available in the capability set, a representation is safe
iff the required action is constant on every realized observation fiber. -/
theorem safeRep_deterministic_iff_fiberConstant
    {S A Y : Type*}
    {B : Set S} {C : Set A} {h : S → Y} {label : S → A}
    (hcap : ∀ s, s ∈ B → label s ∈ C) :
    SafeRep (DeterministicGood label) B C h ↔
      ∀ s, s ∈ B → ∀ t, t ∈ B → h s = h t → label s = label t := by
  constructor
  · intro hsafe s hsB t htB halias
    have hreal : ∃ u, u ∈ B ∧ h u = h s := ⟨s, hsB, rfl⟩
    rcases hsafe (h s) hreal with ⟨a, haC, hgood⟩
    have hgs : a = label s := hgood s hsB rfl
    have hgt : a = label t := hgood t htB halias.symm
    exact hgs.symm.trans hgt
  · intro hfiber y hy
    rcases hy with ⟨s0, hs0B, hs0y⟩
    refine ⟨label s0, hcap s0 hs0B, ?_⟩
    intro s hsB hsy
    change label s0 = label s
    apply hfiber s0 hs0B s hsB
    exact hs0y.trans hsy.symm

/-- Under a deterministic contract with all labels available, one
cross-label collision is an exact local certificate of unsafety. -/
theorem deterministic_crossLabel_alias_blocks_safeRep
    {S A Y : Type*}
    {B : Set S} {C : Set A} {h : S → Y} {label : S → A}
    (hcap : ∀ s, s ∈ B → label s ∈ C)
    {s t : S} (hsB : s ∈ B) (htB : t ∈ B)
    (halias : h s = h t) (hdiff : label s ≠ label t) :
    ¬ SafeRep (DeterministicGood label) B C h := by
  intro hsafe
  have hfiber := (safeRep_deterministic_iff_fiberConstant hcap).mp hsafe
  exact hdiff (hfiber s hsB t htB halias)

/-- Full-observation deterministic obstruction: if the finest allowed probe
map aliases two admissible worlds that require different actions, then every
allowed coarsening is unsafe. -/
theorem deterministic_fullProbe_collision_blocks_all_coarsenings
    {S A YFull YCoarse : Type*}
    {B : Set S} {C : Set A}
    {full : S → YFull} {coarse : S → YCoarse} {label : S → A}
    (hcap : ∀ s, s ∈ B → label s ∈ C)
    {s t : S} (hsB : s ∈ B) (htB : t ∈ B)
    (halias : full s = full t) (hdiff : label s ≠ label t)
    (href : Refines full coarse) :
    ¬ SafeRep (DeterministicGood label) B C coarse := by
  apply unsafeFine_blocks_coarsening
  · exact deterministic_crossLabel_alias_blocks_safeRep hcap hsB htB halias hdiff
  · exact href

end InsacermoActionabilityInformation
