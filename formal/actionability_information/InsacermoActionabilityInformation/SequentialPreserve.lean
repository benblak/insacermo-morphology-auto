import InsacermoActionabilityInformation.BiMonotone

namespace InsacermoActionabilityInformation

/-- Effective capability set after capability availability, governance admissibility,
and a resource/cost budget have all been applied. -/
def EffectiveCaps {A R : Type*} [LE R]
    (C G : Set A) (cost : A → R) (budget : R) : Set A :=
  {a | a ∈ C ∧ a ∈ G ∧ cost a ≤ budget}

/-- Enlarging available capabilities, relaxing governance, or increasing budget
can only enlarge the effective capability set. -/
theorem effectiveCaps_mono
    {A R : Type*} [Preorder R]
    {C C' G G' : Set A} {cost : A → R} {budget budget' : R}
    (hC : C ⊆ C') (hG : G ⊆ G') (hB : budget ≤ budget') :
    EffectiveCaps C G cost budget ⊆ EffectiveCaps C' G' cost budget' := by
  intro a ha
  change a ∈ C ∧ a ∈ G ∧ cost a ≤ budget at ha
  change a ∈ C' ∧ a ∈ G' ∧ cost a ≤ budget'
  exact ⟨hC ha.1, hG ha.2.1, le_trans ha.2.2 hB⟩

/-- Product monotonicity extended with resource budget and governance.
If the old coarse representation was safe, then a finer representation remains
safe after capability/governance enlargement and a weakly larger budget. -/
theorem safeRep_of_refines_of_effectiveCaps_mono
    {S A YFine YCoarse R : Type*} [Preorder R]
    {Good : S → A → Prop} {B : Set S}
    {C C' G G' : Set A} {cost : A → R} {budget budget' : R}
    {fine : S → YFine} {coarse : S → YCoarse}
    (hsafe : SafeRep Good B (EffectiveCaps C G cost budget) coarse)
    (href : Refines fine coarse)
    (hC : C ⊆ C') (hG : G ⊆ G') (hB : budget ≤ budget') :
    SafeRep Good B (EffectiveCaps C' G' cost budget') fine := by
  apply safeRep_of_refines_of_capabilitySubset hsafe href
  exact effectiveCaps_mono hC hG hB

/-- A schedule of future contracts is safe for a representation when the
representation is safe at every indexed future stage after capability,
governance, and resource constraints are applied. -/
def FutureSafe
    {T S A Y R : Type*} [Preorder R]
    (Good : T → S → A → Prop)
    (B : T → Set S)
    (C G : T → Set A)
    (cost : T → A → R)
    (budget : T → R)
    (h : S → Y) : Prop :=
  ∀ t, SafeRep (Good t) (B t)
    (EffectiveCaps (C t) (G t) (cost t) (budget t)) h

/-- Future safety is monotone pointwise in the same product order: finer
information, more capabilities, weaker governance restriction, and more budget
cannot destroy already-established future safety. -/
theorem futureSafe_mono
    {T S A YFine YCoarse R : Type*} [Preorder R]
    {Good : T → S → A → Prop}
    {B : T → Set S}
    {C C' G G' : T → Set A}
    {cost : T → A → R}
    {budget budget' : T → R}
    {fine : S → YFine} {coarse : S → YCoarse}
    (hsafe : FutureSafe Good B C G cost budget coarse)
    (href : Refines fine coarse)
    (hC : ∀ t, C t ⊆ C' t)
    (hG : ∀ t, G t ⊆ G' t)
    (hB : ∀ t, budget t ≤ budget' t) :
    FutureSafe Good B C' G' cost budget' fine := by
  intro t
  exact safeRep_of_refines_of_effectiveCaps_mono
    (hsafe t) href (hC t) (hG t) (hB t)

/-- A legal forgetting step: `fine` may be replaced by the coarser `coarse`
only when the coarse representation remains safe for every declared future
contract. This is the static core of PRESERVE. -/
def PreserveTransition
    {T S A YFine YCoarse R : Type*} [Preorder R]
    (Good : T → S → A → Prop)
    (B : T → Set S)
    (C G : T → Set A)
    (cost : T → A → R)
    (budget : T → R)
    (fine : S → YFine)
    (coarse : S → YCoarse) : Prop :=
  Refines fine coarse ∧ FutureSafe Good B C G cost budget coarse

/-- A PRESERVE-approved transition certifies the future safety of the retained
(coarser) representation by definition. -/
theorem preserveTransition_target_futureSafe
    {T S A YFine YCoarse R : Type*} [Preorder R]
    {Good : T → S → A → Prop}
    {B : T → Set S}
    {C G : T → Set A}
    {cost : T → A → R}
    {budget : T → R}
    {fine : S → YFine} {coarse : S → YCoarse}
    (h : PreserveTransition Good B C G cost budget fine coarse) :
    FutureSafe Good B C G cost budget coarse :=
  h.2

/-- If a forgetting step is PRESERVE-approved, then the original finer
representation was also safe for all declared futures. -/
theorem preserveTransition_source_futureSafe
    {T S A YFine YCoarse R : Type*} [Preorder R]
    {Good : T → S → A → Prop}
    {B : T → Set S}
    {C G : T → Set A}
    {cost : T → A → R}
    {budget : T → R}
    {fine : S → YFine} {coarse : S → YCoarse}
    (h : PreserveTransition Good B C G cost budget fine coarse) :
    FutureSafe Good B C G cost budget fine := by
  exact futureSafe_mono h.2 h.1
    (fun _ => Set.Subset.rfl)
    (fun _ => Set.Subset.rfl)
    (fun _ => le_rfl)

namespace PreserveWitness

open ProbeRepairWitness

abbrev Time := Unit

private def futureGood : Time → World → Action → Prop := fun _ => Good
private def futureB : Time → Set World := fun _ => Set.univ
private def futureC : Time → Set Action := fun _ => baseCaps
private def futureG : Time → Set Action := fun _ => Set.univ
private def futureCost : Time → Action → Nat := fun _ _ => 0
private def futureBudget : Time → Nat := fun _ => 0

theorem fine_future_safe :
    FutureSafe futureGood futureB futureC futureG futureCost futureBudget fineObs := by
  intro t
  cases t
  simpa [futureGood, futureB, futureC, futureG, futureCost, futureBudget,
    EffectiveCaps] using probe_route_safe

theorem coarse_future_not_safe :
    ¬ FutureSafe futureGood futureB futureC futureG futureCost futureBudget coarseObs := by
  intro h
  have hs := h ()
  apply baseline_not_safe
  simpa [futureGood, futureB, futureC, futureG, futureCost, futureBudget,
    EffectiveCaps] using hs

/-- Concrete information-debt witness for PRESERVE: the fine representation is
future-safe and genuinely refines the coarse one, but forgetting to the coarse
representation is not a legal PRESERVE transition. -/
theorem unsafe_forgetting_is_rejected :
    Refines fineObs coarseObs ∧
    FutureSafe futureGood futureB futureC futureG futureCost futureBudget fineObs ∧
    ¬ PreserveTransition futureGood futureB futureC futureG futureCost futureBudget
      fineObs coarseObs := by
  refine ⟨fine_refines_coarse, fine_future_safe, ?_⟩
  intro h
  exact coarse_future_not_safe h.2

end PreserveWitness

end InsacermoActionabilityInformation
