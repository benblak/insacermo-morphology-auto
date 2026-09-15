import InsacermoActionabilityInformation.FutureEnvelope

namespace InsacermoActionabilityInformation

namespace FutureDebt

open FutureEnvelope

/-- Required futures that are not currently guaranteed. -/
def Debt {Q S A Y : Type*}
    (Good : Q → S → A → Prop) (Req : Set Q)
    (B : Set S) (C : Set A) (h : S → Y) : Set Q :=
  Req \ Envelope Good B C h

/-- Zero future debt is exactly full guarantee of the required future family. -/
theorem debt_eq_empty_iff_guarantees
    {Q S A Y : Type*}
    {Good : Q → S → A → Prop} {Req : Set Q}
    {B : Set S} {C : Set A} {h : S → Y} :
    Debt Good Req B C h = ∅ ↔ Guarantees Good Req B C h := by
  constructor
  · intro hzero q hq
    by_contra hnot
    have hmem : q ∈ Debt Good Req B C h := ⟨hq, hnot⟩
    have : q ∈ (∅ : Set Q) := by simpa [hzero] using hmem
    exact this.elim
  · intro hguar
    ext q
    constructor
    · intro hq
      exact False.elim (hq.2 (hguar hq.1))
    · intro hq
      simp at hq

/-- PROBE and/or REPAIR cannot increase future debt. -/
theorem debt_antitone_of_refines_of_capabilitySubset
    {Q S A YFine YCoarse : Type*}
    {Good : Q → S → A → Prop} {Req : Set Q} {B : Set S}
    {C C' : Set A} {fine : S → YFine} {coarse : S → YCoarse}
    (href : Refines fine coarse) (hcap : C ⊆ C') :
    Debt Good Req B C' fine ⊆ Debt Good Req B C coarse := by
  intro q hq
  refine ⟨hq.1, ?_⟩
  intro hqOld
  exact hq.2 ((FutureEnvelope.envelope_mono_of_refines_of_capabilitySubset href hcap) hqOld)

/-- Information refinement alone cannot increase debt. -/
theorem debt_probe_antitone
    {Q S A YFine YCoarse : Type*}
    {Good : Q → S → A → Prop} {Req : Set Q} {B : Set S} {C : Set A}
    {fine : S → YFine} {coarse : S → YCoarse}
    (href : Refines fine coarse) :
    Debt Good Req B C fine ⊆ Debt Good Req B C coarse := by
  exact debt_antitone_of_refines_of_capabilitySubset href Set.Subset.rfl

/-- Capability expansion alone cannot increase debt. -/
theorem debt_repair_antitone
    {Q S A Y : Type*}
    {Good : Q → S → A → Prop} {Req : Set Q} {B : Set S}
    {C C' : Set A} {h : S → Y}
    (hcap : C ⊆ C') :
    Debt Good Req B C' h ⊆ Debt Good Req B C h := by
  exact debt_antitone_of_refines_of_capabilitySubset
    (fine := h) (coarse := h) ⟨id, by intro s; rfl⟩ hcap

/-- A transition is future-preserving for the required family exactly when
none of the currently guaranteed required futures are lost. -/
def PreservesRequired {Q S A Y₀ Y₁ : Type*}
    (Good : Q → S → A → Prop) (Req : Set Q) (B : Set S)
    (C₀ C₁ : Set A) (h₀ : S → Y₀) (h₁ : S → Y₁) : Prop :=
  Req ∩ LostFutures Good B C₀ C₁ h₀ h₁ = ∅

/-- Any PROBE/REPAIR transition preserves all required futures. -/
theorem probeRepair_preservesRequired
    {Q S A YFine YCoarse : Type*}
    {Good : Q → S → A → Prop} {Req : Set Q} {B : Set S}
    {C C' : Set A} {fine : S → YFine} {coarse : S → YCoarse}
    (href : Refines fine coarse) (hcap : C ⊆ C') :
    PreservesRequired Good Req B C C' coarse fine := by
  unfold PreservesRequired
  rw [FutureEnvelope.no_lost_futures_of_refines_of_capabilitySubset href hcap]
  simp

/-- If a transition preserves every required future and there was zero debt
before the transition, then there is still zero debt afterwards. -/
theorem zeroDebt_preserved_of_preservesRequired
    {Q S A Y₀ Y₁ : Type*}
    {Good : Q → S → A → Prop} {Req : Set Q} {B : Set S}
    {C₀ C₁ : Set A} {h₀ : S → Y₀} {h₁ : S → Y₁}
    (hzero : Debt Good Req B C₀ h₀ = ∅)
    (hpres : PreservesRequired Good Req B C₀ C₁ h₀ h₁) :
    Debt Good Req B C₁ h₁ = ∅ := by
  have hguar0 : Guarantees Good Req B C₀ h₀ :=
    (debt_eq_empty_iff_guarantees).mp hzero
  apply (debt_eq_empty_iff_guarantees).mpr
  intro q hq
  by_contra hnotNew
  have hqOld : q ∈ Envelope Good B C₀ h₀ := hguar0 hq
  have hLost : q ∈ LostFutures Good B C₀ C₁ h₀ h₁ := ⟨hqOld, hnotNew⟩
  have hInt : q ∈ Req ∩ LostFutures Good B C₀ C₁ h₀ h₁ := ⟨hq, hLost⟩
  rw [hpres] at hInt
  exact hInt.elim

end FutureDebt

end InsacermoActionabilityInformation
