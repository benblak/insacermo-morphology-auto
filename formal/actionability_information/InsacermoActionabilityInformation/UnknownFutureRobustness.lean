import InsacermoActionabilityInformation.FutureRepairPrice

namespace InsacermoActionabilityInformation

namespace UnknownFutureRobustness

open TemporalObstructionPersistence
open FutureDepthSpectrum
open EventualFutureGeometry

/-- A family of possible future contracts is safe by horizon H when every
bundle that might become exigible has joint recovery depth at most H. -/
def FamilySafeAtHorizon
    {Q X : Type*} [DecidableEq Q]
    (Γ : Set (Finset Q))
    (Avail : X → Set Q) (Step : X → X → Prop)
    (H : ℕ) (x : X) : Prop :=
  ∀ F, F ∈ Γ → DepthAtMost (Spectrum Avail Step x F) H

/-- A family of possible future contracts is eventually safe when every bundle
that might become exigible is jointly recoverable at some finite horizon. -/
def FamilyEventuallySafe
    {Q X : Type*} [DecidableEq Q]
    (Γ : Set (Finset Q))
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) : Prop :=
  ∀ F, F ∈ Γ → (EventualFutureComplex Avail Step x).feasible F

/-- The set of all finite bundles that remain eventually recoverable from x. -/
def EventualFeasibleBundles
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) : Set (Finset Q) :=
  {F | (EventualFutureComplex Avail Step x).feasible F}

/-- The family formulation is exactly set inclusion in the eventual future
complex. -/
theorem familyEventuallySafe_iff_subset_eventualFeasibleBundles
    {Q X : Type*} [DecidableEq Q]
    {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} :
    FamilyEventuallySafe Γ Avail Step x ↔
      Γ ⊆ EventualFeasibleBundles Avail Step x := by
  rfl

/-- A family contains an irreversible bundle when one possible future has
infinite joint recovery depth. -/
def FamilyHasIrreversibleBundle
    {Q X : Type*} [DecidableEq Q]
    (Γ : Set (Finset Q))
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) : Prop :=
  ∃ F, F ∈ Γ ∧ JointIrreversible Avail Step x F

/-- Exact robust unknown-future law: every possible bundle is eventually safe
iff no possible bundle is jointly irreversible. -/
theorem familyEventuallySafe_iff_no_irreversibleBundle
    {Q X : Type*} [DecidableEq Q]
    {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} :
    FamilyEventuallySafe Γ Avail Step x ↔
      ¬ FamilyHasIrreversibleBundle Γ Avail Step x := by
  constructor
  · intro hsafe hbad
    rcases hbad with ⟨F, hFΓ, hirr⟩
    have hfinite : (EventualFutureComplex Avail Step x).feasible F :=
      hsafe F hFΓ
    exact (jointIrreversible_iff_not_hasFiniteJointRecoveryDepth).1 hirr hfinite
  · intro hno F hFΓ
    by_contra hnot
    have hirr : JointIrreversible Avail Step x F :=
      (jointIrreversible_iff_not_hasFiniteJointRecoveryDepth).2 hnot
    exact hno ⟨F, hFΓ, hirr⟩

/-- A finite deadline guarantee is stronger than eventual safety. -/
theorem familySafeAtHorizon_implies_eventuallySafe
    {Q X : Type*} [DecidableEq Q]
    {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X}
    (h : FamilySafeAtHorizon Γ Avail Step H x) :
    FamilyEventuallySafe Γ Avail Step x := by
  intro F hFΓ
  have hdepth : DepthAtMost (Spectrum Avail Step x F) H := h F hFΓ
  apply (eventualFutureComplex_feasible_iff_spectrum_finite).2
  cases hs : Spectrum Avail Step x F with
  | finite d =>
      exact ⟨d, rfl⟩
  | infinite =>
      rw [hs] at hdepth
      simp [DepthAtMost] at hdepth

/-- Enlarging the declared family of possible futures can only make a robust
guarantee harder. Equivalently, any guarantee for Γ also guarantees every
subfamily Γ'. -/
theorem familyEventuallySafe_mono_family
    {Q X : Type*} [DecidableEq Q]
    {Γ Γ' : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X}
    (hsub : Γ' ⊆ Γ)
    (hsafe : FamilyEventuallySafe Γ Avail Step x) :
    FamilyEventuallySafe Γ' Avail Step x := by
  intro F hFΓ'
  exact hsafe F (hsub hFΓ')

/-- The same antitonicity in the family holds at every declared deadline. -/
theorem familySafeAtHorizon_mono_family
    {Q X : Type*} [DecidableEq Q]
    {Γ Γ' : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X}
    (hsub : Γ' ⊆ Γ)
    (hsafe : FamilySafeAtHorizon Γ Avail Step H x) :
    FamilySafeAtHorizon Γ' Avail Step H x := by
  intro F hFΓ'
  exact hsafe F (hsub hFΓ')

/-- A transformation is absolutely admissible for an unknown family Γ when,
after applying it, every future in Γ still has finite joint recovery depth. -/
def RobustlyAdmissibleEventually
    {Q X : Type*} [DecidableEq Q]
    (Γ : Set (Finset Q))
    (Avail : X → Set Q) (Step : X → X → Prop)
    (T : X → X) (x : X) : Prop :=
  FamilyEventuallySafe Γ Avail Step (T x)

/-- Deadline version of robust admissibility. -/
def RobustlyAdmissibleAtHorizon
    {Q X : Type*} [DecidableEq Q]
    (Γ : Set (Finset Q))
    (Avail : X → Set Q) (Step : X → X → Prop)
    (H : ℕ) (T : X → X) (x : X) : Prop :=
  FamilySafeAtHorizon Γ Avail Step H (T x)

/-- A transformation preserves a possible future family relative to the current
state when every Γ-bundle that was eventually feasible before remains so after. -/
def PreservesFamilyEventually
    {Q X : Type*} [DecidableEq Q]
    (Γ : Set (Finset Q))
    (Avail : X → Set Q) (Step : X → X → Prop)
    (before after : X) : Prop :=
  ∀ F, F ∈ Γ →
    (EventualFutureComplex Avail Step before).feasible F →
    (EventualFutureComplex Avail Step after).feasible F

/-- If Γ is already eventually safe before a transformation, then relative
preservation of Γ is exactly absolute eventual safety after the transformation. -/
theorem preservesFamilyEventually_iff_after_safe_of_before_safe
    {Q X : Type*} [DecidableEq Q]
    {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {before after : X}
    (hbefore : FamilyEventuallySafe Γ Avail Step before) :
    PreservesFamilyEventually Γ Avail Step before after ↔
      FamilyEventuallySafe Γ Avail Step after := by
  constructor
  · intro hpres F hFΓ
    exact hpres F hFΓ (hbefore F hFΓ)
  · intro hafter F hFΓ _
    exact hafter F hFΓ

/-- A transformation destroys some possible future in Γ exactly when there is
a Γ-bundle that was eventually feasible before and is not eventually feasible
after. -/
def DestroysPossibleFuture
    {Q X : Type*} [DecidableEq Q]
    (Γ : Set (Finset Q))
    (Avail : X → Set Q) (Step : X → X → Prop)
    (before after : X) : Prop :=
  ∃ F, F ∈ Γ ∧
    (EventualFutureComplex Avail Step before).feasible F ∧
    ¬ (EventualFutureComplex Avail Step after).feasible F

/-- Relative preservation is exactly absence of destruction inside Γ. -/
theorem preservesFamilyEventually_iff_not_destroysPossibleFuture
    {Q X : Type*} [DecidableEq Q]
    {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {before after : X} :
    PreservesFamilyEventually Γ Avail Step before after ↔
      ¬ DestroysPossibleFuture Γ Avail Step before after := by
  constructor
  · intro hpres hdest
    rcases hdest with ⟨F, hFΓ, hbefore, hafter⟩
    exact hafter (hpres F hFΓ hbefore)
  · intro hno F hFΓ hbefore
    by_contra hafter
    exact hno ⟨F, hFΓ, hbefore, hafter⟩

/-- Under an absolute pre-transformation guarantee for Γ, a transformation is
robustly admissible exactly when it destroys no possible future in Γ. -/
theorem robustlyAdmissibleEventually_iff_not_destroys_of_before_safe
    {Q X : Type*} [DecidableEq Q]
    {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {T : X → X} {x : X}
    (hbefore : FamilyEventuallySafe Γ Avail Step x) :
    RobustlyAdmissibleEventually Γ Avail Step T x ↔
      ¬ DestroysPossibleFuture Γ Avail Step x (T x) := by
  unfold RobustlyAdmissibleEventually
  rw [← preservesFamilyEventually_iff_after_safe_of_before_safe hbefore]
  exact preservesFamilyEventually_iff_not_destroysPossibleFuture

end UnknownFutureRobustness

end InsacermoActionabilityInformation
