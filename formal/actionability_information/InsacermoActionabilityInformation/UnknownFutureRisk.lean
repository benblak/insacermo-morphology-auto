import InsacermoActionabilityInformation.UnknownFutureRobustness

namespace InsacermoActionabilityInformation

namespace UnknownFutureRisk

open FutureRobustness
open FutureDepthSpectrum
open EventualFutureGeometry
open FutureTransformationCalculus
open UnknownFutureRobustness

/-- Threshold availability is monotone in the finite horizon. -/
theorem depthAtMost_mono_horizon
    {d : DepthValue} {H : ℕ}
    (h : DepthAtMost d H) :
    DepthAtMost d (H + 1) := by
  cases d with
  | finite n =>
      change n ≤ H at h
      change n ≤ H + 1
      exact Nat.le_trans h (Nat.le_succ H)
  | infinite =>
      change False at h
      contradiction

/-- Unnormalised total mass assigned to a declared family Γ of possible future
bundles.  Normalisation is intentionally not required by the structural kernel. -/
noncomputable def FutureFamilyMass
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (μ : Finset Q → ℝ) (Γ : Set (Finset Q)) : ℝ :=
  WeightedMass μ Γ

/-- Mass of possible future bundles whose recovery depth is at most H. -/
noncomputable def SurvivalMassAtHorizon
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (μ : Finset Q → ℝ) (Γ : Set (Finset Q))
    (S : Finset Q → DepthValue) (H : ℕ) : ℝ :=
  WeightedMass μ {F | F ∈ Γ ∧ DepthAtMost (S F) H}

/-- Mass of possible future bundles that miss deadline H. -/
noncomputable def DeadlineRiskMass
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (μ : Finset Q → ℝ) (Γ : Set (Finset Q))
    (S : Finset Q → DepthValue) (H : ℕ) : ℝ :=
  WeightedMass μ {F | F ∈ Γ ∧ ¬ DepthAtMost (S F) H}

/-- Mass of possible future bundles with infinite recovery depth. -/
noncomputable def IrreversibleRiskMass
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (μ : Finset Q → ℝ) (Γ : Set (Finset Q))
    (S : Finset Q → DepthValue) : ℝ :=
  WeightedMass μ {F | F ∈ Γ ∧ S F = .infinite}

/-- Mass of possible future bundles that remain eventually recoverable. -/
noncomputable def EventualSurvivalMass
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (μ : Finset Q → ℝ) (Γ : Set (Finset Q))
    (S : Finset Q → DepthValue) : ℝ :=
  WeightedMass μ {F | F ∈ Γ ∧ ∃ d, S F = .finite d}

/-- Every irreversibly lost future also misses every finite deadline. -/
theorem irreversibleRisk_le_deadlineRisk
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {μ : Finset Q → ℝ} {Γ : Set (Finset Q)}
    {S : Finset Q → DepthValue} {H : ℕ}
    (hμ : ∀ F, 0 ≤ μ F) :
    IrreversibleRiskMass μ Γ S ≤ DeadlineRiskMass μ Γ S H := by
  unfold IrreversibleRiskMass DeadlineRiskMass
  apply weightedMass_mono hμ
  intro F hF
  rcases hF with ⟨hΓ, hinf⟩
  refine ⟨hΓ, ?_⟩
  intro hH
  rw [hinf] at hH
  simpa [DepthAtMost] using hH

/-- Allowing one more recovery step cannot increase deadline risk. -/
theorem deadlineRiskMass_antitone_horizon
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {μ : Finset Q → ℝ} {Γ : Set (Finset Q)}
    {S : Finset Q → DepthValue} {H : ℕ}
    (hμ : ∀ F, 0 ≤ μ F) :
    DeadlineRiskMass μ Γ S (H + 1) ≤ DeadlineRiskMass μ Γ S H := by
  unfold DeadlineRiskMass
  apply weightedMass_mono hμ
  intro F hF
  rcases hF with ⟨hΓ, hlate⟩
  refine ⟨hΓ, ?_⟩
  intro hH
  apply hlate
  exact depthAtMost_mono_horizon hH

/-- More time cannot decrease the mass of futures that can be recovered by the
declared deadline. -/
theorem survivalMassAtHorizon_mono
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {μ : Finset Q → ℝ} {Γ : Set (Finset Q)}
    {S : Finset Q → DepthValue} {H : ℕ}
    (hμ : ∀ F, 0 ≤ μ F) :
    SurvivalMassAtHorizon μ Γ S H ≤
      SurvivalMassAtHorizon μ Γ S (H + 1) := by
  unfold SurvivalMassAtHorizon
  apply weightedMass_mono hμ
  intro F hF
  exact ⟨hF.1, depthAtMost_mono_horizon hF.2⟩

/-- Spectrum non-worsening cannot increase deadline risk for any nonnegative
finite future law and any declared family Γ. -/
theorem deadlineRiskMass_antitone_nonWorsening
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {μ : Finset Q → ℝ} {Γ : Set (Finset Q)}
    {before after : Finset Q → DepthValue} {H : ℕ}
    (hμ : ∀ F, 0 ≤ μ F)
    (h : SpectrumNonWorsening before after) :
    DeadlineRiskMass μ Γ after H ≤
      DeadlineRiskMass μ Γ before H := by
  unfold DeadlineRiskMass
  apply weightedMass_mono hμ
  intro F hF
  rcases hF with ⟨hΓ, hafterLate⟩
  refine ⟨hΓ, ?_⟩
  intro hbefore
  exact hafterLate (nonWorsening_preserves_horizon_availability h hbefore)

/-- Spectrum non-worsening cannot increase irreversible future-risk mass. -/
theorem irreversibleRiskMass_antitone_nonWorsening
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {μ : Finset Q → ℝ} {Γ : Set (Finset Q)}
    {before after : Finset Q → DepthValue}
    (hμ : ∀ F, 0 ≤ μ F)
    (h : SpectrumNonWorsening before after) :
    IrreversibleRiskMass μ Γ after ≤
      IrreversibleRiskMass μ Γ before := by
  unfold IrreversibleRiskMass
  apply weightedMass_mono hμ
  intro F hF
  rcases hF with ⟨hΓ, hafterInf⟩
  refine ⟨hΓ, ?_⟩
  cases hbefore : before F with
  | finite d =>
      have hfinBefore : ∃ d, before F = .finite d := ⟨d, hbefore⟩
      have hfinAfter := nonWorsening_preserves_eventual_finiteness h hfinBefore
      rcases hfinAfter with ⟨e, he⟩
      rw [hafterInf] at he
      cases he
  | infinite =>
      rfl

/-- Spectrum non-worsening cannot decrease eventual future-survival mass. -/
theorem eventualSurvivalMass_mono_nonWorsening
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {μ : Finset Q → ℝ} {Γ : Set (Finset Q)}
    {before after : Finset Q → DepthValue}
    (hμ : ∀ F, 0 ≤ μ F)
    (h : SpectrumNonWorsening before after) :
    EventualSurvivalMass μ Γ before ≤
      EventualSurvivalMass μ Γ after := by
  unfold EventualSurvivalMass
  apply weightedMass_mono hμ
  intro F hF
  rcases hF with ⟨hΓ, hfinite⟩
  exact ⟨hΓ, nonWorsening_preserves_eventual_finiteness h hfinite⟩

/-- Concrete adapter: deadline risk for a state x is just the risk mass of its
joint future-depth spectrum. -/
noncomputable def StateDeadlineRiskMass
    {Q X : Type*} [Fintype Q] [DecidableEq Q]
    (μ : Finset Q → ℝ) (Γ : Set (Finset Q))
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (H : ℕ) : ℝ :=
  DeadlineRiskMass μ Γ (Spectrum Avail Step x) H

/-- Concrete adapter: irreversible risk for a state x. -/
noncomputable def StateIrreversibleRiskMass
    {Q X : Type*} [Fintype Q] [DecidableEq Q]
    (μ : Finset Q → ℝ) (Γ : Set (Finset Q))
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) : ℝ :=
  IrreversibleRiskMass μ Γ (Spectrum Avail Step x)

end UnknownFutureRisk

end InsacermoActionabilityInformation
