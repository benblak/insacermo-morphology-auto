import InsacermoActionabilityInformation.TemporalJointFutureRisk

namespace InsacermoActionabilityInformation

namespace FutureDepthSpectrum

open FutureRobustness
open TemporalJointContractComplex
open TemporalObstructionPersistence
open TemporalJointFutureRisk

/-- Extended depth of a finite future bundle: either a first finite recovery
horizon, or infinity when no finite common plan can ever realize the bundle. -/
inductive DepthValue where
  | finite (d : ℕ)
  | infinite
  deriving DecidableEq

/-- Threshold predicate for extended future depth. -/
def DepthAtMost : DepthValue → ℕ → Prop
  | .finite d, H => d ≤ H
  | .infinite, _ => False

/-- Natural order on extended depths, with every finite depth below infinity. -/
def DepthLe : DepthValue → DepthValue → Prop
  | .finite d, .finite e => d ≤ e
  | .finite _, .infinite => True
  | .infinite, .finite _ => False
  | .infinite, .infinite => True

/-- The master future-depth spectrum of state `x`: each finite contract bundle
is assigned its first joint recovery horizon, or infinity if it is jointly
irreversible. -/
noncomputable def Spectrum
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (F : Finset Q) : DepthValue := by
  classical
  exact if hfinite : HasFiniteJointRecoveryDepth Avail Step x F then
    .finite (JointRecoveryDepth Avail Step x F hfinite)
  else
    .infinite

/-- Finite depth is exactly finite joint recoverability. -/
theorem spectrum_finite_iff_hasFiniteJointRecoveryDepth
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q} :
    (∃ d, Spectrum Avail Step x F = .finite d) ↔
      HasFiniteJointRecoveryDepth Avail Step x F := by
  classical
  by_cases hfinite : HasFiniteJointRecoveryDepth Avail Step x F
  · constructor
    · intro _
      exact hfinite
    · intro _
      refine ⟨JointRecoveryDepth Avail Step x F hfinite, ?_⟩
      simp [Spectrum, hfinite]
  · constructor
    · intro h
      rcases h with ⟨d, hd⟩
      simp [Spectrum, hfinite] at hd
    · intro h
      exact False.elim (hfinite h)

/-- Infinity in the spectrum is exactly joint irreversibility. -/
theorem spectrum_infinite_iff_jointIrreversible
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q} :
    Spectrum Avail Step x F = .infinite ↔
      JointIrreversible Avail Step x F := by
  classical
  by_cases hfinite : HasFiniteJointRecoveryDepth Avail Step x F
  · constructor
    · intro h
      simp [Spectrum, hfinite] at h
    · intro hirr
      have hnot : ¬ HasFiniteJointRecoveryDepth Avail Step x F :=
        (jointIrreversible_iff_not_hasFiniteJointRecoveryDepth).1 hirr
      exact False.elim (hnot hfinite)
  · constructor
    · intro _
      exact (jointIrreversible_iff_not_hasFiniteJointRecoveryDepth).2 hfinite
    · intro _
      simp [Spectrum, hfinite]

/-- Master sublevel representation: a bundle belongs to the temporal joint
contract complex at horizon `H` exactly when its spectrum depth is at most H. -/
theorem depthAtMost_spectrum_iff_feasible
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q} {H : ℕ} :
    DepthAtMost (Spectrum Avail Step x F) H ↔
      (TemporalContractComplex Avail Step H x).feasible F := by
  classical
  by_cases hfinite : HasFiniteJointRecoveryDepth Avail Step x F
  · rw [show Spectrum Avail Step x F =
        .finite (JointRecoveryDepth Avail Step x F hfinite) by
          simp [Spectrum, hfinite]]
    change JointRecoveryDepth Avail Step x F hfinite ≤ H ↔ _
    constructor
    · intro hle
      have hspec :
          (TemporalContractComplex Avail Step
            (JointRecoveryDepth Avail Step x F hfinite) x).feasible F :=
        jointRecoveryDepth_spec hfinite
      exact temporalContractComplex_mono_of_le hle hspec
    · intro hH
      exact jointRecoveryDepth_minimal hfinite hH
  · rw [show Spectrum Avail Step x F = .infinite by
          simp [Spectrum, hfinite]]
    change False ↔ _
    constructor
    · intro h
      exact False.elim h
    · intro hH
      exact False.elim (hfinite ⟨H, hH⟩)

/-- Equivalent orientation: the whole temporal filtration is recovered as the
sublevel filtration of the single depth spectrum. -/
theorem feasible_iff_depthAtMost_spectrum
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q} {H : ℕ} :
    (TemporalContractComplex Avail Step H x).feasible F ↔
      DepthAtMost (Spectrum Avail Step x F) H := by
  exact depthAtMost_spectrum_iff_feasible.symm

/-- Removing requirements cannot increase future depth. -/
theorem spectrum_monotone_under_subbundle
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {G F : Finset Q}
    (hGF : G ⊆ F) :
    DepthLe (Spectrum Avail Step x G) (Spectrum Avail Step x F) := by
  classical
  by_cases hF : HasFiniteJointRecoveryDepth Avail Step x F
  · let dF := JointRecoveryDepth Avail Step x F hF
    have hFspec : (TemporalContractComplex Avail Step dF x).feasible F := by
      exact jointRecoveryDepth_spec hF
    have hGspec : (TemporalContractComplex Avail Step dF x).feasible G :=
      (TemporalContractComplex Avail Step dF x).downward hFspec hGF
    have hG : HasFiniteJointRecoveryDepth Avail Step x G := ⟨dF, hGspec⟩
    have hGmin : JointRecoveryDepth Avail Step x G hG ≤ dF :=
      jointRecoveryDepth_minimal hG hGspec
    rw [show Spectrum Avail Step x F = .finite dF by
          simp [Spectrum, hF, dF]]
    rw [show Spectrum Avail Step x G =
          .finite (JointRecoveryDepth Avail Step x G hG) by
          simp [Spectrum, hG]]
    exact hGmin
  · rw [show Spectrum Avail Step x F = .infinite by
          simp [Spectrum, hF]]
    cases hG : Spectrum Avail Step x G <;> simp [DepthLe]

/-- Set-level master representation of the entire joint future family. -/
theorem temporalJointFamily_eq_spectrum_sublevel
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {H : ℕ} :
    TemporalJointFamily Avail Step H x =
      {F : Finset Q | DepthAtMost (Spectrum Avail Step x F) H} := by
  ext F
  exact feasible_iff_depthAtMost_spectrum

/-- If two states have identical depth spectra on every finite future bundle,
then every temporal joint contract complex is identical at every horizon. -/
theorem spectrum_equal_implies_all_horizon_feasibility_equal
    {Q X Y : Type*} [DecidableEq Q]
    {AvailX : X → Set Q} {StepX : X → X → Prop} {x : X}
    {AvailY : Y → Set Q} {StepY : Y → Y → Prop} {y : Y}
    (hspec : ∀ F : Finset Q,
      Spectrum AvailX StepX x F = Spectrum AvailY StepY y F) :
    ∀ H F,
      (TemporalContractComplex AvailX StepX H x).feasible F ↔
        (TemporalContractComplex AvailY StepY H y).feasible F := by
  intro H F
  rw [feasible_iff_depthAtMost_spectrum,
      feasible_iff_depthAtMost_spectrum,
      hspec F]

/-- Conversely, agreement of all temporal joint complexes at all horizons
forces equality of the depth spectra. -/
theorem spectrum_eq_of_all_horizon_feasibility_equal
    {Q X Y : Type*} [DecidableEq Q]
    {AvailX : X → Set Q} {StepX : X → X → Prop} {x : X}
    {AvailY : Y → Set Q} {StepY : Y → Y → Prop} {y : Y}
    {F : Finset Q}
    (hall : ∀ H,
      (TemporalContractComplex AvailX StepX H x).feasible F ↔
        (TemporalContractComplex AvailY StepY H y).feasible F) :
    Spectrum AvailX StepX x F = Spectrum AvailY StepY y F := by
  classical
  by_cases hX : HasFiniteJointRecoveryDepth AvailX StepX x F
  · let dX := JointRecoveryDepth AvailX StepX x F hX
    have hXspec : (TemporalContractComplex AvailX StepX dX x).feasible F :=
      jointRecoveryDepth_spec hX
    have hYatX : (TemporalContractComplex AvailY StepY dX y).feasible F :=
      (hall dX).1 hXspec
    have hY : HasFiniteJointRecoveryDepth AvailY StepY y F := ⟨dX, hYatX⟩
    let dY := JointRecoveryDepth AvailY StepY y F hY
    have hYspec : (TemporalContractComplex AvailY StepY dY y).feasible F :=
      jointRecoveryDepth_spec hY
    have hXatY : (TemporalContractComplex AvailX StepX dY x).feasible F :=
      (hall dY).2 hYspec
    have hXY : dX ≤ dY := by
      exact jointRecoveryDepth_minimal hX hXatY
    have hYX : dY ≤ dX := by
      exact jointRecoveryDepth_minimal hY hYatX
    have hdepth : dX = dY := Nat.le_antisymm hXY hYX
    rw [show Spectrum AvailX StepX x F = .finite dX by
          simp [Spectrum, hX, dX]]
    rw [show Spectrum AvailY StepY y F = .finite dY by
          simp [Spectrum, hY, dY]]
    exact congrArg DepthValue.finite hdepth
  · have hY : ¬ HasFiniteJointRecoveryDepth AvailY StepY y F := by
      intro hfiniteY
      rcases hfiniteY with ⟨H, hHY⟩
      have hHX : (TemporalContractComplex AvailX StepX H x).feasible F :=
        (hall H).2 hHY
      exact hX ⟨H, hHX⟩
    simp [Spectrum, hX, hY]

/-- Master representation theorem: equality of depth spectra is equivalent to
agreement of the complete temporal filtration of joint future complexes. -/
theorem spectrum_extensional_iff_all_horizon_complexes
    {Q X Y : Type*} [DecidableEq Q]
    {AvailX : X → Set Q} {StepX : X → X → Prop} {x : X}
    {AvailY : Y → Set Q} {StepY : Y → Y → Prop} {y : Y} :
    (∀ F : Finset Q,
      Spectrum AvailX StepX x F = Spectrum AvailY StepY y F) ↔
      ∀ H F,
        (TemporalContractComplex AvailX StepX H x).feasible F ↔
          (TemporalContractComplex AvailY StepY H y).feasible F := by
  constructor
  · exact spectrum_equal_implies_all_horizon_feasibility_equal
  · intro hall F
    exact spectrum_eq_of_all_horizon_feasibility_equal (fun H => hall H F)

/-- Weighted temporal readiness is exactly a weighted sublevel mass of the
future-depth spectrum: a finite-catalogue CDF of future depth. -/
theorem temporalWeightedJointReadiness_eq_spectrum_sublevel_mass
    {Q X : Type*} [DecidableEq Q]
    {Ω : Finset (Finset Q)} {w : Finset Q → ℝ}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} :
    TemporalWeightedJointReadiness Ω w Avail Step H x =
      ∑ R ∈ Ω, if DepthAtMost (Spectrum Avail Step x R) H then w R else 0 := by
  classical
  unfold TemporalWeightedJointReadiness WeightedCatalogueReadiness
  apply Finset.sum_congr rfl
  intro R hR
  rw [depthAtMost_spectrum_iff_feasible]

/-- Temporal damage is exactly weighted mass crossing the horizon threshold:
recoverable before by H, but not recoverable after by H. -/
theorem temporalWeightedJointDamage_eq_spectrum_threshold_crossing
    {Q X Y : Type*} [DecidableEq Q]
    {Ω : Finset (Finset Q)} {w : Finset Q → ℝ}
    {AvailBefore : X → Set Q} {StepBefore : X → X → Prop} {x : X}
    {AvailAfter : Y → Set Q} {StepAfter : Y → Y → Prop} {y : Y}
    {H : ℕ} :
    TemporalWeightedJointDamage Ω w
        AvailBefore StepBefore x AvailAfter StepAfter y H =
      ∑ R ∈ Ω,
        if DepthAtMost (Spectrum AvailBefore StepBefore x R) H ∧
           ¬ DepthAtMost (Spectrum AvailAfter StepAfter y R) H
        then w R else 0 := by
  classical
  unfold TemporalWeightedJointDamage WeightedCatalogueDamage
  apply Finset.sum_congr rfl
  intro R hR
  rw [depthAtMost_spectrum_iff_feasible,
      depthAtMost_spectrum_iff_feasible]

end FutureDepthSpectrum

end InsacermoActionabilityInformation
