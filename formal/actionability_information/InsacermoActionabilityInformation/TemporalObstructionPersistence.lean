import InsacermoActionabilityInformation.TemporalJointContractComplex

namespace InsacermoActionabilityInformation

namespace TemporalObstructionPersistence

open FutureRobustness
open TemporalJointContractComplex

/-- A finite bundle is a temporal minimal obstruction at horizon `H` when it
is a minimal non-face of the temporal joint contract complex. -/
def TemporalMinimalObstruction
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (H : ℕ) (F : Finset Q) : Prop :=
  MinimalNonface (TemporalContractComplex Avail Step H x) F

/-- A finite bundle has finite joint recovery depth when one common admissible
trajectory satisfies it at some finite horizon. -/
def HasFiniteJointRecoveryDepth
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (F : Finset Q) : Prop :=
  ∃ H, (TemporalContractComplex Avail Step H x).feasible F

/-- A finite bundle is jointly irreversible when no finite horizon ever makes
it a face of the temporal joint contract complex. -/
def JointIrreversible
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (F : Finset Q) : Prop :=
  ∀ H, ¬ (TemporalContractComplex Avail Step H x).feasible F

/-- Joint irreversibility is exactly failure of finite joint recovery depth. -/
theorem jointIrreversible_iff_not_hasFiniteJointRecoveryDepth
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q} :
    JointIrreversible Avail Step x F ↔
      ¬ HasFiniteJointRecoveryDepth Avail Step x F := by
  constructor
  · intro hirr hfinite
    rcases hfinite with ⟨H, hH⟩
    exact hirr H hH
  · intro hnot H hH
    exact hnot ⟨H, hH⟩

/-- Joint feasibility is monotone for arbitrary extension of the horizon. -/
theorem temporalContractComplex_mono_of_le
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {m n : ℕ} (hmn : m ≤ n) {F : Finset Q}
    (hF : (TemporalContractComplex Avail Step m x).feasible F) :
    (TemporalContractComplex Avail Step n x).feasible F := by
  induction hmn with
  | refl => exact hF
  | @step n hmn ih =>
      exact temporalContractComplex_mono_horizon ih

/-- Once a joint bundle becomes feasible, it remains feasible at every later
finite horizon. -/
theorem joint_resolution_persists
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {H : ℕ} {F : Finset Q}
    (hF : (TemporalContractComplex Avail Step H x).feasible F) :
    ∀ H', H ≤ H' → (TemporalContractComplex Avail Step H' x).feasible F := by
  intro H' hle
  exact temporalContractComplex_mono_of_le hle hF

/-- If `F` is a minimal obstruction at horizon `H` and the full bundle remains
infeasible one step later, then `F` is still a minimal obstruction at `H+1`.
Proper sub-bundles cannot become infeasible because the temporal complex only
grows with the horizon. -/
theorem minimalObstruction_persists_if_still_infeasible
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {H : ℕ} {F : Finset Q}
    (hmin : TemporalMinimalObstruction Avail Step x H F)
    (hbadNext : ¬ (TemporalContractComplex Avail Step (H + 1) x).feasible F) :
    TemporalMinimalObstruction Avail Step x (H + 1) F := by
  constructor
  · exact hbadNext
  · intro G hGF
    have hG : (TemporalContractComplex Avail Step H x).feasible G := hmin.2 G hGF
    exact temporalContractComplex_mono_horizon hG

/-- A minimal obstruction that is jointly irreversible remains a minimal
obstruction at every later horizon. -/
theorem minimalObstruction_persists_forever_of_irreversible
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {H₀ : ℕ} {F : Finset Q}
    (hmin : TemporalMinimalObstruction Avail Step x H₀ F)
    (hirr : JointIrreversible Avail Step x F) :
    ∀ H, H₀ ≤ H → TemporalMinimalObstruction Avail Step x H F := by
  intro H hle
  constructor
  · exact hirr H
  · intro G hGF
    have hG0 : (TemporalContractComplex Avail Step H₀ x).feasible G := hmin.2 G hGF
    exact temporalContractComplex_mono_of_le hle hG0

/-- The minimum finite horizon at which a jointly recoverable bundle becomes a
face of the temporal contract complex. -/
noncomputable def JointRecoveryDepth
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (F : Finset Q)
    (hfinite : HasFiniteJointRecoveryDepth Avail Step x F) : ℕ := by
  classical
  exact Nat.find hfinite

/-- The minimum joint recovery depth actually recovers the whole bundle. -/
theorem jointRecoveryDepth_spec
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q}
    (hfinite : HasFiniteJointRecoveryDepth Avail Step x F) :
    (TemporalContractComplex Avail Step
      (JointRecoveryDepth Avail Step x F hfinite) x).feasible F := by
  classical
  unfold JointRecoveryDepth
  exact Nat.find_spec hfinite

/-- The minimum joint recovery depth is no larger than any horizon that already
resolves the bundle. -/
theorem jointRecoveryDepth_minimal
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q}
    (hfinite : HasFiniteJointRecoveryDepth Avail Step x F)
    {H : ℕ}
    (hH : (TemporalContractComplex Avail Step H x).feasible F) :
    JointRecoveryDepth Avail Step x F hfinite ≤ H := by
  classical
  unfold JointRecoveryDepth
  exact Nat.find_min' hfinite hH

/-- Exact first horizon at which a finite bundle becomes jointly feasible. -/
def FirstJointRecoveryAt
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (F : Finset Q) (H : ℕ) : Prop :=
  (TemporalContractComplex Avail Step H x).feasible F ∧
    ∀ h, h < H → ¬ (TemporalContractComplex Avail Step h x).feasible F

/-- The minimum joint recovery depth is an exact first-entry horizon. -/
theorem firstJointRecoveryAt_jointRecoveryDepth
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q}
    (hfinite : HasFiniteJointRecoveryDepth Avail Step x F) :
    FirstJointRecoveryAt Avail Step x F
      (JointRecoveryDepth Avail Step x F hfinite) := by
  classical
  constructor
  · exact jointRecoveryDepth_spec hfinite
  · intro h hh
    unfold JointRecoveryDepth
    exact Nat.find_min hfinite hh

/-- A temporal minimal obstruction has only two eventual fates: either it is
jointly irreversible, or it has a finite first resolution horizon. -/
theorem minimalObstruction_irreversible_or_has_first_resolution
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {H : ℕ} {F : Finset Q}
    (hmin : TemporalMinimalObstruction Avail Step x H F) :
    JointIrreversible Avail Step x F ∨
      ∃ H', H < H' ∧ FirstJointRecoveryAt Avail Step x F H' := by
  classical
  by_cases hfinite : HasFiniteJointRecoveryDepth Avail Step x F
  · right
    let d := JointRecoveryDepth Avail Step x F hfinite
    have hfirst : FirstJointRecoveryAt Avail Step x F d :=
      firstJointRecoveryAt_jointRecoveryDepth hfinite
    have hHd : H < d := by
      by_contra hnot
      have hdH : d ≤ H := Nat.le_of_not_gt hnot
      have hdfeas : (TemporalContractComplex Avail Step d x).feasible F :=
        jointRecoveryDepth_spec hfinite
      have hHfeas : (TemporalContractComplex Avail Step H x).feasible F :=
        temporalContractComplex_mono_of_le hdH hdfeas
      exact hmin.1 hHfeas
    exact ⟨d, hHd, hfirst⟩
  · left
    exact (jointIrreversible_iff_not_hasFiniteJointRecoveryDepth).2 hfinite

end TemporalObstructionPersistence

end InsacermoActionabilityInformation
