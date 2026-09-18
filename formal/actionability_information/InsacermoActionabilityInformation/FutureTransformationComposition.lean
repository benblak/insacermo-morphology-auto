import InsacermoActionabilityInformation.FutureTransformationCalculus

namespace InsacermoActionabilityInformation

namespace FutureTransformationComposition

open FutureDepthSpectrum
open FutureTransformationCalculus

/-- Reflexivity of the extended future-depth order. -/
theorem depthLe_refl (a : DepthValue) : DepthLe a a := by
  cases a <;> simp [DepthLe]

/-- Transitivity of the extended future-depth order. -/
theorem depthLe_trans
    {a b c : DepthValue}
    (hab : DepthLe a b)
    (hbc : DepthLe b c) :
    DepthLe a c := by
  cases a <;> cases b <;> cases c <;> simp [DepthLe] at * <;> omega

/-- Antisymmetry of the extended future-depth order. -/
theorem depthLe_antisymm
    {a b : DepthValue}
    (hab : DepthLe a b)
    (hba : DepthLe b a) :
    a = b := by
  cases a <;> cases b <;> simp [DepthLe] at *
  case finite.finite da db =>
    simp [Nat.le_antisymm hab hba]

/-- Transitivity of strict future-depth improvement. -/
theorem depthLt_trans
    {a b c : DepthValue}
    (hab : DepthLt a b)
    (hbc : DepthLt b c) :
    DepthLt a c := by
  cases a <;> cases b <;> cases c <;> simp [DepthLt] at * <;> omega

/-- A strict improvement followed by a non-worsening step remains a strict
improvement overall. -/
theorem depthLt_of_lt_of_le
    {a b c : DepthValue}
    (hab : DepthLt a b)
    (hbc : DepthLe b c) :
    DepthLt a c := by
  cases a <;> cases b <;> cases c <;>
    simp [DepthLt, DepthLe] at * <;> omega

/-- A non-worsening step followed by a strict improvement remains a strict
improvement overall. -/
theorem depthLt_of_le_of_lt
    {a b c : DepthValue}
    (hab : DepthLe a b)
    (hbc : DepthLt b c) :
    DepthLt a c := by
  cases a <;> cases b <;> cases c <;>
    simp [DepthLt, DepthLe] at * <;> omega

/-- Non-worsening transformations compose. If x→y never makes a future deeper
and y→z never makes a future deeper, then x→z never makes a future deeper. -/
theorem spectrumNonWorsening_trans
    {Q : Type*}
    {x y z : Finset Q → DepthValue}
    (hxy : SpectrumNonWorsening x y)
    (hyz : SpectrumNonWorsening y z) :
    SpectrumNonWorsening x z := by
  intro F
  exact depthLe_trans (hyz F) (hxy F)

/-- Non-improving transformations compose. -/
theorem spectrumNonImproving_trans
    {Q : Type*}
    {x y z : Finset Q → DepthValue}
    (hxy : SpectrumNonImproving x y)
    (hyz : SpectrumNonImproving y z) :
    SpectrumNonImproving x z := by
  intro F
  exact depthLe_trans (hxy F) (hyz F)

/-- Spectrum equivalence is reflexive. -/
theorem spectrumEquivalent_refl
    {Q : Type*}
    (x : Finset Q → DepthValue) :
    SpectrumEquivalent x x := by
  intro F
  rfl

/-- Spectrum equivalence is symmetric. -/
theorem spectrumEquivalent_symm
    {Q : Type*}
    {x y : Finset Q → DepthValue}
    (hxy : SpectrumEquivalent x y) :
    SpectrumEquivalent y x := by
  intro F
  exact (hxy F).symm

/-- Spectrum equivalence is transitive. -/
theorem spectrumEquivalent_trans
    {Q : Type*}
    {x y z : Finset Q → DepthValue}
    (hxy : SpectrumEquivalent x y)
    (hyz : SpectrumEquivalent y z) :
    SpectrumEquivalent x z := by
  intro F
  exact Eq.trans (hxy F) (hyz F)

/-- Spectrum equivalence is exactly mutual non-worsening. -/
theorem spectrumEquivalent_iff_mutual_nonWorsening
    {Q : Type*}
    {x y : Finset Q → DepthValue} :
    SpectrumEquivalent x y ↔
      SpectrumNonWorsening x y ∧ SpectrumNonWorsening y x := by
  constructor
  · intro h
    constructor
    · intro F
      rw [h F]
      exact depthLe_refl (y F)
    · intro F
      rw [h F]
      exact depthLe_refl (y F)
  · rintro ⟨hxy, hyx⟩
    intro F
    exact depthLe_antisymm (hyx F) (hxy F)

/-- If a bundle is accelerated by x→y and y→z is non-worsening, then the
bundle is accelerated by the composite x→z. -/
theorem accelerated_then_nonWorsening
    {Q : Type*}
    {x y z : Finset Q → DepthValue}
    {F : Finset Q}
    (hacc : Accelerated (x F) (y F))
    (hyz : SpectrumNonWorsening y z) :
    Accelerated (x F) (z F) := by
  unfold Accelerated at *
  exact depthLt_of_le_of_lt (hyz F) hacc

/-- If x→y is non-worsening and a bundle is accelerated by y→z, then the
bundle is accelerated by the composite x→z. -/
theorem nonWorsening_then_accelerated
    {Q : Type*}
    {x y z : Finset Q → DepthValue}
    {F : Finset Q}
    (hxy : SpectrumNonWorsening x y)
    (hacc : Accelerated (y F) (z F)) :
    Accelerated (x F) (z F) := by
  unfold Accelerated at *
  exact depthLt_of_lt_of_le hacc (hxy F)

/-- If a bundle is delayed by x→y and y→z is non-improving, then the bundle
is delayed by the composite x→z. -/
theorem delayed_then_nonImproving
    {Q : Type*}
    {x y z : Finset Q → DepthValue}
    {F : Finset Q}
    (hdel : Delayed (x F) (y F))
    (hyz : SpectrumNonImproving y z) :
    Delayed (x F) (z F) := by
  unfold Delayed Accelerated at *
  exact depthLt_of_lt_of_le hdel (hyz F)

/-- If x→y is non-improving and a bundle is delayed by y→z, then the bundle
is delayed by the composite x→z. -/
theorem nonImproving_then_delayed
    {Q : Type*}
    {x y z : Finset Q → DepthValue}
    {F : Finset Q}
    (hxy : SpectrumNonImproving x y)
    (hdel : Delayed (y F) (z F)) :
    Delayed (x F) (z F) := by
  unfold Delayed Accelerated at *
  exact depthLt_of_le_of_lt (hxy F) hdel

/-- Two strict accelerations compose to a strict acceleration. -/
theorem accelerated_trans
    {a b c : DepthValue}
    (hab : Accelerated a b)
    (hbc : Accelerated b c) :
    Accelerated a c := by
  unfold Accelerated at *
  exact depthLt_trans hbc hab

/-- Two strict delays compose to a strict delay. -/
theorem delayed_trans
    {a b c : DepthValue}
    (hab : Delayed a b)
    (hbc : Delayed b c) :
    Delayed a c := by
  unfold Delayed Accelerated at *
  exact depthLt_trans hab hbc

/-- A non-worsening chain preserves every finite-horizon availability fact
through composition. -/
theorem composed_nonWorsening_preserves_horizon
    {Q : Type*}
    {x y z : Finset Q → DepthValue}
    (hxy : SpectrumNonWorsening x y)
    (hyz : SpectrumNonWorsening y z)
    {F : Finset Q} {H : ℕ}
    (hx : DepthAtMost (x F) H) :
    DepthAtMost (z F) H := by
  exact nonWorsening_preserves_horizon_availability
    (spectrumNonWorsening_trans hxy hyz) hx

/-- A non-improving chain reflects every finite-horizon availability fact
back through composition. -/
theorem composed_nonImproving_reflects_horizon
    {Q : Type*}
    {x y z : Finset Q → DepthValue}
    (hxy : SpectrumNonImproving x y)
    (hyz : SpectrumNonImproving y z)
    {F : Finset Q} {H : ℕ}
    (hz : DepthAtMost (z F) H) :
    DepthAtMost (x F) H := by
  exact nonImproving_reflects_horizon_availability
    (spectrumNonImproving_trans hxy hyz) hz

end FutureTransformationComposition

end InsacermoActionabilityInformation
