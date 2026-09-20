import InsacermoActionabilityInformation.FutureTransformationComposition
import InsacermoActionabilityInformation.EventualFutureGeometry

namespace InsacermoActionabilityInformation
namespace FutureDamageCompositionLaw

open FutureDepthSpectrum
open FutureTransformationCalculus
open FutureTransformationComposition
open EventualFutureGeometry

/-- Once a future bundle is destroyed, any subsequent non-improving step
cannot recreate it: infinity is absorbing under non-improvement. -/
theorem destroyed_then_nonImproving_stays_destroyed
    {a b c : DepthValue}
    (hab : Destroyed a b)
    (hbc : DepthLe b c) :
    Destroyed a c := by
  rcases hab with ⟨d, ha, hb⟩
  subst a
  subst b
  cases c with
  | finite e =>
      simp [DepthLe] at hbc
  | infinite =>
      exact ⟨d, rfl, rfl⟩

/-- Dually, once a future bundle is created, any subsequent non-worsening step
cannot lose finite recoverability. -/
theorem created_then_nonWorsening_stays_finite
    {a b c : DepthValue}
    (hab : Created a b)
    (hcb : DepthLe c b) :
    ∃ e, c = .finite e := by
  rcases hab with ⟨d, ha, hb⟩
  subst a
  subst b
  cases c with
  | finite e =>
      exact ⟨e, rfl⟩
  | infinite =>
      simp [DepthLe] at hcb

/-- If the composite of two non-improving steps destroys a bundle, then the
destruction occurs at one of the two stages. -/
theorem composite_destruction_localizes
    {a b c : DepthValue}
    (hab : DepthLe a b)
    (hbc : DepthLe b c)
    (hac : Destroyed a c) :
    Destroyed a b ∨ Destroyed b c := by
  rcases hac with ⟨d, ha, hc⟩
  subst a
  subst c
  cases b with
  | finite e =>
      exact Or.inr ⟨e, rfl, rfl⟩
  | infinite =>
      exact Or.inl ⟨d, rfl, rfl⟩

/-- Exact two-step law under non-improvement: a composite destruction happens
iff destruction happens in at least one stage. -/
theorem composite_destruction_iff_stage_destruction
    {a b c : DepthValue}
    (hab : DepthLe a b)
    (hbc : DepthLe b c) :
    Destroyed a c ↔ Destroyed a b ∨ Destroyed b c := by
  constructor
  · intro hac
    exact composite_destruction_localizes hab hbc hac
  · intro h
    rcases h with habDestr | hbcDestr
    · exact destroyed_then_nonImproving_stays_destroyed habDestr hbc
    · rcases hbcDestr with ⟨d, hb, hc⟩
      subst b
      subst c
      cases a with
      | finite da =>
          exact ⟨da, rfl, rfl⟩
      | infinite =>
          simp [DepthLe] at hab

/-- Spectrum-level two-step destruction law. If both transformations are
non-improving over every bundle, then a bundle is destroyed by the composite
exactly when one of the two stages destroys it. -/
theorem spectrum_composite_destruction_iff_stage_destruction
    {Q : Type*}
    {x y z : Finset Q → DepthValue}
    (hxy : SpectrumNonImproving x y)
    (hyz : SpectrumNonImproving y z)
    (F : Finset Q) :
    Destroyed (x F) (z F) ↔
      Destroyed (x F) (y F) ∨ Destroyed (y F) (z F) := by
  exact composite_destruction_iff_stage_destruction (hxy F) (hyz F)

/-- No-hidden-destruction corollary: if neither stage destroys a bundle and
both stages are non-improving, then the composite cannot destroy it. -/
theorem no_hidden_composite_destruction
    {Q : Type*}
    {x y z : Finset Q → DepthValue}
    (hxy : SpectrumNonImproving x y)
    (hyz : SpectrumNonImproving y z)
    {F : Finset Q}
    (h1 : ¬ Destroyed (x F) (y F))
    (h2 : ¬ Destroyed (y F) (z F)) :
    ¬ Destroyed (x F) (z F) := by
  intro hcomp
  exact (spectrum_composite_destruction_iff_stage_destruction hxy hyz F).1 hcomp |>.elim h1 h2

/-- Once a bundle has become jointly irreversible, a globally non-improving
transformation cannot repair it back to finite depth. -/
theorem nonImproving_cannot_repair_destroyed_bundle
    {Q : Type*}
    {before after : Finset Q → DepthValue}
    (h : SpectrumNonImproving before after)
    {F : Finset Q}
    (hinf : before F = .infinite) :
    after F = .infinite := by
  exact nonImproving_preserves_infinity h hinf

end FutureDamageCompositionLaw
end InsacermoActionabilityInformation
