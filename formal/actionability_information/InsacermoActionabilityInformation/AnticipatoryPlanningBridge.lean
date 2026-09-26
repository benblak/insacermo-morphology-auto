import InsacermoActionabilityInformation.FutureDepthSpectrum
import InsacermoActionabilityInformation.TemporalJointFutureRisk
import Mathlib

namespace InsacermoActionabilityInformation

namespace AnticipatoryPlanningBridge

open FutureDepthSpectrum
open TemporalJointFutureRisk

/-- Finite-catalogue expected future cost.  Weights need not be normalised in
the structural kernel; probability normalisation is an external modelling
choice. -/
noncomputable def ExpectedFutureCost
    {Q : Type*} [DecidableEq Q]
    (Ω : Finset (Finset Q))
    (w : Finset Q → ℝ)
    (futureCost : Finset Q → ℝ) : ℝ := by
  classical
  exact ∑ F ∈ Ω, w F * futureCost F

/-- Binary cost of missing a declared recovery deadline. -/
def DeadlineMissCost
    {Q : Type*}
    (S : Finset Q → DepthValue) (H : ℕ) (F : Finset Q) : ℝ :=
  if DepthAtMost (S F) H then 0 else 1

/-- Expected future cost obtained by assigning unit cost to every catalogue
bundle that misses deadline H. -/
noncomputable def ExpectedDeadlineMissCost
    {Q : Type*} [DecidableEq Q]
    (Ω : Finset (Finset Q))
    (w : Finset Q → ℝ)
    (S : Finset Q → DepthValue) (H : ℕ) : ℝ :=
  ExpectedFutureCost Ω w (DeadlineMissCost S H)

/-- The same quantity written directly as weighted deadline-risk mass on a
finite catalogue. -/
noncomputable def CatalogueDeadlineRisk
    {Q : Type*} [DecidableEq Q]
    (Ω : Finset (Finset Q))
    (w : Finset Q → ℝ)
    (S : Finset Q → DepthValue) (H : ℕ) : ℝ := by
  classical
  exact ∑ F ∈ Ω, if ¬ DepthAtMost (S F) H then w F else 0

/-- Binary expected future cost is exactly weighted deadline-risk mass. -/
theorem expectedDeadlineMissCost_eq_catalogueDeadlineRisk
    {Q : Type*} [DecidableEq Q]
    {Ω : Finset (Finset Q)}
    {w : Finset Q → ℝ}
    {S : Finset Q → DepthValue} {H : ℕ} :
    ExpectedDeadlineMissCost Ω w S H =
      CatalogueDeadlineRisk Ω w S H := by
  classical
  unfold ExpectedDeadlineMissCost ExpectedFutureCost
    DeadlineMissCost CatalogueDeadlineRisk
  apply Finset.sum_congr rfl
  intro F hF
  by_cases h : DepthAtMost (S F) H
  · simp [h]
  · simp [h]

/-- Scalar anticipatory objective: immediate plan cost plus an estimated future
cost. -/
def AnticipatoryObjective
    {Plan : Type*}
    (immediateCost futureCost : Plan → ℝ) (p : Plan) : ℝ :=
  immediateCost p + futureCost p

/-- INSACERMO deadline-risk objective obtained by feeding the complete
post-plan future-depth spectrum into the anticipatory scalar objective. -/
noncomputable def InsacermoDeadlineObjective
    {Q Plan : Type*} [DecidableEq Q]
    (Ω : Finset (Finset Q))
    (w : Finset Q → ℝ)
    (postSpectrum : Plan → Finset Q → DepthValue)
    (H : ℕ) (immediateCost : Plan → ℝ) (p : Plan) : ℝ :=
  AnticipatoryObjective immediateCost
    (fun q => CatalogueDeadlineRisk Ω w (postSpectrum q) H) p

/-- The usual immediate-plus-expected-future-cost architecture is recovered
exactly when future cost is the binary deadline-miss penalty. -/
theorem insacermoDeadlineObjective_eq_anticipatory_expectedMissCost
    {Q Plan : Type*} [DecidableEq Q]
    {Ω : Finset (Finset Q)}
    {w : Finset Q → ℝ}
    {postSpectrum : Plan → Finset Q → DepthValue}
    {H : ℕ} {immediateCost : Plan → ℝ} {p : Plan} :
    InsacermoDeadlineObjective Ω w postSpectrum H immediateCost p =
      AnticipatoryObjective immediateCost
        (fun q => ExpectedDeadlineMissCost Ω w (postSpectrum q) H) p := by
  unfold InsacermoDeadlineObjective AnticipatoryObjective
  rw [expectedDeadlineMissCost_eq_catalogueDeadlineRisk]

/-- Hard contract preservation at a deadline: every required future bundle
must lie below the deadline in the post-plan depth spectrum. -/
def PreservesRequiredBundlesAt
    {Q : Type*} [DecidableEq Q]
    (Req : Finset (Finset Q))
    (S : Finset Q → DepthValue) (H : ℕ) : Prop :=
  ∀ F, F ∈ Req → DepthAtMost (S F) H

/-! ### Separation witness

Two plans can tie under a symmetric scalar expected-future-cost objective while
destroying different hard future contracts.  The scalar is not wrong; it is
simply a projection that forgets the identity of the lost obligation.
-/

inductive TwoGoal
  | alpha
  | beta
  deriving DecidableEq, Fintype

inductive TwoPlan
  | loseAlpha
  | loseBeta
  deriving DecidableEq, Fintype

open TwoGoal TwoPlan

def alphaBundle : Finset TwoGoal := {alpha}
def betaBundle : Finset TwoGoal := {beta}

def symmetricCatalogue : Finset (Finset TwoGoal) :=
  {alphaBundle, betaBundle}

def unitWeight : Finset TwoGoal → ℝ := fun _ => 1

def postSpectrum : TwoPlan → Finset TwoGoal → DepthValue
  | loseAlpha, F =>
      if F = alphaBundle then .infinite else .finite 0
  | loseBeta, F =>
      if F = betaBundle then .infinite else .finite 0

def zeroImmediateCost : TwoPlan → ℝ := fun _ => 0

def requireAlpha : Finset (Finset TwoGoal) := {alphaBundle}

/-- Under the symmetric catalogue, each plan loses exactly one unit-weight
future bundle, so the scalar expected deadline penalty ties. -/
theorem symmetric_expected_future_cost_ties :
    ExpectedDeadlineMissCost symmetricCatalogue unitWeight
        (postSpectrum loseAlpha) 0 =
      ExpectedDeadlineMissCost symmetricCatalogue unitWeight
        (postSpectrum loseBeta) 0 := by
  simp [ExpectedDeadlineMissCost, ExpectedFutureCost, DeadlineMissCost,
    symmetricCatalogue, unitWeight, postSpectrum, alphaBundle, betaBundle,
    DepthAtMost]

/-- Therefore the full immediate-plus-expected-future-cost objective also ties
when immediate costs are equal. -/
theorem anticipatory_scalar_objective_ties :
    InsacermoDeadlineObjective symmetricCatalogue unitWeight postSpectrum 0
        zeroImmediateCost loseAlpha =
      InsacermoDeadlineObjective symmetricCatalogue unitWeight postSpectrum 0
        zeroImmediateCost loseBeta := by
  unfold InsacermoDeadlineObjective AnticipatoryObjective
  rw [← expectedDeadlineMissCost_eq_catalogueDeadlineRisk,
      ← expectedDeadlineMissCost_eq_catalogueDeadlineRisk]
  exact symmetric_expected_future_cost_ties

/-- The plan that loses alpha violates the hard alpha contract. -/
theorem loseAlpha_breaks_required_alpha :
    ¬ PreservesRequiredBundlesAt requireAlpha
        (postSpectrum loseAlpha) 0 := by
  simp [PreservesRequiredBundlesAt, requireAlpha, postSpectrum,
    alphaBundle, DepthAtMost]

/-- The plan that loses beta preserves the hard alpha contract. -/
theorem loseBeta_preserves_required_alpha :
    PreservesRequiredBundlesAt requireAlpha
        (postSpectrum loseBeta) 0 := by
  intro F hF
  simp [requireAlpha] at hF
  subst F
  simp [postSpectrum, alphaBundle, betaBundle, DepthAtMost]

/-- Equal scalar anticipatory cost does not imply equal contract preservation.

This is the exact boundary: an expected future cost can rank or tie plans by an
aggregate statistic, while INSACERMO can retain the identity and joint
structure of the future obligations that the plan preserves or destroys. -/
theorem equal_expected_cost_can_hide_contract_difference :
    InsacermoDeadlineObjective symmetricCatalogue unitWeight postSpectrum 0
        zeroImmediateCost loseAlpha =
      InsacermoDeadlineObjective symmetricCatalogue unitWeight postSpectrum 0
        zeroImmediateCost loseBeta ∧
    ¬ PreservesRequiredBundlesAt requireAlpha (postSpectrum loseAlpha) 0 ∧
      PreservesRequiredBundlesAt requireAlpha (postSpectrum loseBeta) 0 := by
  exact ⟨anticipatory_scalar_objective_ties,
    loseAlpha_breaks_required_alpha,
    loseBeta_preserves_required_alpha⟩

end AnticipatoryPlanningBridge

end InsacermoActionabilityInformation
