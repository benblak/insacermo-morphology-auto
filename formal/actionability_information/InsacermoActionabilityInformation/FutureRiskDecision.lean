import InsacermoActionabilityInformation.UnknownFutureRisk

namespace InsacermoActionabilityInformation

namespace FutureRiskDecision

open FutureDepthSpectrum
open FutureTransformationCalculus
open UnknownFutureRisk

/-- A present action is budget-feasible when its declared cost is at most B. -/
def ActionFeasibleWithinBudget
    {Action : Type*}
    (cost : Action → ℕ) (B : ℕ) (a : Action) : Prop :=
  cost a ≤ B

/-- Irreversible future-risk induced by a present action. -/
noncomputable def ActionIrreversibleRisk
    {Q X Action : Type*} [Fintype Q] [DecidableEq Q]
    (μ : Finset Q → ℝ) (Γ : Set (Finset Q))
    (Avail : X → Set Q) (Step : X → X → Prop)
    (applyAction : Action → X → X)
    (x : X) (a : Action) : ℝ :=
  StateIrreversibleRiskMass μ Γ Avail Step (applyAction a x)

/-- Deadline future-risk induced by a present action. -/
noncomputable def ActionDeadlineRisk
    {Q X Action : Type*} [Fintype Q] [DecidableEq Q]
    (μ : Finset Q → ℝ) (Γ : Set (Finset Q))
    (Avail : X → Set Q) (Step : X → X → Prop)
    (applyAction : Action → X → X)
    (x : X) (H : ℕ) (a : Action) : ℝ :=
  StateDeadlineRiskMass μ Γ Avail Step (applyAction a x) H

/-- An action is irreversibility-risk optimal under budget B when it is
budget-feasible and no budget-feasible alternative has smaller irreversible
future-risk mass. -/
def IsIrreversibleRiskOptimalWithinBudget
    {Q X Action : Type*} [Fintype Q] [DecidableEq Q]
    (μ : Finset Q → ℝ) (Γ : Set (Finset Q))
    (Avail : X → Set Q) (Step : X → X → Prop)
    (applyAction : Action → X → X) (cost : Action → ℕ)
    (x : X) (B : ℕ) (a : Action) : Prop :=
  ActionFeasibleWithinBudget cost B a ∧
  ∀ b, ActionFeasibleWithinBudget cost B b →
    ActionIrreversibleRisk μ Γ Avail Step applyAction x a ≤
      ActionIrreversibleRisk μ Γ Avail Step applyAction x b

/-- Deadline-risk optimality under a budget. -/
def IsDeadlineRiskOptimalWithinBudget
    {Q X Action : Type*} [Fintype Q] [DecidableEq Q]
    (μ : Finset Q → ℝ) (Γ : Set (Finset Q))
    (Avail : X → Set Q) (Step : X → X → Prop)
    (applyAction : Action → X → X) (cost : Action → ℕ)
    (x : X) (H B : ℕ) (a : Action) : Prop :=
  ActionFeasibleWithinBudget cost B a ∧
  ∀ b, ActionFeasibleWithinBudget cost B b →
    ActionDeadlineRisk μ Γ Avail Step applyAction x H a ≤
      ActionDeadlineRisk μ Γ Avail Step applyAction x H b

/-- A risk-optimal action is necessarily budget-feasible. -/
theorem irreversibleRiskOptimal_feasible
    {Q X Action : Type*} [Fintype Q] [DecidableEq Q]
    {μ : Finset Q → ℝ} {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyAction : Action → X → X} {cost : Action → ℕ}
    {x : X} {B : ℕ} {a : Action}
    (h : IsIrreversibleRiskOptimalWithinBudget
      μ Γ Avail Step applyAction cost x B a) :
    ActionFeasibleWithinBudget cost B a :=
  h.1

/-- An irreversible-risk optimum beats every other feasible action. -/
theorem irreversibleRiskOptimal_le_feasible
    {Q X Action : Type*} [Fintype Q] [DecidableEq Q]
    {μ : Finset Q → ℝ} {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyAction : Action → X → X} {cost : Action → ℕ}
    {x : X} {B : ℕ} {a b : Action}
    (ha : IsIrreversibleRiskOptimalWithinBudget
      μ Γ Avail Step applyAction cost x B a)
    (hb : ActionFeasibleWithinBudget cost B b) :
    ActionIrreversibleRisk μ Γ Avail Step applyAction x a ≤
      ActionIrreversibleRisk μ Γ Avail Step applyAction x b :=
  ha.2 b hb

/-- Deadline-risk optimum beats every other action satisfying the same budget. -/
theorem deadlineRiskOptimal_le_feasible
    {Q X Action : Type*} [Fintype Q] [DecidableEq Q]
    {μ : Finset Q → ℝ} {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyAction : Action → X → X} {cost : Action → ℕ}
    {x : X} {H B : ℕ} {a b : Action}
    (ha : IsDeadlineRiskOptimalWithinBudget
      μ Γ Avail Step applyAction cost x H B a)
    (hb : ActionFeasibleWithinBudget cost B b) :
    ActionDeadlineRisk μ Γ Avail Step applyAction x H a ≤
      ActionDeadlineRisk μ Γ Avail Step applyAction x H b :=
  ha.2 b hb

/-- If action a has a non-worsening future-depth spectrum relative to action b,
then a cannot have higher irreversible risk under any nonnegative future law. -/
theorem nonWorsening_action_irreversibleRisk_le
    {Q X Action : Type*} [Fintype Q] [DecidableEq Q]
    {μ : Finset Q → ℝ} {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyAction : Action → X → X}
    {x : X} {a b : Action}
    (hμ : ∀ F, 0 ≤ μ F)
    (hspec : SpectrumNonWorsening
      (Spectrum Avail Step (applyAction b x))
      (Spectrum Avail Step (applyAction a x))) :
    ActionIrreversibleRisk μ Γ Avail Step applyAction x a ≤
      ActionIrreversibleRisk μ Γ Avail Step applyAction x b := by
  unfold ActionIrreversibleRisk StateIrreversibleRiskMass
  exact irreversibleRiskMass_antitone_nonWorsening hμ hspec

/-- The same dominance law holds for every finite deadline. -/
theorem nonWorsening_action_deadlineRisk_le
    {Q X Action : Type*} [Fintype Q] [DecidableEq Q]
    {μ : Finset Q → ℝ} {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyAction : Action → X → X}
    {x : X} {H : ℕ} {a b : Action}
    (hμ : ∀ F, 0 ≤ μ F)
    (hspec : SpectrumNonWorsening
      (Spectrum Avail Step (applyAction b x))
      (Spectrum Avail Step (applyAction a x))) :
    ActionDeadlineRisk μ Γ Avail Step applyAction x H a ≤
      ActionDeadlineRisk μ Γ Avail Step applyAction x H b := by
  unfold ActionDeadlineRisk StateDeadlineRiskMass
  exact deadlineRiskMass_antitone_nonWorsening hμ hspec

/-- If a is no more expensive than b and spectrum-non-worsening relative to b,
then whenever b is budget-feasible, a is also budget-feasible and weakly
risk-dominates b. -/
theorem cost_and_spectrum_dominance
    {Q X Action : Type*} [Fintype Q] [DecidableEq Q]
    {μ : Finset Q → ℝ} {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyAction : Action → X → X} {cost : Action → ℕ}
    {x : X} {B : ℕ} {a b : Action}
    (hμ : ∀ F, 0 ≤ μ F)
    (hcost : cost a ≤ cost b)
    (hspec : SpectrumNonWorsening
      (Spectrum Avail Step (applyAction b x))
      (Spectrum Avail Step (applyAction a x)))
    (hb : ActionFeasibleWithinBudget cost B b) :
    ActionFeasibleWithinBudget cost B a ∧
      ActionIrreversibleRisk μ Γ Avail Step applyAction x a ≤
        ActionIrreversibleRisk μ Γ Avail Step applyAction x b := by
  constructor
  · exact Nat.le_trans hcost hb
  · exact nonWorsening_action_irreversibleRisk_le hμ hspec

end FutureRiskDecision

end InsacermoActionabilityInformation
