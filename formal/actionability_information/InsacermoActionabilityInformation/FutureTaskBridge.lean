import InsacermoActionabilityInformation.DecisionSemantics
import InsacermoActionabilityInformation.FutureRobustness
import Mathlib

namespace InsacermoActionabilityInformation

namespace FutureTaskBridge

open DecisionSemantics
open FutureRobustness

variable {Q X : Type*}

/-- Pointwise future-task preservation: every declared future task remains
individually available at the current state.

This is the direct set-valued bridge to future-task / attainable-utility style
option preservation. -/
def PointwiseFutureTaskPreserved
    (Req : Set Q) (Avail : X → Set Q) (x : X) : Prop :=
  Req ⊆ Avail x

/-- Pointwise future-task preservation is exactly INSACERMO strict PRESERVE. -/
theorem pointwiseFutureTaskPreserved_iff_preserve
    {Req : Set Q} {Avail : X → Set Q} {x : X} :
    PointwiseFutureTaskPreserved Req Avail x ↔
      PRESERVE Req Avail x := by
  rfl

/-- At horizon zero, INSACERMO weighted readiness is exactly the weighted mass
of currently available future tasks.  Thus the weighted future-task score is
a zero-horizon projection of the temporal recoverability machinery. -/
theorem weightedReadiness_zero_eq_current_future_mass
    {Q X : Type*} [Fintype Q]
    {w : Q → ℝ} {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} :
    WeightedReadiness w Avail Step 0 x =
      WeightedMass w (Avail x) := by
  rfl

section JointContracts

variable {Q : Type*} [DecidableEq Q]

/-- Pointwise preservation for a finite contract complex: every requested task
is feasible as a singleton. -/
def PointwiseSingletonFeasible
    (K : ContractComplex Q) (Req : Finset Q) : Prop :=
  ∀ q, q ∈ Req → K.feasible {q}

/-- Joint contract preservation: the whole requested future bundle is jointly
feasible. -/
def JointBundleFeasible
    (K : ContractComplex Q) (Req : Finset Q) : Prop :=
  K.feasible Req

/-- Joint feasibility always implies pointwise singleton feasibility in a
downward-closed contract complex. -/
theorem jointBundleFeasible_implies_pointwiseSingletonFeasible
    {K : ContractComplex Q} {Req : Finset Q}
    (hjoint : JointBundleFeasible K Req) :
    PointwiseSingletonFeasible K Req := by
  intro q hq
  apply K.downward hjoint
  exact Finset.singleton_subset_iff.mpr hq

end JointContracts

/-! ### Strict separation witness

Both future tasks below remain individually feasible, while the two-task bundle
is jointly infeasible.  This exhibits information present in an INSACERMO
contract complex that a purely pointwise future-task preservation criterion
cannot see.
-/

inductive TwoFutureTask
  | alpha
  | beta
  deriving DecidableEq, Fintype

open TwoFutureTask

/-- Toy contract complex in which at most one of the two future tasks can be
satisfied jointly. -/
def singletonCapacityContract : ContractComplex TwoFutureTask where
  feasible := fun F => F.card ≤ 1
  downward := by
    intro R T hR hTR
    exact le_trans (Finset.card_le_card hTR) hR

def bothFutureTasks : Finset TwoFutureTask :=
  {alpha, beta}

/-- Each future task is individually feasible. -/
theorem bothFutureTasks_pointwise_feasible :
    PointwiseSingletonFeasible singletonCapacityContract bothFutureTasks := by
  intro q hq
  simp [singletonCapacityContract]

/-- But the future-task pair is not jointly feasible. -/
theorem bothFutureTasks_not_jointly_feasible :
    ¬ JointBundleFeasible singletonCapacityContract bothFutureTasks := by
  simp [JointBundleFeasible, singletonCapacityContract, bothFutureTasks]

/-- Pointwise future-task preservation does not imply preservation of the
joint future contract. -/
theorem pointwise_future_tasks_do_not_imply_joint_contract :
    PointwiseSingletonFeasible singletonCapacityContract bothFutureTasks ∧
      ¬ JointBundleFeasible singletonCapacityContract bothFutureTasks := by
  exact ⟨bothFutureTasks_pointwise_feasible,
    bothFutureTasks_not_jointly_feasible⟩

end FutureTaskBridge

end InsacermoActionabilityInformation
