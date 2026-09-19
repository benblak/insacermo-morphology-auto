import InsacermoActionabilityInformation.RepairPlanDuality
import InsacermoActionabilityInformation.UnknownFutureRobustness
import InsacermoActionabilityInformation.FutureRiskDecision

namespace InsacermoActionabilityInformation

namespace MasterClosureV1

open TemporalJointContractComplex
open TemporalObstructionPersistence
open FutureDepthSpectrum
open EventualFutureGeometry
open FutureRepairPrice
open UnknownFutureRobustness
open RepairPlanDuality

/-! # INSACERMO Core V1 master closure

This file adds no new operational semantics.  It proves that the previously
verified temporal-depth, common-plan, repair-budget, and unknown-future
formulations are exact views of the same finite-bundle feasibility structure.
-/

/-- **Master finite-horizon equivalence.**
A bundle lies below the future-depth threshold H iff there exists one
kernel-certified joint plan for that whole bundle at horizon H. -/
theorem depthAtMost_iff_certifiedCommonPlan
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} {F : Finset Q} :
    DepthAtMost (Spectrum Avail Step x F) H ↔
      BundleFeasible
        (CertifiedJointPlanGood
          (Avail := Avail) (Step := Step) (H := H) (x := x)) F := by
  rw [depthAtMost_spectrum_iff_feasible]
  change JointRecoverable Avail Step H x (↑F : Set Q) ↔ _
  exact jointRecoverable_iff_bundleFeasible_certifiedPlan

/-- **Master finite-horizon family equivalence.**
Unknown-future safety at horizon H is exactly the statement that every
possible future bundle in Γ admits one certified common plan by H. -/
theorem familySafeAtHorizon_iff_all_certifiedCommonPlans
    {Q X : Type*} [DecidableEq Q]
    {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} :
    FamilySafeAtHorizon Γ Avail Step H x ↔
      ∀ F, F ∈ Γ →
        BundleFeasible
          (CertifiedJointPlanGood
            (Avail := Avail) (Step := Step) (H := H) (x := x)) F := by
  constructor
  · intro hsafe F hFΓ
    exact (depthAtMost_iff_certifiedCommonPlan).mp (hsafe F hFΓ)
  · intro hplans F hFΓ
    exact (depthAtMost_iff_certifiedCommonPlan).mpr (hplans F hFΓ)

/-- A finite-horizon certificate together with the horizon at which it works.
This is an existential certificate of eventual joint feasibility, not a claim
that the subtype itself is a physical trajectory representation. -/
def EventualCertifiedJointPlan
    {Q X : Type*}
    (Avail : X → Set Q) (Step : X → X → Prop) (x : X) :=
  Σ H : ℕ, CertifiedJointPlan Avail Step H x

/-- A future is supported by an eventual certificate when it belongs to the
bundle certified at that certificate's finite horizon. -/
def EventualCertifiedJointPlanGood
    {Q X : Type*}
    {Avail : X → Set Q} {Step : X → X → Prop} {x : X}
    (p : EventualCertifiedJointPlan Avail Step x) (q : Q) : Prop :=
  q ∈ p.2.1

/-- **Master eventual equivalence.**
Eventual joint feasibility is exactly existence of some finite-horizon
certificate supporting the whole bundle. -/
theorem eventualFeasible_iff_eventualCertifiedCommonPlan
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q} :
    (EventualFutureComplex Avail Step x).feasible F ↔
      BundleFeasible
        (EventualCertifiedJointPlanGood
          (Avail := Avail) (Step := Step) (x := x)) F := by
  constructor
  · intro hfinite
    change HasFiniteJointRecoveryDepth Avail Step x F at hfinite
    rcases hfinite with ⟨H, hH⟩
    have hjoint : JointRecoverable Avail Step H x (↑F : Set Q) := by
      exact hH
    refine ⟨⟨H, ⟨(↑F : Set Q), hjoint⟩⟩, ?_⟩
    intro q hq
    exact hq
  · rintro ⟨⟨H, p⟩, hp⟩
    change HasFiniteJointRecoveryDepth Avail Step x F
    refine ⟨H, ?_⟩
    change JointRecoverable Avail Step H x (↑F : Set Q)
    apply jointRecoverable_downward H x p.2
    intro q hq
    exact hp q hq

/-- **Master eventual family equivalence.**
An unknown family Γ is eventually safe iff every possible future bundle admits
some finite-horizon joint certificate. -/
theorem familyEventuallySafe_iff_all_eventualCertifiedCommonPlans
    {Q X : Type*} [DecidableEq Q]
    {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} :
    FamilyEventuallySafe Γ Avail Step x ↔
      ∀ F, F ∈ Γ →
        BundleFeasible
          (EventualCertifiedJointPlanGood
            (Avail := Avail) (Step := Step) (x := x)) F := by
  constructor
  · intro hsafe F hFΓ
    exact (eventualFeasible_iff_eventualCertifiedCommonPlan).mp
      (hsafe F hFΓ)
  · intro hplans F hFΓ
    exact (eventualFeasible_iff_eventualCertifiedCommonPlan).mpr
      (hplans F hFΓ)

/-- **Repair/common-plan bridge.**
A deadline repair exists within budget b iff some repair of cost at most b
moves the state to one admitting a certified common plan for the whole bundle
by horizon H. -/
theorem deadlineRepairWithinBudget_iff_repair_to_certifiedCommonPlan
    {Q X Repair : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X} {cost : Repair → ℕ}
    {x : X} {F : Finset Q} {H b : ℕ} :
    DeadlineRepairWithinBudget
        Avail Step applyRepair cost x F H b ↔
      ∃ r : Repair, cost r ≤ b ∧
        BundleFeasible
          (CertifiedJointPlanGood
            (Avail := Avail) (Step := Step)
            (H := H) (x := applyRepair r x)) F := by
  constructor
  · rintro ⟨r, hcost, hdepth⟩
    refine ⟨r, hcost, ?_⟩
    exact (depthAtMost_iff_certifiedCommonPlan).mp hdepth
  · rintro ⟨r, hcost, hplan⟩
    refine ⟨r, hcost, ?_⟩
    exact (depthAtMost_iff_certifiedCommonPlan).mpr hplan

/-- **Unknown-future destruction law in common-plan form.**
If Γ is safe before a transformation, then the transformation destroys no
possible Γ-future iff every Γ-bundle still admits some finite-horizon joint
certificate afterwards. -/
theorem noDestruction_iff_all_eventualCommonPlans_after
    {Q X : Type*} [DecidableEq Q]
    {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {T : X → X} {x : X}
    (hbefore : FamilyEventuallySafe Γ Avail Step x) :
    ¬ DestroysPossibleFuture Γ Avail Step x (T x) ↔
      ∀ F, F ∈ Γ →
        BundleFeasible
          (EventualCertifiedJointPlanGood
            (Avail := Avail) (Step := Step) (x := T x)) F := by
  constructor
  · intro hno
    have hrobust :
        RobustlyAdmissibleEventually Γ Avail Step T x :=
      (robustlyAdmissibleEventually_iff_not_destroys_of_before_safe hbefore).2 hno
    change FamilyEventuallySafe Γ Avail Step (T x) at hrobust
    exact (familyEventuallySafe_iff_all_eventualCertifiedCommonPlans).mp hrobust
  · intro hplans
    have hsafeAfter :
        FamilyEventuallySafe Γ Avail Step (T x) :=
      (familyEventuallySafe_iff_all_eventualCertifiedCommonPlans).mpr hplans
    have hrobust :
        RobustlyAdmissibleEventually Γ Avail Step T x := by
      exact hsafeAfter
    exact (robustlyAdmissibleEventually_iff_not_destroys_of_before_safe hbefore).1
      hrobust

/-- **Compact master law.**
Under a pre-transformation unknown-future guarantee, "allowed to transform
without destroying a possible future" is exactly "every declared possible
future still has some finite common-plan certificate afterwards". -/
theorem coreV1_master_unknownFutureLaw
    {Q X : Type*} [DecidableEq Q]
    {Γ : Set (Finset Q)}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {T : X → X} {x : X}
    (hbefore : FamilyEventuallySafe Γ Avail Step x) :
    RobustlyAdmissibleEventually Γ Avail Step T x ↔
      ∀ F, F ∈ Γ →
        BundleFeasible
          (EventualCertifiedJointPlanGood
            (Avail := Avail) (Step := Step) (x := T x)) F := by
  change FamilyEventuallySafe Γ Avail Step (T x) ↔ _
  exact familyEventuallySafe_iff_all_eventualCertifiedCommonPlans

end MasterClosureV1

end InsacermoActionabilityInformation
