import Std
import MultiProbePlannerKernel

/-!
INSACERMO — Proof-Carrying Multi-Probe Runtime Kernel V1

This kernel specializes the multi-probe planner theorem to the finite candidate
set that an executable runtime can actually audit.

A runtime REFUSE certificate is therefore scoped precisely:
it proves that no contract-satisfying plan in the supplied audited candidate set
is affordable under the strict reserve rule.
-/

namespace INSACERMO.ProofCarryingMultiProbeRuntimeV1

open InsacermoMultiProbeBudget
open InsacermoMultiProbePlanner

def FiniteCandidateOptimal
    (candidates : List (List Nat))
    (chosen : List Nat) : Prop :=
  chosen ∈ candidates ∧
  ∀ other : List Nat, other ∈ candidates →
    planPrice chosen ≤ planPrice other

theorem finite_optimal_affordable_if_any_candidate_is
    (rho0 debt : Nat)
    (candidates : List (List Nat))
    (chosen witness : List Nat)
    (hopt : FiniteCandidateOptimal candidates chosen)
    (hwitness : witness ∈ candidates)
    (haff : PlanAffordable rho0 debt witness) :
    PlanAffordable rho0 debt chosen := by
  rcases hopt with ⟨_, hmin⟩
  exact lower_price_preserves_affordability
    rho0 debt chosen witness (hmin witness hwitness) haff

theorem finite_optimal_unaffordable_refuses_all_candidates
    (rho0 debt : Nat)
    (candidates : List (List Nat))
    (chosen : List Nat)
    (hopt : FiniteCandidateOptimal candidates chosen)
    (hunsafe : ¬ PlanAffordable rho0 debt chosen) :
    ∀ other : List Nat, other ∈ candidates →
      ¬ PlanAffordable rho0 debt other := by
  intro other hmem haff
  apply hunsafe
  rcases hopt with ⟨_, hmin⟩
  exact lower_price_preserves_affordability
    rho0 debt chosen other (hmin other hmem) haff

structure RuntimePlanCertificate where
  rho0 : Nat
  debtBefore : Nat
  chosen : List Nat
  totalPrice : Nat
  debtAfter : Nat
  reserveLeft : Nat
  priceCorrect : totalPrice = planPrice chosen
  debtCorrect : debtAfter = debtAfterPlan debtBefore chosen
  reserveCorrect : reserveLeft = rho0 - debtAfter

def ExecuteCertificateSound (c : RuntimePlanCertificate) : Prop :=
  c.debtAfter < c.rho0

theorem execute_certificate_implies_plan_affordable
    (c : RuntimePlanCertificate)
    (hsound : ExecuteCertificateSound c) :
    PlanAffordable c.rho0 c.debtBefore c.chosen := by
  unfold ExecuteCertificateSound at hsound
  unfold PlanAffordable
  rw [← c.debtCorrect]
  exact hsound

theorem certificate_total_price_recomputes
    (c : RuntimePlanCertificate) :
    c.totalPrice = c.chosen.sum := by
  simpa [planPrice] using c.priceCorrect

theorem certificate_remaining_reserve_recomputes
    (c : RuntimePlanCertificate) :
    c.reserveLeft = c.rho0 - c.debtAfter := by
  exact c.reserveCorrect

inductive RuntimePlanVerdict where
  | execute
  | refuse
deriving DecidableEq, Repr

def CertifiedRuntimeVerdict
    (candidates : List (List Nat))
    (c : RuntimePlanCertificate)
    (v : RuntimePlanVerdict) : Prop :=
  FiniteCandidateOptimal candidates c.chosen ∧
  match v with
  | .execute => ExecuteCertificateSound c
  | .refuse => ¬ ExecuteCertificateSound c

theorem certified_execute_is_affordable
    (candidates : List (List Nat))
    (c : RuntimePlanCertificate)
    (h : CertifiedRuntimeVerdict candidates c .execute) :
    PlanAffordable c.rho0 c.debtBefore c.chosen := by
  exact execute_certificate_implies_plan_affordable c h.2

theorem certified_refuse_excludes_all_audited_candidates
    (candidates : List (List Nat))
    (c : RuntimePlanCertificate)
    (h : CertifiedRuntimeVerdict candidates c .refuse) :
    ∀ other : List Nat, other ∈ candidates →
      ¬ PlanAffordable c.rho0 c.debtBefore other := by
  rcases h with ⟨hopt, hnot⟩
  apply finite_optimal_unaffordable_refuses_all_candidates
    c.rho0 c.debtBefore candidates c.chosen hopt
  intro haff
  apply hnot
  unfold ExecuteCertificateSound
  have hraw : debtAfterPlan c.debtBefore c.chosen < c.rho0 := by
    exact haff
  rw [← c.debtCorrect] at hraw
  exact hraw

#print axioms finite_optimal_affordable_if_any_candidate_is
#print axioms finite_optimal_unaffordable_refuses_all_candidates
#print axioms execute_certificate_implies_plan_affordable
#print axioms certificate_total_price_recomputes
#print axioms certificate_remaining_reserve_recomputes
#print axioms certified_execute_is_affordable
#print axioms certified_refuse_excludes_all_audited_candidates

end INSACERMO.ProofCarryingMultiProbeRuntimeV1
