import Std
import CostlyProbeMinimal
import SafeProbeTheorem
import ProbeRepairKernel
import ProbePriceKernel
import ProbeReserveDebtBridge
import MultiProbeBudgetKernel

/-!
INSACERMO — Multi-Probe Planner Kernel V1

This layer does not invent a new opaque utility score.
Among candidate plans that satisfy the same external contract, it orders plans by
their certified total probe-repair price (sum of prices).

Core consequence:
if the selected contract-satisfying plan has no greater certified price than every
other contract-satisfying candidate, then the existence of any affordable
contract-satisfying candidate implies that the selected plan is affordable too.

Thus minimum certified probe price preserves at least as much reserve as any
compared contract-satisfying plan.
-/

namespace InsacermoMultiProbePlanner

open InsacermoMultiProbeBudget

def planPrice (prices : List Nat) : Nat :=
  prices.sum

def reserveLeft (rho0 debt : Nat) (prices : List Nat) : Nat :=
  rho0 - debtAfterPlan debt prices

theorem lower_price_gives_lower_debt
    (debt : Nat)
    (p q : List Nat)
    (hprice : planPrice p ≤ planPrice q) :
    debtAfterPlan debt p ≤ debtAfterPlan debt q := by
  unfold planPrice at hprice
  unfold debtAfterPlan
  omega

theorem lower_price_preserves_affordability
    (rho0 debt : Nat)
    (p q : List Nat)
    (hprice : planPrice p ≤ planPrice q)
    (hq : PlanAffordable rho0 debt q) :
    PlanAffordable rho0 debt p := by
  unfold PlanAffordable debtAfterPlan at *
  unfold planPrice at hprice
  omega

theorem lower_price_preserves_more_reserve
    (rho0 debt : Nat)
    (p q : List Nat)
    (hprice : planPrice p ≤ planPrice q) :
    reserveLeft rho0 debt q ≤ reserveLeft rho0 debt p := by
  unfold reserveLeft
  have hdebt := lower_price_gives_lower_debt debt p q hprice
  omega

def ContractOptimalPlan
    (Contract : List Nat → Prop)
    (chosen : List Nat) : Prop :=
  Contract chosen ∧
  ∀ other : List Nat, Contract other →
    planPrice chosen ≤ planPrice other

theorem optimal_contract_plan_is_affordable_if_any_is
    (rho0 debt : Nat)
    (Contract : List Nat → Prop)
    (chosen witness : List Nat)
    (hopt : ContractOptimalPlan Contract chosen)
    (hwitnessContract : Contract witness)
    (hwitnessAffordable : PlanAffordable rho0 debt witness) :
    PlanAffordable rho0 debt chosen := by
  rcases hopt with ⟨_, hmin⟩
  exact lower_price_preserves_affordability
    rho0 debt chosen witness (hmin witness hwitnessContract) hwitnessAffordable

theorem optimal_contract_plan_maximizes_reserve_left
    (rho0 debt : Nat)
    (Contract : List Nat → Prop)
    (chosen other : List Nat)
    (hopt : ContractOptimalPlan Contract chosen)
    (hother : Contract other) :
    reserveLeft rho0 debt other ≤ reserveLeft rho0 debt chosen := by
  rcases hopt with ⟨_, hmin⟩
  exact lower_price_preserves_more_reserve
    rho0 debt chosen other (hmin other hother)

theorem optimal_unaffordable_implies_all_contract_plans_unaffordable
    (rho0 debt : Nat)
    (Contract : List Nat → Prop)
    (chosen : List Nat)
    (hopt : ContractOptimalPlan Contract chosen)
    (hchosenUnsafe : ¬ PlanAffordable rho0 debt chosen) :
    ∀ other : List Nat, Contract other →
      ¬ PlanAffordable rho0 debt other := by
  intro other hother hotherAffordable
  apply hchosenUnsafe
  rcases hopt with ⟨_, hmin⟩
  exact lower_price_preserves_affordability
    rho0 debt chosen other (hmin other hother) hotherAffordable

theorem planner_afford_or_refuse
    (rho0 debt : Nat)
    (Contract : List Nat → Prop)
    (chosen : List Nat)
    (hopt : ContractOptimalPlan Contract chosen) :
    PlanAffordable rho0 debt chosen ∨
    (∀ other : List Nat, Contract other →
      ¬ PlanAffordable rho0 debt other) := by
  by_cases h : PlanAffordable rho0 debt chosen
  · exact Or.inl h
  · exact Or.inr
      (optimal_unaffordable_implies_all_contract_plans_unaffordable
        rho0 debt Contract chosen hopt h)

#print axioms lower_price_gives_lower_debt
#print axioms lower_price_preserves_affordability
#print axioms lower_price_preserves_more_reserve
#print axioms optimal_contract_plan_is_affordable_if_any_is
#print axioms optimal_contract_plan_maximizes_reserve_left
#print axioms optimal_unaffordable_implies_all_contract_plans_unaffordable
#print axioms planner_afford_or_refuse

end InsacermoMultiProbePlanner
