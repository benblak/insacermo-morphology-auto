import Std
import CostlyProbeMinimal
import SafeProbeTheorem
import ProbeRepairKernel
import ProbePriceKernel
import ProbeReserveDebtBridge

/-!
INSACERMO — Multi-Probe Budget Kernel V1

A probe plan is represented by a list of certified nonnegative repair prices.
The existing debt is carried forward additively.

The strict INSACERMO reserve rule remains unchanged:
  finalDebt < rho0

This file proves the elementary but crucial planning invariant:
if a whole multi-probe plan is affordable, then its first probe is affordable and
the remaining suffix is affordable from the updated debt. Therefore execution can
proceed recursively without silently crossing the reserve boundary.
-/

namespace InsacermoMultiProbeBudget

/-- Debt after paying a sequence of certified probe prices. -/
def debtAfterPlan (debt : Nat) (prices : List Nat) : Nat :=
  debt + prices.sum

/-- A complete probe-price plan respects the same strict reserve rule. -/
def PlanAffordable (rho0 debt : Nat) (prices : List Nat) : Prop :=
  debtAfterPlan debt prices < rho0

theorem empty_plan_iff_existing_safe
    (rho0 debt : Nat) :
    PlanAffordable rho0 debt [] ↔
      InsacermoProbeReserveDebt.DebtSafe rho0 debt := by
  simp [PlanAffordable, debtAfterPlan, InsacermoProbeReserveDebt.DebtSafe]

/-- A one-probe plan is exactly the previously certified bridge rule. -/
theorem singleton_plan_iff_probe_affordable
    (rho0 debt price : Nat) :
    PlanAffordable rho0 debt [price] ↔
      InsacermoProbeReserveDebt.ProbeAffordable rho0 debt price := by
  simp [PlanAffordable, debtAfterPlan, InsacermoProbeReserveDebt.ProbeAffordable,
    Nat.add_assoc]

/--
Recursive budget law: an affordable nonempty plan has an affordable first probe,
and its suffix is affordable from the updated debt.
-/
theorem affordable_cons_decomposes
    (rho0 debt price : Nat)
    (rest : List Nat)
    (h : PlanAffordable rho0 debt (price :: rest)) :
    InsacermoProbeReserveDebt.ProbeAffordable rho0 debt price ∧
    PlanAffordable rho0 (debt + price) rest := by
  unfold PlanAffordable debtAfterPlan at h
  simp only [List.sum_cons] at h
  constructor
  · unfold InsacermoProbeReserveDebt.ProbeAffordable
    omega
  · unfold PlanAffordable debtAfterPlan
    simpa [Nat.add_assoc] using h

/--
Conversely, if the remaining suffix is affordable after paying the first price,
then the whole plan is affordable.
-/
theorem affordable_cons_of_suffix
    (rho0 debt price : Nat)
    (rest : List Nat)
    (hrest : PlanAffordable rho0 (debt + price) rest) :
    PlanAffordable rho0 debt (price :: rest) := by
  unfold PlanAffordable debtAfterPlan at *
  simpa [Nat.add_assoc] using hrest

/--
Exact recursion law for multi-probe affordability.
-/
theorem affordable_cons_iff_suffix
    (rho0 debt price : Nat)
    (rest : List Nat) :
    PlanAffordable rho0 debt (price :: rest) ↔
    PlanAffordable rho0 (debt + price) rest := by
  constructor
  · intro h
    exact (affordable_cons_decomposes rho0 debt price rest h).2
  · intro h
    exact affordable_cons_of_suffix rho0 debt price rest h

/--
Any affordable plan leaves the current debt itself strictly below reserve.
-/
theorem plan_affordable_implies_current_safe
    (rho0 debt : Nat)
    (prices : List Nat)
    (h : PlanAffordable rho0 debt prices) :
    InsacermoProbeReserveDebt.DebtSafe rho0 debt := by
  unfold PlanAffordable debtAfterPlan at h
  unfold InsacermoProbeReserveDebt.DebtSafe
  omega

/--
Adding another nonnegative certified probe price to an affordable plan may only
consume reserve; if the extended plan is affordable, the original plan is affordable.
-/
theorem affordable_append_implies_prefix
    (rho0 debt price : Nat)
    (prices : List Nat)
    (h : PlanAffordable rho0 debt (prices ++ [price])) :
    PlanAffordable rho0 debt prices := by
  unfold PlanAffordable debtAfterPlan at *
  simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  omega

/--
Strict boundary remains strict for plans: equality with reserve is refused.
-/
theorem plan_at_reserve_is_refused
    (rho0 debt : Nat)
    (prices : List Nat)
    (h : debtAfterPlan debt prices = rho0) :
    ¬ PlanAffordable rho0 debt prices := by
  unfold PlanAffordable
  omega

#print axioms empty_plan_iff_existing_safe
#print axioms singleton_plan_iff_probe_affordable
#print axioms affordable_cons_decomposes
#print axioms affordable_cons_of_suffix
#print axioms affordable_cons_iff_suffix
#print axioms plan_affordable_implies_current_safe
#print axioms affordable_append_implies_prefix
#print axioms plan_at_reserve_is_refused

end InsacermoMultiProbeBudget
