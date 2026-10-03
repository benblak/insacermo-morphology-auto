import Std
import CostlyProbeMinimal
import SafeProbeTheorem
import ProbeRepairKernel

/-!
INSACERMO — Probe Price Kernel V1

This layer turns structural minimal repair into cost minimality.

No particular numerical cost formula is assumed. Instead, a repair cost may take values
in any preordered type and only has to be monotone under inclusion:
repairing more worlds cannot be cheaper than repairing a subset.

For a fixed observation fiber and a fixed candidate action, the exact RepairSet from
ProbeRepairKernel is then automatically cost-minimal among all sufficient repairs.

A second theorem lifts this to a globally optimal candidate action: if a candidate a*
has repair-set cost no larger than every other candidate action, then its repair set is
no more expensive than any sufficient single-action repair whatsoever.
-/

namespace InsacermoProbePrice

/-- Monotonicity of a repair cost under set inclusion. -/
def MonotoneRepairCost {W C : Type} [Preorder C]
    (cost : (W → Prop) → C) : Prop :=
  ∀ R S : W → Prop,
    (∀ w : W, R w → S w) →
    cost R ≤ cost S

/--
For a fixed candidate action, the exact structural RepairSet is cost-minimal
for every monotone repair cost.
-/
theorem repairset_is_cost_minimal_for_action
    {W A O C : Type}
    [DecidableEq O]
    [Preorder C]
    (feasible : W → A → Prop)
    (observe : W → O)
    (o : O)
    (a : A)
    (cost : (W → Prop) → C)
    (hcost : MonotoneRepairCost cost)
    (R : W → Prop)
    (hR : ∀ w : W, observe w = o →
      InsacermoProbeRepair.RepairedFeasible feasible R a w a) :
    cost (InsacermoProbeRepair.RepairSet feasible observe o a) ≤ cost R := by
  apply hcost
  exact InsacermoProbeRepair.repairset_is_minimal feasible observe o a R hR

/--
A candidate action aStar is optimal on the fiber when the cost of its exact RepairSet
is no larger than the repair-set cost for any other action.
-/
def OptimalRepairAction
    {W A O C : Type}
    [DecidableEq O]
    [Preorder C]
    (feasible : W → A → Prop)
    (observe : W → O)
    (o : O)
    (cost : (W → Prop) → C)
    (aStar : A) : Prop :=
  ∀ a : A,
    cost (InsacermoProbeRepair.RepairSet feasible observe o aStar) ≤
    cost (InsacermoProbeRepair.RepairSet feasible observe o a)

/--
Global single-action optimality:
if aStar minimizes exact repair-set cost across candidate actions, then the repair
for aStar costs no more than any sufficient repair R for any candidate action a.
-/
theorem optimal_action_gives_global_single_action_minimum
    {W A O C : Type}
    [DecidableEq O]
    [Preorder C]
    (feasible : W → A → Prop)
    (observe : W → O)
    (o : O)
    (cost : (W → Prop) → C)
    (hcost : MonotoneRepairCost cost)
    (aStar a : A)
    (hopt : OptimalRepairAction feasible observe o cost aStar)
    (R : W → Prop)
    (hR : ∀ w : W, observe w = o →
      InsacermoProbeRepair.RepairedFeasible feasible R a w a) :
    cost (InsacermoProbeRepair.RepairSet feasible observe o aStar) ≤ cost R := by
  exact le_trans
    (hopt a)
    (repairset_is_cost_minimal_for_action feasible observe o a cost hcost R hR)

/--
If the candidate action is already common on the fiber, its exact RepairSet is empty,
so every monotone cost ranks it no above any repair that contains the empty set.
-/
theorem common_action_has_empty_repair
    {W A O : Type}
    [DecidableEq O]
    (feasible : W → A → Prop)
    (observe : W → O)
    (o : O)
    (a : A)
    (hcommon : ∀ w : W, observe w = o → feasible w a) :
    ∀ w : W, ¬ InsacermoProbeRepair.RepairSet feasible observe o a w := by
  exact InsacermoProbeRepair.repairset_empty_when_common feasible observe o a hcommon

#print axioms repairset_is_cost_minimal_for_action
#print axioms optimal_action_gives_global_single_action_minimum
#print axioms common_action_has_empty_repair

end InsacermoProbePrice
