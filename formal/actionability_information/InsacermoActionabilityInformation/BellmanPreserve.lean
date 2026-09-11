import InsacermoActionabilityInformation.SequentialPlanner

namespace InsacermoActionabilityInformation

/-- The tail of a valid nonempty plan is valid from the first move's target. -/
theorem validPlan_tail
    {X : Type*} {Legal : X → Move X → Prop}
    {x : X} {m : Move X} {ms : List (Move X)}
    (h : ValidPlanFrom Legal x (m :: ms)) :
    ValidPlanFrom Legal m.next ms :=
  h.2

/-- The tail of a safe-reaching nonempty plan still reaches the same safe region
from the first move's target. -/
theorem reachesSafe_tail
    {X : Type*} {Safe : X → Prop} {Legal : X → Move X → Prop}
    {x : X} {m : Move X} {ms : List (Move X)}
    (h : ReachesSafe Safe Legal x (m :: ms)) :
    ReachesSafe Safe Legal m.next ms := by
  exact ⟨h.1.2, h.2⟩

/-- A legal first move can be prepended to any safe-reaching continuation. -/
theorem reachesSafe_cons
    {X : Type*} {Safe : X → Prop} {Legal : X → Move X → Prop}
    {x : X} {m : Move X} {ms : List (Move X)}
    (hm : Legal x m)
    (hms : ReachesSafe Safe Legal m.next ms) :
    ReachesSafe Safe Legal x (m :: ms) := by
  exact ⟨⟨hm, hms.1⟩, hms.2⟩

/-- Bellman's principle of optimality for the INSACERMO finite-plan planner:
if a nonempty plan is globally minimum-cost from `x`, then its continuation is
globally minimum-cost from the state reached after the first move. -/
theorem optimalPlan_tail
    {X : Type*} {Safe : X → Prop} {Legal : X → Move X → Prop}
    {x : X} {m : Move X} {ms : List (Move X)}
    (hopt : OptimalPlan Safe Legal x (m :: ms)) :
    OptimalPlan Safe Legal m.next ms := by
  have hreachTail : ReachesSafe Safe Legal m.next ms := reachesSafe_tail hopt.1
  refine ⟨hreachTail, ?_⟩
  intro q hq
  have hlegal : Legal x m := hopt.1.1.1
  have hpre : ReachesSafe Safe Legal x (m :: q) := reachesSafe_cons hlegal hq
  have hcost := hopt.2 (m :: q) hpre
  simpa [planCost] using hcost

/-- No globally optimal plan can contain a strictly cheaper safe continuation
from the state after its first move. -/
theorem no_strictly_better_tail_of_optimal
    {X : Type*} {Safe : X → Prop} {Legal : X → Move X → Prop}
    {x : X} {m : Move X} {ms q : List (Move X)}
    (hopt : OptimalPlan Safe Legal x (m :: ms))
    (hq : ReachesSafe Safe Legal m.next q) :
    ¬ planCost q < planCost ms := by
  have htail := optimalPlan_tail hopt
  exact Nat.not_lt_of_ge (htail.2 q hq)

/-- Recursive certificate saying every information-losing step in a plan is
covered by the stage-local PRESERVE guard. -/
def PreserveCompliant {X : Type*}
    (PreserveOK : X → Move X → Prop) : X → List (Move X) → Prop
  | _, [] => True
  | x, m :: ms =>
      (m.forgets = true → PreserveOK x m) ∧
      PreserveCompliant PreserveOK m.next ms

/-- Any plan valid under `LegalStep BaseAllowed PreserveOK` is globally
PRESERVE-compliant at every forgetting transition. -/
theorem validPlan_legalStep_preserveCompliant
    {X : Type*}
    {BaseAllowed PreserveOK : X → Move X → Prop}
    {x : X} {p : List (Move X)}
    (hvalid : ValidPlanFrom (LegalStep BaseAllowed PreserveOK) x p) :
    PreserveCompliant PreserveOK x p := by
  induction p generalizing x with
  | nil =>
      trivial
  | cons m ms ih =>
      exact ⟨hvalid.1.2, ih hvalid.2⟩

/-- In particular, an optimal safe plan cannot bypass PRESERVE: every forgetting
move occurring in the optimum already carries its required preservation proof. -/
theorem optimalPlan_preserveCompliant
    {X : Type*}
    {Safe : X → Prop}
    {BaseAllowed PreserveOK : X → Move X → Prop}
    {x : X} {p : List (Move X)}
    (hopt : OptimalPlan Safe (LegalStep BaseAllowed PreserveOK) x p) :
    PreserveCompliant PreserveOK x p := by
  exact validPlan_legalStep_preserveCompliant hopt.1.1

/-- Bellman + PRESERVE composition: for an optimal nonempty plan under the
PRESERVE-aware legality relation, the first forgetting move is certified and
the remaining suffix is itself an optimal PRESERVE-aware safe plan. -/
theorem bellman_preserve_step
    {X : Type*}
    {Safe : X → Prop}
    {BaseAllowed PreserveOK : X → Move X → Prop}
    {x : X} {m : Move X} {ms : List (Move X)}
    (hopt : OptimalPlan Safe (LegalStep BaseAllowed PreserveOK) x (m :: ms)) :
    (m.forgets = true → PreserveOK x m) ∧
    OptimalPlan Safe (LegalStep BaseAllowed PreserveOK) m.next ms := by
  exact ⟨hopt.1.1.1.2, optimalPlan_tail hopt⟩

end InsacermoActionabilityInformation
