import C3.RecursiveTotalPlanKernelV1
import ExactRepairCheckerV1

/-!
INSACERMO TOTAL × C3 × REPAIR — TEMPORAL CONTRACT BRIDGE V1.

This bridge REUSES existing theorems:
- C3 recursive dynamic plans and verified policy trees
- exact rational linear REPAIR checker and dual budget impossibility.

An external future obligation is declared as FutureOK : Scenario → Recipe → Prop
and checked at every terminal reachable scenario, not silently discarded.
The repair matrix A, rhs, and allowed goods are FIXED across transformations:
if a transformation changes them, it requires an explicit updated model;
the global no-go theorem would not apply.

This is a proof of compatibility for this declared grammar, NOT a formal
refinement of every historical MAX TOTAL module, and not a universal solver.
-/

namespace INSACERMO.TotalRepairFuture

open INSACERMO.RecursiveC3
open INSACERMO.C3PP
open INSACERMO.C3
open InsacermoExactRepair

universe u v w
variable {Scenario : Type u} {Probe : Type v} {Outcome : Type w}

/-- A rational candidate provided by a constructor; proof verification is
    independent of how it was produced. -/
structure Recipe where
  amount : Nat → Nat
  denominator : Nat

/-- A dynamic C3 model whose final actions are exact repair candidates.
    Action cost is checked in good via exact 365*sum ≤ 40*denominator.
    C3 actionCost=0 because the annual budget is a constraint, not a
    fungible probe-budget charge. -/
def repairModel
    (m n : Nat) (A : Nat → Nat → Nat) (rhs : Nat → Nat)
    (allowed : Nat → Bool)
    (FutureOK : Scenario → Recipe → Prop)
    (probeOK : Probe → Prop) (probePrice : Probe → Nat)
    (observes : Probe → Scenario → Outcome → Prop)
    (transform : Probe → Outcome → Scenario → Scenario) :
    DynamicProblem Scenario Recipe Probe Outcome :=
  { base :=
    { allowed := fun p => p.denominator > 0
      probeAllowed := probeOK
      good := fun p s =>
        checkPrimal m n A rhs allowed p.amount p.denominator = true ∧
        365 * sumN n p.amount ≤ 40 * p.denominator ∧ FutureOK s p
      observes := observes
      actionCost := fun _ => 0
      probeCost := probePrice }
    transform := transform }

/-- A property of a plan: every reachable terminal branch obeys its
    declared future obligation. -/
def FutureCertified
    (M : DynamicProblem Scenario Recipe Probe Outcome)
    (FutureOK : Scenario → Recipe → Prop) :
    Nat → (Scenario → Prop) → Plan Recipe Probe Outcome → Prop
  | 0, X, .act p => ∀ s, X s → FutureOK s p
  | 0, _, .probe _ _ => False
  | _ + 1, X, .act p => ∀ s, X s → FutureOK s p
  | k + 1, X, .probe q next =>
      ∀ o, FutureCertified M FutureOK k (AfterDynamic M q X o) (next o)

/-- A verified C3 repair tree cannot skip future obligations, including
    obligations on states reached after branching and transformation. -/
theorem verified_plan_preserves_all_declared_futures
    (m n : Nat) (A : Nat → Nat → Nat) (rhs : Nat → Nat)
    (allowed : Nat → Bool)
    (FutureOK : Scenario → Recipe → Prop)
    (probeOK : Probe → Prop) (probePrice : Probe → Nat)
    (observes : Probe → Scenario → Outcome → Prop)
    (transform : Probe → Outcome → Scenario → Scenario)
    (depth : Nat) :
    ∀ (budget : Nat) (X : Scenario → Prop)
      (t : Plan Recipe Probe Outcome),
      PlanValid
        (repairModel m n A rhs allowed FutureOK probeOK probePrice observes transform)
        depth budget X t →
      FutureCertified
        (repairModel m n A rhs allowed FutureOK probeOK probePrice observes transform)
        FutureOK depth X t := by
  induction depth with
  | zero =>
      intro budget X t hv
      cases t with
      | act p =>
          intro s hs
          exact (hv.2.2 s hs).2.2
      | probe q next =>
          exact False.elim hv
  | succ depth ih =>
      intro budget X t hv
      cases t with
      | act p =>
          intro s hs
          exact (hv.2.2 s hs).2.2
      | probe q next =>
          intro o
          exact ih _ _ _ (hv.2.2.2 o)

/-- A constructive witness produces a verified C3 policy-tree certificate
    that includes both the annual LP constraints AND the future obligations. -/
theorem certified_repair_constructive
    (m n : Nat) (A : Nat → Nat → Nat) (rhs : Nat → Nat)
    (allowed : Nat → Bool)
    (FutureOK : Scenario → Recipe → Prop)
    (probeOK : Probe → Prop) (probePrice : Probe → Nat)
    (observes : Probe → Scenario → Outcome → Prop)
    (transform : Probe → Outcome → Scenario → Scenario)
    (p : Recipe) (X : Scenario → Prop) (depth budget : Nat)
    (hD : p.denominator > 0)
    (hprimal : checkPrimal m n A rhs allowed p.amount p.denominator = true)
    (hbudget : 365 * sumN n p.amount ≤ 40 * p.denominator)
    (hfuture : ∀ s, X s → FutureOK s p) :
    PlanValid
      (repairModel m n A rhs allowed FutureOK probeOK probePrice observes transform)
      depth budget X (.act p) := by
  cases depth with
  | zero =>
      exact ⟨hD, Nat.zero_le _, fun s hs => ⟨hprimal, hbudget, hfuture s hs⟩⟩
  | succ k =>
      exact ⟨hD, Nat.zero_le _, fun s hs => ⟨hprimal, hbudget, hfuture s hs⟩⟩

/-- An uncertain true envelope X between L and U inherits any C3 plan
    guaranteed for U, even after recursive transformations. -/
theorem unknown_future_envelope_sound
    (M : DynamicProblem Scenario Recipe Probe Outcome)
    (L X U : Scenario → Prop)
    (hLX : Incl L X) (hXU : Incl X U)
    (depth budget : Nat)
    (hU : CanDynamic M depth budget U) :
    CanDynamic M depth budget X :=
  can_dynamic_world_monotone M depth budget U X hXU hU

/-- If any feasible annual construction exists in a world, a valid LP
    primal candidate must exist; a dual infeasibility certificate blocks it.
    This is independent of the C3 probe/transform grammar, provided these
    operations do not alter A, rhs, or the admissible resources. -/
theorem impossible_direct_if_dual_gap
    (m n : Nat) (A : Nat → Nat → Nat) (rhs : Nat → Nat)
    (allowed : Nat → Bool)
    (FutureOK : Scenario → Recipe → Prop)
    (probeOK : Probe → Prop) (probePrice : Probe → Nat)
    (observes : Probe → Scenario → Outcome → Prop)
    (transform : Probe → Outcome → Scenario → Scenario)
    (y : Nat → Nat) (E : Nat)
    (hdual : checkDual m n A allowed y E = true)
    (hgap : 40 * (10 * E) < 365 * sumN m (fun i => rhs i * y i))
    (X : Scenario → Prop) (hne : ∃ s, X s) (budget : Nat) :
    ¬ Direct
      (repairModel m n A rhs allowed FutureOK probeOK probePrice observes transform).base
      budget X := by
  rintro ⟨p, hpAllowed, hpCost, hpGood⟩
  obtain ⟨s, hs⟩ := hne
  rcases hpGood s hs with ⟨hpr, hb, hfuture⟩
  have hprValid := checked_primal_sound m n A rhs allowed p.amount p.denominator hpr
  have hImpossible :=
    checked_budget_impossible m n A rhs allowed y E hdual hgap
      p.denominator hpAllowed p.amount hprValid
  exact hImpossible hb

/-- MAIN COMPOSITION NO-GO:
    a dual proof of insufficient resources means NO finite C3 policy tree
    can solve any nonempty declared future scenario envelope, no matter how
    deep the branching, when probes cannot change fixed resource constraints.
    FutureOK is arbitrary: we do not "repair" a failed present contract by
    silently relaxing a future one. -/
theorem dual_certificate_blocks_every_dynamic_plan
    (m n : Nat) (A : Nat → Nat → Nat) (rhs : Nat → Nat)
    (allowed : Nat → Bool)
    (FutureOK : Scenario → Recipe → Prop)
    (probeOK : Probe → Prop) (probePrice : Probe → Nat)
    (observes : Probe → Scenario → Outcome → Prop)
    (transform : Probe → Outcome → Scenario → Scenario)
    (y : Nat → Nat) (E : Nat)
    (hdual : checkDual m n A allowed y E = true)
    (hgap : 40 * (10 * E) < 365 * sumN m (fun i => rhs i * y i))
    (depth : Nat) :
    ∀ budget X, (∃ s, X s) →
      ¬ CanDynamic
        (repairModel m n A rhs allowed FutureOK probeOK probePrice observes transform)
        depth budget X := by
  induction depth with
  | zero =>
      intro budget X hne can
      exact impossible_direct_if_dual_gap
        m n A rhs allowed FutureOK probeOK probePrice observes transform
        y E hdual hgap X hne budget can
  | succ k ih =>
      intro budget X hne can
      cases can with
      | inl direct =>
          exact impossible_direct_if_dual_gap
            m n A rhs allowed FutureOK probeOK probePrice observes transform
            y E hdual hgap X hne budget direct
      | inr branch =>
          rcases branch with ⟨q, hq, hc, htotal, hbranches⟩
          obtain ⟨s, hs⟩ := hne
          obtain ⟨o, ho⟩ := htotal s hs
          let M := repairModel m n A rhs allowed FutureOK probeOK probePrice observes transform
          have hneAfter : ∃ t, AfterDynamic M q X o t :=
            ⟨M.transform q o s, s, hs, ho, rfl⟩
          exact ih _ _ hneAfter (hbranches o)

/-- A dual witness excludes robust plans for any true future belief X
    satisfying L subset X, provided L is nonempty. -/
theorem epistemic_lower_envelope_dual_refusal
    (m n : Nat) (A : Nat → Nat → Nat) (rhs : Nat → Nat)
    (allowed : Nat → Bool)
    (FutureOK : Scenario → Recipe → Prop)
    (probeOK : Probe → Prop) (probePrice : Probe → Nat)
    (observes : Probe → Scenario → Outcome → Prop)
    (transform : Probe → Outcome → Scenario → Scenario)
    (y : Nat → Nat) (E : Nat)
    (hdual : checkDual m n A allowed y E = true)
    (hgap : 40 * (10 * E) < 365 * sumN m (fun i => rhs i * y i))
    (L X : Scenario → Prop) (hLX : Incl L X) (hneL : ∃ s, L s)
    (depth budget : Nat) :
    ¬ CanDynamic
      (repairModel m n A rhs allowed FutureOK probeOK probePrice observes transform)
      depth budget X := by
  obtain ⟨s, hs⟩ := hneL
  exact dual_certificate_blocks_every_dynamic_plan
    m n A rhs allowed FutureOK probeOK probePrice observes transform
    y E hdual hgap depth budget X ⟨s, hLX s hs⟩

end INSACERMO.TotalRepairFuture
