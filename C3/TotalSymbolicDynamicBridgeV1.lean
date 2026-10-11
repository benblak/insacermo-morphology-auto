import C3.AdaptiveBudgetKernel
import DynamicJointureKernelV1
import SymbolicTransformationSynthesisV1
import MaxDualSynthesisCertificateV1

/-!
INSACERMO TOTAL C3 integration (2026-10-11).
Real bridge across the already verified historical kernels:
* dynamic branch image for observation + state transformation
* symbolic optimal control and repair WITHOUT a command catalogue
* C3++ finite-horizon cost-constrained planner
* independently checkable existence and impossibility witnesses.

Scope: deterministic observation, declared law set and transitions, static branch
transformation, exact one-dimensional interval constraints, natural-number budget.
No claim about an unconstrained or fully general runtime.
-/

namespace INSACERMO.TotalC3

open INSACERMO.C3
open INSACERMO.C3PP
open InsacermoSymbolic
open InsacermoDynamic

universe u v
variable {Law : Type u} {Outcome : Type v}

abbrev Scenario (Law : Type u) := Bound × Law
abbrev Control := Nat × Nat

/-- Control and repair are synthesized from interval constraints.
    The only charged final-action resource is the repair reserve. -/
def intervalProblem (Law : Type u) (Outcome : Type v)
    (observe : Scenario Law → Outcome) (probePrice : Nat) :
    Problem (Scenario Law) Control Unit Outcome where
  allowed := fun _ => True
  probeAllowed := fun _ => True
  good := fun p s => s.1.1 ≤ p.1 ∧ p.1 ≤ s.1.2 + p.2
  observes := fun _ s o => observe s = o
  actionCost := fun p => p.2
  probeCost := fun _ => probePrice

def branchImage (observe : Scenario Law → Outcome)
    (transform : Outcome → Scenario Law → Scenario Law)
    (X : Scenario Law → Prop) (o : Outcome) : Scenario Law → Prop :=
  BranchImage observe transform X o

/-- Each transformed observable scenario appears in the symbolic constraint list. -/
def Covers (observe : Scenario Law → Outcome)
    (transform : Outcome → Scenario Law → Scenario Law)
    (X : Scenario Law → Prop) (groups : Outcome → List Bound) : Prop :=
  ∀ o y, branchImage observe transform X o y → y.1 ∈ groups o

/-- No artificial constraints: every listed branch constraint has a real
    possible transformed scenario as a witness (law is kept in the scenario). -/
def Realizes (observe : Scenario Law → Outcome)
    (transform : Outcome → Scenario Law → Scenario Law)
    (X : Scenario Law → Prop) (groups : Outcome → List Bound) : Prop :=
  ∀ o c, c ∈ groups o → ∃ y, branchImage observe transform X o y ∧ y.1 = c

def candidate (xs : List Bound) : Control := (demand xs, optimalRepair xs)

theorem candidate_is_feasible (xs : List Bound) :
    Feasible xs (candidate xs).1 (candidate xs).2 :=
  synthesized_sound xs

/-- Actual constructive bridge: the 2026-10-10 symbolic synthesis theorem
    produces a C3++ policy witness valid on the transformed branch. -/
theorem branch_direct_constructive
    (observe : Scenario Law → Outcome)
    (transform : Outcome → Scenario Law → Scenario Law)
    (groups : Outcome → List Bound) (X : Scenario Law → Prop)
    (hcover : Covers observe transform X groups)
    (o : Outcome) (budget : Nat)
    (hbudget : optimalRepair (groups o) ≤ budget) :
    Direct (intervalProblem Law Outcome observe 0) budget
      (branchImage observe transform X o) := by
  refine ⟨candidate (groups o), trivial, ?_, ?_⟩
  · exact hbudget
  · intro y hy
    exact candidate_is_feasible (groups o) y.1 (hcover o y hy)

/-- A realizability certificate prevents us from claiming impossibility merely
    because the branch list contained fictitious or unobserved constraints. -/
theorem branch_direct_lower_bound
    (observe : Scenario Law → Outcome)
    (transform : Outcome → Scenario Law → Scenario Law)
    (groups : Outcome → List Bound) (X : Scenario Law → Prop)
    (hreal : Realizes observe transform X groups)
    (o : Outcome) (budget : Nat)
    (h : Direct (intervalProblem Law Outcome observe 0) budget
      (branchImage observe transform X o)) :
    optimalRepair (groups o) ≤ budget := by
  rcases h with ⟨p, hp, hprice, hgood⟩
  have hf : Feasible (groups o) p.1 p.2 := by
    intro c hc
    obtain ⟨y, hy, hcy⟩ := hreal o c hc
    have hyGood := hgood y hy
    change y.1.1 ≤ p.1 ∧ p.1 ≤ y.1.2 + p.2 at hyGood
    simpa [hcy] using hyGood
  exact Nat.le_trans (synthesized_minimal (groups o) p.1 p.2 hf) hprice

/-- Necessary AND sufficient repair budget, for each chosen dynamic branch.
    This is not just a restatement: it composes two older kernels and C3++. -/
theorem branch_direct_iff_budget
    (observe : Scenario Law → Outcome)
    (transform : Outcome → Scenario Law → Scenario Law)
    (groups : Outcome → List Bound) (X : Scenario Law → Prop)
    (hcover : Covers observe transform X groups)
    (hreal : Realizes observe transform X groups)
    (o : Outcome) (budget : Nat) :
    Direct (intervalProblem Law Outcome observe 0) budget
      (branchImage observe transform X o) ↔
      optimalRepair (groups o) ≤ budget := by
  constructor
  · exact branch_direct_lower_bound observe transform groups X hreal o budget
  · exact branch_direct_constructive observe transform groups X hcover o budget

/-- If an observed branch needs more reserve than the budget, no control
    policy in the declared numeric grammar can satisfy that branch. -/
theorem branch_budget_refusal
    (observe : Scenario Law → Outcome)
    (transform : Outcome → Scenario Law → Scenario Law)
    (groups : Outcome → List Bound) (X : Scenario Law → Prop)
    (hreal : Realizes observe transform X groups)
    (o : Outcome) (budget : Nat)
    (hgap : budget < optimalRepair (groups o)) :
    ¬ Direct (intervalProblem Law Outcome observe 0) budget
       (branchImage observe transform X o) := by
  intro h
  have hbound := branch_direct_lower_bound observe transform groups X hreal o budget h
  exact Nat.not_le_of_gt hgap hbound

/-- This is the original dynamic observation/transform operator,
    instantiated with the new C3++ feasibility predicate. -/
theorem dynamic_probe_iff_symbolic_budgets
    (observe : Scenario Law → Outcome)
    (transform : Outcome → Scenario Law → Scenario Law)
    (groups : Outcome → List Bound) (X : Scenario Law → Prop)
    (hcover : Covers observe transform X groups)
    (hreal : Realizes observe transform X groups)
    (budget : Nat) :
    ProbeOp (fun _ => True) observe transform
      (Direct (intervalProblem Law Outcome observe 0) budget) X ↔
      ∀ o, optimalRepair (groups o) ≤ budget := by
  constructor
  · intro h o
    exact (branch_direct_iff_budget observe transform groups X hcover hreal o budget).mp (h.2 o)
  · intro h
    exact ⟨(by intro s hs; trivial),
      (fun o => (branch_direct_iff_budget observe transform groups X hcover hreal o budget).mpr (h o))⟩

/-- A direct, inspectable certificate contains an explicit control and reserve.
    Its correctness is derived from the historical synthesis theorem. -/
theorem branch_certificate
    (observe : Scenario Law → Outcome)
    (transform : Outcome → Scenario Law → Scenario Law)
    (groups : Outcome → List Bound) (X : Scenario Law → Prop)
    (hcover : Covers observe transform X groups) (o : Outcome) :
    ∀ y, branchImage observe transform X o y →
      y.1.1 ≤ (candidate (groups o)).1 ∧
      (candidate (groups o)).1 ≤ y.1.2 + (candidate (groups o)).2 := by
  intro y hy
  exact candidate_is_feasible (groups o) y.1 (hcover o y hy)

/-- The bridge to the C3++ Bellman recursion for an observation that does not
    change the state. With state changes, the dynamic theorem above applies;
    full multi-step transformed-state Bellman remains future work. -/
theorem identity_probe_enters_bellman
    (observe : Scenario Law → Outcome)
    (groups : Outcome → List Bound) (X : Scenario Law → Prop)
    (hcover : Covers observe (fun _ s => s) X groups)
    (probePrice budget : Nat)
    (hprice : probePrice ≤ budget)
    (hbranches : ∀ o, optimalRepair (groups o) ≤ budget - probePrice) :
    Can (intervalProblem Law Outcome observe probePrice) 1 budget X := by
  apply Or.inr
  refine ⟨(), trivial, hprice, ?_, ?_⟩
  · intro s hs
    exact ⟨observe s, rfl⟩
  · intro o
    have hd :
        Direct (intervalProblem Law Outcome observe 0) (budget - probePrice)
          (branchImage observe (fun _ s => s) X o) :=
      branch_direct_constructive observe (fun _ s => s) groups X hcover o
        (budget - probePrice) (hbranches o)
    have hsub :
        Incl (After (intervalProblem Law Outcome observe probePrice) () X o)
          (branchImage observe (fun _ s => s) X o) := by
      intro s hs
      exact ⟨s, hs.1, hs.2, rfl⟩
    exact direct_sound (intervalProblem Law Outcome observe probePrice)
      (budget - probePrice) hsub hd

/-- The older coupled 3-variable obstruction remains an explicit, independent
    certificate: zero repair is impossible, one unit is sufficient. -/
theorem coupled_minimal_repair_certificate (r : Nat) :
    (∃ u v w : Nat, InsacermoMaxDual.Feasible3 u v w r) ↔ 1 ≤ r :=
  InsacermoMaxDual.exact_minimal_repair r

end INSACERMO.TotalC3
