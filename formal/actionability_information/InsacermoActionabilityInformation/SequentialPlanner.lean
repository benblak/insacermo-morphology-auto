import InsacermoActionabilityInformation.SequentialPreserve

namespace InsacermoActionabilityInformation

/-- Forward repair classes. PRESERVE is deliberately not included: it is a
legality constraint on information-loss transitions, not a repair direction. -/
inductive MoveKind where
  | probe
  | repair
  | probeRepair
  deriving DecidableEq, Repr

/-- A candidate transition in the sequential planner. `forgets = true` marks
an information-losing move which must be separately certified by PRESERVE. -/
structure Move (X : Type*) where
  next : X
  kind : MoveKind
  cost : Nat
  forgets : Bool

/-- A transition is legal when the base transition contract permits it and,
if it forgets information, the PRESERVE guard certifies it. -/
def LegalStep {X : Type*}
    (BaseAllowed PreserveOK : X → Move X → Prop)
    (x : X) (m : Move X) : Prop :=
  BaseAllowed x m ∧ (m.forgets = true → PreserveOK x m)

/-- Every legal forgetting move carries a PRESERVE certificate. -/
theorem legal_forgetting_requires_preserve
    {X : Type*}
    {BaseAllowed PreserveOK : X → Move X → Prop}
    {x : X} {m : Move X}
    (hlegal : LegalStep BaseAllowed PreserveOK x m)
    (hforget : m.forgets = true) :
    PreserveOK x m :=
  hlegal.2 hforget

/-- State reached after executing a finite plan. -/
def finalState {X : Type*} : X → List (Move X) → X
  | x, [] => x
  | _, m :: ms => finalState m.next ms

/-- Additive natural-valued plan cost. Natural costs guarantee existence of a
minimum cost whenever at least one safe finite plan exists. -/
def planCost {X : Type*} : List (Move X) → Nat
  | [] => 0
  | m :: ms => m.cost + planCost ms

/-- All steps of a plan satisfy the legal transition contract. -/
def ValidPlanFrom {X : Type*}
    (Legal : X → Move X → Prop) : X → List (Move X) → Prop
  | _, [] => True
  | x, m :: ms => Legal x m ∧ ValidPlanFrom Legal m.next ms

/-- A legal plan terminates in the safe region. -/
def ReachesSafe {X : Type*}
    (Safe : X → Prop) (Legal : X → Move X → Prop)
    (x : X) (p : List (Move X)) : Prop :=
  ValidPlanFrom Legal x p ∧ Safe (finalState x p)

/-- There exists at least one finite legal plan from `x` into the safe region. -/
def ReachableSafe {X : Type*}
    (Safe : X → Prop) (Legal : X → Move X → Prop)
    (x : X) : Prop :=
  ∃ p, ReachesSafe Safe Legal x p

/-- A safe state is trivially reachable by the empty plan. -/
theorem reachableSafe_of_safe
    {X : Type*} {Safe : X → Prop} {Legal : X → Move X → Prop} {x : X}
    (hsafe : Safe x) :
    ReachableSafe Safe Legal x := by
  refine ⟨[], ?_⟩
  exact ⟨trivial, hsafe⟩

/-- REFUSE (no safe reachable state) implies the current state is not already
safe, because ACT always has the empty plan. -/
theorem not_safe_of_not_reachableSafe
    {X : Type*} {Safe : X → Prop} {Legal : X → Move X → Prop} {x : X}
    (hrefuse : ¬ ReachableSafe Safe Legal x) :
    ¬ Safe x := by
  intro hsafe
  exact hrefuse (reachableSafe_of_safe hsafe)

/-- Reachability constrained by a total sequential resource budget. -/
def ReachableSafeWithin {X : Type*}
    (Safe : X → Prop) (Legal : X → Move X → Prop)
    (budget : Nat) (x : X) : Prop :=
  ∃ p, ReachesSafe Safe Legal x p ∧ planCost p ≤ budget

/-- More sequential budget cannot destroy an already-feasible safe plan. -/
theorem reachableSafeWithin_mono
    {X : Type*} {Safe : X → Prop} {Legal : X → Move X → Prop}
    {b b' : Nat} {x : X}
    (hbb : b ≤ b')
    (h : ReachableSafeWithin Safe Legal b x) :
    ReachableSafeWithin Safe Legal b' x := by
  rcases h with ⟨p, hp, hcost⟩
  exact ⟨p, hp, le_trans hcost hbb⟩

/-- A safe-reaching plan with exactly total cost `n`. -/
def CanReachAtCost {X : Type*}
    (Safe : X → Prop) (Legal : X → Move X → Prop)
    (x : X) (n : Nat) : Prop :=
  ∃ p, ReachesSafe Safe Legal x p ∧ planCost p = n

/-- Whenever a safe finite plan exists, the set of its natural-valued costs
has a least element. This requires no finiteness assumption on the state graph. -/
theorem optimalCost_exists_of_reachable
    {X : Type*} {Safe : X → Prop} {Legal : X → Move X → Prop} {x : X}
    (hreach : ReachableSafe Safe Legal x) :
    ∃ n, CanReachAtCost Safe Legal x n ∧
      ∀ m, CanReachAtCost Safe Legal x m → n ≤ m := by
  classical
  have hex : ∃ n, CanReachAtCost Safe Legal x n := by
    rcases hreach with ⟨p, hp⟩
    exact ⟨planCost p, p, hp, rfl⟩
  let n := Nat.find hex
  refine ⟨n, Nat.find_spec hex, ?_⟩
  intro m hm
  exact Nat.find_min' hex hm

/-- Global minimum-cost safe plan. -/
def OptimalPlan {X : Type*}
    (Safe : X → Prop) (Legal : X → Move X → Prop)
    (x : X) (p : List (Move X)) : Prop :=
  ReachesSafe Safe Legal x p ∧
    ∀ q, ReachesSafe Safe Legal x q → planCost p ≤ planCost q

/-- Reachability implies existence of a globally minimum-cost finite plan. -/
theorem optimalPlan_exists_of_reachable
    {X : Type*} {Safe : X → Prop} {Legal : X → Move X → Prop} {x : X}
    (hreach : ReachableSafe Safe Legal x) :
    ∃ p, OptimalPlan Safe Legal x p := by
  rcases optimalCost_exists_of_reachable hreach with ⟨n, hn, hmin⟩
  rcases hn with ⟨p, hp, hpcost⟩
  refine ⟨p, hp, ?_⟩
  intro q hq
  calc
    planCost p = n := hpcost
    _ ≤ planCost q := hmin (planCost q) ⟨q, hq, rfl⟩

/-- First repair direction of a nonempty plan. -/
def firstKind {X : Type*} : List (Move X) → Option MoveKind
  | [] => none
  | m :: _ => some m.kind

/-- A repair kind belongs to the optimal router frontier when some globally
minimum-cost safe plan starts with that kind. Several kinds may coexist. -/
def OptimalFrontierKind {X : Type*}
    (Safe : X → Prop) (Legal : X → Move X → Prop)
    (x : X) (k : MoveKind) : Prop :=
  ∃ p, OptimalPlan Safe Legal x p ∧ firstKind p = some k

/-- Any unsafe but safely reachable state has a nonempty optimal route frontier. -/
theorem optimalFrontier_nonempty_of_unsafe_reachable
    {X : Type*} {Safe : X → Prop} {Legal : X → Move X → Prop} {x : X}
    (hunsafe : ¬ Safe x)
    (hreach : ReachableSafe Safe Legal x) :
    ∃ k, OptimalFrontierKind Safe Legal x k := by
  rcases optimalPlan_exists_of_reachable hreach with ⟨p, hp⟩
  cases p with
  | nil =>
      exfalso
      apply hunsafe
      simpa [OptimalPlan, ReachesSafe, finalState] using hp.1.2
  | cons m ms =>
      refine ⟨m.kind, ?_⟩
      exact ⟨m :: ms, hp, rfl⟩

/-- Static sequential router completeness.
Every state is exactly in one of three semantic regimes at the top level:
ACT now; REFUSE because no legal finite safe trajectory exists; or a nonempty
optimal repair frontier (whose members are PROBE, REPAIR, and/or PROBE+REPAIR).
The frontier is intentionally allowed to contain multiple incomparable kinds. -/
theorem planner_router_complete
    {X : Type*} (Safe : X → Prop) (Legal : X → Move X → Prop) (x : X) :
    Safe x ∨
      (¬ Safe x ∧ ¬ ReachableSafe Safe Legal x) ∨
      (¬ Safe x ∧ ReachableSafe Safe Legal x ∧
        ∃ k, OptimalFrontierKind Safe Legal x k) := by
  classical
  by_cases hsafe : Safe x
  · exact Or.inl hsafe
  · by_cases hreach : ReachableSafe Safe Legal x
    · exact Or.inr (Or.inr ⟨hsafe, hreach,
        optimalFrontier_nonempty_of_unsafe_reachable hsafe hreach⟩)
    · exact Or.inr (Or.inl ⟨hsafe, hreach⟩)

/-- The three top-level router regimes are pairwise exclusive in the expected
sense: ACT cannot also be REFUSE, and REFUSE cannot have an optimal frontier. -/
theorem act_not_refuse
    {X : Type*} {Safe : X → Prop} {Legal : X → Move X → Prop} {x : X}
    (hsafe : Safe x) :
    ¬ (¬ ReachableSafe Safe Legal x) := by
  intro h
  exact h (reachableSafe_of_safe hsafe)

end InsacermoActionabilityInformation
