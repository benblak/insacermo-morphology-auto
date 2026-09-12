import InsacermoActionabilityInformation.BeliefBellmanActionability
import InsacermoActionabilityInformation.SequentialPlanner

namespace InsacermoActionabilityInformation

/-- One declared planner candidate is safe exactly when its belief
representation and capability set satisfy the fixed Bellman-optimal
`SafeRep` contract. -/
def BellmanCandidateSafe
    {I S A O Y : Type*}
    [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (fallback : FiniteLaw S)
    (stageCost : FiniteLaw S → A → ℚ)
    (terminalCost : FiniteLaw S → ℚ)
    (n : Nat)
    (B : Set (FiniteLaw S))
    (caps : I → Set A)
    (obs : I → FiniteLaw S → Y)
    (i : I) : Prop :=
  BellmanSafeRep T Z fallback stageCost terminalCost n B (caps i) (obs i)

/-- Planner legality is the pre-existing sequential legality contract:
a base-allowed move is legal, and an information-losing move additionally
requires a PRESERVE certificate. -/
def BellmanPlannerLegal {I : Type*}
    (BaseAllowed PreserveOK : I → Move I → Prop) : I → Move I → Prop :=
  LegalStep BaseAllowed PreserveOK

/-- ACT at a candidate is definitionally the current Bellman actionability
predicate. -/
def BellmanPlannerAct
    {I S A O Y : Type*}
    [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (fallback : FiniteLaw S)
    (stageCost : FiniteLaw S → A → ℚ)
    (terminalCost : FiniteLaw S → ℚ)
    (n : Nat)
    (B : Set (FiniteLaw S))
    (caps : I → Set A)
    (obs : I → FiniteLaw S → Y)
    (i : I) : Prop :=
  BellmanCandidateSafe T Z fallback stageCost terminalCost n B caps obs i

/-- REFUSE means that no legal finite candidate trajectory reaches Bellman
actionability under the declared search graph and PRESERVE rules. -/
def BellmanPlannerRefuse
    {I S A O Y : Type*}
    [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (fallback : FiniteLaw S)
    (stageCost : FiniteLaw S → A → ℚ)
    (terminalCost : FiniteLaw S → ℚ)
    (n : Nat)
    (B : Set (FiniteLaw S))
    (caps : I → Set A)
    (obs : I → FiniteLaw S → Y)
    (BaseAllowed PreserveOK : I → Move I → Prop)
    (i : I) : Prop :=
  ¬ ReachableSafe
      (BellmanCandidateSafe T Z fallback stageCost terminalCost n B caps obs)
      (BellmanPlannerLegal BaseAllowed PreserveOK)
      i

/-- An optimal Bellman-planner frontier kind is a PROBE, REPAIR, or
PROBE+REPAIR first move of some globally minimum-cost legal route to a
Bellman-actionable candidate. -/
def BellmanOptimalFrontierKind
    {I S A O Y : Type*}
    [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (fallback : FiniteLaw S)
    (stageCost : FiniteLaw S → A → ℚ)
    (terminalCost : FiniteLaw S → ℚ)
    (n : Nat)
    (B : Set (FiniteLaw S))
    (caps : I → Set A)
    (obs : I → FiniteLaw S → Y)
    (BaseAllowed PreserveOK : I → Move I → Prop)
    (i : I) (k : MoveKind) : Prop :=
  OptimalFrontierKind
    (BellmanCandidateSafe T Z fallback stageCost terminalCost n B caps obs)
    (BellmanPlannerLegal BaseAllowed PreserveOK)
    i k

/-- Any Bellman-actionable current candidate is ACT by definition. -/
theorem bellmanPlanner_act_iff_current_safe
    {I S A O Y : Type*}
    [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    {T : A → S → FiniteLaw S}
    {Z : A → S → FiniteLaw O}
    {fallback : FiniteLaw S}
    {stageCost : FiniteLaw S → A → ℚ}
    {terminalCost : FiniteLaw S → ℚ}
    {n : Nat} {B : Set (FiniteLaw S)}
    {caps : I → Set A} {obs : I → FiniteLaw S → Y} {i : I} :
    BellmanPlannerAct T Z fallback stageCost terminalCost n B caps obs i ↔
      BellmanSafeRep T Z fallback stageCost terminalCost n B (caps i) (obs i) := by
  rfl

/-- Every legal information-losing belief-planner move must carry the declared
PRESERVE certificate. -/
theorem bellmanPlanner_forgetting_requires_preserve
    {I : Type*}
    {BaseAllowed PreserveOK : I → Move I → Prop}
    {i : I} {m : Move I}
    (hlegal : BellmanPlannerLegal BaseAllowed PreserveOK i m)
    (hforget : m.forgets = true) :
    PreserveOK i m := by
  exact legal_forgetting_requires_preserve hlegal hforget

/-- If a Bellman-actionable candidate is legally reachable, a globally
minimum-cost finite route exists. -/
theorem bellmanPlanner_optimalPlan_exists_of_reachable
    {I S A O Y : Type*}
    [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    {T : A → S → FiniteLaw S}
    {Z : A → S → FiniteLaw O}
    {fallback : FiniteLaw S}
    {stageCost : FiniteLaw S → A → ℚ}
    {terminalCost : FiniteLaw S → ℚ}
    {n : Nat} {B : Set (FiniteLaw S)}
    {caps : I → Set A} {obs : I → FiniteLaw S → Y}
    {BaseAllowed PreserveOK : I → Move I → Prop} {i : I}
    (hreach : ReachableSafe
      (BellmanCandidateSafe T Z fallback stageCost terminalCost n B caps obs)
      (BellmanPlannerLegal BaseAllowed PreserveOK) i) :
    ∃ p, OptimalPlan
      (BellmanCandidateSafe T Z fallback stageCost terminalCost n B caps obs)
      (BellmanPlannerLegal BaseAllowed PreserveOK) i p := by
  exact optimalPlan_exists_of_reachable hreach

/-- Every unsafe but reachable belief-planner state has a nonempty optimal
route frontier. Its witness kind is one of the constructor-level directions
PROBE, REPAIR, or PROBE+REPAIR. -/
theorem bellmanPlanner_frontier_nonempty_of_unsafe_reachable
    {I S A O Y : Type*}
    [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    {T : A → S → FiniteLaw S}
    {Z : A → S → FiniteLaw O}
    {fallback : FiniteLaw S}
    {stageCost : FiniteLaw S → A → ℚ}
    {terminalCost : FiniteLaw S → ℚ}
    {n : Nat} {B : Set (FiniteLaw S)}
    {caps : I → Set A} {obs : I → FiniteLaw S → Y}
    {BaseAllowed PreserveOK : I → Move I → Prop} {i : I}
    (hunsafe : ¬ BellmanCandidateSafe T Z fallback stageCost terminalCost n B caps obs i)
    (hreach : ReachableSafe
      (BellmanCandidateSafe T Z fallback stageCost terminalCost n B caps obs)
      (BellmanPlannerLegal BaseAllowed PreserveOK) i) :
    ∃ k, BellmanOptimalFrontierKind T Z fallback stageCost terminalCost n B
      caps obs BaseAllowed PreserveOK i k := by
  exact optimalFrontier_nonempty_of_unsafe_reachable hunsafe hreach

/-- Belief-space INSACERMO router completeness.
For every declared candidate state exactly the intended top-level alternatives
are available semantically: ACT now; REFUSE because no legal finite route can
reach Bellman actionability; or an unsafe but reachable state with a nonempty
globally minimum-cost PROBE / REPAIR / PROBE+REPAIR frontier. -/
theorem bellmanPlanner_router_complete
    {I S A O Y : Type*}
    [Fintype S] [Fintype A] [Nonempty A] [Fintype O]
    (T : A → S → FiniteLaw S)
    (Z : A → S → FiniteLaw O)
    (fallback : FiniteLaw S)
    (stageCost : FiniteLaw S → A → ℚ)
    (terminalCost : FiniteLaw S → ℚ)
    (n : Nat)
    (B : Set (FiniteLaw S))
    (caps : I → Set A)
    (obs : I → FiniteLaw S → Y)
    (BaseAllowed PreserveOK : I → Move I → Prop)
    (i : I) :
    BellmanPlannerAct T Z fallback stageCost terminalCost n B caps obs i ∨
      (¬ BellmanPlannerAct T Z fallback stageCost terminalCost n B caps obs i ∧
        BellmanPlannerRefuse T Z fallback stageCost terminalCost n B caps obs
          BaseAllowed PreserveOK i) ∨
      (¬ BellmanPlannerAct T Z fallback stageCost terminalCost n B caps obs i ∧
        ¬ BellmanPlannerRefuse T Z fallback stageCost terminalCost n B caps obs
          BaseAllowed PreserveOK i ∧
        ∃ k, BellmanOptimalFrontierKind T Z fallback stageCost terminalCost n B
          caps obs BaseAllowed PreserveOK i k) := by
  simpa [BellmanPlannerAct, BellmanPlannerRefuse, BellmanOptimalFrontierKind,
    BellmanPlannerLegal] using
    (planner_router_complete
      (BellmanCandidateSafe T Z fallback stageCost terminalCost n B caps obs)
      (LegalStep BaseAllowed PreserveOK) i)

end InsacermoActionabilityInformation
