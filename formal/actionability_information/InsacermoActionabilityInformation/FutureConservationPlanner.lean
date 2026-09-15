import InsacermoActionabilityInformation.FutureDebt

namespace InsacermoActionabilityInformation

namespace FutureConservationPlanner

/-- Abstract INSACERMO planning state.  Each state carries the set of required
futures currently in debt. -/
structure DebtState (Q X : Type*) where
  world : X
  debt : Set Q

/-- A transition is debt-nonincreasing when it cannot introduce a newly
unmet required future. -/
def DebtNonIncreasing {Q X : Type*}
    (Step : DebtState Q X → DebtState Q X → Prop) : Prop :=
  ∀ s t, Step s t → t.debt ⊆ s.debt

/-- Zero debt is the planner target. -/
def Goal {Q X : Type*} (s : DebtState Q X) : Prop :=
  s.debt = ∅

/-- Reflexive-transitive reachability under an abstract transition relation. -/
inductive Reach {α : Type*} (Step : α → α → Prop) : α → α → Prop
  | refl (s : α) : Reach Step s s
  | tail {s t u : α} : Reach Step s t → Step t u → Reach Step s u

/-- Debt monotonicity lifts from one step to every finite plan. -/
theorem reach_debt_subset
    {Q X : Type*} {Step : DebtState Q X → DebtState Q X → Prop}
    (hmono : DebtNonIncreasing Step) :
    ∀ {s t}, Reach Step s t → t.debt ⊆ s.debt := by
  intro s t hreach
  induction hreach with
  | refl => exact Set.Subset.rfl
  | tail hreach hstep ih =>
      exact Set.Subset.trans (hmono _ _ hstep) ih

/-- Once zero debt is reached, every debt-nonincreasing continuation remains
at zero debt.  This is the abstract PRESERVE invariant. -/
theorem zeroDebt_absorbing
    {Q X : Type*} {Step : DebtState Q X → DebtState Q X → Prop}
    (hmono : DebtNonIncreasing Step)
    {s t : DebtState Q X} (hs : Goal s) (hreach : Reach Step s t) :
    Goal t := by
  have hsub : t.debt ⊆ s.debt := reach_debt_subset hmono hreach
  unfold Goal at hs ⊢
  ext q
  constructor
  · intro hq
    have : q ∈ s.debt := hsub hq
    simpa [hs] using this
  · intro hq
    simp at hq

/-- A plan solves the required future contract when it reaches zero debt. -/
def Solves {Q X : Type*}
    (Step : DebtState Q X → DebtState Q X → Prop)
    (start : DebtState Q X) : Prop :=
  ∃ goal, Reach Step start goal ∧ Goal goal

/-- If a zero-debt state is reachable, then every further debt-nonincreasing
continuation also solves the contract. -/
theorem solution_closed_under_safe_continuation
    {Q X : Type*} {Step : DebtState Q X → DebtState Q X → Prop}
    (hmono : DebtNonIncreasing Step)
    {start mid finish : DebtState Q X}
    (hsm : Reach Step start mid) (hgoal : Goal mid)
    (hmf : Reach Step mid finish) :
    Reach Step start finish ∧ Goal finish := by
  constructor
  · induction hmf with
    | refl => exact hsm
    | tail hreach hstep ih => exact Reach.tail ih hstep
  · exact zeroDebt_absorbing hmono hgoal hmf

/-- Concrete debt state extracted from the INSACERMO FutureDebt object. -/
def ofContractState
    {Q S A Y X : Type*}
    (Good : Q → S → A → Prop) (Req : Set Q)
    (B : Set S) (C : Set A) (h : S → Y) (x : X) : DebtState Q X :=
  ⟨x, FutureDebt.Debt Good Req B C h⟩

/-- For a concrete INSACERMO contract state, planner goal is exactly full
future guarantee. -/
theorem goal_ofContractState_iff_guarantees
    {Q S A Y X : Type*}
    {Good : Q → S → A → Prop} {Req : Set Q}
    {B : Set S} {C : Set A} {h : S → Y} {x : X} :
    Goal (ofContractState Good Req B C h x) ↔
      FutureEnvelope.Guarantees Good Req B C h := by
  exact FutureDebt.debt_eq_empty_iff_guarantees

end FutureConservationPlanner

end InsacermoActionabilityInformation
