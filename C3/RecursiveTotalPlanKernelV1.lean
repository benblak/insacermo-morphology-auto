import C3.TotalSymbolicDynamicBridgeV1

/-!
INSACERMO C3 TOTAL RECURSIVE PLAN KERNEL (2026-10-11)

Integrates C3++ budgeted search with genuine observation-dependent state changes
at EACH depth. A complete policy tree, not an oracle returning ACT by fiat,
is validated recursively on all possible observations.

State and law remain explicit in Scenario. No probabilistic assumptions.
Optimality refers to the declared policy/probe/transition grammar, not reality
outside the declared laws. Nat.find gives an exact existence-based bound,
but is not an executable optimizer.
-/

namespace INSACERMO.RecursiveC3
open INSACERMO.C3
open INSACERMO.C3PP

universe u v w z
variable {Scenario : Type u} {Policy : Type v}
         {Probe : Type w} {Outcome : Type z}

structure DynamicProblem (Scenario : Type u) (Policy : Type v)
    (Probe : Type w) (Outcome : Type z) where
  base : Problem Scenario Policy Probe Outcome
  transform : Probe → Outcome → Scenario → Scenario

/-- The state really changes after sensing; possible results may overlap. -/
def AfterDynamic (m : DynamicProblem Scenario Policy Probe Outcome)
    (q : Probe) (X : Scenario → Prop) (o : Outcome) : Scenario → Prop :=
  fun y => ∃ x, X x ∧ m.base.observes q x o ∧ m.transform q o x = y

/-- The controller must handle every admissible outcome after each change. -/
def CanDynamic (m : DynamicProblem Scenario Policy Probe Outcome) :
    Nat → Nat → (Scenario → Prop) → Prop
  | 0, b, X => Direct m.base b X
  | n + 1, b, X =>
      Direct m.base b X ∨
      ∃ q, m.base.probeAllowed q ∧ m.base.probeCost q ≤ b ∧
        Total m.base q X ∧
        ∀ o, CanDynamic m n (b - m.base.probeCost q)
          (AfterDynamic m q X o)

/-- A concrete policy tree supplied by a synthesizer. -/
inductive Plan (Policy : Type v) (Probe : Type w) (Outcome : Type z) where
  | act (p : Policy)
  | probe (q : Probe) (next : Outcome → Plan Policy Probe Outcome)

/-- Independent checker specification for a serialized tree and a budget. -/
def PlanValid (m : DynamicProblem Scenario Policy Probe Outcome) :
    Nat → Nat → (Scenario → Prop) → Plan Policy Probe Outcome → Prop
  | 0, b, X, .act p =>
      m.base.allowed p ∧ m.base.actionCost p ≤ b ∧
      ∀ s, X s → m.base.good p s
  | 0, _, _, .probe _ _ => False
  | _ + 1, b, X, .act p =>
      m.base.allowed p ∧ m.base.actionCost p ≤ b ∧
      ∀ s, X s → m.base.good p s
  | n + 1, b, X, .probe q next =>
      m.base.probeAllowed q ∧ m.base.probeCost q ≤ b ∧
      Total m.base q X ∧
      ∀ o, PlanValid m n (b - m.base.probeCost q)
        (AfterDynamic m q X o) (next o)

theorem can_iff_verified_plan
    (m : DynamicProblem Scenario Policy Probe Outcome) (n : Nat) :
    ∀ b X, CanDynamic m n b X ↔
      ∃ t : Plan Policy Probe Outcome, PlanValid m n b X t := by
  induction n with
  | zero =>
      intro b X
      constructor
      · rintro ⟨p, hp, hc, hg⟩
        exact ⟨.act p, ⟨hp, hc, hg⟩⟩
      · rintro ⟨t, hv⟩
        cases t with
        | act p =>
            exact ⟨p, hv.1, hv.2.1, hv.2.2⟩
        | probe q next =>
            exact False.elim hv
  | succ n ih =>
      intro b X
      constructor
      · intro h
        cases h with
        | inl hd =>
            rcases hd with ⟨p, hp, hc, hg⟩
            exact ⟨.act p, ⟨hp, hc, hg⟩⟩
        | inr hq =>
            rcases hq with ⟨q, hqallowed, hcost, htotal, hbranches⟩
            classical
            have htrees : ∀ o : Outcome,
                ∃ t : Plan Policy Probe Outcome,
                PlanValid m n (b - m.base.probeCost q)
                  (AfterDynamic m q X o) t := by
              intro o
              exact (ih _ _).mp (hbranches o)
            let child : Outcome → Plan Policy Probe Outcome :=
              fun o => Classical.choose (htrees o)
            refine ⟨.probe q child, ⟨hqallowed, hcost, htotal, ?_⟩⟩
            intro o
            exact Classical.choose_spec (htrees o)
      · rintro ⟨t, hv⟩
        cases t with
        | act p =>
            exact Or.inl ⟨p, hv.1, hv.2.1, hv.2.2⟩
        | probe q next =>
            rcases hv with ⟨hqallowed, hcost, htotal, hchildren⟩
            apply Or.inr
            refine ⟨q, hqallowed, hcost, htotal, ?_⟩
            intro o
            exact (ih _ _).mpr ⟨next o, hchildren o⟩

theorem after_dynamic_monotone
    (m : DynamicProblem Scenario Policy Probe Outcome)
    (q : Probe) (o : Outcome) {X Y : Scenario → Prop}
    (hYX : Incl Y X) :
    Incl (AfterDynamic m q Y o) (AfterDynamic m q X o) := by
  intro z hz
  rcases hz with ⟨x, hx, ho, hresult⟩
  exact ⟨x, hYX x hx, ho, hresult⟩

theorem can_dynamic_world_monotone
    (m : DynamicProblem Scenario Policy Probe Outcome)
    (n : Nat) : ∀ b X Y,
      Incl Y X → CanDynamic m n b X → CanDynamic m n b Y := by
  induction n with
  | zero =>
      intro b X Y hYX h
      exact direct_sound m.base b hYX h
  | succ n ih =>
      intro b X Y hYX h
      cases h with
      | inl hd =>
          exact Or.inl (direct_sound m.base b hYX hd)
      | inr hq =>
          rcases hq with ⟨q, hallowed, hcost, htotal, hbranches⟩
          apply Or.inr
          refine ⟨q, hallowed, hcost, ?_, ?_⟩
          · intro s hs
            exact htotal s (hYX s hs)
          · intro o
            exact ih _ _ _
              (after_dynamic_monotone m q o hYX) (hbranches o)

theorem can_dynamic_budget_monotone
    (m : DynamicProblem Scenario Policy Probe Outcome)
    (n : Nat) : ∀ b b' X,
      b ≤ b' → CanDynamic m n b X → CanDynamic m n b' X := by
  induction n with
  | zero =>
      intro b b' X hbb h
      exact direct_budget_monotone m.base hbb h
  | succ n ih =>
      intro b b' X hbb h
      cases h with
      | inl hd =>
          exact Or.inl (direct_budget_monotone m.base hbb hd)
      | inr hq =>
          rcases hq with ⟨q, hallowed, hcost, htotal, hbranches⟩
          apply Or.inr
          refine ⟨q, hallowed, Nat.le_trans hcost hbb, htotal, ?_⟩
          intro o
          exact ih _ _ _ (Nat.sub_le_sub_right hbb _) (hbranches o)

theorem can_dynamic_horizon_monotone
    (m : DynamicProblem Scenario Policy Probe Outcome)
    (n b : Nat) (X : Scenario → Prop) :
    CanDynamic m n b X → CanDynamic m (n + 1) b X := by
  induction n generalizing b X with
  | zero =>
      intro h
      exact Or.inl h
  | succ n ih =>
      intro h
      cases h with
      | inl hd => exact Or.inl hd
      | inr hq =>
          rcases hq with ⟨q, hallowed, hcost, htotal, hbranches⟩
          exact Or.inr ⟨q, hallowed, hcost, htotal,
            fun o => ih _ _ (hbranches o)⟩

/-- A mathematical, inspectable OPTIMALITY CERTIFICATE: a feasible budget
    and an independent lower bound against every feasible competitor. -/
def OptimalBudget (m : DynamicProblem Scenario Policy Probe Outcome)
    (n b : Nat) (X : Scenario → Prop) : Prop :=
  CanDynamic m n b X ∧ ∀ k, CanDynamic m n k X → b ≤ k

theorem optimal_budget_has_verified_tree
    (m : DynamicProblem Scenario Policy Probe Outcome)
    (n b : Nat) (X : Scenario → Prop)
    (h : OptimalBudget m n b X) :
    ∃ t : Plan Policy Probe Outcome,
      PlanValid m n b X t :=
  (can_iff_verified_plan m n b X).mp h.1

theorem verified_tree_and_lower_bound_are_optimal
    (m : DynamicProblem Scenario Policy Probe Outcome)
    (n b : Nat) (X : Scenario → Prop)
    (t : Plan Policy Probe Outcome)
    (hValid : PlanValid m n b X t)
    (hLower : ∀ k, CanDynamic m n k X → b ≤ k) :
    OptimalBudget m n b X :=
  ⟨(can_iff_verified_plan m n b X).mpr ⟨t, hValid⟩, hLower⟩

theorem optimal_budget_unique
    (m : DynamicProblem Scenario Policy Probe Outcome)
    (n b c : Nat) (X : Scenario → Prop)
    (hb : OptimalBudget m n b X)
    (hc : OptimalBudget m n c X) : b = c :=
  Nat.le_antisymm (hb.2 c hc.1) (hc.2 b hb.1)

/-- Any verified tree has a valid plan over the declared scenario envelope;
    it is only certified *minimal* if the lower bound is also supplied. -/
theorem verified_plan_guarantees_feasibility
    (m : DynamicProblem Scenario Policy Probe Outcome)
    (n b : Nat) (X : Scenario → Prop)
    (t : Plan Policy Probe Outcome)
    (ht : PlanValid m n b X t) : CanDynamic m n b X :=
  (can_iff_verified_plan m n b X).mpr ⟨t, ht⟩

end INSACERMO.RecursiveC3
