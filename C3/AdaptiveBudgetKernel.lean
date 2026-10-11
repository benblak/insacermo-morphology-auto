import C3.UnknownLawsProbeKernel

/- INSACERMO C3++: finite-horizon robust adaptive planning under a budget.
   This model is exact relative to declared policy/probe sets, observation supports
   and nonnegative natural-number costs. It does not assume probabilistic learning. -/
namespace INSACERMO.C3PP
open INSACERMO.C3
universe u v w z

variable {Scenario : Type u} {Policy : Type v} {Probe : Type w} {Outcome : Type z}

structure Problem (Scenario : Type u) (Policy : Type v)
    (Probe : Type w) (Outcome : Type z) where
  allowed : Policy → Prop
  probeAllowed : Probe → Prop
  good : Policy → Scenario → Prop
  observes : Probe → Scenario → Outcome → Prop
  actionCost : Policy → Nat
  probeCost : Probe → Nat

def Direct (m : Problem Scenario Policy Probe Outcome)
    (budget : Nat) (X : Scenario → Prop) : Prop :=
  ∃ p, m.allowed p ∧ m.actionCost p ≤ budget ∧
    ∀ s, X s → m.good p s

def Total (m : Problem Scenario Policy Probe Outcome)
    (q : Probe) (X : Scenario → Prop) : Prop :=
  ∀ s, X s → ∃ o, m.observes q s o

def After (m : Problem Scenario Policy Probe Outcome)
    (q : Probe) (X : Scenario → Prop) (o : Outcome) : Scenario → Prop :=
  fun s => X s ∧ m.observes q s o

def Can (m : Problem Scenario Policy Probe Outcome) :
    Nat → Nat → (Scenario → Prop) → Prop
  | 0, b, X => Direct m b X
  | n + 1, b, X =>
      Direct m b X ∨
        ∃ q, m.probeAllowed q ∧ m.probeCost q ≤ b ∧
          Total m q X ∧
          ∀ o, Can m n (b - m.probeCost q) (After m q X o)

theorem horizon_zero (m : Problem Scenario Policy Probe Outcome)
    (b : Nat) (X : Scenario → Prop) :
    Can m 0 b X ↔ Direct m b X := Iff.rfl

theorem bellman_step (m : Problem Scenario Policy Probe Outcome)
    (n b : Nat) (X : Scenario → Prop) :
    Can m (n + 1) b X ↔
      Direct m b X ∨
        ∃ q, m.probeAllowed q ∧ m.probeCost q ≤ b ∧
          Total m q X ∧
          ∀ o, Can m n (b - m.probeCost q) (After m q X o) := Iff.rfl

theorem direct_sound (m : Problem Scenario Policy Probe Outcome)
    (b : Nat) {X Y : Scenario → Prop}
    (hXY : Incl Y X) (h : Direct m b X) : Direct m b Y := by
  rcases h with ⟨p, hp, hc, hg⟩
  exact ⟨p, hp, hc, fun s hs => hg s (hXY s hs)⟩

theorem can_antitone_world (m : Problem Scenario Policy Probe Outcome)
    (n : Nat) : ∀ (b : Nat) (X Y : Scenario → Prop),
    Incl Y X → Can m n b X → Can m n b Y := by
  induction n with
  | zero =>
      intro b X Y hXY h
      exact direct_sound m b hXY h
  | succ n ih =>
      intro b X Y hXY h
      cases h with
      | inl hd =>
          exact Or.inl (direct_sound m b hXY hd)
      | inr hq =>
          rcases hq with ⟨q, hallowed, hcost, htotal, hbranches⟩
          apply Or.inr
          refine ⟨q, hallowed, hcost, ?_, ?_⟩
          · intro s hs
            exact htotal s (hXY s hs)
          · intro o
            apply ih (b - m.probeCost q) (After m q X o) (After m q Y o)
            · intro s hs
              exact ⟨hXY s hs.1, hs.2⟩
            · exact hbranches o

theorem direct_budget_monotone (m : Problem Scenario Policy Probe Outcome)
    {b b' : Nat} {X : Scenario → Prop}
    (hbb : b ≤ b') (h : Direct m b X) : Direct m b' X := by
  rcases h with ⟨p, hp, hc, hg⟩
  exact ⟨p, hp, Nat.le_trans hc hbb, hg⟩

theorem can_budget_monotone (m : Problem Scenario Policy Probe Outcome)
    (n : Nat) : ∀ (b b' : Nat) (X : Scenario → Prop),
    b ≤ b' → Can m n b X → Can m n b' X := by
  induction n with
  | zero =>
      intro b b' X hbb h
      exact direct_budget_monotone m hbb h
  | succ n ih =>
      intro b b' X hbb h
      cases h with
      | inl hd =>
          exact Or.inl (direct_budget_monotone m hbb hd)
      | inr hq =>
          rcases hq with ⟨q, hallowed, hcost, htotal, hbranches⟩
          apply Or.inr
          refine ⟨q, hallowed, Nat.le_trans hcost hbb, htotal, ?_⟩
          intro o
          exact ih (b - m.probeCost q) (b' - m.probeCost q)
            (After m q X o) (Nat.sub_le_sub_right hbb _) (hbranches o)

theorem can_horizon_monotone (m : Problem Scenario Policy Probe Outcome)
    (n b : Nat) (X : Scenario → Prop) :
    Can m n b X → Can m (n + 1) b X := by
  induction n generalizing b X with
  | zero =>
      intro h
      exact Or.inl h
  | succ n ih =>
      intro h
      cases h with
      | inl hd =>
          exact Or.inl hd
      | inr hq =>
          rcases hq with ⟨q, hallowed, hcost, htotal, hbranches⟩
          apply Or.inr
          exact ⟨q, hallowed, hcost, htotal, fun o => ih _ _ (hbranches o)⟩

theorem no_probe_at_zero_horizon (m : Problem Scenario Policy Probe Outcome)
    (b : Nat) (X : Scenario → Prop)
    (h : ¬ Direct m b X) : ¬ Can m 0 b X := h

end INSACERMO.C3PP
