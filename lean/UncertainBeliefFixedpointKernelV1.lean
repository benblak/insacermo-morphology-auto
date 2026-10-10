import Std

/-! Finite-belief safety and reachability closure, model-relative. -/
namespace InsacermoUncertainBelief
universe u v
abbrev Belief (S : Type u) := S → Prop
def Subset {S : Type u} (A B : Belief S) : Prop := ∀ s, A s → B s
def Pre {S : Type u} {Action : Type v}
    (legal : Action → Belief S → Prop)
    (succ : Action → Belief S → Belief S → Prop)
    (K : Belief S → Prop) (B : Belief S) : Prop :=
  ∃ a, legal a B ∧ ∀ B', succ a B B' → K B'
def SafeStep {S : Type u} {Action : Type v}
    (safe : Belief S → Prop)
    (legal : Action → Belief S → Prop)
    (succ : Action → Belief S → Belief S → Prop)
    (K : Belief S → Prop) (B : Belief S) : Prop :=
  safe B ∧ Pre legal succ K B
def ReachStep {S : Type u} {Action : Type v}
    (goal safe : Belief S → Prop)
    (legal : Action → Belief S → Prop)
    (succ : Action → Belief S → Belief S → Prop)
    (K : Belief S → Prop) (B : Belief S) : Prop :=
  goal B ∨ (safe B ∧ Pre legal succ K B)
theorem pre_monotone {S : Type u} {Action : Type v}
    (legal : Action → Belief S → Prop)
    (succ : Action → Belief S → Belief S → Prop)
    {K L : Belief S → Prop}
    (h : ∀ B, K B → L B)
    {B : Belief S} (hb : Pre legal succ K B) :
    Pre legal succ L B := by
  obtain ⟨a, ha, hs⟩ := hb
  exact ⟨a, ha, fun x hx => h x (hs x hx)⟩
theorem safeStep_monotone {S : Type u} {Action : Type v}
    (safe : Belief S → Prop)
    (legal : Action → Belief S → Prop)
    (succ : Action → Belief S → Belief S → Prop)
    {K L : Belief S → Prop}
    (h : ∀ B, K B → L B)
    {B : Belief S} (hb : SafeStep safe legal succ K B) :
    SafeStep safe legal succ L B := by
  exact ⟨hb.1, pre_monotone legal succ h hb.2⟩
theorem reachStep_monotone {S : Type u} {Action : Type v}
    (goal safe : Belief S → Prop)
    (legal : Action → Belief S → Prop)
    (succ : Action → Belief S → Belief S → Prop)
    {K L : Belief S → Prop}
    (h : ∀ B, K B → L B)
    {B : Belief S} (hb : ReachStep goal safe legal succ K B) :
    ReachStep goal safe legal succ L B := by
  rcases hb with hg | ⟨hs,hp⟩
  · exact Or.inl hg
  · exact Or.inr ⟨hs, pre_monotone legal succ h hp⟩
end InsacermoUncertainBelief
