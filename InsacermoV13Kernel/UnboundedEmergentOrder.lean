import Mathlib.Data.Fin.Pigeonhole
import InsacermoV13Kernel.DiscoveryDialect

namespace InsacermoV13Kernel
namespace UnboundedEmergentOrder

abbrev World (n : Nat) := Fin n × Bool

inductive Action (n : Nat)
  | even (i : Fin n)
  | oddAll
  | pair (i : Fin n)
deriving DecidableEq

def available {n : Nat} (C : Fin n → Prop) : Action n → Prop
  | .even _ => True
  | .oddAll => True
  | .pair i => C i

def admissible {n : Nat} : World n → Action n → Prop
  | (i, false), .even j => i = j
  | (_, false), .oddAll => False
  | (i, false), .pair j => i = j
  | (_, true), .even _ => False
  | (_, true), .oddAll => True
  | (i, true), .pair j => i = j

@[simp] theorem pair_available_iff {n : Nat} {C : Fin n → Prop} {i : Fin n} :
    available C (.pair i) ↔ C i := by
  rfl

@[simp] theorem even_available {n : Nat} {C : Fin n → Prop} {i : Fin n} :
    available C (.even i) := by
  trivial

@[simp] theorem oddAll_available {n : Nat} {C : Fin n → Prop} :
    available C (.oddAll : Action n) := by
  trivial

theorem admissible_even_same_index
    {n : Nat} {i j : Fin n} {a : Action n}
    (hi : admissible (i, false) a)
    (hj : admissible (j, false) a) :
    i = j := by
  cases a with
  | even k =>
      simp [admissible] at hi hj
      exact hi.trans hj.symm
  | oddAll =>
      simp [admissible] at hi
  | pair k =>
      simp [admissible] at hi hj
      exact hi.trans hj.symm

theorem missing_odd_forces_oddAll
    {n : Nat} {C : Fin n → Prop} {i : Fin n} {a : Action n}
    (hmiss : ¬ C i)
    (havail : available C a)
    (hadm : admissible (i, true) a) :
    a = .oddAll := by
  cases a with
  | even j =>
      simp [admissible] at hadm
  | oddAll =>
      rfl
  | pair j =>
      simp [available, admissible] at havail hadm
      subst j
      exact False.elim (hmiss havail)

theorem actionCover_succ
    {n : Nat} (C : Fin n → Prop) :
    ActionCover (available C) admissible (n + 1) := by
  let actions : Fin (n + 1) → Action n :=
    Fin.cases .oddAll (fun i => .even i)
  refine ⟨actions, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [actions, available]
    · simp [actions, available]
  · rintro ⟨i, b⟩
    cases b with
    | false =>
        refine ⟨i.succ, ?_⟩
        simp [actions, admissible]
    | true =>
        refine ⟨0, ?_⟩
        simp [actions, admissible]

theorem actionCover_full (n : Nat) :
    ActionCover (available (fun _ : Fin n => True)) admissible n := by
  refine ⟨(fun i => .pair i), ?_, ?_⟩
  · intro i
    simp [available]
  · rintro ⟨i, b⟩
    refine ⟨i, ?_⟩
    cases b <;> simp [admissible]

theorem actionCover_lower_n
    {n k : Nat} {C : Fin n → Prop}
    (hcover : ActionCover (available C) admissible k) :
    n ≤ k := by
  rcases hcover with ⟨actions, havail, hcover⟩
  have hex :
      ∀ i : Fin n, ∃ j : Fin k, admissible (i, false) (actions j) := by
    intro i
    exact hcover (i, false)
  let pick : Fin n → Fin k := fun i => Classical.choose (hex i)
  have hpick : ∀ i : Fin n, admissible (i, false) (actions (pick i)) := by
    intro i
    exact Classical.choose_spec (hex i)
  apply Fin.le_of_injective pick
  intro i j hij
  have hj := hpick j
  rw [← hij] at hj
  exact admissible_even_same_index (hpick i) hj

theorem actionCover_lower_succ
    {n k : Nat} {C : Fin n → Prop}
    (hmissing : ∃ i, ¬ C i)
    (hcover : ActionCover (available C) admissible k) :
    n + 1 ≤ k := by
  rcases hmissing with ⟨miss, hmiss⟩
  rcases hcover with ⟨actions, havail, hcover⟩
  have hex :
      ∀ i : Fin n, ∃ j : Fin k, admissible (i, false) (actions j) := by
    intro i
    exact hcover (i, false)
  let pick : Fin n → Fin k := fun i => Classical.choose (hex i)
  have hpick : ∀ i : Fin n, admissible (i, false) (actions (pick i)) := by
    intro i
    exact Classical.choose_spec (hex i)
  rcases hcover (miss, true) with ⟨oddSlot, hoddAdm⟩
  have hoddAction : actions oddSlot = (.oddAll : Action n) :=
    missing_odd_forces_oddAll hmiss (havail oddSlot) hoddAdm
  have hne : ∀ i : Fin n, pick i ≠ oddSlot := by
    intro i heq
    have hi := hpick i
    rw [heq, hoddAction] at hi
    simp [admissible] at hi
  let embed : Fin (n + 1) → Fin k :=
    Fin.cases oddSlot pick
  apply Fin.le_of_injective embed
  intro x y hxy
  rcases Fin.eq_zero_or_eq_succ x with hx | ⟨i, hx⟩
  · rcases Fin.eq_zero_or_eq_succ y with hy | ⟨j, hy⟩
    · exact hx.trans hy.symm
    · subst x
      subst y
      have h : oddSlot = pick j := by
        simpa [embed] using hxy
      exact False.elim (hne j h.symm)
  · rcases Fin.eq_zero_or_eq_succ y with hy | ⟨j, hy⟩
    · subst x
      subst y
      have h : pick i = oddSlot := by
        simpa [embed] using hxy
      exact False.elim (hne i h)
    · subst x
      subst y
      have hp : pick i = pick j := by
        simpa [embed] using hxy
      have hj := hpick j
      rw [← hp] at hj
      have hij : i = j := admissible_even_same_index (hpick i) hj
      exact congrArg Fin.succ hij

theorem isMinActionCover_full (n : Nat) :
    IsMinActionCover
      (available (fun _ : Fin n => True))
      admissible
      n := by
  refine ⟨actionCover_full n, ?_⟩
  intro k hk
  exact actionCover_lower_n hk

theorem isMinActionCover_proper
    {n : Nat} {C : Fin n → Prop}
    (hmissing : ∃ i, ¬ C i) :
    IsMinActionCover (available C) admissible (n + 1) := by
  refine ⟨actionCover_succ C, ?_⟩
  intro k hk
  exact actionCover_lower_succ hmissing hk

theorem isMinSafeSymbols_full
    {n : Nat} (hn : 0 < n) :
    IsMinSafeSymbols
      (available (fun _ : Fin n => True))
      admissible
      n := by
  haveI : Nonempty (World n) :=
    ⟨(⟨0, hn⟩, false)⟩
  exact (isMinSafeSymbols_iff_isMinActionCover).2 (isMinActionCover_full n)

theorem isMinSafeSymbols_proper
    {n : Nat} (hn : 0 < n)
    {C : Fin n → Prop}
    (hmissing : ∃ i, ¬ C i) :
    IsMinSafeSymbols (available C) admissible (n + 1) := by
  haveI : Nonempty (World n) :=
    ⟨(⟨0, hn⟩, false)⟩
  exact (isMinSafeSymbols_iff_isMinActionCover).2
    (isMinActionCover_proper hmissing)

theorem unbounded_emergent_order_profile
    (n : Nat) (hn : 0 < n) :
    IsMinSafeSymbols
        (available (fun _ : Fin n => True))
        admissible
        n ∧
    ∀ C : Fin n → Prop,
      (∃ i, ¬ C i) →
        IsMinSafeSymbols (available C) admissible (n + 1) := by
  constructor
  · exact isMinSafeSymbols_full hn
  · intro C hmissing
    exact isMinSafeSymbols_proper hn hmissing

end UnboundedEmergentOrder
end InsacermoV13Kernel
