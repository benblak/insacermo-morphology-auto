/-
  INSACERMO / experimental design: identifying an unknown local law
  from one complete set of pattern responses.

  Mathematical contract:
  • finite local patterns A, outputs B
  • same deterministic rule at all sites
  • observations accurately report the rule's response
  • the chosen experiment covers every pattern

  This formalizes conditional identifiability, NOT identification of
  arbitrary physics, nor proof of computational universality of Rule 110.
  Lean 4.20 / Mathlib. Separate from the frozen MAX TOTAL engine.
-/
import Mathlib

namespace OneExperiment

/-- Any rule fitting all observations is identical to the hidden rule,
    provided every possible local pattern occurs in the experiment. -/
theorem exact_law_from_covering_experiment
    {I A B : Type*}
    (probe : I → A) (actual candidate : A → B)
    (covers : Function.Surjective probe)
    (agrees : ∀ i : I, candidate (probe i) = actual (probe i)) :
    candidate = actual := by
  funext a
  obtain ⟨i, hi⟩ := covers a
  rw [← hi]
  exact agrees i

/-- A missing local pattern makes unique identification impossible.
    Two genuinely different Boolean laws give identical observed data. -/
theorem missing_pattern_gives_two_indistinguishable_laws
    {I A : Type*} [DecidableEq A]
    (probe : I → A) (missing : A)
    (not_seen : ∀ i : I, probe i ≠ missing) :
    (∀ i : I, (fun _ : A => false) (probe i) =
        (fun a : A => decide (a = missing)) (probe i)) ∧
    ((fun _ : A => false) ≠
        (fun a : A => decide (a = missing))) := by
  constructor
  · intro i
    simp [not_seen i]
  · intro h
    have hh := congrFun h missing
    simp at hh

/-- The cyclic 8-cell initial state 00010111.
    Index i is the cell position modulo 8. -/
def seedBit (i : Nat) : Bool :=
  decide (i % 8 = 3 ∨ i % 8 = 5 ∨ i % 8 = 6 ∨ i % 8 = 7)

/-- Three-bit local neighborhood: 4*left + 2*center + right. -/
def pattern (i : Fin 8) : Nat :=
  4 * (if seedBit (i.val + 7) then 1 else 0) +
  2 * (if seedBit i.val then 1 else 0) +
      (if seedBit (i.val + 1) then 1 else 0)

def observedPattern (i : Fin 8) : Fin 8 :=
  ⟨(pattern i) % 8, Nat.mod_lt _ (by decide)⟩

/-- Machine-checked fact: this single 8-cell experiment contains
    all eight 3-bit neighborhoods (each exactly once). -/
theorem seed_covers_all_patterns :
    Function.Surjective observedPattern := by
  intro x
  fin_cases x
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨5, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨7, by decide⟩
  · exact ⟨6, by decide⟩

/-- Consequence: all 256 radius-one Boolean laws are uniquely identified
    from their simultaneous response to this eight-cell seed. -/
theorem one_shot_identification
    (actual candidate : Fin 8 → Bool)
    (h : ∀ i : Fin 8,
      candidate (observedPattern i) = actual (observedPattern i)) :
    candidate = actual := by
  exact exact_law_from_covering_experiment
    observedPattern actual candidate seed_covers_all_patterns h

#print axioms exact_law_from_covering_experiment
#print axioms missing_pattern_gives_two_indistinguishable_laws
#print axioms seed_covers_all_patterns
#print axioms one_shot_identification

end OneExperiment
