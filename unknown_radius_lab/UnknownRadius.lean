/-
INSACERMO — Experimentation exacte d'une loi inconnue, rayon inconnu <= 6.

General mathematical claims:
1. If every possible local input pattern occurs in a single parallel probe,
   its Boolean response identifies any law in the declared finite class.
2. With fewer observed cells than local patterns, a different law exists
   that agrees on the whole experiment but differs on an unobserved pattern.
3. The same argument is instantiated at 8192 patterns (radius 6).
4. The number of full radius-6 Boolean local laws is 2^8192.

IMPORTANT: This source does NOT certify the FKM implementation nor the
experimental Python runtime. The two de Bruijn generators and finite tests
are audited separately in Python. Mathematical facts are classical.
-/
import Mathlib

namespace InsacermoUnknownRadius

universe u v w

/-- Complete experimental coverage forces uniqueness of the law. -/
theorem one_experiment_identifies_any_law
    {I : Type u} {Pattern : Type v} {Output : Type w}
    (ask : I → Pattern) (real candidate : Pattern → Output)
    (complete : Function.Surjective ask)
    (same_observed : ∀ i : I, candidate (ask i) = real (ask i)) :
    candidate = real := by
  funext pattern
  obtain ⟨i, hi⟩ := complete pattern
  rw [← hi]
  exact same_observed i

/-- With fewer probe locations than possible motifs, a motif is unseen. -/
theorem short_experiment_has_missing_pattern
    {locations patterns : Nat}
    (short : locations < patterns)
    (ask : Fin locations → Fin patterns) :
    ∃ pattern : Fin patterns, ∀ i : Fin locations, ask i ≠ pattern := by
  classical
  by_contra h
  have complete : Function.Surjective ask := by
    intro p
    by_contra hp
    apply h
    refine ⟨p, ?_⟩
    intro i
    intro heq
    apply hp
    exact ⟨i, heq⟩
  have hle : patterns ≤ locations := by
    simpa only [Nat.card_fin] using
      (Nat.card_le_card_of_surjective ask complete)
  omega

/-- An incomplete experiment cannot identify every law; here the two
    competing laws are explicit and have exactly the same observations. -/
theorem incomplete_experiment_has_ambiguity
    {locations patterns : Nat}
    (short : locations < patterns)
    (ask : Fin locations → Fin patterns) :
    ∃ first second : Fin patterns → Bool,
      first ≠ second ∧
      ∀ i : Fin locations, first (ask i) = second (ask i) := by
  classical
  obtain ⟨missing, unseen⟩ :=
    short_experiment_has_missing_pattern short ask
  refine ⟨(fun _ => false), (fun x => decide (x = missing)), ?_, ?_⟩
  · intro same
    have h := congrFun same missing
    simp at h
  · intro i
    simp [unseen i]

/-- Radius <= 6 has 2^13 = 8192 possible local configurations.
    Any simultaneous single-step experiment with fewer cells cannot
    distinguish all binary radius-six Boolean rules. -/
theorem fewer_than_8192_cells_cannot_suffice
    {locations : Nat} (short : locations < 8192)
    (ask : Fin locations → Fin 8192) :
    ∃ first second : Fin 8192 → Bool,
      first ≠ second ∧
      ∀ i, first (ask i) = second (ask i) := by
  exact incomplete_experiment_has_ambiguity short ask

/-- The astronomical family size is a count, not an enumeration. -/
theorem radius_six_family_size :
    Fintype.card (Fin 8192 → Bool) = 2 ^ 8192 := by
  simp

/-- For an observed full table, two competing reduced descriptions
    cannot differ if every reduced input has a larger-pattern witness. -/
theorem minimal_radius_factor_unique
    {Big Small : Type*}
    (project : Big → Small) (complete : Function.Surjective project)
    (g h : Small → Bool)
    (same : ∀ x : Big, g (project x) = h (project x)) :
    g = h := by
  exact one_experiment_identifies_any_law project h g complete same

#print axioms one_experiment_identifies_any_law
#print axioms short_experiment_has_missing_pattern
#print axioms incomplete_experiment_has_ambiguity
#print axioms fewer_than_8192_cells_cannot_suffice
#print axioms radius_six_family_size
#print axioms minimal_radius_factor_unique

end InsacermoUnknownRadius
