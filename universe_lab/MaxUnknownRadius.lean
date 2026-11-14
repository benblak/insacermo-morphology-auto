/-
INSACERMO — sharp information barrier for unknown local binary rule.
The local radius R is bounded but effective radius is unknown.

A single synchronous transition on n sites returns n Boolean outputs.
If a designed experiment is to identify ALL radius-R local laws, it must
exercise all 2^(2R+1) local neighborhoods. Otherwise two different laws
return the exact same observation.

The theorem is classical combinatorial identification; it is not a new
physical law and proves nothing about natural-world radius bounds.
Standalone Lean v4.20 Mathlib, frozen INSACERMO MAX TOTAL unchanged.
-/
import Mathlib

namespace MaxUnknownRadius

/-- A complete observed set of local patterns uniquely determines any
two candidate laws agreeing with the observed outputs. -/
theorem covering_implies_unique
    {I A : Type*}
    (probe : I → A) (actual candidate : A → Bool)
    (covers : Function.Surjective probe)
    (agree : ∀ i, candidate (probe i) = actual (probe i)) :
    candidate = actual := by
  funext x
  obtain ⟨i, rfl⟩ := covers x
  exact agree i

/-- If an experiment does not cover a pattern, then there are two
distinct Boolean laws which are observationally indistinguishable. -/
theorem uncovered_implies_ambiguity
    {I A : Type*} [DecidableEq A]
    (probe : I → A) (hidden : A)
    (absent : ∀ i, probe i ≠ hidden) :
    (∀ i, (fun _ : A => false) (probe i) =
            (fun x : A => decide (x = hidden)) (probe i)) ∧
    ((fun _ : A => false) ≠
            (fun x : A => decide (x = hidden))) := by
  constructor
  · intro i
    simp [absent i]
  · intro h
    have hi := congrFun h hidden
    simp at hi

/-- General finite cardinal information lower bound:
one local response per experimental site, so all possible local patterns
cannot be covered unless experiment has at least as many sites. -/
theorem minimum_observation_sites
    {n k : Nat} (probe : Fin n → Fin (2 ^ k))
    (h : Function.Surjective probe) :
    2 ^ k ≤ n := by
  have hcard := Fintype.card_le_of_surjective probe h
  simpa using hcard

/-- With symmetric radius r, there are 2^(2r+1) neighborhoods.
For r=6, at least 8192 simultaneous cell measurements are necessary. -/
theorem radius_six_requires_8192
    {n : Nat}
    (probe : Fin n → Fin (2 ^ (2*6+1)))
    (h : Function.Surjective probe) :
    8192 ≤ n := by
  have hi := minimum_observation_sites probe h
  norm_num at hi ⊢
  exact hi

#print axioms covering_implies_unique
#print axioms uncovered_implies_ambiguity
#print axioms minimum_observation_sites
#print axioms radius_six_requires_8192

end MaxUnknownRadius
