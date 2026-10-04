import Std

/-!
INSACERMO — Effective Semantic State Bound V1

No Mathlib/Finset dependency is introduced.

After exact quotienting, a semantic belief over n effective classes can be
encoded by n Boolean membership bits. We explicitly enumerate all such bit
signatures. The enumeration has length 2^n and every Boolean list of length n
occurs in it.

Therefore the semantic belief universe has an explicit cover of size 2^n.
This is a semantic-state upper bound, not a wall-clock runtime theorem.
-/

namespace InsacermoEffectiveStateBound

/-- Explicit enumeration of all Boolean belief signatures of length n. -/
def bitBeliefs : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      (bitBeliefs n).map (fun xs => false :: xs) ++
      (bitBeliefs n).map (fun xs => true :: xs)

/-- The explicit semantic-belief enumeration contains 2^n entries. -/
theorem bitBeliefs_length (n : Nat) :
    (bitBeliefs n).length = 2 ^ n := by
  induction n with
  | zero =>
      simp [bitBeliefs]
  | succ n ih =>
      simp [bitBeliefs, ih, Nat.pow_succ]
      omega

/-- Every Boolean signature of length n occurs in the 2^n-entry enumeration. -/
theorem mem_bitBeliefs_of_length :
    ∀ (n : Nat) (bits : List Bool),
      bits.length = n → bits ∈ bitBeliefs n := by
  intro n
  induction n with
  | zero =>
      intro bits hlen
      have hb : bits = [] := List.eq_nil_of_length_eq_zero hlen
      subst bits
      simp [bitBeliefs]
  | succ n ih =>
      intro bits hlen
      cases bits with
      | nil =>
          simp at hlen
      | cons b tail =>
          have htail : tail.length = n := by
            simpa using Nat.succ.inj hlen
          have hmem : tail ∈ bitBeliefs n := ih tail htail
          cases b <;> simp [bitBeliefs, hmem]

/--
Semantic-state cover theorem: n effective classes admit a complete explicit
belief cover with exactly 2^n encoded states.
-/
theorem effective_belief_cover
    (n : Nat) :
    (bitBeliefs n).length = 2 ^ n ∧
    ∀ bits : List Bool, bits.length = n → bits ∈ bitBeliefs n := by
  exact ⟨bitBeliefs_length n, mem_bitBeliefs_of_length n⟩

/--
Raw multiplicity does not enter this semantic cover: once the quotient has
n effective classes, the cover size is 2^n regardless of how many raw rows
were merged into those classes.
-/
theorem raw_multiplicity_absent_from_cover
    (rawCount effectiveCount : Nat) :
    (bitBeliefs effectiveCount).length = 2 ^ effectiveCount := by
  exact bitBeliefs_length effectiveCount

#print axioms bitBeliefs_length
#print axioms mem_bitBeliefs_of_length
#print axioms effective_belief_cover
#print axioms raw_multiplicity_absent_from_cover

end InsacermoEffectiveStateBound
