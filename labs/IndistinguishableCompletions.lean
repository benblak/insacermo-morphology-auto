/-!
INSACERMO epistemic boundary: with arbitrary Boolean laws, a finite
non-exhaustive observation transcript does not determine a global law.
This checks the necessary REFUSE_UNCONDITIONAL boundary; it does NOT
certify the Python synthesis algorithm or any physical law.
-/
namespace InsacermoUnknownLaw

def flippedAt (x : Nat) (f : Nat → Bool) (z : Nat) : Bool :=
  if z = x then ! f z else f z

theorem observations_do_not_distinguish
    (observed : List Nat) (x : Nat) (h : x ∉ observed)
    (f : Nat → Bool) :
    (∀ y ∈ observed, flippedAt x f y = f y) ∧
    flippedAt x f x ≠ f x := by
  constructor
  · intro y hy
    have yne : y ≠ x := by
      intro e
      apply h
      simpa [e] using hy
    simp [flippedAt, yne]
  · cases hx : f x <;> simp [flippedAt, hx]

theorem a_second_law_always_exists
    (observed : List Nat) (x : Nat) (h : x ∉ observed)
    (f : Nat → Bool) :
    ∃ g : Nat → Bool,
      (∀ y ∈ observed, g y = f y) ∧ (g x ≠ f x) := by
  rcases observations_do_not_distinguish observed x h f with ⟨agree, differ⟩
  exact ⟨flippedAt x f, agree, differ⟩

end InsacermoUnknownLaw
