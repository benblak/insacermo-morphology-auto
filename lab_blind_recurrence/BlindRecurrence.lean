/- INSACERMO blind-sequence benchmark: exact algebra and finite-prefix impossibility.
   No extension of the frozen MAX TOTAL engine.
   Lean 4.20, no Mathlib, no sorry/admit.
-/
import Init

namespace BlindRecurrence

/-- The classic quadratic identity associated to a recurrence
  w = A*v + B*u. It does not establish that a measured sequence
  continues to obey the recurrence. -/
def Q (A B u v : Int) : Int := v*v - A*u*v - B*u*u

theorem quadratic_step (A B u v : Int) :
    Q A B v (A*v + B*u) = (-B)*Q A B u v := by
  simp only [Q, sub_eq_add_neg, mul_add, add_mul]
  -- After multiplication has been distributed, all monomials are
  -- identical up to commutativity; linear normalization finishes.
  simp only [mul_assoc, mul_left_comm, mul_comm]
  omega

/-- A prediction using only a fixed observed prefix cannot be correct
for both of two sequences with that same prefix and different next values. -/
theorem no_universal_next_prediction
    (T : Nat) (s t : Nat → Int)
    (same_prefix : ∀ i : Fin T, s i.val = t i.val)
    (different_future : s T ≠ t T)
    (predict : (Fin T → Int) → Int) :
    ¬ (predict (fun i => s i.val) = s T ∧
       predict (fun i => t i.val) = t T) := by
  intro h
  have hseq : (fun i : Fin T => s i.val) =
      (fun i : Fin T => t i.val) := by
    funext i
    exact same_prefix i
  apply different_future
  calc
    s T = predict (fun i => s i.val) := h.1.symm
    _ = predict (fun i => t i.val) := by rw [hseq]
    _ = t T := h.2

#print axioms quadratic_step
#print axioms no_universal_next_prediction

end BlindRecurrence
