/-
INSACERMO HTRU2 -- exact information barrier, Lean 4.20.0, Init only.
Independent proof; no modification to the frozen INSACERMO motor.

Assumption: two possible worlds have the same observation, but opposite
correct binary labels. No deterministic action function on the observation
can get BOTH worlds right. Any universally safe optional action must
abstain on their common observation.

This theorem does NOT prove that real-world HTRU2 data are identical in
their full numeric measurements. It applies to the eight FIXED binary
signatures used in the preregistered experiment.
-/
import Init

namespace InsacermoIndistinguishability

universe u v
variable {W : Type u} {O : Type v}
variable (observe : W → O) (label : W → Bool)

def AlwaysSafe (act : O → Option Bool) : Prop :=
  ∀ w : W, ∀ a : Bool, act (observe w) = some a → a = label w

/-- Equal observation forces equal deterministic classification. -/
theorem deterministic_same_prediction
    (predict : O → Bool) (x y : W)
    (same : observe x = observe y) :
    predict (observe x) = predict (observe y) := by
  rw [same]

/-- A deterministic classifier cannot correctly label two observationally
identical worlds that have different true labels. -/
theorem no_two_correct
    (predict : O → Bool) (x y : W)
    (same : observe x = observe y)
    (different : label x ≠ label y) :
    ¬ (predict (observe x) = label x ∧
       predict (observe y) = label y) := by
  intro h
  apply different
  calc
    label x = predict (observe x) := h.1.symm
    _ = predict (observe y) := by rw [same]
    _ = label y := h.2

/-- Certified refusal is necessary for a classifier required to be correct
on EVERY possible world, when two worlds are observationally indistinguishable. -/
theorem safe_must_refuse
    (act : O → Option Bool) (hSafe : AlwaysSafe observe label act)
    (x y : W)
    (same : observe x = observe y)
    (different : label x ≠ label y) :
    act (observe x) = none := by
  cases h : act (observe x) with
  | none => rfl
  | some a =>
      have hx : a = label x := hSafe x a h
      have hy : a = label y := hSafe y a (by rw [← same]; exact h)
      exact False.elim (different (hx.symm.trans hy))

/-- The same refusal is forced at the other world. -/
theorem safe_must_refuse_both
    (act : O → Option Bool) (hSafe : AlwaysSafe observe label act)
    (x y : W)
    (same : observe x = observe y)
    (different : label x ≠ label y) :
    act (observe x) = none ∧ act (observe y) = none := by
  have h := safe_must_refuse observe label act hSafe x y same different
  exact ⟨h, by rw [← same]; exact h⟩

/-- Having a collection of additional probes does not help when each probe
returns exactly the same value in both worlds. -/
theorem no_set_of_probes_can_separate
    {I : Type v} (probes : I → W → Bool)
    (x y : W)
    (equal_every_probe : ∀ i : I, probes i x = probes i y)
    (different : label x ≠ label y) :
    ∀ classifier : (I → Bool) → Bool,
      ¬ (classifier (fun i => probes i x) = label x ∧
         classifier (fun i => probes i y) = label y) := by
  intro classifier
  have hSame : (fun i => probes i x) = (fun i => probes i y) := by
    funext i
    exact equal_every_probe i
  exact no_two_correct (fun i : I => probes i) label classifier x y hSame different

#print axioms deterministic_same_prediction
#print axioms no_two_correct
#print axioms safe_must_refuse
#print axioms safe_must_refuse_both
#print axioms no_set_of_probes_can_separate

end InsacermoIndistinguishability
