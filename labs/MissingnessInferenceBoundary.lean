/-!
INSACERMO inverse observation epistemic kernel: missing wave magnitude is
not entailed by observation schedule, and cannot be inferred from mask alone.
This is independent of whether NOAA dropouts correlate with wind or pressure.
-/
namespace InsacermoMissingness

def observedHeight (hasMeasurement : Bool) (height : Nat) : Option Nat :=
  if hasMeasurement then some height else none

theorem missing_height_is_unidentifiable (a b : Nat) (h : a ≠ b) :
    observedHeight false a = observedHeight false b ∧ a ≠ b := by
  simp [observedHeight, h]

theorem measured_height_is_identifiable (a b : Nat)
    (h : observedHeight true a = observedHeight true b) : a = b := by
  simpa [observedHeight] using h

theorem no_universal_guess_from_missing_values
    (guess : Option Nat → Nat) :
    (∃ physicalHeight : Nat,
      observedHeight false physicalHeight = none ∧
      guess none ≠ physicalHeight) := by
  let n := guess none
  refine ⟨n + 1, ?_, ?_⟩
  · rfl
  · omega

def oneOfThree (t : Nat) : Bool := t % 3 == 1

theorem cyclic_observation_mask (t : Nat) :
    oneOfThree (t + 3) = oneOfThree t := by
  simp [oneOfThree]

theorem one_slot_out_of_three :
    [oneOfThree 0, oneOfThree 1, oneOfThree 2] =
      [false, true, false] := by decide

end InsacermoMissingness
