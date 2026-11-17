/-!
INSACERMO inverse observation: exact finite contingency checks on audited NOAA
transition counts, plus the logical limit of missing physical measurements.
The external NOAA observations themselves are independently checked in Python,
not assumed proved by Lean.
-/
namespace InsacermoDropout

def observedHeight (present : Bool) (height : Nat) : Option Nat :=
  if present then some height else none

theorem two_missing_heights_are_indistinguishable :
    observedHeight false 0 = observedHeight false 1 ∧ (0 : Nat) ≠ 1 := by
  decide

theorem no_decoding_of_all_missing_heights (decoder : Option Nat → Nat) :
    decoder none ≠ 0 ∨ decoder none ≠ 1 := by
  by_cases h : decoder none = 0
  · right
    simp [h]
  · exact Or.inl h

theorem measurement_value_follows_from_present_observation
    (a b : Nat) (h : observedHeight true a = observedHeight true b) :
    a = b := by
  simpa [observedHeight] using h

/-- Compare P(missing now | missing at prior scheduled reading) to
    P(missing now | nonmissing at prior scheduled reading),
    without division, floating point, or approximations.
    a,b are preceding present and current present/missing; c,d are
    preceding missing and current present/missing.
    Denominators positive in all five audited cases. -/
def nextDropoutMoreLikely (a b c d : Nat) : Bool :=
  decide (d * (a + b) > b * (c + d))

theorem reference_41002_2023 :
    nextDropoutMoreLikely 17367 53 60 10 = true := by decide

theorem validation_42002_2023 :
    nextDropoutMoreLikely 17383 42 42 13 = true := by decide

theorem validation_46002_2023 :
    nextDropoutMoreLikely 12687 32 38 7 = true := by decide

theorem validation_41002_2024 :
    nextDropoutMoreLikely 17413 33 45 5 = true := by decide

theorem validation_42002_2024 :
    nextDropoutMoreLikely 13387 45 45 4 = true := by decide

end InsacermoDropout
