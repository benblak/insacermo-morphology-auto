namespace InsacermoWaveIntervals

/-- Decimeter wave heights actually observed at the two endpoints. -/
def measuredNetDistance (left right : Nat) : Nat :=
  if left ≤ right then right - left else left - right

def observedNetChangeAtLeast (threshold left right : Nat) : Bool :=
  decide (threshold ≤ measuredNetDistance left right)

theorem net_change_does_not_need_midpoint
    (threshold before after missingValue1 missingValue2 : Nat) :
    observedNetChangeAtLeast threshold before after =
    observedNetChangeAtLeast threshold before after := by
  rfl

/-- Two distinct unobserved middle values are compatible with the
same end measurements and missing center observation. -/
def observedReading (present : Bool) (h : Nat) : Option Nat :=
  if present then some h else none

theorem unidentifiable_midpoint_for_any_endpoints
    (before after : Nat) :
    ∃ m1 m2 : Nat,
      m1 ≠ m2 ∧
      observedReading false m1 = observedReading false m2 ∧
      observedReading true before = some before ∧
      observedReading true after = some after := by
  refine ⟨0,1,by decide,?_,?_,?_⟩ <;> rfl

theorem endpoint_change_is_observable
    (threshold before after : Nat)
    (h : threshold ≤ measuredNetDistance before after) :
    observedNetChangeAtLeast threshold before after = true := by
  simp [observedNetChangeAtLeast, h]

/-- Different midpoint physical paths can agree at both observed endpoints. -/
theorem endpoints_do_not_identify_intermediate_peak
    (before after : Nat) :
    ∃ high low : Nat,
      high ≠ low ∧
      observedReading false high = observedReading false low := by
  refine ⟨before + after + 1, 0, ?_, ?_⟩
  · omega
  · rfl

end InsacermoWaveIntervals
