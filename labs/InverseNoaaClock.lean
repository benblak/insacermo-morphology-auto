/-!
INSACERMO inverse observation laboratory.
Lean certifies the exact Boolean arithmetic of a three-slot observation clock
and non-identifiability outside queried times; NOT the empirical NOAA source
or an unrestricted physical law.
-/
namespace InsacermoInverseClock

def waveObserved (slot : Nat) : Bool := slot % 3 == 1

theorem three_slot_period (t : Nat) :
    waveObserved (t + 3) = waveObserved t := by
  simp [waveObserved, Nat.add_mod]

theorem three_slot_pattern :
    waveObserved 0 = false ∧
    waveObserved 1 = true ∧
    waveObserved 2 = false := by
  decide

theorem cannot_have_period_one :
    waveObserved 0 ≠ waveObserved 1 := by decide

theorem cannot_have_period_two :
    waveObserved 1 ≠ waveObserved 3 := by decide

theorem exact_one_record_per_three_slots :
    ((List.range 3).filter (fun t => waveObserved t)).length = 1 := by
  decide

def alteredAt (f : Nat → Bool) (needle t : Nat) : Bool :=
  if t = needle then !(f t) else f t

theorem unqueried_exception_indistinguishable
    (times : List Nat) (needle : Nat) (notQueried : needle ∉ times)
    (f : Nat → Bool) :
    (∀ t ∈ times, alteredAt f needle t = f t) ∧
    alteredAt f needle needle ≠ f needle := by
  constructor
  · intro t ht
    have different : t ≠ needle := by
      intro h
      apply notQueried
      simpa [h] using ht
    simp [alteredAt, different]
  · cases h : f needle <;> simp [alteredAt, h]

end InsacermoInverseClock
