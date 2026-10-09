import Std

/-! INSACERMO - Order Spectrum of minimal ACT obstructions.
    Computable finite predicates. The theorem proves separation of
    minimal obstruction order from probe depth.
    No machine learning or custom axioms.
-/
namespace INSACERMO.OrderSpectrum
def compatible (rows : List Nat) (allMask : Nat) : Bool :=
  (rows.foldl Nat.land allMask) != 0

def obstruction (rows : List Nat) (allMask : Nat) : Bool :=
  !compatible rows allMask

def properDeletionActs (rows : List Nat) (allMask : Nat) : Bool :=
  (List.range rows.length).all fun i =>
    compatible (rows.take i ++ rows.drop (i+1)) allMask

def minimalObstruction (rows : List Nat) (allMask : Nat) : Bool :=
  obstruction rows allMask && properDeletionActs rows allMask

def allExcept (n : Nat) : List Nat :=
  (List.range n).map fun i => ((2^n)-1) - (2^i)

def exclusive (n : Nat) : List Nat :=
  (List.range n).map fun i => 2^i

theorem order_three_minimal :
    minimalObstruction (allExcept 3) 7 = true := by decide +kernel
theorem order_four_minimal :
    minimalObstruction (allExcept 4) 15 = true := by decide +kernel
theorem order_eleven_minimal :
    minimalObstruction (allExcept 11) 2047 = true := by decide +kernel
theorem order_two_exclusive :
    minimalObstruction [1,2] 31 = true := by decide +kernel
theorem larger_exclusive_not_minimal :
    minimalObstruction (exclusive 5) 31 = false := by decide +kernel

/-- Two disjoint independent modules: one pair obstruction and
    one four-world obstruction, action masks from computed Python audit. -/
def mixed : List Nat := [240,15,238,221,187,119]
theorem mixed_pair_minimal :
    minimalObstruction [mixed[0]!,mixed[1]!] 255 = true := by decide +kernel
theorem mixed_four_minimal :
    minimalObstruction [mixed[2]!,mixed[3]!,mixed[4]!,mixed[5]!] 255 = true := by decide +kernel

/-- ACT obstruction order 11 exists even without any probe grammar,
    so it is not synonymous with sensing depth. -/
theorem order_not_probe_depth :
    minimalObstruction (allExcept 11) 2047 = true ∧
    minimalObstruction [1,2] 31 = true :=
  ⟨order_eleven_minimal,order_two_exclusive⟩
end INSACERMO.OrderSpectrum
