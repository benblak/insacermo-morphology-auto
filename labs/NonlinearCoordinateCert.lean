/-!
INSACERMO, November 2026. New isolated logical-arithmetic certificate.
The previously discovered 5-input abstraction is 0x0356fca9.
Finite witnesses come from sealed, independently replayed synthetic oracle data.
The original MAX TOTAL / C3 proof kernel is NOT modified.
-/
namespace InsacermoNonlinearCoordinate

set_option maxRecDepth 14000
set_option maxHeartbeats 8000000

def bit (n i : Nat) : Nat := (n / (2 ^ i)) % 2

def permuteAndFlip (x : Nat) (p : Array Nat) (flips : Nat) : Nat :=
  (List.range 5).foldl (fun sum k =>
    sum + ((bit x k + bit flips k) % 2) * (2 ^ (p.getD k 0))) 0

def localGate (x : Nat) (enabled : Bool) (target u v truth : Nat) : Nat :=
  if enabled then
    Nat.xor x ((bit truth (bit x u + 2 * bit x v)) * (2 ^ target))
  else x

def verifiedTransform (observed : Nat)
    (lp : Array Nat) (lm lf : Nat)
    (lg : Bool) (lt lu lv ltruth : Nat)
    (rp : Array Nat) (rm rf : Nat)
    (rg : Bool) (rt ru rv rtruth : Nat) : Bool :=
  (List.range 32).all (fun x =>
    ((bit observed (localGate (permuteAndFlip x lp lm) lg lt lu lv ltruth) + lf) % 2) ==
    ((bit 56032425 (localGate (permuteAndFlip x rp rm) rg rt ru rv rtruth) + rf) % 2))

/-- Any two-control Boolean function, without specifying its truth table,
can be used to update a third bit reversibly by XOR. -/
theorem every_two_control_boolean_gate_is_reversible
    (b u v : Bool) (f : Bool → Bool → Bool) :
    (b != f u v) != f u v = b := by
  cases b <;> cases h : f u v <;> decide

/-- The concrete NOR truth table (0001) cannot be an affine Boolean
expression a XOR b*u XOR c*v: it is genuinely non-linear. -/
theorem discovered_nor_gate_not_affine :
    ¬ ∃ a b c : Bool, ∀ u v : Bool,
      ((a != (b && u)) != (c && v)) = (!u && !v) := by
  decide

/-- Check each finite 32-point coordinate witness explicitly against the
previously sealed concept. Not a global 24-bit physical-law certificate. -/
theorem source0_exact :
  verifiedTransform 862372758 #[0,2,4,3,1] 2 0
    false 0 0 0 0 #[0,1,2,3,4] 0 0 false 0 0 0 0 = true := by decide

theorem source1_new_affine :
  verifiedTransform 3325491722 #[0,1,4,2,3] 21 0
    true 0 3 4 6 #[0,1,2,3,4] 0 0 false 0 0 0 0 = true := by decide

theorem source2_old_coordinate_match :
  verifiedTransform 2775125955 #[0,1,3,4,2] 11 0
    false 0 0 0 0 #[0,1,2,3,4] 0 0 false 0 0 0 0 = true := by decide

theorem target0_new_nonlinear :
  verifiedTransform 3325465443 #[0,2,3,4,1] 6 0
    true 1 0 2 1 #[0,1,2,3,4] 0 0 false 0 0 0 0 = true := by decide

theorem target1_new_nonlinear :
  verifiedTransform 3776896290 #[0,2,4,1,3] 20 0
    true 0 1 4 1 #[0,1,2,3,4] 0 0 false 0 0 0 0 = true := by decide

theorem target2_two_step_transform :
  verifiedTransform 1701422677 #[4,2,3,1,0] 15 0
    true 1 2 3 6 #[0,1,2,3,4] 0 0 true 0 1 2 2 = true := by decide

theorem target3_rare_exception_projected :
  verifiedTransform 1013564310 #[0,2,4,3,1] 22 0
    true 1 2 4 1 #[0,1,2,3,4] 0 0 false 0 0 0 0 = true := by decide

end InsacermoNonlinearCoordinate
