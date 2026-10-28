import Lean
namespace Erdos736LeanPrecheck
-- This file is deliberately a PARTIAL audit. It does not certify f(736)=609.
-- It verifies the exact arithmetic around the NEW endpoint 736 independently
-- of the Python certificate; the full 113-node upper bound is NOT imported.

def forbiddenAt736 (b : Nat) : Bool :=
  (0 < b && b < 736) &&
  (b * 736 % (b + 736) == 0) &&
  (0 < b * 736 / (b + 736)) &&
  (b * 736 / (b + 736) < b)

def newTriples736 : List (Nat × Nat × Nat) :=
  ((List.range 737).filter forbiddenAt736).map
    (fun b => (b * 736 / (b + 736), b, 736))

theorem exact_new_triples_at_736 :
    newTriples736 = [(207, 288, 736), (224, 322, 736)] := by
  decide +kernel

theorem total_subtraction : 736 - 127 = 609 := by decide

-- An exact logic implication: if all admissible sets exclude >=127 vertices,
-- none has more than 609 elements. The antecedent is NOT proved in this file.
theorem upper_bound_from_exclusions (excludedCount retainedCount : Nat)
    (partition : excludedCount + retainedCount = 736)
    (minimumExclusions : 127 ≤ excludedCount) :
    retainedCount ≤ 609 := by omega

#print axioms exact_new_triples_at_736
#print axioms total_subtraction
#print axioms upper_bound_from_exclusions
end Erdos736LeanPrecheck
