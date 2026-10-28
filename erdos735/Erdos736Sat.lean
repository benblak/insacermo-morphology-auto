import Std.Tactic.BVDecide
namespace Erdos736Sat
set_option maxHeartbeats 0

def c3 (s : BitVec 3) : BitVec 3 :=
  (if s.getLsbD 0 then (1#3) else (0#3)) +
  (if s.getLsbD 1 then (1#3) else (0#3)) +
  (if s.getLsbD 2 then (1#3) else (0#3))

theorem mini_test (s : BitVec 3) :
    (s.getLsbD 0 && s.getLsbD 1 && s.getLsbD 2) = false →
    c3 s ≤ (2#3) := by
  intro h
  simp only [c3]
  bv_decide

#print axioms mini_test
end Erdos736Sat
