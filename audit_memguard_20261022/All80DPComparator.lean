import audit_memguard_20261022.All80DeclaredInstances
/-!
Fair comparator: dynamic programming witnesses from the *same* 80 historical
MemGuard contracts are checked by the *same* PortableC3 Lean kernel as the C3
witnesses. The DP planner is independent; its proof checker is deliberately
identical. This file does NOT prove performance, SHA hashes, or optimality.
-/
namespace MemGuardC3FairComparator
open PortableC3 MemGuardC3All80

def dpTree (isExit : Bool) : Tree :=
  if isExit then
    Tree.probe 2 (Tree.act 0) (Tree.act 1)
  else Tree.act 0

set_option maxRecDepth 16384
set_option maxHeartbeats 100000000

theorem dp_on_exact_same_eighty_models :
    runCases.all (fun p =>
      checkTree (modelFor p.1 p.2) 3 3 upper (dpTree p.1)) = true := by
  decide +kernel

theorem all_dp_strategies_safe (p : Bool × Nat)
    (hp : p ∈ runCases) :
    Safe (modelFor p.1 p.2) 3 3 upper (dpTree p.1) := by
  have h : checkTree (modelFor p.1 p.2) 3 3 upper (dpTree p.1) = true :=
    (List.all_eq_true.mp dp_on_exact_same_eighty_models) p hp
  exact accepted_certificate_sound _ _ _ _ _ h
end MemGuardC3FairComparator
