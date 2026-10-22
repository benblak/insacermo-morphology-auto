import C3.PortableExactSearchV1
namespace MemGuardC3Audit_EXIT_200
open PortableC3
def m : Model := {
  worldCount := 4
  actionCount := 2
  probeCount := 3
  good := [[true,false]
  sense := [[2,1,1,1]
  nextFalse := [[0,1,2,3]
  nextTrue := [[0,1,2,3]
  actionCost := [0,0]
  probeCost := [1,1,1]
}
def upper : List Nat := [0,1,2,3]
def choice : Tree := (Tree.probe 0 (Tree.probe 0 (Tree.probe 2 (Tree.act 0) (Tree.act 1)) (Tree.act 0)) (Tree.act 0))
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
theorem model_wellformed : wellFormed m upper = true := by decide +kernel
theorem decision_verified : checkTree m 3 3 upper choice = true := by decide +kernel
theorem all_branches_safe : Safe m 3 3 upper choice :=
  accepted_certificate_sound m 3 3 upper choice decision_verified
end MemGuardC3Audit_EXIT_200
