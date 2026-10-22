import C3.PortableExactSearchV1
namespace INSACERMO.C3OneDecision
open PortableC3
def mustActionsModel : Model := {
 worldCount := 4
 actionCount := 2
 probeCount := 3
 good := [[true,false],[true,false],[true,true],[false,true]]
 sense := [[2,1,1,1],[1,2,1,1],[1,1,1,2]]
 nextFalse := [[0,1,2,3],[0,1,2,3],[0,1,2,3]]
 nextTrue := [[0,1,2,3],[0,1,2,3],[0,1,2,3]]
 actionCost := [0,0]
 probeCost := [1,1,1]
}
def mayActionsModel : Model := {
 worldCount := 4
 actionCount := 2
 probeCount := 3
 good := [[true,false],[true,false],[true,true],[false,true]]
 sense := [[2,1,1,1],[1,2,1,1],[1,1,1,2]]
 nextFalse := [[0,1,2,3],[0,1,2,3],[0,1,2,3]]
 nextTrue := [[0,1,2,3],[0,1,2,3],[0,1,2,3]]
 actionCost := [0,0]
 probeCost := [1,1,1]
}
def upper : List Nat := [0,1,2,3]
def lower : List Nat := [0,1,2,3]
def mustFlags : List Bool := [true,true]
def mayFlags : List Bool := [true,true]
def repairFlags : List Bool := [false,false,false]
def repairSensor (q : Nat) : Bool := (repairFlags[q]?).getD false
theorem policy_bounds : ((List.range 2).all (fun a =>
  !(boolAt mustFlags a) || boolAt mayFlags a)) = true := by decide +kernel
theorem actual_repair_transformation : ((List.range 3).all (fun q =>
  !(repairSensor q) || upper.any (fun w =>
    ((permits (senseAt mustActionsModel q w) false) && decide (nextAt mustActionsModel q w false ≠ w)) ||
    ((permits (senseAt mustActionsModel q w) true) && decide (nextAt mustActionsModel q w true ≠ w))))) = true := by decide +kernel
theorem reserve_enforced : 0 + 3 < 5 ∧ 3 ≤ 3 := by decide +kernel
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
theorem input_upper_ok : wellFormed mustActionsModel upper = true := by decide +kernel
theorem input_lower_ok : wellFormed mayActionsModel lower = true := by decide +kernel
theorem lower_subset_upper : (lower.all (fun w => upper.contains w)) = true := by decide +kernel
def choice : Tree := (Tree.probe 0 (Tree.probe 0 (Tree.probe 1 (Tree.act 1) (Tree.act 0)) (Tree.act 0)) (Tree.act 0))
theorem decision_verified : checkTree mustActionsModel 3 3 upper choice = true := by decide +kernel
theorem all_branches_safe : Safe mustActionsModel 3 3 upper choice :=
  accepted_certificate_sound mustActionsModel 3 3 upper choice decision_verified
end INSACERMO.C3OneDecision
