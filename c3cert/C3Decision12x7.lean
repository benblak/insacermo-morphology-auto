import C3.PortableVerifierSoundnessV1
namespace INSACERMO.C3OneDecision
open PortableC3
def mustActionsModel : Model := { worldCount := 12
 actionCount := 12
 probeCount := 7
 good := [[true,false,false,false,false,false,false,false,false,false,false,false],[false,true,false,false,false,false,false,false,false,false,false,false],[false,false,true,false,false,false,false,false,false,false,false,false],[false,false,false,true,false,false,false,false,false,false,false,false],[false,false,false,false,true,false,false,false,false,false,false,false],[false,false,false,false,false,true,false,false,false,false,false,false],[false,false,false,false,false,false,true,false,false,false,false,false],[false,false,false,false,false,false,false,true,false,false,false,false],[false,false,false,false,false,false,false,false,true,false,false,false],[false,false,false,false,false,false,false,false,false,true,false,false],[false,false,false,false,false,false,false,false,false,false,true,false],[false,false,false,false,false,false,false,false,false,false,false,true]]
 sense := [[1,2,1,2,1,2,1,2,1,1,1,1],[1,1,2,2,1,1,1,1,2,1,1,2],[1,2,1,2,2,2,1,1,2,2,2,1],[1,1,2,1,1,1,2,2,2,2,2,1],[1,2,2,2,1,1,2,2,2,2,1,2],[2,2,1,2,1,2,2,1,2,2,1,1],[1,2,1,2,2,2,1,1,1,2,2,1]]
 nextFalse := [[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11]]
 nextTrue := [[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11]]
 actionCost := [0,0,0,0,0,0,0,0,0,0,0,0]
 probeCost := [1,1,1,1,1,1,1]
}
def mayActionsModel : Model := { worldCount := 12
 actionCount := 12
 probeCount := 7
 good := [[true,false,false,false,false,false,false,false,false,false,false,false],[false,true,false,false,false,false,false,false,false,false,false,false],[false,false,true,false,false,false,false,false,false,false,false,false],[false,false,false,true,false,false,false,false,false,false,false,false],[false,false,false,false,true,false,false,false,false,false,false,false],[false,false,false,false,false,true,false,false,false,false,false,false],[false,false,false,false,false,false,true,false,false,false,false,false],[false,false,false,false,false,false,false,true,false,false,false,false],[false,false,false,false,false,false,false,false,true,false,false,false],[false,false,false,false,false,false,false,false,false,true,false,false],[false,false,false,false,false,false,false,false,false,false,true,false],[false,false,false,false,false,false,false,false,false,false,false,true]]
 sense := [[1,2,1,2,1,2,1,2,1,1,1,1],[1,1,2,2,1,1,1,1,2,1,1,2],[1,2,1,2,2,2,1,1,2,2,2,1],[1,1,2,1,1,1,2,2,2,2,2,1],[1,2,2,2,1,1,2,2,2,2,1,2],[2,2,1,2,1,2,2,1,2,2,1,1],[1,2,1,2,2,2,1,1,1,2,2,1]]
 nextFalse := [[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11]]
 nextTrue := [[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11]]
 actionCost := [0,0,0,0,0,0,0,0,0,0,0,0]
 probeCost := [1,1,1,1,1,1,1]
}
def upper : List Nat := [0,1,2,3,4,5,6,7,8,9,10,11]
def lower : List Nat := upper
def choice : Tree := Tree.probe 0
 (Tree.probe 2
  (Tree.probe 1 (Tree.probe 3 (Tree.act 0) (Tree.act 6))
                 (Tree.probe 3 (Tree.act 11) (Tree.act 2)))
  (Tree.probe 4 (Tree.probe 3 (Tree.act 4) (Tree.act 10))
                 (Tree.probe 1 (Tree.act 9) (Tree.act 8))))
 (Tree.probe 1
  (Tree.probe 2 (Tree.act 7) (Tree.probe 4 (Tree.act 5) (Tree.act 1)))
  (Tree.act 3))
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
theorem input_upper_ok : wellFormed mustActionsModel upper = true := by decide +kernel
theorem input_lower_ok : wellFormed mayActionsModel lower = true := by decide +kernel
theorem decision_verified : checkTree mustActionsModel 4 4 upper choice = true := by decide +kernel
theorem all_branches_safe : Safe mustActionsModel 4 4 upper choice :=
  accepted_certificate_sound mustActionsModel 4 4 upper choice decision_verified
#print axioms decision_verified
#print axioms all_branches_safe
end INSACERMO.C3OneDecision
