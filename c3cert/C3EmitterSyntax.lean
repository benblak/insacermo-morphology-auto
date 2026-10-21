import C3.PortableVerifierSoundnessV1
open PortableC3
-- Verbatim structural fragment emitted by frozen insacermo_one_engine.py for fresh case #39.
def mustActionsModel : Model := {
 worldCount := 5
 actionCount := 7
 probeCount := 3
 good := [[false,false,true,false,false,false,true],[false,false,false,false,false,false,false],[false,false,true,false,false,false,false],[false,false,true,false,false,false],[false,false,true,false,false,false,false]]
 sense := [[3,2,3,3,3],[3,3,3,3,2],[1,3,1,1,3]]
 nextFalse := [[0,1,2,0,4],[0,1,2,3,4],[0,3,3,3,4]]
 nextTrue := [[0,3,2,0,4],[0,1,2,3,4],[0,3,0,0,4]]
 actionCost := [0,0,0,0,1,0,0]
 probeCost := [1,1,1]
}
#check mustActionsModel
