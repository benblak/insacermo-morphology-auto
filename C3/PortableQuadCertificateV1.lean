import C3.PortableFiniteVerifierV1
namespace PortableC3.Quad

def model : PortableC3.Model := {
  worldCount := 8
  actionCount := 4
  probeCount := 4
  good := [[false,false,false,false],[false,false,false,false],[false,false,false,false],[false,false,false,false],[true,false,false,false],[false,true,false,false],[false,false,true,false],[false,false,false,true]]
  sense := [[1,2,1,2,1,2,1,2],[1,1,2,2,1,1,2,2],[1,1,1,1,1,1,1,1],[3,3,3,3,3,3,3,3]]
  nextFalse := [[0,1,2,3,4,5,6,7],[0,1,2,3,4,5,6,7],[4,5,6,7,4,5,6,7],[0,1,2,3,4,5,6,7]]
  nextTrue := [[0,1,2,3,4,5,6,7],[0,1,2,3,4,5,6,7],[4,5,6,7,4,5,6,7],[0,1,2,3,4,5,6,7]]
  actionCost := [0,0,0,0]
  probeCost := [1,1,1,1]
}
def start : List Nat := [0,1,2,3]
def emitted : PortableC3.Tree :=
  .probe 0
    (.probe 1 (.probe 2 (.act 0) (.act 0)) (.probe 2 (.act 2) (.act 0)))
    (.probe 1 (.probe 2 (.act 1) (.act 0)) (.probe 2 (.act 3) (.act 0)))

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

theorem input_well_formed : PortableC3.wellFormed model start = true := by
  decide +kernel

theorem policy_certificate : PortableC3.checkTree model 3 3 start emitted = true := by
  decide +kernel

theorem no_cheaper_strategy : PortableC3.canFinite model 3 2 start = false := by
  decide +kernel

theorem tampered_certificate_rejected :
    PortableC3.checkTree model 3 3 start (.act 4) = false := by
  decide +kernel
end PortableC3.Quad
