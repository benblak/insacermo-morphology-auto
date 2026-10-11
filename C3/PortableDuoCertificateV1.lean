import C3.PortableFiniteVerifierV1
namespace PortableC3.Duo

def model : PortableC3.Model := {
  worldCount := 2
  actionCount := 2
  probeCount := 2
  good := [[true,false],[false,true]]
  sense := [[1,2],[3,3]]
  nextFalse := [[0,1],[0,1]]
  nextTrue := [[0,1],[0,1]]
  actionCost := [0,0]
  probeCost := [1,1]
}
def start : List Nat := [0,1]
def emitted : PortableC3.Tree := .probe 0 (.act 0) (.act 1)

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

theorem input_well_formed : PortableC3.wellFormed model start = true := by
  decide +kernel

theorem policy_certificate : PortableC3.checkTree model 1 1 start emitted = true := by
  decide +kernel

theorem no_cheaper_strategy : PortableC3.canFinite model 1 0 start = false := by
  decide +kernel

theorem tampered_certificate_rejected :
    PortableC3.checkTree model 1 1 start (.act 2) = false := by
  decide +kernel
end PortableC3.Duo
