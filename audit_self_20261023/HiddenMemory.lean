import C3.PortableExactSearchV1

namespace INSACERMO.HiddenMemory
open PortableC3

def m : Model := {
 worldCount := 3
 actionCount := 1
 probeCount := 1
 good := [[true], [true], [false]]
 sense := [[3,3,3]]
 nextFalse := [[0,2,2]]
 nextTrue := [[0,2,2]]
 actionCost := [0]
 probeCost := [0]
}
def x : List Nat := [0,1]
def tick (xs : List Nat) := after m xs 0 false
set_option maxRecDepth 8192

theorem well_formed : wellFormed m x = true := by decide +kernel
theorem identical_initial_capability : direct m 0 x = true := by decide +kernel
theorem same_observation_both_outcomes :
  after m x 0 false = after m x 0 true := by decide +kernel
theorem future_states_differ : tick x = [0,2] := by decide +kernel
theorem future_action_no_longer_robust : direct m 0 (tick x) = false := by
  decide +kernel
theorem world_zero_keeps_ability : direct m 0 (tick [0]) = true := by
  decide +kernel
theorem world_one_loses_ability : direct m 0 (tick [1]) = false := by
  decide +kernel

end INSACERMO.HiddenMemory
