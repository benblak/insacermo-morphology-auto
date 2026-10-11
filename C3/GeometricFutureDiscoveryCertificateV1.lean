import C3.PortableExactSearchV1

/-! INSACERMO: geometry graph future obligations, independently modeled.
    Worlds 0/1 are observed fault masks 1/32. World 2 has both repaired.
    ACT edges consume the present route, so future route must remain.
    Probe 0 senses which repair is needed; probe 1/2 perform repairs.
    The finite grammar is complete as proved by PortableExactSearchV1.
-/
namespace INSACERMO.GeoFuture
open PortableC3

def m : Model := {
 worldCount := 3
 actionCount := 3
 probeCount := 3
 good := [
  [false,false,false],
  [false,false,false],
  [true,true,false]]
 sense := [[2,1,3],[3,3,3],[3,3,3]]
 nextFalse := [[0,1,2],[2,1,2],[0,2,2]]
 nextTrue := [[0,1,2],[2,1,2],[0,2,2]]
 actionCost := [0,0,0]
 probeCost := [1,2,2]
}
def initial : List Nat := [0,1]
def tree : Tree := .probe 0
  (.probe 2 (.act 0) (.act 0))
  (.probe 1 (.act 0) (.act 0))
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
theorem input_wellformed : wellFormed m initial = true := by decide +kernel
theorem adaptive_plan_valid : checkTree m 2 3 initial tree = true := by decide +kernel
theorem below_three_impossible : canFinite m 2 2 initial = false := by decide +kernel
theorem exact_minimum_budget :
    checkTree m 2 3 initial tree = true ∧
    ∀ b, b < 3 → canFinite m 2 b initial = false := by
  constructor
  · exact adaptive_plan_valid
  · intro b hb
    exact one_infeasible_budget_excludes_all_cheaper
      m 2 2 initial below_three_impossible b (by omega)
theorem sound_full_tree : Safe m 2 3 initial tree :=
  accepted_certificate_sound m 2 3 initial tree adaptive_plan_valid

end INSACERMO.GeoFuture
