import C3.PortableExactSearchV1

namespace PortableC3.PendulumFineConditional
/- A HYPOTHETICAL precision of 3ms separates predictions at 0.330m.
   This hypothesis is not established by pendulum sensor calibration;
   the training sqrt fit can exceed 3ms, so this does NOT validate a real law. -/
def model : PortableC3.Model := {
  worldCount := 2
  actionCount := 2
  probeCount := 2
  good := [[true, false], [false, true]]
  sense := [[1, 2], [3, 3]]
  nextFalse := [[0, 1], [0, 1]]
  nextTrue := [[0, 1], [0, 1]]
  actionCost := [0, 0]
  probeCost := [1, 1]
}
def start : List Nat := [0, 1]
def depth : Nat := 4
def emitted : PortableC3.Tree := .probe 0 (.act 0) (.act 1)

theorem model_valid : PortableC3.wellFormed model start = true := by decide +kernel
theorem one_probe_tree_is_safe :
    PortableC3.checkTree model depth 1 start emitted = true := by decide +kernel
theorem zero_probe_cannot_identify :
    PortableC3.canFinite model depth 0 start = false := by decide +kernel

theorem one_probe_is_optimal :
    PortableC3.checkTree model depth 1 start emitted = true ∧
    (∀ b, b < 1 → PortableC3.canFinite model depth b start = false) := by
  constructor
  · exact one_probe_tree_is_safe
  · intro b hb
    have hle : b ≤ 0 := by omega
    exact PortableC3.one_infeasible_budget_excludes_all_cheaper
      model depth 0 start zero_probe_cannot_identify b hle
#print axioms one_probe_is_optimal
end PortableC3.PendulumFineConditional
