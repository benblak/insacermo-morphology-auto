import C3.PortableExactSearchV1

namespace PortableC3.PendulumReportSet
/- Policy 2 is a declared, abstract reporting action, safe for both fitted laws.
   It is NOT a physical repair or a proof that either law is physically true. -/
def model : PortableC3.Model := {
  worldCount := 2
  actionCount := 3
  probeCount := 2
  good := [[true, false, true], [false, true, true]]
  sense := [[3, 3], [3, 3]]
  nextFalse := [[0, 1], [0, 1]]
  nextTrue := [[0, 1], [0, 1]]
  actionCost := [0, 0, 0]
  probeCost := [1, 1]
}
def start : List Nat := [0, 1]
def depth : Nat := 4
def emitted : PortableC3.Tree := .act 2

theorem model_valid : PortableC3.wellFormed model start = true := by decide +kernel
theorem report_compatible_set_is_safe :
    PortableC3.checkTree model depth 0 start emitted = true := by decide +kernel
theorem zero_is_minimal_cost :
    PortableC3.checkTree model depth 0 start emitted = true ∧
    (∀ b, b < 0 → PortableC3.canFinite model depth b start = false) := by
  constructor
  · exact report_compatible_set_is_safe
  · intro b hb
    omega
#print axioms report_compatible_set_is_safe
end PortableC3.PendulumReportSet
