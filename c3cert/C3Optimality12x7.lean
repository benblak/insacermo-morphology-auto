import C3Decision12x7
namespace INSACERMO.C3OneDecision
open PortableC3
set_option maxRecDepth 16384
set_option maxRecDepth 16384
set_option maxHeartbeats 40000000

/-- Exhaustive finite AND/OR decision: no plan with three probes and budget three. -/
theorem depth_three_impossible :
    canFinite mustActionsModel 3 3 upper = false := by
  decide +kernel

/-- Four queries suffice, and three queries cannot suffice. -/
theorem exact_minimum_four :
    checkTree mustActionsModel 4 4 upper choice = true ∧
    canFinite mustActionsModel 3 3 upper = false :=
  ⟨decision_verified, depth_three_impossible⟩

#print axioms depth_three_impossible
#print axioms exact_minimum_four
end INSACERMO.C3OneDecision
