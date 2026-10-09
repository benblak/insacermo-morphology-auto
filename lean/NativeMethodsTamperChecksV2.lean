import SolverV3PortablePlanKernelV1
import NativeMethodsPlannerGeneratedV2

namespace INSACERMO.NativeMethodsTamper

open InsacermoSolverV3PortablePlanKernelV1
open InsacermoTotalRuntimeSolverV3PlanV1

theorem kernel_independent_plan_recheck :
    PortablePlanCertificateValid portableInstance certifiedPlan
      certifiedDepth certifiedTotalProbeCost certifiedRootProbe := by
  decide +kernel

def swappedBranches : Plan := Plan.probe 0 [(0, Plan.act 3), (1, Plan.act 1)]

theorem swapped_branches_rejected :
    checkPlanFuel portableInstance 1 (fullBelief portableInstance) []
      swappedBranches = false := by
  decide +kernel

theorem changed_cost_rejected :
    ¬ PortablePlanCertificateValid portableInstance certifiedPlan 1 1 (some 0) := by
  decide +kernel

theorem false_zero_depth_rejected :
    ¬ PortablePlanCertificateValid portableInstance certifiedPlan 0 2 (some 0) := by
  decide +kernel

theorem swapped_root_claim_rejected :
    ¬ PortablePlanCertificateValid portableInstance certifiedPlan 1 2 (some 1) := by
  decide +kernel

def invalidLeaf : Plan := Plan.act 0

theorem false_direct_act_rejected :
    checkPlanFuel portableInstance 0 (fullBelief portableInstance) []
      invalidLeaf = false := by
  decide +kernel

end INSACERMO.NativeMethodsTamper
