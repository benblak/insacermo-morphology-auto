import SolverV3PortablePlanKernelV1

namespace InsacermoTotalRuntimeSolverV3PlanV1

open InsacermoSolverV3PortablePlanKernelV1

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def goodTable : List (List Bool) :=
  [[false, true, false, false, false],
  [false, false, false, true, false]]

def probeOutcomeTable : List (List Nat) :=
  [[0, 1],
  [0, 0]]

def portableInstance : PortableInstance where
  worldCount := 2
  actionCount := 5
  probeCount := 2
  good := fun w a => (goodTable.getD w []).getD a false
  probeOutcome := fun p w => (probeOutcomeTable.getD p []).getD w 0

def certifiedPlan : Plan :=
  Plan.probe 0 [(0, Plan.act 1), (1, Plan.act 3)]

def sourceFactsDigest : String := "sha256:0b01640c976926eda059f06b77f9d622ac303e1bead1189921d5ee6a9b18769c"
def certifiedDepth : Nat := 1
def certifiedTotalProbeCost : Nat := 2
def certifiedRootProbe : Option Nat := some 0

theorem solver_v3_portable_plan_certificate_v1 :
    PortablePlanCertificateValid
      portableInstance
      certifiedPlan
      certifiedDepth
      certifiedTotalProbeCost
      certifiedRootProbe := by
  native_decide

end InsacermoTotalRuntimeSolverV3PlanV1
