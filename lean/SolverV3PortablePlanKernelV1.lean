import Std
namespace InsacermoSolverV3PortablePlanKernelV1

structure PortableInstance where
  worldCount : Nat
  actionCount : Nat
  probeCount : Nat
  good : Nat → Nat → Bool
  probeOutcome : Nat → Nat → Nat

inductive Plan where
  | act : Nat → Plan
  | probe : Nat → List (Nat × Plan) → Plan
deriving Repr

def fullBelief (i : PortableInstance) : List Nat := List.range i.worldCount

def probeCell (i : PortableInstance) (belief : List Nat)
    (p outcome : Nat) : List Nat :=
  belief.filter fun w => i.probeOutcome p w == outcome

def outcomeCovered (i : PortableInstance) (belief : List Nat)
    (p : Nat) (branches : List (Nat × Plan)) : Bool :=
  belief.all fun w => branches.any fun b => b.1 == i.probeOutcome p w

def branchKeysUnique (branches : List (Nat × Plan)) : Bool :=
  let keys := branches.map Prod.fst
  keys.eraseDups == keys

def probeSplitsOn (i : PortableInstance) (belief : List Nat) (p : Nat) : Bool :=
  belief.any fun w => belief.any fun v =>
    i.probeOutcome p w != i.probeOutcome p v

def checkPlanFuel (i : PortableInstance) :
    Nat → List Nat → List Nat → Plan → Bool
  | 0, belief, _used, .act a =>
      a < i.actionCount && belief.all (fun w => i.good w a)
  | 0, _, _, .probe _ _ => false
  | _ + 1, belief, _, .act a =>
      a < i.actionCount && belief.all (fun w => i.good w a)
  | fuel + 1, belief, used, .probe p branches =>
      p < i.probeCount &&
      !used.contains p &&
      probeSplitsOn i belief p &&
      branchKeysUnique branches &&
      outcomeCovered i belief p branches &&
      branches.all (fun b =>
        let cell := probeCell i belief p b.1
        !cell.isEmpty && checkPlanFuel i fuel cell (p :: used) b.2)

def hasProbePathLength : Nat → Plan → Bool
  | 0, .act _ => true
  | 0, .probe _ _ => false
  | _ + 1, .act _ => false
  | d + 1, .probe _ branches =>
      branches.any fun b => hasProbePathLength d b.2

def planCostFuel (i : PortableInstance) :
    Nat → List Nat → Plan → Nat
  | 0, _, .act _ => 0
  | 0, _, .probe _ _ => 0
  | _ + 1, _, .act _ => 0
  | fuel + 1, belief, .probe p branches =>
      belief.length +
      branches.foldl (fun acc b =>
        acc + planCostFuel i fuel (probeCell i belief p b.1) b.2) 0

def rootProbe? : Plan → Option Nat
  | .act _ => none
  | .probe p _ => some p

def PortablePlanCertificateValid (i : PortableInstance) (plan : Plan)
    (expectedDepth expectedCost : Nat) (expectedRoot : Option Nat) : Prop :=
  checkPlanFuel i expectedDepth (fullBelief i) [] plan = true ∧
  hasProbePathLength expectedDepth plan = true ∧
  planCostFuel i expectedDepth (fullBelief i) plan = expectedCost ∧
  rootProbe? plan = expectedRoot

instance certDecidable (i : PortableInstance) (plan : Plan)
    (expectedDepth expectedCost : Nat) (expectedRoot : Option Nat) :
    Decidable (PortablePlanCertificateValid i plan expectedDepth expectedCost expectedRoot) := by
  unfold PortablePlanCertificateValid
  infer_instance

end InsacermoSolverV3PortablePlanKernelV1
