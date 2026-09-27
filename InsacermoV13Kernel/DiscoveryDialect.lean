import InsacermoV13Kernel.FrontierFactorization

namespace InsacermoV13Kernel

/-- Total right-to-forget dividend produced by adding both capabilities. -/
def JointDividend (a d : Nat) : Int :=
  (a : Int) - (d : Int)

/-- Sum of the two isolated right-to-forget dividends. -/
def IsolatedDividend (a b c : Nat) : Int :=
  ((a : Int) - (b : Int)) + ((a : Int) - (c : Int))

/-- Residual local interaction:
    what the joint capability pair does beyond the isolated effects. -/
def FutureInteraction (a b c d : Nat) : Int :=
  JointDividend a d - IsolatedDividend a b c

/-- Definition lock: the interaction term is exactly the unexplained remainder. -/
theorem futureInteraction_definition (a b c d : Nat) :
    FutureInteraction a b c d =
      JointDividend a d - IsolatedDividend a b c := by
  rfl

/-- The strict-synergy square already observed by INSACERMO has positive interaction. -/
theorem futureInteraction_strict_synergy_witness :
    FutureInteraction 2 2 2 1 = 1 := by
  decide

/-- A redundancy square has negative interaction. -/
theorem futureInteraction_redundancy_witness :
    FutureInteraction 2 1 1 1 = -1 := by
  decide

end InsacermoV13Kernel
