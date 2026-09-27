import InsacermoV13Kernel.FrontierFactorization

namespace InsacermoV13Kernel

/-- Total right-to-forget dividend produced by adding both capabilities. -/
def JointDividend (a d : Nat) : Int :=
  (a : Int) - (d : Int)

/-- Sum of the two isolated right-to-forget dividends. -/
def IsolatedDividend (a b c : Nat) : Int :=
  ((a : Int) - (b : Int)) + ((a : Int) - (c : Int))

/-- Residual local interaction:
    what the joint capability pair does beyond the sum of the isolated effects. -/
def FutureInteraction (a b c d : Nat) : Int :=
  JointDividend a d - IsolatedDividend a b c

/-- Exact INSACERMO interaction decomposition:
    joint gain = isolated-u gain + isolated-v gain + residual interaction. -/
theorem jointDividend_decomposition (a b c d : Nat) :
    JointDividend a d =
      IsolatedDividend a b c + FutureInteraction a b c d := by
  simp [FutureInteraction]

/-- If neither capability changes the requirement alone, all joint improvement
    is interaction. -/
theorem futureInteraction_pure_complementarity (a d : Nat) :
    FutureInteraction a a a d = JointDividend a d := by
  simp [FutureInteraction, IsolatedDividend]

/-- Every local interaction lies in exactly one sign regime:
    redundancy/substitution, local additivity, or complementarity. -/
theorem futureInteraction_trichotomy (a b c d : Nat) :
    FutureInteraction a b c d < 0 ∨
    FutureInteraction a b c d = 0 ∨
    0 < FutureInteraction a b c d := by
  exact lt_trichotomy (FutureInteraction a b c d) 0

end InsacermoV13Kernel
