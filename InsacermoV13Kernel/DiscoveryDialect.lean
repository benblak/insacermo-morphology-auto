import Mathlib
import InsacermoV13Kernel.FrontierFactorization

namespace InsacermoV13Kernel

/-- Signed local interaction on one capability square.
    Positive values mean the joint gain exceeds the sum of the two isolated gains;
    negative values mean redundancy/substitution; zero is locally additive. -/
def FutureInteraction (a b c d : Nat) : Int :=
  (b : Int) + (c : Int) - (a : Int) - (d : Int)


/-- Exact decomposition of the joint right-to-forget dividend:
    joint gain = isolated gain of u + isolated gain of v + interaction. -/
theorem jointDividend_decomposition (a b c d : Nat) :
    (a : Int) - (d : Int) =
      ((a : Int) - (b : Int)) +
      ((a : Int) - (c : Int)) +
      FutureInteraction a b c d := by
  simp [FutureInteraction]
  ring

/-- Monotonicity alone confines the interaction to the total joint-change band.
    Here a=m(C), b=m(C+u), c=m(C+v), d=m(C+u+v). -/
theorem futureInteraction_band
    {a b c d : Nat}
    (hba : b ≤ a) (hca : c ≤ a)
    (hdb : d ≤ b) (hdc : d ≤ c) :
    (d : Int) - (a : Int) ≤ FutureInteraction a b c d ∧
    FutureInteraction a b c d ≤ (a : Int) - (d : Int) := by
  constructor <;> simp [FutureInteraction] <;> omega

/-- Pure complementarity: neither capability changes the requirement alone,
    but the pair does. It saturates the positive interaction bound. -/
theorem futureInteraction_pure_complementarity
    {a d : Nat} (hda : d ≤ a) :
    FutureInteraction a a a d = (a : Int) - (d : Int) := by
  simp [FutureInteraction]
  omega

/-- Pure redundancy/substitution: either capability alone already attains the
    same requirement as the pair. It saturates the negative interaction bound. -/
theorem futureInteraction_pure_redundancy
    {a d : Nat} (hda : d ≤ a) :
    FutureInteraction a d d d = (d : Int) - (a : Int) := by
  simp [FutureInteraction]
  omega

/-- The interaction sign always falls into exactly the familiar three regimes:
    complementarity, local additivity, or redundancy. -/
theorem futureInteraction_trichotomy (a b c d : Nat) :
    FutureInteraction a b c d < 0 ∨
    FutureInteraction a b c d = 0 ∨
    0 < FutureInteraction a b c d := by
  exact lt_trichotomy (FutureInteraction a b c d) 0

end InsacermoV13Kernel
