import InsacermoActionabilityInformation.CapabilityComplementarity

namespace InsacermoActionabilityInformation

/-- Binary coarse-safety indicator for the square witness. -/
def SquareCoarseGain (C : Set SquareAction) : Nat :=
  if SafeRep SquareGood Set.univ C SquareCoarseObs then 1 else 0

/-- The base capability set has no coarse-safety gain. -/
theorem squareGain_base_zero : SquareCoarseGain SquareBaseCaps = 0 := by
  simp [SquareCoarseGain, squareCoarse_unsafe_base]

/-- Adding a0 alone has no gain. -/
theorem squareGain_add0_zero : SquareCoarseGain SquareCapsAdd0 = 0 := by
  simp [SquareCoarseGain, squareCoarse_unsafe_add0]

/-- Adding a3 alone has no gain. -/
theorem squareGain_add3_zero : SquareCoarseGain SquareCapsAdd3 = 0 := by
  simp [SquareCoarseGain, squareCoarse_unsafe_add3]

/-- Adding both repair actions unlocks the coarse representation. -/
theorem squareGain_both_one : SquareCoarseGain SquareCapsBoth = 1 := by
  simp [SquareCoarseGain, squareCoarse_safe_both]

/-- Strict increasing returns witness. The marginal gain of adding `a0` is
zero at the base capability set but one after `a3` has already been added. -/
theorem square_strict_increasing_returns :
    (SquareCoarseGain SquareCapsAdd0 - SquareCoarseGain SquareBaseCaps) <
    (SquareCoarseGain SquareCapsBoth - SquareCoarseGain SquareCapsAdd3) := by
  simp [squareGain_base_zero, squareGain_add0_zero,
    squareGain_add3_zero, squareGain_both_one]

/-- Explicit failure of the diminishing-returns inequality associated with
submodularity for this capability gain functional. -/
theorem square_capability_gain_not_diminishing_returns :
    ¬ ((SquareCoarseGain SquareCapsBoth - SquareCoarseGain SquareCapsAdd3) ≤
       (SquareCoarseGain SquareCapsAdd0 - SquareCoarseGain SquareBaseCaps)) := by
  simp [squareGain_base_zero, squareGain_add0_zero,
    squareGain_add3_zero, squareGain_both_one]

/-- A compact bundled certificate of non-submodular behavior in the finite
witness: individual repairs have zero gain, while their combination has
positive gain. -/
theorem square_capability_gain_synergy_certificate :
    SquareCoarseGain SquareBaseCaps = 0 ∧
    SquareCoarseGain SquareCapsAdd0 = 0 ∧
    SquareCoarseGain SquareCapsAdd3 = 0 ∧
    SquareCoarseGain SquareCapsBoth = 1 ∧
    (SquareCoarseGain SquareCapsAdd0 - SquareCoarseGain SquareBaseCaps) <
      (SquareCoarseGain SquareCapsBoth - SquareCoarseGain SquareCapsAdd3) := by
  exact ⟨squareGain_base_zero,
    squareGain_add0_zero,
    squareGain_add3_zero,
    squareGain_both_one,
    square_strict_increasing_returns⟩

end InsacermoActionabilityInformation
