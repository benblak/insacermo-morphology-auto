import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

open scoped BigOperators

namespace InsacermoActionabilityInformation

open Finset

/--
`actionEntropy p` is the Shannon entropy, in nats, of the conditional
ACT-action distribution `p`.
-/
noncomputable def actionEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/--
`totalDecisionEntropy q p` is the entropy of the full decision label:
REFUSE has mass `1-q`; ACT action `i` has mass `q * p i`.
-/
noncomputable def totalDecisionEntropy {ι : Type*} [Fintype ι]
    (q : ℝ) (p : ι → ℝ) : ℝ :=
  Real.negMulLog (1 - q) + ∑ i, Real.negMulLog (q * p i)

/--
Exact ACT/REFUSE decomposition.

If `p` is a normalized conditional distribution on actions (`∑ pᵢ = 1`), then

  H(total decision) = h₂(q) + q H(action | ACT).

Mathlib's `Real.binEntropy` uses natural logarithms, so this theorem is in nats.
Changing logarithm base multiplies both sides by the same constant.
-/
theorem totalDecisionEntropy_eq_binEntropy_add
    {ι : Type*} [Fintype ι] (q : ℝ) (p : ι → ℝ)
    (hp : ∑ i, p i = 1) :
    totalDecisionEntropy q p = Real.binEntropy q + q * actionEntropy p := by
  unfold totalDecisionEntropy actionEntropy
  simp_rw [Real.negMulLog_mul]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  rw [← Finset.mul_sum]
  rw [hp]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

/--
If actionability rate `q` and the conditional ACT-action entropy are unchanged,
then the total decision entropy is unchanged.
-/
theorem totalDecisionEntropy_congr
    {ι : Type*} [Fintype ι]
    (q : ℝ) (p p' : ι → ℝ)
    (hp : ∑ i, p i = 1) (hp' : ∑ i, p' i = 1)
    (hact : actionEntropy p = actionEntropy p') :
    totalDecisionEntropy q p = totalDecisionEntropy q p' := by
  rw [totalDecisionEntropy_eq_binEntropy_add q p hp]
  rw [totalDecisionEntropy_eq_binEntropy_add q p' hp']
  rw [hact]

/--
At full actionability (`q = 1`), the ACT/REFUSE routing term vanishes and the
full decision entropy is exactly the ACT-action entropy.
-/
theorem totalDecisionEntropy_one
    {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∑ i, p i = 1) :
    totalDecisionEntropy 1 p = actionEntropy p := by
  rw [totalDecisionEntropy_eq_binEntropy_add 1 p hp]
  simp

/--
At zero actionability (`q = 0`), the full decision entropy is zero: every state
receives the same REFUSE decision label.
-/
theorem totalDecisionEntropy_zero
    {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∑ i, p i = 1) :
    totalDecisionEntropy 0 p = 0 := by
  rw [totalDecisionEntropy_eq_binEntropy_add 0 p hp]
  simp

/--
Abstract fixed-actionability monotonicity corollary: once `q` is fixed, any
weak decrease in the conditional ACT-action entropy gives a weak decrease in
total decision entropy.
-/
theorem totalDecisionEntropy_mono_of_actionEntropy
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ℝ) (p : ι → ℝ) (p' : κ → ℝ)
    (hp : ∑ i, p i = 1) (hp' : ∑ j, p' j = 1)
    (hq : 0 ≤ q)
    (hact : actionEntropy p' ≤ actionEntropy p) :
    totalDecisionEntropy q p' ≤ totalDecisionEntropy q p := by
  rw [totalDecisionEntropy_eq_binEntropy_add q p' hp']
  rw [totalDecisionEntropy_eq_binEntropy_add q p hp]
  have hmul : q * actionEntropy p' ≤ q * actionEntropy p :=
    mul_le_mul_of_nonneg_left hact hq
  linarith

end InsacermoActionabilityInformation
