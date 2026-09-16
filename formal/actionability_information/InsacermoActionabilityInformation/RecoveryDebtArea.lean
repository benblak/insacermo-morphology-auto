import InsacermoActionabilityInformation.RecoveryDepthIrreversibility
import InsacermoActionabilityInformation.FutureRobustness

namespace InsacermoActionabilityInformation

namespace RecoveryDebtArea

open TemporalRecoverabilityEnvelope
open RecoveryDepthIrreversibility
open scoped BigOperators

/-- Finite debt count induced by an arbitrary natural-valued recovery-depth
function. A future contributes at horizon `H` exactly while `H < d q`. -/
def DebtCountAt {Q : Type*} [DecidableEq Q]
    (Req : Finset Q) (d : Q → ℕ) (H : ℕ) : ℕ :=
  (Req.filter (fun q => H < d q)).card

/-- Finite layer-cake identity: if every required recovery depth is bounded by
`B`, then total recovery depth equals the discrete area under the temporal-debt
curve. -/
theorem totalDepth_eq_debtArea
    {Q : Type*} [DecidableEq Q]
    (Req : Finset Q) (d : Q → ℕ) (B : ℕ)
    (hB : ∀ q ∈ Req, d q ≤ B) :
    (∑ q ∈ Req, d q) =
      ∑ H ∈ Finset.range B, DebtCountAt Req d H := by
  classical
  calc
    (∑ q ∈ Req, d q) =
        ∑ q ∈ Req, ∑ H ∈ Finset.range B, if H < d q then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      have hfilter :
          (Finset.range B).filter (fun H => H < d q) = Finset.range (d q) := by
        ext H
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · intro h
          exact h.2
        · intro hd
          exact ⟨lt_of_lt_of_le hd (hB q hq), hd⟩
      rw [← Finset.sum_filter]
      rw [hfilter]
      simp
    _ = ∑ H ∈ Finset.range B,
          ∑ q ∈ Req, if H < d q then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ H ∈ Finset.range B, DebtCountAt Req d H := by
      apply Finset.sum_congr rfl
      intro H hH
      unfold DebtCountAt
      rw [← Finset.sum_filter]
      simp

/-- Weighted debt mass at horizon `H` for an arbitrary recovery-depth
function. -/
def WeightedDebtAt {Q : Type*} [DecidableEq Q]
    (Req : Finset Q) (w : Q → ℝ) (d : Q → ℕ) (H : ℕ) : ℝ :=
  ∑ q ∈ Req.filter (fun q => H < d q), w q

/-- Weighted layer-cake identity. The left side is the total weighted recovery
burden; the right side is the area under weighted temporal debt. -/
theorem totalWeightedDepth_eq_weightedDebtArea
    {Q : Type*} [DecidableEq Q]
    (Req : Finset Q) (w : Q → ℝ) (d : Q → ℕ) (B : ℕ)
    (hB : ∀ q ∈ Req, d q ≤ B) :
    (∑ q ∈ Req, d q • w q) =
      ∑ H ∈ Finset.range B, WeightedDebtAt Req w d H := by
  classical
  calc
    (∑ q ∈ Req, d q • w q) =
        ∑ q ∈ Req,
          ∑ H ∈ Finset.range B, if H < d q then w q else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      have hfilter :
          (Finset.range B).filter (fun H => H < d q) = Finset.range (d q) := by
        ext H
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · intro h
          exact h.2
        · intro hd
          exact ⟨lt_of_lt_of_le hd (hB q hq), hd⟩
      rw [← Finset.sum_filter]
      rw [hfilter]
      simp
    _ = ∑ H ∈ Finset.range B,
          ∑ q ∈ Req, if H < d q then w q else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ H ∈ Finset.range B, WeightedDebtAt Req w d H := by
      apply Finset.sum_congr rfl
      intro H hH
      unfold WeightedDebtAt
      rw [← Finset.sum_filter]

/-- Recovery depth on a declared finite requirement set, extended by zero off
that set so it can be used as an ordinary total function. -/
noncomputable def RecoveryDepthOnReq
    {Q X : Type*} [DecidableEq Q]
    (Req : Finset Q)
    (Avail : X → Set Q) (Step : X → X → Prop) (x : X)
    (hfinite : ∀ q, q ∈ Req → HasFiniteRecoveryDepth Avail Step x q)
    (q : Q) : ℕ := by
  classical
  exact if hq : q ∈ Req then
    RecoveryDepth Avail Step x q (hfinite q hq)
  else 0

/-- On a required future, missing the horizon-`H` recoverability envelope is
exactly the strict inequality `H < recovery depth`. -/
theorem not_recoverable_iff_horizon_lt_depth
    {Q X : Type*} [DecidableEq Q]
    {Req : Finset Q}
    {Avail : X → Set Q} {Step : X → X → Prop} {x : X}
    (hfinite : ∀ q, q ∈ Req → HasFiniteRecoveryDepth Avail Step x q)
    {q : Q} (hq : q ∈ Req) {H : ℕ} :
    q ∉ RecoverableEnvelope Avail Step H x ↔
      H < RecoveryDepthOnReq Req Avail Step x hfinite q := by
  classical
  let hf := hfinite q hq
  have hdepth :
      RecoveryDepthOnReq Req Avail Step x hfinite q =
        RecoveryDepth Avail Step x q hf := by
    simp [RecoveryDepthOnReq, hq]
  rw [hdepth]
  constructor
  · intro hnot
    by_contra hlt
    have hle : RecoveryDepth Avail Step x q hf ≤ H := Nat.le_of_not_gt hlt
    have hspec : q ∈ RecoverableEnvelope Avail Step
        (RecoveryDepth Avail Step x q hf) x :=
      recoveryDepth_spec hf
    exact hnot (recoverableEnvelope_mono_of_le hle hspec)
  · intro hlt hH
    have hmin : RecoveryDepth Avail Step x q hf ≤ H :=
      recoveryDepth_minimal hf hH
    exact (Nat.not_lt_of_ge hmin) hlt

/-- Core-V1 debt count at horizon `H`, restricted to a finite declared future
set. -/
noncomputable def CoreDebtCountAt
    {Q X : Type*} [DecidableEq Q]
    (Req : Finset Q)
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (H : ℕ) : ℕ := by
  classical
  exact (Req.filter (fun q => q ∉ RecoverableEnvelope Avail Step H x)).card

/-- The abstract debt count generated from minimum recovery depths is exactly
the finite Core-V1 temporal-debt count. -/
theorem debtCountAt_eq_coreDebtCountAt
    {Q X : Type*} [DecidableEq Q]
    {Req : Finset Q}
    {Avail : X → Set Q} {Step : X → X → Prop} {x : X}
    (hfinite : ∀ q, q ∈ Req → HasFiniteRecoveryDepth Avail Step x q)
    (H : ℕ) :
    DebtCountAt Req (RecoveryDepthOnReq Req Avail Step x hfinite) H =
      CoreDebtCountAt Req Avail Step x H := by
  classical
  unfold DebtCountAt CoreDebtCountAt
  congr 1
  ext q
  by_cases hq : q ∈ Req
  · simp [hq, not_recoverable_iff_horizon_lt_depth hfinite hq]
  · simp [hq]

/-- Main Core-V1 recovery-area theorem: once all required futures have finite
recovery depth bounded by `B`, the sum of their minimum recovery depths is
exactly the discrete area under the temporal debt curve up to `B`. -/
theorem totalRecoveryDepth_eq_temporalDebtArea
    {Q X : Type*} [DecidableEq Q]
    (Req : Finset Q)
    (Avail : X → Set Q) (Step : X → X → Prop) (x : X)
    (hfinite : ∀ q, q ∈ Req → HasFiniteRecoveryDepth Avail Step x q)
    (B : ℕ)
    (hB : ∀ q ∈ Req,
      RecoveryDepthOnReq Req Avail Step x hfinite q ≤ B) :
    (∑ q ∈ Req, RecoveryDepthOnReq Req Avail Step x hfinite q) =
      ∑ H ∈ Finset.range B, CoreDebtCountAt Req Avail Step x H := by
  classical
  rw [totalDepth_eq_debtArea Req
    (RecoveryDepthOnReq Req Avail Step x hfinite) B hB]
  apply Finset.sum_congr rfl
  intro H hH
  exact debtCountAt_eq_coreDebtCountAt hfinite H

/-- Weighted Core-V1 debt at horizon `H` over a finite future contract. -/
noncomputable def CoreWeightedDebtAt
    {Q X : Type*} [DecidableEq Q]
    (Req : Finset Q) (w : Q → ℝ)
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (H : ℕ) : ℝ := by
  classical
  exact ∑ q ∈ Req.filter (fun q => q ∉ RecoverableEnvelope Avail Step H x), w q

/-- Weighted version of the Core-V1 recovery-area theorem. -/
theorem totalWeightedRecoveryDepth_eq_temporalDebtArea
    {Q X : Type*} [DecidableEq Q]
    (Req : Finset Q) (w : Q → ℝ)
    (Avail : X → Set Q) (Step : X → X → Prop) (x : X)
    (hfinite : ∀ q, q ∈ Req → HasFiniteRecoveryDepth Avail Step x q)
    (B : ℕ)
    (hB : ∀ q ∈ Req,
      RecoveryDepthOnReq Req Avail Step x hfinite q ≤ B) :
    (∑ q ∈ Req, RecoveryDepthOnReq Req Avail Step x hfinite q • w q) =
      ∑ H ∈ Finset.range B, CoreWeightedDebtAt Req w Avail Step x H := by
  classical
  rw [totalWeightedDepth_eq_weightedDebtArea Req w
    (RecoveryDepthOnReq Req Avail Step x hfinite) B hB]
  apply Finset.sum_congr rfl
  intro H hH
  unfold WeightedDebtAt CoreWeightedDebtAt
  have hfilter :
      Req.filter (fun q => H < RecoveryDepthOnReq Req Avail Step x hfinite q) =
        Req.filter (fun q => q ∉ RecoverableEnvelope Avail Step H x) := by
    ext q
    by_cases hq : q ∈ Req
    · simp [hq, not_recoverable_iff_horizon_lt_depth hfinite hq]
    · simp [hq]
  rw [hfilter]

end RecoveryDebtArea

end InsacermoActionabilityInformation
