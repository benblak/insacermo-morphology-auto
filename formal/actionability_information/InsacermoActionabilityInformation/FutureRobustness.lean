import InsacermoActionabilityInformation.TemporalRecoverabilityEnvelope

namespace InsacermoActionabilityInformation

namespace FutureRobustness

/-- A finite-contract complex. `feasible R` means that the finite bundle of
future requirements `R` can be satisfied jointly.  Downward closure encodes
the contract principle that removing requirements cannot destroy feasibility. -/
structure ContractComplex (α : Type*) [DecidableEq α] where
  feasible : Finset α → Prop
  downward : ∀ {R T : Finset α}, feasible R → T ⊆ R → feasible T

/-- A minimal non-face of the future-contract complex: the bundle itself is
not jointly feasible, while every proper sub-bundle is. -/
def MinimalNonface {α : Type*} [DecidableEq α]
    (K : ContractComplex α) (F : Finset α) : Prop :=
  ¬ K.feasible F ∧ ∀ G, G ⊂ F → K.feasible G

/-- Infeasibility is upward closed: once a bundle is impossible, adding more
requirements cannot restore it. -/
theorem failure_upward
    {α : Type*} [DecidableEq α]
    {K : ContractComplex α} {R T : Finset α}
    (hbad : ¬ K.feasible R) (hsub : R ⊆ T) :
    ¬ K.feasible T := by
  intro hT
  exact hbad (K.downward hT hsub)

/-- Radius-`r` contractual robustness around a currently considered bundle
`R`: every extension by at most `r` additional requirements remains feasible. -/
def RobustAtRadius {α : Type*} [DecidableEq α]
    (K : ContractComplex α) (R : Finset α) (r : ℕ) : Prop :=
  ∀ A : Finset α, A.card ≤ r → K.feasible (R ∪ A)

/-- Feasibility is exactly radius-zero robustness. -/
theorem robustAtRadius_zero_of_feasible
    {α : Type*} [DecidableEq α]
    {K : ContractComplex α} {R : Finset α}
    (hR : K.feasible R) :
    RobustAtRadius K R 0 := by
  intro A hcard
  have hzero : A.card = 0 := Nat.eq_zero_of_le_zero hcard
  have hA : A = ∅ := Finset.card_eq_zero.mp hzero
  subst A
  simpa using hR

/-- Any explicit extension of size at most `r` that breaks feasibility is a
certificate that radius-`r` robustness fails. -/
theorem not_robust_of_breaking_extension
    {α : Type*} [DecidableEq α]
    {K : ContractComplex α} {R A : Finset α} {r : ℕ}
    (hcard : A.card ≤ r)
    (hbad : ¬ K.feasible (R ∪ A)) :
    ¬ RobustAtRadius K R r := by
  intro hrob
  exact hbad (hrob A hcard)

/-- A minimal non-face containing `R` gives an explicit finite robustness
failure: adding exactly the missing elements of that obstruction reaches the
non-face. -/
theorem minimalNonface_gives_breaking_extension
    {α : Type*} [DecidableEq α]
    {K : ContractComplex α} {R F : Finset α}
    (hF : MinimalNonface K F)
    (hRF : R ⊆ F) :
    ¬ RobustAtRadius K R (F \ R).card := by
  apply not_robust_of_breaking_extension (K := K) (R := R) (A := F \ R)
      (r := (F \ R).card) le_rfl
  have hunion : R ∪ (F \ R) = F := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hxR | hxD
      · exact hRF hxR
      · exact (Finset.mem_sdiff.mp hxD).1
    · intro hxF
      by_cases hxR : x ∈ R
      · exact Finset.mem_union.mpr (Or.inl hxR)
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_sdiff.mpr ⟨hxF, hxR⟩))
  rw [hunion]
  exact hF.1

/-- Around the empty contract, robustness through radius `r` is exactly the
absence of any failed contract of cardinality at most `r`.  This is the clean
bridge from obstruction depth to a worst-case future-robustness radius. -/
theorem robustAtRadius_empty_iff_all_small_feasible
    {α : Type*} [DecidableEq α]
    {K : ContractComplex α} {r : ℕ} :
    RobustAtRadius K ∅ r ↔
      ∀ F : Finset α, F.card ≤ r → K.feasible F := by
  constructor
  · intro hrob F hcard
    simpa using hrob F hcard
  · intro hall A hcard
    simpa using hall A hcard

/-- The exact set of finite contracts destroyed by a transformation from
`before` to `after`.  No probability model is required for this object. -/
def LostContracts {α : Type*} [DecidableEq α]
    (before after : ContractComplex α) : Set (Finset α) :=
  {R | before.feasible R ∧ ¬ after.feasible R}

@[simp] theorem mem_lostContracts_iff
    {α : Type*} [DecidableEq α]
    {before after : ContractComplex α} {R : Finset α} :
    R ∈ LostContracts before after ↔
      before.feasible R ∧ ¬ after.feasible R := by
  rfl

/-- If every contract feasible before remains feasible after, the destruction
set is empty. -/
theorem no_lostContracts_of_preservation
    {α : Type*} [DecidableEq α]
    {before after : ContractComplex α}
    (hpres : ∀ R, before.feasible R → after.feasible R) :
    LostContracts before after = ∅ := by
  ext R
  constructor
  · intro hR
    exact False.elim (hR.2 (hpres R hR.1))
  · intro hR
    simp at hR

/-- The first-cardinality notion of damage can be stated without choosing a
probability law: some lost contract is already visible by size `k`. -/
def DamageAtMost {α : Type*} [DecidableEq α]
    (before after : ContractComplex α) (k : ℕ) : Prop :=
  ∃ R, R ∈ LostContracts before after ∧ R.card ≤ k

/-- Point-mass valuation of a set.  This is the deterministic Dirac probe used
to recover set inclusion from universal probabilistic comparisons. -/
def PointMass {Q : Type*} (q : Q) (K : Set Q) : ℕ :=
  if q ∈ K then 1 else 0

/-- Point-mass order at one future is exactly implication of membership. -/
theorem pointMass_le_iff
    {Q : Type*} {q : Q} {K L : Set Q} :
    PointMass q K ≤ PointMass q L ↔ (q ∈ K → q ∈ L) := by
  by_cases hK : q ∈ K <;> by_cases hL : q ∈ L <;>
    simp [PointMass, hK, hL]

/-- The deterministic inclusion order is exactly the order respected by every
Dirac future.  Hence probability does not replace the old INSACERMO order: it
extends it. -/
theorem all_pointMass_order_iff_subset
    {Q : Type*} {K L : Set Q} :
    (∀ q, PointMass q K ≤ PointMass q L) ↔ K ⊆ L := by
  constructor
  · intro h q hq
    exact (pointMass_le_iff.mp (h q)) hq
  · intro h q
    exact pointMass_le_iff.mpr (fun hq => h hq)

/-- Finite weighted mass of a future family.  Nonnegative weights may be read
as an unnormalised finite future law; normalisation is deliberately kept out
of the structural kernel. -/
noncomputable def WeightedMass {Q : Type*} [Fintype Q]
    (w : Q → ℝ) (K : Set Q) : ℝ :=
  ∑ q, if q ∈ K then w q else 0

/-- Inclusion of future families monotonically increases every nonnegative
finite weighted survival mass. -/
theorem weightedMass_mono
    {Q : Type*} [Fintype Q]
    {w : Q → ℝ} {K L : Set Q}
    (hw : ∀ q, 0 ≤ w q)
    (hsub : K ⊆ L) :
    WeightedMass w K ≤ WeightedMass w L := by
  classical
  unfold WeightedMass
  apply Finset.sum_le_sum
  intro q hq
  by_cases hK : q ∈ K
  · have hL : q ∈ L := hsub hK
    simp [hK, hL]
  · by_cases hL : q ∈ L
    · simp [hK, hL, hw q]
    · simp [hK, hL]

/-- Weighted future readiness at horizon `H`, obtained by valuing the existing
Core-V1 recoverability envelope rather than changing its definition. -/
noncomputable def WeightedReadiness
    {Q X : Type*} [Fintype Q]
    (w : Q → ℝ) (Avail : X → Set Q) (Step : X → X → Prop)
    (H : ℕ) (x : X) : ℝ :=
  WeightedMass w
    (TemporalRecoverabilityEnvelope.RecoverableEnvelope Avail Step H x)

/-- More recovery time cannot reduce weighted readiness for any nonnegative
finite future law. -/
theorem weightedReadiness_mono_horizon
    {Q X : Type*} [Fintype Q]
    {w : Q → ℝ} {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X}
    (hw : ∀ q, 0 ≤ w q) :
    WeightedReadiness w Avail Step H x ≤
      WeightedReadiness w Avail Step (H + 1) x := by
  unfold WeightedReadiness
  exact weightedMass_mono hw
    (TemporalRecoverabilityEnvelope.recoverableEnvelope_mono_horizon H x)

/-- Weighted temporal debt: the future-law mass of required contracts that are
still outside the Core-V1 recoverability envelope at horizon `H`. -/
noncomputable def WeightedTemporalDebt
    {Q X : Type*} [Fintype Q]
    (w : Q → ℝ) (Req : Set Q)
    (Avail : X → Set Q) (Step : X → X → Prop)
    (H : ℕ) (x : X) : ℝ :=
  WeightedMass w
    (TemporalRecoverabilityEnvelope.TemporalDebt Req Avail Step H x)

/-- The ModeChoice-style debt-collapse law in weighted form: temporal debt is
antitone in the recovery horizon. -/
theorem weightedTemporalDebt_antitone_horizon
    {Q X : Type*} [Fintype Q]
    {w : Q → ℝ} {Req : Set Q}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X}
    (hw : ∀ q, 0 ≤ w q) :
    WeightedTemporalDebt w Req Avail Step (H + 1) x ≤
      WeightedTemporalDebt w Req Avail Step H x := by
  unfold WeightedTemporalDebt
  exact weightedMass_mono hw
    TemporalRecoverabilityEnvelope.temporalDebt_antitone_horizon

end FutureRobustness

end InsacermoActionabilityInformation
