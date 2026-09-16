import InsacermoActionabilityInformation.TemporalObstructionPersistence

namespace InsacermoActionabilityInformation

namespace TemporalJointFutureRisk

open FutureRobustness
open TemporalJointContractComplex

/-- The family of all finite future-contract bundles jointly recoverable from
state `x` by horizon `H`.  This is the set-level view of the temporal contract
complex and is convenient for future-law comparisons. -/
def TemporalJointFamily
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (H : ℕ) (x : X) : Set (Finset Q) :=
  {R | (TemporalContractComplex Avail Step H x).feasible R}

/-- The temporal joint future family grows with the planning horizon. -/
theorem temporalJointFamily_mono_horizon
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} :
    TemporalJointFamily Avail Step H x ⊆
      TemporalJointFamily Avail Step (H + 1) x := by
  intro R hR
  exact temporalContractComplex_mono_horizon hR

/-- Structural preservation of all finite joint future bundles at a fixed
horizon.  This is the exact contract-level meaning of a transformation causing
no loss of future joint actionability. -/
def JointPreservesAt
    {Q X Y : Type*} [DecidableEq Q]
    (AvailBefore : X → Set Q) (StepBefore : X → X → Prop) (x : X)
    (AvailAfter : Y → Set Q) (StepAfter : Y → Y → Prop) (y : Y)
    (H : ℕ) : Prop :=
  ∀ R : Finset Q,
    (TemporalContractComplex AvailBefore StepBefore H x).feasible R →
      (TemporalContractComplex AvailAfter StepAfter H y).feasible R

/-- Exact finite bundles lost by a transformation at horizon `H`. -/
def TemporalLostBundles
    {Q X Y : Type*} [DecidableEq Q]
    (AvailBefore : X → Set Q) (StepBefore : X → X → Prop) (x : X)
    (AvailAfter : Y → Set Q) (StepAfter : Y → Y → Prop) (y : Y)
    (H : ℕ) : Set (Finset Q) :=
  LostContracts
    (TemporalContractComplex AvailBefore StepBefore H x)
    (TemporalContractComplex AvailAfter StepAfter H y)

@[simp] theorem mem_temporalLostBundles_iff
    {Q X Y : Type*} [DecidableEq Q]
    {AvailBefore : X → Set Q} {StepBefore : X → X → Prop} {x : X}
    {AvailAfter : Y → Set Q} {StepAfter : Y → Y → Prop} {y : Y}
    {H : ℕ} {R : Finset Q} :
    R ∈ TemporalLostBundles AvailBefore StepBefore x
      AvailAfter StepAfter y H ↔
      (TemporalContractComplex AvailBefore StepBefore H x).feasible R ∧
      ¬ (TemporalContractComplex AvailAfter StepAfter H y).feasible R := by
  rfl

/-- A transformation preserves every joint future bundle exactly when its
horizon-specific lost-bundle set is empty. -/
theorem jointPreservesAt_iff_no_temporalLostBundles
    {Q X Y : Type*} [DecidableEq Q]
    {AvailBefore : X → Set Q} {StepBefore : X → X → Prop} {x : X}
    {AvailAfter : Y → Set Q} {StepAfter : Y → Y → Prop} {y : Y}
    {H : ℕ} :
    JointPreservesAt AvailBefore StepBefore x
      AvailAfter StepAfter y H ↔
      TemporalLostBundles AvailBefore StepBefore x
        AvailAfter StepAfter y H = ∅ := by
  constructor
  · intro hpres
    apply no_lostContracts_of_preservation
    exact hpres
  · intro hzero R hbefore
    by_contra hafter
    have hlost : R ∈ TemporalLostBundles AvailBefore StepBefore x
        AvailAfter StepAfter y H := ⟨hbefore, hafter⟩
    rw [hzero] at hlost
    exact hlost.elim

/-- Universal deterministic future-law comparison recovers exactly structural
preservation.  Dirac probes over complete future bundles detect every possible
lost joint contract. -/
theorem all_bundle_pointMass_order_iff_jointPreservesAt
    {Q X Y : Type*} [DecidableEq Q]
    {AvailBefore : X → Set Q} {StepBefore : X → X → Prop} {x : X}
    {AvailAfter : Y → Set Q} {StepAfter : Y → Y → Prop} {y : Y}
    {H : ℕ} :
    (∀ R : Finset Q,
      PointMass R (TemporalJointFamily AvailBefore StepBefore H x) ≤
        PointMass R (TemporalJointFamily AvailAfter StepAfter H y)) ↔
      JointPreservesAt AvailBefore StepBefore x
        AvailAfter StepAfter y H := by
  constructor
  · intro h R hbefore
    have hmemBefore : R ∈ TemporalJointFamily AvailBefore StepBefore H x := hbefore
    have hmemAfter : R ∈ TemporalJointFamily AvailAfter StepAfter H y :=
      (pointMass_le_iff.mp (h R)) hmemBefore
    exact hmemAfter
  · intro h R
    apply pointMass_le_iff.mpr
    intro hmemBefore
    exact h R hmemBefore

/-- Weighted readiness of a finite catalogue `Ω` of possible future bundles.
Weights may be unnormalised; probability normalisation is deliberately kept
outside the structural kernel. -/
noncomputable def WeightedCatalogueReadiness
    {Q : Type*} [DecidableEq Q]
    (Ω : Finset (Finset Q)) (w : Finset Q → ℝ)
    (K : ContractComplex Q) : ℝ := by
  classical
  exact ∑ R ∈ Ω, if K.feasible R then w R else 0

/-- Weighted mass of catalogue futures that were feasible before a
transformation and are infeasible after it. -/
noncomputable def WeightedCatalogueDamage
    {Q : Type*} [DecidableEq Q]
    (Ω : Finset (Finset Q)) (w : Finset Q → ℝ)
    (before after : ContractComplex Q) : ℝ := by
  classical
  exact ∑ R ∈ Ω,
    if before.feasible R ∧ ¬ after.feasible R then w R else 0

/-- On a catalogue, a pure-loss transformation means that every bundle feasible
after was already feasible before.  The transformation may destroy futures but
does not create new ones on the audited catalogue. -/
def CatalogueNoGain
    {Q : Type*} [DecidableEq Q]
    (Ω : Finset (Finset Q))
    (before after : ContractComplex Q) : Prop :=
  ∀ R, R ∈ Ω → after.feasible R → before.feasible R

/-- Exact finite weighted decomposition under pure loss:
readiness before = readiness after + mass of the futures destroyed.
No nonnegativity assumption is needed for the algebraic identity. -/
theorem weightedCatalogue_exact_damage_of_noGain
    {Q : Type*} [DecidableEq Q]
    {Ω : Finset (Finset Q)} {w : Finset Q → ℝ}
    {before after : ContractComplex Q}
    (hNoGain : CatalogueNoGain Ω before after) :
    WeightedCatalogueReadiness Ω w before =
      WeightedCatalogueReadiness Ω w after +
        WeightedCatalogueDamage Ω w before after := by
  classical
  unfold WeightedCatalogueReadiness WeightedCatalogueDamage
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro R hRΩ
  by_cases hbefore : before.feasible R
  · by_cases hafter : after.feasible R
    · simp [hbefore, hafter]
    · simp [hbefore, hafter]
  · have hafter : ¬ after.feasible R := by
      intro ha
      exact hbefore (hNoGain R hRΩ ha)
    simp [hbefore, hafter]

/-- A structurally preserved catalogue has exactly zero weighted destruction
mass, for arbitrary real weights. -/
theorem weightedCatalogueDamage_zero_of_preservation
    {Q : Type*} [DecidableEq Q]
    {Ω : Finset (Finset Q)} {w : Finset Q → ℝ}
    {before after : ContractComplex Q}
    (hpres : ∀ R, R ∈ Ω → before.feasible R → after.feasible R) :
    WeightedCatalogueDamage Ω w before after = 0 := by
  classical
  unfold WeightedCatalogueDamage
  apply Finset.sum_eq_zero
  intro R hRΩ
  by_cases hbefore : before.feasible R
  · have hafter : after.feasible R := hpres R hRΩ hbefore
    simp [hbefore, hafter]
  · simp [hbefore]

/-- Temporal weighted readiness for a catalogue of complete future bundles. -/
noncomputable def TemporalWeightedJointReadiness
    {Q X : Type*} [DecidableEq Q]
    (Ω : Finset (Finset Q)) (w : Finset Q → ℝ)
    (Avail : X → Set Q) (Step : X → X → Prop)
    (H : ℕ) (x : X) : ℝ :=
  WeightedCatalogueReadiness Ω w (TemporalContractComplex Avail Step H x)

/-- Temporal weighted damage caused by a transformation at a fixed horizon. -/
noncomputable def TemporalWeightedJointDamage
    {Q X Y : Type*} [DecidableEq Q]
    (Ω : Finset (Finset Q)) (w : Finset Q → ℝ)
    (AvailBefore : X → Set Q) (StepBefore : X → X → Prop) (x : X)
    (AvailAfter : Y → Set Q) (StepAfter : Y → Y → Prop) (y : Y)
    (H : ℕ) : ℝ :=
  WeightedCatalogueDamage Ω w
    (TemporalContractComplex AvailBefore StepBefore H x)
    (TemporalContractComplex AvailAfter StepAfter H y)

/-- With nonnegative future weights, more planning time cannot reduce joint
weighted readiness. -/
theorem temporalWeightedJointReadiness_mono_horizon
    {Q X : Type*} [DecidableEq Q]
    {Ω : Finset (Finset Q)} {w : Finset Q → ℝ}
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X}
    (hw : ∀ R, R ∈ Ω → 0 ≤ w R) :
    TemporalWeightedJointReadiness Ω w Avail Step H x ≤
      TemporalWeightedJointReadiness Ω w Avail Step (H + 1) x := by
  classical
  unfold TemporalWeightedJointReadiness WeightedCatalogueReadiness
  apply Finset.sum_le_sum
  intro R hRΩ
  by_cases hH : (TemporalContractComplex Avail Step H x).feasible R
  · have hNext :
        (TemporalContractComplex Avail Step (H + 1) x).feasible R :=
      temporalContractComplex_mono_horizon hH
    simp [hH, hNext]
  · by_cases hNext :
      (TemporalContractComplex Avail Step (H + 1) x).feasible R
    · simpa [hH, hNext] using hw R hRΩ
    · simp [hH, hNext]

/-- Exact temporal damage law.  If the after-system is a pure loss of joint
future capability on catalogue `Ω`, then the drop in readiness is exactly the
weighted mass of the bundles destroyed. -/
theorem temporalWeightedJoint_exact_damage_of_noGain
    {Q X Y : Type*} [DecidableEq Q]
    {Ω : Finset (Finset Q)} {w : Finset Q → ℝ}
    {AvailBefore : X → Set Q} {StepBefore : X → X → Prop} {x : X}
    {AvailAfter : Y → Set Q} {StepAfter : Y → Y → Prop} {y : Y}
    {H : ℕ}
    (hNoGain : CatalogueNoGain Ω
      (TemporalContractComplex AvailBefore StepBefore H x)
      (TemporalContractComplex AvailAfter StepAfter H y)) :
    TemporalWeightedJointReadiness Ω w
        AvailBefore StepBefore H x =
      TemporalWeightedJointReadiness Ω w
        AvailAfter StepAfter H y +
      TemporalWeightedJointDamage Ω w
        AvailBefore StepBefore x AvailAfter StepAfter y H := by
  exact weightedCatalogue_exact_damage_of_noGain hNoGain

/-- Difference form of the exact temporal damage law. -/
theorem temporalWeightedJoint_readiness_drop_eq_damage
    {Q X Y : Type*} [DecidableEq Q]
    {Ω : Finset (Finset Q)} {w : Finset Q → ℝ}
    {AvailBefore : X → Set Q} {StepBefore : X → X → Prop} {x : X}
    {AvailAfter : Y → Set Q} {StepAfter : Y → Y → Prop} {y : Y}
    {H : ℕ}
    (hNoGain : CatalogueNoGain Ω
      (TemporalContractComplex AvailBefore StepBefore H x)
      (TemporalContractComplex AvailAfter StepAfter H y)) :
    TemporalWeightedJointReadiness Ω w AvailBefore StepBefore H x -
      TemporalWeightedJointReadiness Ω w AvailAfter StepAfter H y =
      TemporalWeightedJointDamage Ω w
        AvailBefore StepBefore x AvailAfter StepAfter y H := by
  have h := temporalWeightedJoint_exact_damage_of_noGain
    (Ω := Ω) (w := w)
    (AvailBefore := AvailBefore) (StepBefore := StepBefore) (x := x)
    (AvailAfter := AvailAfter) (StepAfter := StepAfter) (y := y)
    (H := H) hNoGain
  linarith

end TemporalJointFutureRisk

end InsacermoActionabilityInformation
