import InsacermoActionabilityInformation.FutureTransformationComposition

namespace InsacermoActionabilityInformation

namespace EventualFutureGeometry

open FutureRobustness
open TemporalJointContractComplex
open TemporalObstructionPersistence
open FutureDepthSpectrum
open FutureTransformationCalculus
open FutureTransformationComposition

/-- The eventual future complex at state x. A finite bundle is a face exactly
when there exists some finite horizon at which one common admissible trajectory
can satisfy the whole bundle. -/
noncomputable def EventualFutureComplex
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) : ContractComplex Q where
  feasible F := HasFiniteJointRecoveryDepth Avail Step x F
  downward := by
    intro R T hR hTR
    rcases hR with ⟨H, hRH⟩
    refine ⟨H, ?_⟩
    exact (TemporalContractComplex Avail Step H x).downward hRH hTR

/-- Eventual feasibility is exactly finite depth in the master spectrum. -/
theorem eventualFutureComplex_feasible_iff_spectrum_finite
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q} :
    (EventualFutureComplex Avail Step x).feasible F ↔
      ∃ d, Spectrum Avail Step x F = .finite d := by
  exact (spectrum_finite_iff_hasFiniteJointRecoveryDepth).symm

/-- Eventual infeasibility is exactly infinite future depth. -/
theorem eventualFutureComplex_infeasible_iff_spectrum_infinite
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q} :
    ¬ (EventualFutureComplex Avail Step x).feasible F ↔
      Spectrum Avail Step x F = .infinite := by
  constructor
  · intro hnot
    have hirr : JointIrreversible Avail Step x F :=
      (jointIrreversible_iff_not_hasFiniteJointRecoveryDepth).2 hnot
    exact (spectrum_infinite_iff_jointIrreversible).2 hirr
  · intro hinf
    have hirr : JointIrreversible Avail Step x F :=
      (spectrum_infinite_iff_jointIrreversible).1 hinf
    exact (jointIrreversible_iff_not_hasFiniteJointRecoveryDepth).1 hirr

/-- A minimal obstruction of the eventual complex is an irreducible bundle
whose whole future is impossible at every finite horizon although every proper
sub-bundle is eventually recoverable. -/
def EventualMinimalObstruction
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (F : Finset Q) : Prop :=
  MinimalNonface (EventualFutureComplex Avail Step x) F

/-- Every eventual minimal obstruction is genuinely jointly irreversible. -/
theorem eventualMinimalObstruction_implies_jointIrreversible
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q}
    (hmin : EventualMinimalObstruction Avail Step x F) :
    JointIrreversible Avail Step x F := by
  exact (jointIrreversible_iff_not_hasFiniteJointRecoveryDepth).2 hmin.1

/-- Every proper sub-bundle of an eventual minimal obstruction has finite
joint recovery depth. -/
theorem eventualMinimalObstruction_proper_subbundles_finite
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q}
    (hmin : EventualMinimalObstruction Avail Step x F) :
    ∀ G, G ⊂ F → HasFiniteJointRecoveryDepth Avail Step x G := by
  intro G hGF
  exact hmin.2 G hGF

/-- Exact characterization of irreducible hidden joint impossibility. -/
theorem eventualMinimalObstruction_iff_irreversible_and_all_proper_finite
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q} :
    EventualMinimalObstruction Avail Step x F ↔
      JointIrreversible Avail Step x F ∧
      ∀ G, G ⊂ F → HasFiniteJointRecoveryDepth Avail Step x G := by
  constructor
  · intro h
    exact ⟨eventualMinimalObstruction_implies_jointIrreversible h,
      eventualMinimalObstruction_proper_subbundles_finite h⟩
  · rintro ⟨hirr, hproper⟩
    constructor
    · exact (jointIrreversible_iff_not_hasFiniteJointRecoveryDepth).1 hirr
    · exact hproper

/-- A pair is a hidden joint impossibility when both singleton futures are
eventually recoverable but the pair is jointly irreversible. -/
def HiddenJointPair
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (q r : Q) : Prop :=
  HasFiniteJointRecoveryDepth Avail Step x {q} ∧
  HasFiniteJointRecoveryDepth Avail Step x {r} ∧
  JointIrreversible Avail Step x {q, r}

/-- Every two-element eventual minimal obstruction yields a hidden joint pair. -/
theorem hiddenJointPair_of_eventualMinimalObstruction_pair
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {q r : Q}
    (hqr : q ≠ r)
    (hmin : EventualMinimalObstruction Avail Step x {q, r}) :
    HiddenJointPair Avail Step x q r := by
  have hqsub : ({q} : Finset Q) ⊂ {q, r} := by
    constructor
    · intro z hz
      simp at hz ⊢
      exact Or.inl hz
    · intro hback
      have hrin : r ∈ ({q} : Finset Q) := hback (by simp)
      simp at hrin
      exact hqr hrin.symm
  have hrsub : ({r} : Finset Q) ⊂ {q, r} := by
    constructor
    · intro z hz
      simp at hz ⊢
      exact Or.inr hz
    · intro hback
      have hqin : q ∈ ({r} : Finset Q) := hback (by simp)
      simp at hqin
      exact hqr hqin
  exact ⟨hmin.2 {q} hqsub, hmin.2 {r} hrsub,
    eventualMinimalObstruction_implies_jointIrreversible hmin⟩

/-- Horizonwise availability inclusion completely characterizes the extended
depth order. -/
theorem depthLe_iff_all_threshold_implications
    {a b : DepthValue} :
    DepthLe a b ↔ ∀ H, DepthAtMost b H → DepthAtMost a H := by
  constructor
  · intro hab H hb
    exact depthAtMost_of_depthLe hab hb
  · intro hall
    cases a with
    | finite da =>
        cases b with
        | finite db =>
            change da ≤ db
            exact hall db (by simp [DepthAtMost])
        | infinite =>
            simp [DepthLe]
    | infinite =>
        cases b with
        | finite db =>
            exfalso
            have hfalse : DepthAtMost (.infinite) db :=
              hall db (by simp [DepthAtMost])
            simpa [DepthAtMost] using hfalse
        | infinite =>
            simp [DepthLe]

/-- Whole-spectrum non-worsening is equivalent to inclusion of every finite
horizon sublevel family. This is the exact bridge between transformation order
and filtration inclusion. -/
theorem spectrumNonWorsening_iff_all_horizon_inclusion
    {Q : Type*}
    {before after : Finset Q → DepthValue} :
    SpectrumNonWorsening before after ↔
      ∀ H F, DepthAtMost (before F) H → DepthAtMost (after F) H := by
  constructor
  · intro h H F hbefore
    exact nonWorsening_preserves_horizon_availability h hbefore
  · intro hall F
    exact (depthLe_iff_all_threshold_implications).2 (fun H => hall H F)

/-- Equivalent spectra are exactly equality of all finite-horizon sublevel
families. -/
theorem spectrumEquivalent_iff_all_horizon_thresholds_equal
    {Q : Type*}
    {before after : Finset Q → DepthValue} :
    SpectrumEquivalent before after ↔
      ∀ H F, DepthAtMost (before F) H ↔ DepthAtMost (after F) H := by
  constructor
  · intro h H F
    rw [h F]
  · intro hall F
    apply depthLe_antisymm
    · exact (depthLe_iff_all_threshold_implications).2
        (fun H hafter => (hall H F).2 hafter)
    · exact (depthLe_iff_all_threshold_implications).2
        (fun H hbefore => (hall H F).1 hbefore)

/-- A non-worsening spectrum transformation cannot destroy an eventually
recoverable future bundle. -/
theorem nonWorsening_preserves_eventual_finiteness
    {Q : Type*}
    {before after : Finset Q → DepthValue}
    (h : SpectrumNonWorsening before after)
    {F : Finset Q}
    (hfinite : ∃ d, before F = .finite d) :
    ∃ e, after F = .finite e := by
  rcases hfinite with ⟨d, hd⟩
  have hafterThreshold : DepthAtMost (after F) d := by
    apply nonWorsening_preserves_horizon_availability h
    simpa [hd, DepthAtMost]
  cases hAF : after F with
  | finite e =>
      exact ⟨e, rfl⟩
  | infinite =>
      rw [hAF] at hafterThreshold
      simp [DepthAtMost] at hafterThreshold

/-- Dually, a non-improving spectrum transformation cannot create a finite
future from infinity. -/
theorem nonImproving_preserves_infinity
    {Q : Type*}
    {before after : Finset Q → DepthValue}
    (h : SpectrumNonImproving before after)
    {F : Finset Q}
    (hinf : before F = .infinite) :
    after F = .infinite := by
  cases hafter : after F with
  | finite d =>
      have hbefore : DepthAtMost (before F) d :=
        nonImproving_reflects_horizon_availability h (by
          simp [hafter, DepthAtMost])
      rw [hinf] at hbefore
      simp [DepthAtMost] at hbefore
  | infinite =>
      rfl

end EventualFutureGeometry

end InsacermoActionabilityInformation
