import InsacermoActionabilityInformation.FutureDepthSpectrum

namespace InsacermoActionabilityInformation

namespace FutureDepthBellman

open FutureRobustness
open TemporalJointContractComplex
open TemporalObstructionPersistence
open FutureDepthSpectrum

/-- The residual finite future bundle after consuming every contract already
available at the current state. -/
noncomputable def Residual
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (x : X) (F : Finset Q) : Finset Q := by
  classical
  exact F.filter (fun q => q ∉ Avail x)

@[simp] theorem coe_residual
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {x : X} {F : Finset Q} :
    (↑(Residual Avail x F) : Set Q) = (↑F : Set Q) \ Avail x := by
  classical
  ext q
  simp [Residual]

/-- Horizon zero is exactly immediate joint availability. -/
theorem spectrum_zero_iff_immediate
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q} :
    DepthAtMost (Spectrum Avail Step x F) 0 ↔
      (↑F : Set Q) ⊆ Avail x := by
  rw [depthAtMost_spectrum_iff_feasible]
  rfl

/-- Bellman sublevel equation for the future-depth spectrum.

A bundle has depth at most `H+1` at `x` exactly when either it is already
available at `x`, or one admissible successor can carry the residual bundle
within horizon `H`. This is the dynamic-programming law induced by the
verified common-trajectory joint-recovery semantics. -/
theorem spectrum_succ_iff_immediate_or_step
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} {F : Finset Q} :
    DepthAtMost (Spectrum Avail Step x F) (H + 1) ↔
      (↑F : Set Q) ⊆ Avail x ∨
        ∃ y, Step x y ∧
          DepthAtMost (Spectrum Avail Step y (Residual Avail x F)) H := by
  rw [depthAtMost_spectrum_iff_feasible]
  change JointRecoverable Avail Step (H + 1) x (↑F : Set Q) ↔ _
  constructor
  · intro h
    rcases h with hnow | ⟨y, hxy, hrest⟩
    · exact Or.inl hnow
    · refine Or.inr ⟨y, hxy, ?_⟩
      apply (depthAtMost_spectrum_iff_feasible).2
      change JointRecoverable Avail Step H y
        (↑(Residual Avail x F) : Set Q)
      simpa using hrest
  · intro h
    rcases h with hnow | ⟨y, hxy, hdepth⟩
    · exact Or.inl hnow
    · refine Or.inr ⟨y, hxy, ?_⟩
      have hrest :
          (TemporalContractComplex Avail Step H y).feasible
            (Residual Avail x F) :=
        (depthAtMost_spectrum_iff_feasible).1 hdepth
      change JointRecoverable Avail Step H y
        (↑(Residual Avail x F) : Set Q) at hrest
      simpa using hrest

/-- Away from the immediate case, the spectrum obeys a pure one-step Bellman
recursion. -/
theorem spectrum_succ_iff_step_of_not_immediate
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} {F : Finset Q}
    (hnot : ¬ (↑F : Set Q) ⊆ Avail x) :
    DepthAtMost (Spectrum Avail Step x F) (H + 1) ↔
      ∃ y, Step x y ∧
        DepthAtMost (Spectrum Avail Step y (Residual Avail x F)) H := by
  rw [spectrum_succ_iff_immediate_or_step]
  simp [hnot]

/-- A certified successor recovery gives an immediate upper bound on the
current bundle depth. -/
theorem spectrum_succ_of_step
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x y : X} {F : Finset Q}
    (hxy : Step x y)
    (hres : DepthAtMost (Spectrum Avail Step y (Residual Avail x F)) H) :
    DepthAtMost (Spectrum Avail Step x F) (H + 1) := by
  exact (spectrum_succ_iff_immediate_or_step).2
    (Or.inr ⟨y, hxy, hres⟩)

/-- Finite joint recoverability has the same first-step Bellman decomposition:
either the bundle is immediate, or some successor has finitely recoverable
residual obligations. -/
theorem hasFiniteJointRecoveryDepth_iff_immediate_or_step
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q} :
    HasFiniteJointRecoveryDepth Avail Step x F ↔
      (↑F : Set Q) ⊆ Avail x ∨
        ∃ y, Step x y ∧
          HasFiniteJointRecoveryDepth Avail Step y (Residual Avail x F) := by
  constructor
  · rintro ⟨H, hH⟩
    cases H with
    | zero =>
        exact Or.inl ((spectrum_zero_iff_immediate).1
          ((depthAtMost_spectrum_iff_feasible).2 hH))
    | succ H =>
        have hdepth :
            DepthAtMost (Spectrum Avail Step x F) (H + 1) :=
          (depthAtMost_spectrum_iff_feasible).2 hH
        rcases (spectrum_succ_iff_immediate_or_step).1 hdepth with
          hnow | ⟨y, hxy, hres⟩
        · exact Or.inl hnow
        · refine Or.inr ⟨y, hxy, H, ?_⟩
          exact (depthAtMost_spectrum_iff_feasible).1 hres
  · intro h
    rcases h with hnow | ⟨y, hxy, hfinite⟩
    · refine ⟨0, ?_⟩
      exact (depthAtMost_spectrum_iff_feasible).1
        ((spectrum_zero_iff_immediate).2 hnow)
    · rcases hfinite with ⟨H, hH⟩
      refine ⟨H + 1, ?_⟩
      apply (depthAtMost_spectrum_iff_feasible).1
      exact spectrum_succ_of_step hxy
        ((depthAtMost_spectrum_iff_feasible).2 hH)

/-- Joint irreversibility is the coinductive failure side of the Bellman law:
the bundle is not immediate and every admissible successor leaves an
irreversible residual bundle. -/
theorem jointIrreversible_iff_not_immediate_and_all_successors
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q} :
    JointIrreversible Avail Step x F ↔
      ¬ (↑F : Set Q) ⊆ Avail x ∧
        ∀ y, Step x y →
          JointIrreversible Avail Step y (Residual Avail x F) := by
  constructor
  · intro hirr
    have hnotfinite : ¬ HasFiniteJointRecoveryDepth Avail Step x F :=
      (jointIrreversible_iff_not_hasFiniteJointRecoveryDepth).1 hirr
    constructor
    · intro hnow
      apply hnotfinite
      exact (hasFiniteJointRecoveryDepth_iff_immediate_or_step).2
        (Or.inl hnow)
    · intro y hxy
      apply (jointIrreversible_iff_not_hasFiniteJointRecoveryDepth).2
      intro hfinite
      apply hnotfinite
      exact (hasFiniteJointRecoveryDepth_iff_immediate_or_step).2
        (Or.inr ⟨y, hxy, hfinite⟩)
  · rintro ⟨hnot, hall⟩
    apply (jointIrreversible_iff_not_hasFiniteJointRecoveryDepth).2
    intro hfinite
    rcases (hasFiniteJointRecoveryDepth_iff_immediate_or_step).1 hfinite with
      hnow | ⟨y, hxy, hres⟩
    · exact hnot hnow
    · have hirrRes := hall y hxy
      have hnotRes :
          ¬ HasFiniteJointRecoveryDepth Avail Step y (Residual Avail x F) :=
        (jointIrreversible_iff_not_hasFiniteJointRecoveryDepth).1 hirrRes
      exact hnotRes hres

/-- Infinity itself therefore satisfies a Bellman equation: a future bundle is
at infinite depth exactly when it is not immediate and every admissible
successor leaves an infinite-depth residual bundle. -/
theorem spectrum_infinite_iff_not_immediate_and_all_successors
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {F : Finset Q} :
    Spectrum Avail Step x F = .infinite ↔
      ¬ (↑F : Set Q) ⊆ Avail x ∧
        ∀ y, Step x y →
          Spectrum Avail Step y (Residual Avail x F) = .infinite := by
  constructor
  · intro hinf
    have hirr : JointIrreversible Avail Step x F :=
      (spectrum_infinite_iff_jointIrreversible).1 hinf
    rcases (jointIrreversible_iff_not_immediate_and_all_successors).1 hirr with
      ⟨hnot, hall⟩
    refine ⟨hnot, ?_⟩
    intro y hxy
    exact (spectrum_infinite_iff_jointIrreversible).2 (hall y hxy)
  · rintro ⟨hnot, hall⟩
    apply (spectrum_infinite_iff_jointIrreversible).2
    apply (jointIrreversible_iff_not_immediate_and_all_successors).2
    refine ⟨hnot, ?_⟩
    intro y hxy
    exact (spectrum_infinite_iff_jointIrreversible).1 (hall y hxy)

end FutureDepthBellman

end InsacermoActionabilityInformation
