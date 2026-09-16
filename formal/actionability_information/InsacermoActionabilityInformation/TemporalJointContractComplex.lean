import InsacermoActionabilityInformation.FutureRobustness
import InsacermoActionabilityInformation.RecoveryDebtArea

namespace InsacermoActionabilityInformation

namespace TemporalJointContractComplex

open TemporalRecoverabilityEnvelope
open FutureRobustness

/-- Joint finite-horizon recoverability for a bundle of future contracts.

The crucial point is that the whole residual bundle must follow one common
successor at each step. Contracts already satisfied at the current state are
removed from the residual obligation; the remaining contracts must then be
satisfied along the same admissible trajectory before the horizon expires.

This is strictly stronger than asking every contract to be individually
recoverable, because individual recoverability may use incompatible branches. -/
def JointRecoverable {Q X : Type*}
    (Avail : X → Set Q) (Step : X → X → Prop) : ℕ → X → Set Q → Prop
  | 0, x, R => R ⊆ Avail x
  | n + 1, x, R =>
      R ⊆ Avail x ∨
        ∃ y, Step x y ∧ JointRecoverable Avail Step n y (R \ Avail x)

@[simp] theorem jointRecoverable_zero
    {Q X : Type*} (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (R : Set Q) :
    JointRecoverable Avail Step 0 x R ↔ R ⊆ Avail x := by
  rfl

@[simp] theorem jointRecoverable_empty
    {Q X : Type*} (Avail : X → Set Q) (Step : X → X → Prop)
    (H : ℕ) (x : X) :
    JointRecoverable Avail Step H x ∅ := by
  cases H with
  | zero => exact Set.empty_subset _
  | succ n => exact Or.inl (Set.empty_subset _)

/-- Removing future requirements cannot destroy joint recoverability. -/
theorem jointRecoverable_downward
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop} :
    ∀ H x {R T : Set Q},
      JointRecoverable Avail Step H x R →
      T ⊆ R →
      JointRecoverable Avail Step H x T := by
  intro H
  induction H with
  | zero =>
      intro x R T hR hTR
      exact Set.Subset.trans hTR hR
  | succ n ih =>
      intro x R T hR hTR
      rcases hR with hnow | ⟨y, hxy, hrest⟩
      · exact Or.inl (Set.Subset.trans hTR hnow)
      · by_cases hTnow : T ⊆ Avail x
        · exact Or.inl hTnow
        · refine Or.inr ⟨y, hxy, ?_⟩
          apply ih y hrest
          intro q hq
          exact ⟨hTR hq.1, hq.2⟩

/-- More planning time cannot destroy joint recoverability. -/
theorem jointRecoverable_mono_horizon
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop} :
    ∀ H x R,
      JointRecoverable Avail Step H x R →
      JointRecoverable Avail Step (H + 1) x R := by
  intro H
  induction H with
  | zero =>
      intro x R hR
      exact Or.inl hR
  | succ n ih =>
      intro x R hR
      rcases hR with hnow | ⟨y, hxy, hrest⟩
      · exact Or.inl hnow
      · exact Or.inr ⟨y, hxy, ih y (R \ Avail x) hrest⟩

/-- On singleton contracts, joint recoverability is exactly the existing
per-contract temporal recoverability envelope. -/
theorem jointRecoverable_singleton_iff_recoverableEnvelope
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop} :
    ∀ H x q,
      JointRecoverable Avail Step H x ({q} : Set Q) ↔
        q ∈ RecoverableEnvelope Avail Step H x := by
  intro H
  induction H with
  | zero =>
      intro x q
      simp [JointRecoverable]
  | succ n ih =>
      intro x q
      constructor
      · intro hjoint
        rcases hjoint with hnow | ⟨y, hxy, hrest⟩
        · exact Or.inl (hnow (by simp))
        · by_cases hqx : q ∈ Avail x
          · exact Or.inl hqx
          · have hdiff : ({q} : Set Q) \ Avail x = ({q} : Set Q) := by
              ext z
              constructor
              · intro hz
                exact hz.1
              · intro hz
                have hzq : z = q := by simpa using hz
                subst z
                exact ⟨by simp, hqx⟩
            rw [hdiff] at hrest
            exact Or.inr ⟨y, hxy, (ih y q).mp hrest⟩
      · intro hsingle
        rcases hsingle with hnow | ⟨y, hxy, hy⟩
        · exact Or.inl (by
            intro z hz
            have hzq : z = q := by simpa using hz
            subst z
            exact hnow)
        · by_cases hqx : q ∈ Avail x
          · exact Or.inl (by
              intro z hz
              have hzq : z = q := by simpa using hz
              subst z
              exact hqx)
          · have hdiff : ({q} : Set Q) \ Avail x = ({q} : Set Q) := by
              ext z
              constructor
              · intro hz
                exact hz.1
              · intro hz
                have hzq : z = q := by simpa using hz
                subst z
                exact ⟨by simp, hqx⟩
            refine Or.inr ⟨y, hxy, ?_⟩
            rw [hdiff]
            exact (ih y q).mpr hy

/-- A jointly recoverable bundle is individually recoverable contract by
contract. The converse is deliberately not assumed. -/
theorem jointRecoverable_implies_individual
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} {R : Set Q}
    (hjoint : JointRecoverable Avail Step H x R) :
    R ⊆ RecoverableEnvelope Avail Step H x := by
  intro q hq
  have hsingle :
      JointRecoverable Avail Step H x ({q} : Set Q) := by
    apply jointRecoverable_downward hjoint
    intro z hz
    have hzq : z = q := by simpa using hz
    subst z
    exact hq
  exact (jointRecoverable_singleton_iff_recoverableEnvelope H x q).mp hsingle

/-- Joint recoverability therefore implies the previous Core-V1 `SafeWithin`
condition for the same finite or infinite requirement set. -/
theorem jointRecoverable_implies_safeWithin
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} {R : Set Q}
    (hjoint : JointRecoverable Avail Step H x R) :
    SafeWithin R Avail Step H x := by
  apply safeWithin_iff_required_subset_recoverableEnvelope.mpr
  exact jointRecoverable_implies_individual hjoint

/-- The temporal joint contract complex at state `x` and horizon `H`.
A finite bundle is a face exactly when one common admissible trajectory can
satisfy all contracts in the bundle by the deadline. -/
def TemporalContractComplex
    {Q X : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (H : ℕ) (x : X) : ContractComplex Q where
  feasible R := JointRecoverable Avail Step H x (↑R : Set Q)
  downward := by
    intro R T hR hTR
    apply jointRecoverable_downward hR
    intro q hq
    exact hTR hq

/-- Horizon zero recovers the immediate joint contract complex: every contract
in the bundle must be actionable now. -/
theorem temporalContractComplex_zero_iff
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {R : Finset Q} :
    (TemporalContractComplex Avail Step 0 x).feasible R ↔
      (↑R : Set Q) ⊆ Avail x := by
  rfl

/-- The temporal joint complex grows monotonically with the planning horizon. -/
theorem temporalContractComplex_mono_horizon
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} {R : Finset Q}
    (hR : (TemporalContractComplex Avail Step H x).feasible R) :
    (TemporalContractComplex Avail Step (H + 1) x).feasible R := by
  exact jointRecoverable_mono_horizon H x (↑R : Set Q) hR

/-- Singleton faces of the temporal joint complex coincide exactly with the
existing recoverability envelope. Thus the new complex is a conservative
extension of the verified singleton semantics. -/
theorem singleton_feasible_iff_recoverableEnvelope
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} {q : Q} :
    (TemporalContractComplex Avail Step H x).feasible {q} ↔
      q ∈ RecoverableEnvelope Avail Step H x := by
  simpa [TemporalContractComplex] using
    (jointRecoverable_singleton_iff_recoverableEnvelope
      (Avail := Avail) (Step := Step) H x q)

/-- Every face of the temporal joint complex is safe according to the earlier
per-contract deadline semantics. This is one-way because different singleton
recovery routes need not be compatible with one common trajectory. -/
theorem feasible_implies_safeWithin
    {Q X : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} {R : Finset Q}
    (hR : (TemporalContractComplex Avail Step H x).feasible R) :
    SafeWithin (↑R : Set Q) Avail Step H x := by
  exact jointRecoverable_implies_safeWithin hR

end TemporalJointContractComplex

end InsacermoActionabilityInformation
