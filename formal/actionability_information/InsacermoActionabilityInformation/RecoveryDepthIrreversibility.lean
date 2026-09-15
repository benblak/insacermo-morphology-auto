import InsacermoActionabilityInformation.TemporalRecoverabilityEnvelope

namespace InsacermoActionabilityInformation

namespace RecoveryDepthIrreversibility

open TemporalRecoverabilityEnvelope

/-- Futures that can be recovered at some finite planning horizon. -/
def EventuallyRecoverableEnvelope {Q X : Type*}
    (Avail : X → Set Q) (Step : X → X → Prop) (x : X) : Set Q :=
  {q | ∃ H, q ∈ RecoverableEnvelope Avail Step H x}

/-- A future has finite recovery depth exactly when some finite horizon recovers it. -/
def HasFiniteRecoveryDepth {Q X : Type*}
    (Avail : X → Set Q) (Step : X → X → Prop) (x : X) (q : Q) : Prop :=
  ∃ H, q ∈ RecoverableEnvelope Avail Step H x

/-- Required futures that cannot be recovered at any finite horizon. -/
def IrreversibleDebt {Q X : Type*}
    (Req : Set Q) (Avail : X → Set Q) (Step : X → X → Prop) (x : X) : Set Q :=
  Req \ EventuallyRecoverableEnvelope Avail Step x

/-- Required futures that miss horizon `H` but remain recoverable at some later
finite horizon. -/
def LateDebt {Q X : Type*}
    (Req : Set Q) (Avail : X → Set Q) (Step : X → X → Prop)
    (H : ℕ) (x : X) : Set Q :=
  TemporalDebt Req Avail Step H x \ IrreversibleDebt Req Avail Step x

/-- Recovery within a declared horizon. -/
def RecoveryDepthAtMost {Q X : Type*}
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (q : Q) (H : ℕ) : Prop :=
  q ∈ RecoverableEnvelope Avail Step H x

/-- Exact first horizon at which a future enters the recoverability envelope. -/
def FirstRecoveryAt {Q X : Type*}
    (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (q : Q) (H : ℕ) : Prop :=
  RecoveryDepthAtMost Avail Step x q H ∧
    ∀ h, h < H → ¬ RecoveryDepthAtMost Avail Step x q h

/-- Recoverability is monotone for arbitrary finite horizon extension. -/
theorem recoverableEnvelope_mono_of_le
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {m n : ℕ} (hmn : m ≤ n) :
    RecoverableEnvelope Avail Step m x ⊆
      RecoverableEnvelope Avail Step n x := by
  induction hmn with
  | refl => exact Set.Subset.rfl
  | @step n hmn ih =>
      exact Set.Subset.trans ih (recoverableEnvelope_mono_horizon n x)

/-- Every finite-horizon recoverable future is eventually recoverable. -/
theorem recoverableEnvelope_subset_eventuallyRecoverable
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {H : ℕ} :
    RecoverableEnvelope Avail Step H x ⊆
      EventuallyRecoverableEnvelope Avail Step x := by
  intro q hq
  exact ⟨H, hq⟩

/-- A one-step predecessor inherits eventual recoverability from its successor. -/
theorem step_eventual_recoverability
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop}
    {x y : X} (hxy : Step x y) :
    EventuallyRecoverableEnvelope Avail Step y ⊆
      EventuallyRecoverableEnvelope Avail Step x := by
  intro q hq
  rcases hq with ⟨H, hH⟩
  exact ⟨H + 1, step_recoverability hxy hH⟩

/-- Irreversible debt is contained in every finite-horizon temporal debt. -/
theorem irreversibleDebt_subset_temporalDebt
    {Q X : Type*} {Req : Set Q} {Avail : X → Set Q}
    {Step : X → X → Prop} {x : X} {H : ℕ} :
    IrreversibleDebt Req Avail Step x ⊆
      TemporalDebt Req Avail Step H x := by
  intro q hq
  refine ⟨hq.1, ?_⟩
  intro hH
  exact hq.2 ⟨H, hH⟩

/-- Exact decomposition of deadline debt into irreversible debt and debt that
is merely late relative to the chosen deadline. -/
theorem temporalDebt_eq_irreversibleDebt_union_lateDebt
    {Q X : Type*} {Req : Set Q} {Avail : X → Set Q}
    {Step : X → X → Prop} {x : X} {H : ℕ} :
    TemporalDebt Req Avail Step H x =
      IrreversibleDebt Req Avail Step x ∪ LateDebt Req Avail Step H x := by
  ext q
  constructor
  · intro hq
    by_cases hi : q ∈ IrreversibleDebt Req Avail Step x
    · exact Or.inl hi
    · exact Or.inr ⟨hq, hi⟩
  · intro hq
    rcases hq with hi | hl
    · exact irreversibleDebt_subset_temporalDebt hi
    · exact hl.1

/-- Eventual safety means that every required future has some finite recovery
plan, with no common deadline imposed yet. -/
def EventuallySafe {Q X : Type*}
    (Req : Set Q) (Avail : X → Set Q) (Step : X → X → Prop) (x : X) : Prop :=
  Req ⊆ EventuallyRecoverableEnvelope Avail Step x

/-- Eventual safety is exactly zero irreversible debt. -/
theorem eventuallySafe_iff_irreversibleDebt_eq_empty
    {Q X : Type*} {Req : Set Q} {Avail : X → Set Q}
    {Step : X → X → Prop} {x : X} :
    EventuallySafe Req Avail Step x ↔
      IrreversibleDebt Req Avail Step x = ∅ := by
  constructor
  · intro hsafe
    ext q
    constructor
    · intro hq
      exact False.elim (hq.2 (hsafe hq.1))
    · intro hq
      simp at hq
  · intro hzero q hq
    by_contra hnot
    have hmem : q ∈ IrreversibleDebt Req Avail Step x := ⟨hq, hnot⟩
    rw [hzero] at hmem
    exact hmem.elim

/-- Eventual recoverability and finite recovery depth are definitionally the
same notion. -/
theorem eventuallyRecoverable_iff_hasFiniteRecoveryDepth
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {q : Q} :
    q ∈ EventuallyRecoverableEnvelope Avail Step x ↔
      HasFiniteRecoveryDepth Avail Step x q := by
  rfl

/-- The minimum finite horizon recovering a future, provided that such a
horizon exists. -/
noncomputable def RecoveryDepth
    {Q X : Type*} (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (q : Q) (hfinite : HasFiniteRecoveryDepth Avail Step x q) : ℕ := by
  classical
  exact Nat.find hfinite

/-- The minimum recovery depth actually recovers the future. -/
theorem recoveryDepth_spec
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {q : Q} (hfinite : HasFiniteRecoveryDepth Avail Step x q) :
    RecoveryDepthAtMost Avail Step x q
      (RecoveryDepth Avail Step x q hfinite) := by
  classical
  unfold RecoveryDepth RecoveryDepthAtMost
  exact Nat.find_spec hfinite

/-- The recovery depth is no larger than any horizon that already recovers the
future. -/
theorem recoveryDepth_minimal
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {q : Q} (hfinite : HasFiniteRecoveryDepth Avail Step x q)
    {H : ℕ} (hH : RecoveryDepthAtMost Avail Step x q H) :
    RecoveryDepth Avail Step x q hfinite ≤ H := by
  classical
  unfold RecoveryDepth RecoveryDepthAtMost at *
  exact Nat.find_min' hfinite hH

/-- The minimum recovery depth is an exact first-entry horizon. -/
theorem firstRecoveryAt_recoveryDepth
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {q : Q} (hfinite : HasFiniteRecoveryDepth Avail Step x q) :
    FirstRecoveryAt Avail Step x q
      (RecoveryDepth Avail Step x q hfinite) := by
  classical
  constructor
  · exact recoveryDepth_spec hfinite
  · intro h hh
    unfold RecoveryDepthAtMost
    exact Nat.find_min hfinite (by simpa [RecoveryDepth] using hh)

/-- Every eventually recoverable future has an exact first recovery horizon. -/
theorem eventuallyRecoverable_has_firstRecoveryAt
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {q : Q}
    (hev : q ∈ EventuallyRecoverableEnvelope Avail Step x) :
    ∃ H, FirstRecoveryAt Avail Step x q H := by
  have hfinite : HasFiniteRecoveryDepth Avail Step x q := hev
  exact ⟨RecoveryDepth Avail Step x q hfinite,
    firstRecoveryAt_recoveryDepth hfinite⟩

/-- Deadline safety says exactly that every required future has recovery depth
at most the declared horizon. -/
theorem safeWithin_iff_all_required_recoveryDepthAtMost
    {Q X : Type*} {Req : Set Q} {Avail : X → Set Q}
    {Step : X → X → Prop} {x : X} {H : ℕ} :
    SafeWithin Req Avail Step H x ↔
      ∀ q, q ∈ Req → RecoveryDepthAtMost Avail Step x q H := by
  constructor
  · intro hsafe q hq
    exact (safeWithin_iff_required_subset_recoverableEnvelope.mp hsafe) hq
  · intro hdepth
    apply safeWithin_iff_required_subset_recoverableEnvelope.mpr
    intro q hq
    exact hdepth q hq

/-- If every required future is eventually recoverable, deadline safety at `H`
is equivalent to every minimum recovery depth being at most `H`. -/
theorem safeWithin_iff_all_minimalDepth_le
    {Q X : Type*} {Req : Set Q} {Avail : X → Set Q}
    {Step : X → X → Prop} {x : X} {H : ℕ}
    (hfinite : ∀ q, q ∈ Req → HasFiniteRecoveryDepth Avail Step x q) :
    SafeWithin Req Avail Step H x ↔
      ∀ q (hq : q ∈ Req), RecoveryDepth Avail Step x q (hfinite q hq) ≤ H := by
  constructor
  · intro hsafe q hq
    have hH : RecoveryDepthAtMost Avail Step x q H :=
      (safeWithin_iff_all_required_recoveryDepthAtMost.mp hsafe) q hq
    exact recoveryDepth_minimal (hfinite q hq) hH
  · intro hbound
    apply safeWithin_iff_all_required_recoveryDepthAtMost.mpr
    intro q hq
    have hspec : RecoveryDepthAtMost Avail Step x q
        (RecoveryDepth Avail Step x q (hfinite q hq)) :=
      recoveryDepth_spec (hfinite q hq)
    exact recoverableEnvelope_mono_of_le (hbound q hq) hspec

end RecoveryDepthIrreversibility

end InsacermoActionabilityInformation
