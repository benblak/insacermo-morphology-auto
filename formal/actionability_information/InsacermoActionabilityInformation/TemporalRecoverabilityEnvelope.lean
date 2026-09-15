import InsacermoActionabilityInformation.FutureConservationPlanner

namespace InsacermoActionabilityInformation

namespace TemporalRecoverabilityEnvelope

/-- The horizon-`H` recoverability envelope.  At horizon zero it is the set of
futures available now.  At horizon `H+1`, a future is recoverable either if it
is available now or if one admissible transition reaches a state from which it
is recoverable within horizon `H`. -/
def RecoverableEnvelope {Q X : Type*}
    (Avail : X → Set Q) (Step : X → X → Prop) : ℕ → X → Set Q
  | 0, x => Avail x
  | n + 1, x =>
      Avail x ∪ {q | ∃ y, Step x y ∧ q ∈ RecoverableEnvelope Avail Step n y}

@[simp] theorem recoverableEnvelope_zero
    {Q X : Type*} (Avail : X → Set Q) (Step : X → X → Prop) (x : X) :
    RecoverableEnvelope Avail Step 0 x = Avail x := by
  rfl

@[simp] theorem mem_recoverableEnvelope_succ
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop}
    {n : ℕ} {x : X} {q : Q} :
    q ∈ RecoverableEnvelope Avail Step (n + 1) x ↔
      q ∈ Avail x ∨
        ∃ y, Step x y ∧ q ∈ RecoverableEnvelope Avail Step n y := by
  rfl

/-- Anything available now remains in every finite-horizon recoverability
envelope. -/
theorem available_subset_recoverableEnvelope
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop} :
    ∀ n x, Avail x ⊆ RecoverableEnvelope Avail Step n x := by
  intro n x q hq
  cases n with
  | zero => exact hq
  | succ n => exact Or.inl hq

/-- One admissible step transports every horizon-`n` recoverable future at the
successor into the horizon-`n+1` recoverability envelope at the predecessor. -/
theorem step_recoverability
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop}
    {n : ℕ} {x y : X} (hxy : Step x y) :
    RecoverableEnvelope Avail Step n y ⊆
      RecoverableEnvelope Avail Step (n + 1) x := by
  intro q hq
  exact Or.inr ⟨y, hxy, hq⟩

/-- More time cannot destroy a recoverable future. -/
theorem recoverableEnvelope_mono_horizon
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop} :
    ∀ n x,
      RecoverableEnvelope Avail Step n x ⊆
        RecoverableEnvelope Avail Step (n + 1) x := by
  intro n
  induction n with
  | zero =>
      intro x q hq
      exact Or.inl hq
  | succ n ih =>
      intro x q hq
      rcases hq with hnow | ⟨y, hxy, hy⟩
      · exact Or.inl hnow
      · exact Or.inr ⟨y, hxy, ih y hy⟩

/-- Required futures not currently available. -/
def InstantDebt {Q X : Type*}
    (Req : Set Q) (Avail : X → Set Q) (x : X) : Set Q :=
  Req \ Avail x

/-- Required futures that cannot be restored within the declared horizon. -/
def TemporalDebt {Q X : Type*}
    (Req : Set Q) (Avail : X → Set Q) (Step : X → X → Prop)
    (H : ℕ) (x : X) : Set Q :=
  Req \ RecoverableEnvelope Avail Step H x

/-- Required futures that are unavailable now but are recoverable before the
deadline.  This is the exact gap between immediate debt and deadline debt. -/
def DeferredDebt {Q X : Type*}
    (Req : Set Q) (Avail : X → Set Q) (Step : X → X → Prop)
    (H : ℕ) (x : X) : Set Q :=
  InstantDebt Req Avail x \ TemporalDebt Req Avail Step H x

/-- At horizon zero, temporal debt is exactly immediate debt. -/
@[simp] theorem temporalDebt_zero
    {Q X : Type*} (Req : Set Q) (Avail : X → Set Q)
    (Step : X → X → Prop) (x : X) :
    TemporalDebt Req Avail Step 0 x = InstantDebt Req Avail x := by
  rfl

/-- Deadline debt can only shrink when the available planning horizon grows. -/
theorem temporalDebt_antitone_horizon
    {Q X : Type*} {Req : Set Q} {Avail : X → Set Q}
    {Step : X → X → Prop} {n : ℕ} {x : X} :
    TemporalDebt Req Avail Step (n + 1) x ⊆
      TemporalDebt Req Avail Step n x := by
  intro q hq
  refine ⟨hq.1, ?_⟩
  intro hn
  exact hq.2 (recoverableEnvelope_mono_horizon n x hn)

/-- Deadline debt is always a subset of immediate debt: planning can classify
some currently unmet futures as recoverable, but it cannot manufacture a debt
that was not already unmet now. -/
theorem temporalDebt_subset_instantDebt
    {Q X : Type*} {Req : Set Q} {Avail : X → Set Q}
    {Step : X → X → Prop} {H : ℕ} {x : X} :
    TemporalDebt Req Avail Step H x ⊆ InstantDebt Req Avail x := by
  intro q hq
  refine ⟨hq.1, ?_⟩
  intro hnow
  exact hq.2 (available_subset_recoverableEnvelope H x hnow)

/-- Exact debt decomposition: every currently unmet required future is either
still unrecoverable by the deadline, or is currently unmet but recoverable by
then. -/
theorem instantDebt_eq_temporalDebt_union_deferredDebt
    {Q X : Type*} {Req : Set Q} {Avail : X → Set Q}
    {Step : X → X → Prop} {H : ℕ} {x : X} :
    InstantDebt Req Avail x =
      TemporalDebt Req Avail Step H x ∪
        DeferredDebt Req Avail Step H x := by
  ext q
  constructor
  · intro hq
    by_cases ht : q ∈ TemporalDebt Req Avail Step H x
    · exact Or.inl ht
    · exact Or.inr ⟨hq, ht⟩
  · intro hq
    rcases hq with ht | hd
    · exact temporalDebt_subset_instantDebt ht
    · exact hd.1

/-- A required-future family is safe by a deadline exactly when its temporal
debt at that deadline is empty. -/
def SafeWithin {Q X : Type*}
    (Req : Set Q) (Avail : X → Set Q) (Step : X → X → Prop)
    (H : ℕ) (x : X) : Prop :=
  TemporalDebt Req Avail Step H x = ∅

/-- Zero deadline debt is exactly inclusion of every required future in the
horizon recoverability envelope. -/
theorem safeWithin_iff_required_subset_recoverableEnvelope
    {Q X : Type*} {Req : Set Q} {Avail : X → Set Q}
    {Step : X → X → Prop} {H : ℕ} {x : X} :
    SafeWithin Req Avail Step H x ↔
      Req ⊆ RecoverableEnvelope Avail Step H x := by
  constructor
  · intro hsafe q hq
    by_contra hnot
    have hmem : q ∈ TemporalDebt Req Avail Step H x := ⟨hq, hnot⟩
    rw [hsafe] at hmem
    exact hmem.elim
  · intro hsub
    unfold SafeWithin
    ext q
    constructor
    · intro hq
      exact False.elim (hq.2 (hsub hq.1))
    · intro hq
      simp at hq

/-- If all required futures are available now, they are safe for every later
deadline as well. -/
theorem currentGuarantee_implies_safeWithin
    {Q X : Type*} {Req : Set Q} {Avail : X → Set Q}
    {Step : X → X → Prop} {H : ℕ} {x : X}
    (hnow : Req ⊆ Avail x) :
    SafeWithin Req Avail Step H x := by
  apply safeWithin_iff_required_subset_recoverableEnvelope.mpr
  intro q hq
  exact available_subset_recoverableEnvelope H x (hnow hq)

/-- More recovery time preserves deadline safety. -/
theorem safeWithin_mono_horizon
    {Q X : Type*} {Req : Set Q} {Avail : X → Set Q}
    {Step : X → X → Prop} {n : ℕ} {x : X}
    (hsafe : SafeWithin Req Avail Step n x) :
    SafeWithin Req Avail Step (n + 1) x := by
  apply safeWithin_iff_required_subset_recoverableEnvelope.mpr
  intro q hq
  have hn : q ∈ RecoverableEnvelope Avail Step n x :=
    (safeWithin_iff_required_subset_recoverableEnvelope.mp hsafe) hq
  exact recoverableEnvelope_mono_horizon n x hn

/-- Strict temporal-recovery witness: a future may be unavailable now and yet
become recoverable after one admissible transition.  This is the formal gap
between instantaneous preservation and preservation-by-deadline. -/
theorem unavailable_now_but_recoverable_in_one_step
    {Q X : Type*} {Avail : X → Set Q} {Step : X → X → Prop}
    {q : Q} {x y : X}
    (hnot : q ∉ Avail x) (hxy : Step x y) (hy : q ∈ Avail y) :
    q ∉ Avail x ∧ q ∈ RecoverableEnvelope Avail Step 1 x := by
  refine ⟨hnot, ?_⟩
  exact Or.inr ⟨y, hxy, hy⟩

end TemporalRecoverabilityEnvelope

end InsacermoActionabilityInformation
