import InsacermoActionabilityInformation.RecoveryDepthIrreversibility

namespace InsacermoActionabilityInformation

namespace DecisionSemantics

open FutureEnvelope
open TemporalRecoverabilityEnvelope
open RecoveryDepthIrreversibility

/-!
# INSACERMO public decision semantics

The public words are deliberately separated into three semantic layers.

* `ACT`, `RECOVER`, `REFUSE` classify the status of a future at a state.
* `PROBE`, `REPAIR` describe recovery mechanisms.
* `PRESERVE`, `DESTROY` certify transitions relative to required futures.

They are therefore not seven mutually exclusive constructors.  In particular,
a PROBE or REPAIR route is also a RECOVER route when it restores a future in
one admissible step.
-/

section Status

variable {Q X : Type*}

/-- ACT: the future is safely actionable now. -/
def ACT (Avail : X → Set Q) (x : X) (q : Q) : Prop :=
  q ∈ Avail x

/-- RECOVER at deadline `H`: the future is not actionable now, but remains
recoverable within the declared finite horizon. -/
def RECOVER (Avail : X → Set Q) (Step : X → X → Prop)
    (H : ℕ) (x : X) (q : Q) : Prop :=
  q ∉ Avail x ∧ q ∈ RecoverableEnvelope Avail Step H x

/-- REFUSE: no finite admissible plan can recover the future. -/
def REFUSE (Avail : X → Set Q) (Step : X → X → Prop)
    (x : X) (q : Q) : Prop :=
  q ∉ EventuallyRecoverableEnvelope Avail Step x

/-- ACT and RECOVER are disjoint by construction. -/
theorem act_excludes_recover
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} {q : Q} :
    ACT Avail x q → ¬ RECOVER Avail Step H x q := by
  intro hact hrecover
  exact hrecover.1 hact

/-- ACT can never be REFUSE: an available future is already recoverable at
horizon zero. -/
theorem act_excludes_refuse
    {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {q : Q} :
    ACT Avail x q → ¬ REFUSE Avail Step x q := by
  intro hact hrefuse
  apply hrefuse
  exact ⟨0, hact⟩

/-- Finite-horizon RECOVER can never be REFUSE. -/
theorem recover_excludes_refuse
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} {q : Q} :
    RECOVER Avail Step H x q → ¬ REFUSE Avail Step x q := by
  intro hrecover hrefuse
  exact hrefuse (recoverableEnvelope_subset_eventuallyRecoverable hrecover.2)

/-- A required future is REFUSE exactly when it belongs to irreversible debt. -/
theorem refuse_iff_mem_irreversibleDebt_of_required
    {Req : Set Q} {Avail : X → Set Q} {Step : X → X → Prop}
    {x : X} {q : Q} (hreq : q ∈ Req) :
    REFUSE Avail Step x q ↔
      q ∈ IrreversibleDebt Req Avail Step x := by
  constructor
  · intro hrefuse
    exact ⟨hreq, hrefuse⟩
  · intro hdebt
    exact hdebt.2

/-- RECOVER supplies finite recovery depth. -/
theorem recover_hasFiniteRecoveryDepth
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} {q : Q}
    (hrecover : RECOVER Avail Step H x q) :
    HasFiniteRecoveryDepth Avail Step x q := by
  exact ⟨H, hrecover.2⟩

/-- If a future is RECOVER by deadline `H`, its minimum recovery depth is at
most `H`. -/
theorem recover_minimalDepth_le_deadline
    {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {x : X} {q : Q}
    (hrecover : RECOVER Avail Step H x q) :
    RecoveryDepth Avail Step x q (recover_hasFiniteRecoveryDepth hrecover) ≤ H := by
  exact recoveryDepth_minimal (recover_hasFiniteRecoveryDepth hrecover) hrecover.2

end Status

section Mechanisms

variable {Q X : Type*}

/-- PROBE: the future is unavailable now, and some declared probe transition
restores immediate actionability.  The separate assumption that probe steps
are admissible planner steps is used by the soundness theorem below. -/
def PROBE (Avail : X → Set Q) (ProbeStep : X → X → Prop)
    (x : X) (q : Q) : Prop :=
  q ∉ Avail x ∧ ∃ y, ProbeStep x y ∧ q ∈ Avail y

/-- REPAIR: the future is unavailable now, and some declared repair transition
restores immediate actionability. -/
def REPAIR (Avail : X → Set Q) (RepairStep : X → X → Prop)
    (x : X) (q : Q) : Prop :=
  q ∉ Avail x ∧ ∃ y, RepairStep x y ∧ q ∈ Avail y

/-- A PROBE transition that is also an admissible planner transition is a
one-step RECOVER route. -/
theorem probe_implies_recover_one
    {Avail : X → Set Q} {ProbeStep Step : X → X → Prop}
    {x : X} {q : Q}
    (hadm : ∀ a b, ProbeStep a b → Step a b)
    (hprobe : PROBE Avail ProbeStep x q) :
    RECOVER Avail Step 1 x q := by
  rcases hprobe with ⟨hnot, y, hprobeStep, hy⟩
  refine ⟨hnot, ?_⟩
  exact Or.inr ⟨y, hadm x y hprobeStep, hy⟩

/-- A REPAIR transition that is also an admissible planner transition is a
one-step RECOVER route. -/
theorem repair_implies_recover_one
    {Avail : X → Set Q} {RepairStep Step : X → X → Prop}
    {x : X} {q : Q}
    (hadm : ∀ a b, RepairStep a b → Step a b)
    (hrepair : REPAIR Avail RepairStep x q) :
    RECOVER Avail Step 1 x q := by
  rcases hrepair with ⟨hnot, y, hrepairStep, hy⟩
  refine ⟨hnot, ?_⟩
  exact Or.inr ⟨y, hadm x y hrepairStep, hy⟩

end Mechanisms

section TransitionPermission

variable {Q X : Type*}

/-- Strict PRESERVE: all required futures remain actionable immediately after
the transition. -/
def PRESERVE (Req : Set Q) (Avail : X → Set Q) (after : X) : Prop :=
  Req ⊆ Avail after

/-- Deadline PRESERVE: all required futures remain recoverable by horizon `H`
after the transition. -/
def PRESERVE_WITHIN (Req : Set Q) (Avail : X → Set Q)
    (Step : X → X → Prop) (H : ℕ) (after : X) : Prop :=
  SafeWithin Req Avail Step H after

/-- DESTROY permission is contract-relative: a declared destructive transition
is permitted when, after taking it, every required future remains recoverable
within the declared horizon. -/
def DESTROY (Req : Set Q) (Avail : X → Set Q)
    (Step DestroyStep : X → X → Prop) (H : ℕ) (before after : X) : Prop :=
  DestroyStep before after ∧ PRESERVE_WITHIN Req Avail Step H after

/-- Immediate preservation implies preservation at every finite deadline. -/
theorem preserve_implies_preserveWithin
    {Req : Set Q} {Avail : X → Set Q} {Step : X → X → Prop}
    {H : ℕ} {after : X}
    (hpres : PRESERVE Req Avail after) :
    PRESERVE_WITHIN Req Avail Step H after := by
  exact currentGuarantee_implies_safeWithin hpres

/-- A permitted destructive transition has zero temporal debt at its declared
deadline. -/
theorem destroy_implies_zero_temporalDebt
    {Req : Set Q} {Avail : X → Set Q} {Step DestroyStep : X → X → Prop}
    {H : ℕ} {before after : X}
    (hdestroy : DESTROY Req Avail Step DestroyStep H before after) :
    TemporalDebt Req Avail Step H after = ∅ := by
  exact hdestroy.2

/-- A permitted destructive transition cannot place any required future in
irreversible debt. -/
theorem destroy_excludes_irreversible_required_future
    {Req : Set Q} {Avail : X → Set Q} {Step DestroyStep : X → X → Prop}
    {H : ℕ} {before after : X} {q : Q}
    (hdestroy : DESTROY Req Avail Step DestroyStep H before after)
    (hreq : q ∈ Req) :
    q ∉ IrreversibleDebt Req Avail Step after := by
  intro hirr
  have htemp : q ∈ TemporalDebt Req Avail Step H after :=
    irreversibleDebt_subset_temporalDebt hirr
  rw [destroy_implies_zero_temporalDebt hdestroy] at htemp
  exact htemp.elim

end TransitionPermission

section ContractInstantiation

variable {Q S A Y : Type*}

/-- ACT instantiated on the verified INSACERMO FutureEnvelope. -/
theorem act_futureEnvelope_iff_safeRep
    {Good : Q → S → A → Prop} {B : Set S} {C : Set A}
    {h : S → Y} {q : Q} :
    ACT (fun _ : Unit => Envelope Good B C h) () q ↔
      SafeRep (Good q) B C h := by
  exact mem_envelope_iff

/-- A representation refinement is a certified PROBE-style monotone move on
the future envelope: it cannot remove any currently actionable future. -/
theorem probe_refinement_preserves_envelope
    {YFine YCoarse : Type*}
    {Good : Q → S → A → Prop} {B : Set S} {C : Set A}
    {fine : S → YFine} {coarse : S → YCoarse}
    (href : Refines fine coarse) :
    Envelope Good B C coarse ⊆ Envelope Good B C fine := by
  exact envelope_probe_mono href

/-- Capability expansion is a certified REPAIR-style monotone move on the
future envelope. -/
theorem repair_expansion_preserves_envelope
    {Good : Q → S → A → Prop} {B : Set S} {C C' : Set A}
    {h : S → Y} (hcap : C ⊆ C') :
    Envelope Good B C h ⊆ Envelope Good B C' h := by
  exact envelope_repair_mono hcap

end ContractInstantiation

end DecisionSemantics

end InsacermoActionabilityInformation
