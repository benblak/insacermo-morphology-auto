import InsacermoActionabilityInformation.SafeRepAuditBridge

namespace InsacermoActionabilityInformation

namespace FutureEnvelope

/-- The INSACERMO future envelope: the set of declared future contracts that
remain safely actionable under the current ambiguity set, capability set and
representation. -/
def Envelope {Q S A Y : Type*}
    (Good : Q → S → A → Prop) (B : Set S) (C : Set A) (h : S → Y) : Set Q :=
  {q | SafeRep (Good q) B C h}

@[simp] theorem mem_envelope_iff
    {Q S A Y : Type*}
    {Good : Q → S → A → Prop} {B : Set S} {C : Set A} {h : S → Y} {q : Q} :
    q ∈ Envelope Good B C h ↔ SafeRep (Good q) B C h := by
  rfl

/-- A declared required-future family is currently guaranteed exactly when it
is contained in the future envelope. -/
def Guarantees {Q S A Y : Type*}
    (Good : Q → S → A → Prop) (Req : Set Q)
    (B : Set S) (C : Set A) (h : S → Y) : Prop :=
  Req ⊆ Envelope Good B C h

/-- Futures lost by a transition are exactly the contracts that belonged to
the old envelope but not to the new one. -/
def LostFutures {Q S A Y₀ Y₁ : Type*}
    (Good : Q → S → A → Prop) (B : Set S)
    (C₀ C₁ : Set A) (h₀ : S → Y₀) (h₁ : S → Y₁) : Set Q :=
  Envelope Good B C₀ h₀ \ Envelope Good B C₁ h₁

/-- The envelope is jointly monotone in information refinement and capability
expansion.  A PROBE (finer representation) and/or REPAIR (larger capability
set) cannot destroy a future that was already safely actionable. -/
theorem envelope_mono_of_refines_of_capabilitySubset
    {Q S A YFine YCoarse : Type*}
    {Good : Q → S → A → Prop} {B : Set S}
    {C C' : Set A} {fine : S → YFine} {coarse : S → YCoarse}
    (href : Refines fine coarse) (hcap : C ⊆ C') :
    Envelope Good B C coarse ⊆ Envelope Good B C' fine := by
  intro q hq
  exact safeRep_of_refines_of_capabilitySubset hq href hcap

/-- Information-only monotonicity of the future envelope. -/
theorem envelope_probe_mono
    {Q S A YFine YCoarse : Type*}
    {Good : Q → S → A → Prop} {B : Set S} {C : Set A}
    {fine : S → YFine} {coarse : S → YCoarse}
    (href : Refines fine coarse) :
    Envelope Good B C coarse ⊆ Envelope Good B C fine := by
  exact envelope_mono_of_refines_of_capabilitySubset href Set.Subset.rfl

/-- Capability-only monotonicity of the future envelope. -/
theorem envelope_repair_mono
    {Q S A Y : Type*}
    {Good : Q → S → A → Prop} {B : Set S}
    {C C' : Set A} {h : S → Y}
    (hcap : C ⊆ C') :
    Envelope Good B C h ⊆ Envelope Good B C' h := by
  exact envelope_mono_of_refines_of_capabilitySubset
    (fine := h) (coarse := h) ⟨id, by intro s; rfl⟩ hcap

/-- Any PROBE/REPAIR transition has no lost futures. -/
theorem no_lost_futures_of_refines_of_capabilitySubset
    {Q S A YFine YCoarse : Type*}
    {Good : Q → S → A → Prop} {B : Set S}
    {C C' : Set A} {fine : S → YFine} {coarse : S → YCoarse}
    (href : Refines fine coarse) (hcap : C ⊆ C') :
    LostFutures Good B C C' coarse fine = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro q hq
  change q ∈ Envelope Good B C coarse ∧ q ∉ Envelope Good B C' fine at hq
  exact hq.2 ((envelope_mono_of_refines_of_capabilitySubset href hcap) hq.1)

/-- A PROBE/REPAIR transition preserves every currently guaranteed required
future. -/
theorem guarantees_mono_of_refines_of_capabilitySubset
    {Q S A YFine YCoarse : Type*}
    {Good : Q → S → A → Prop} {Req : Set Q} {B : Set S}
    {C C' : Set A} {fine : S → YFine} {coarse : S → YCoarse}
    (hreq : Guarantees Good Req B C coarse)
    (href : Refines fine coarse) (hcap : C ⊆ C') :
    Guarantees Good Req B C' fine := by
  exact Set.Subset.trans hreq
    (envelope_mono_of_refines_of_capabilitySubset href hcap)

section FiniteAudit

variable {Q S A Y : Type*} [DecidableEq S] [DecidableEq Y]

/-- Uniform obstruction-rank bound for all currently required future
contracts. -/
def UniformRequiredObstructionRankAtMost
    (Good : Q → S → A → Prop) (Req : Set Q)
    (C : Set A) (k : ℕ) : Prop :=
  ∀ q, q ∈ Req →
    ActionabilityAudit.CommonActionObstructionRankAtMost (Good q) C k

/-- Every required future contract passes the depth-`k` audit in every
realized fiber of the current representation. -/
def PassesRequiredFiberAudit
    (Good : Q → S → A → Prop) (Req : Set Q)
    (C : Set A) (k : ℕ) (B : Finset S) (h : S → Y) : Prop :=
  ∀ q, q ∈ Req → SafeRepAudit.PassesFiberAudit (Good q) C k B h

/-- Exact multi-future certification theorem.  If every required contract has
obstruction rank at most `k`, then the whole required future family is inside
the future envelope iff every required contract passes its fiber audits
through depth `k`. -/
theorem guarantees_iff_passesRequiredFiberAudit_of_uniformRank
    {Good : Q → S → A → Prop} {Req : Set Q}
    {C : Set A} {k : ℕ} {B : Finset S} {h : S → Y}
    (hC : C.Nonempty)
    (hrank : UniformRequiredObstructionRankAtMost Good Req C k) :
    Guarantees Good Req (↑B : Set S) C h ↔
      PassesRequiredFiberAudit Good Req C k B h := by
  constructor
  · intro hguar q hq
    exact SafeRepAudit.safeRep_implies_passesFiberAudit (hguar hq)
  · intro haudit q hq
    exact SafeRepAudit.safeRep_of_obstructionRankAtMost_of_passesFiberAudit
      hC (hrank q hq) (haudit q hq)

/-- Pointwise exact safe-destruction depth for a whole required future family:
a common depth `k` bounds every required contract's obstruction rank iff
maximal information destruction is audit-complete at depth `k` for every
required contract. -/
theorem uniformRank_iff_allRequired_constantDestructionAuditComplete
    {Good : Q → S → A → Prop} {Req : Set Q}
    {C : Set A} (hC : C.Nonempty) (k : ℕ) :
    UniformRequiredObstructionRankAtMost Good Req C k ↔
      ∀ q, q ∈ Req →
        SafeRepAudit.ConstantDestructionAuditComplete (Good q) C k := by
  constructor
  · intro hrank q hq
    exact (SafeRepAudit.obstructionRankAtMost_iff_constantDestructionAuditComplete
      (Good := Good q) hC k).mp (hrank q hq)
  · intro hcomplete q hq
    exact (SafeRepAudit.obstructionRankAtMost_iff_constantDestructionAuditComplete
      (Good := Good q) hC k).mpr (hcomplete q hq)

/-- A single required future with a minimal obstruction larger than `k`
produces a concrete false-safe certificate for maximal destruction: all local
checks through `k` pass on that witness, yet the future leaves the envelope
after total collapse. -/
theorem required_largeObstruction_witnesses_falseSafeDestruction
    {Good : Q → S → A → Prop} {Req : Set Q}
    {C : Set A} {k : ℕ} {q : Q} {M : Finset S}
    (hC : C.Nonempty) (_hq : q ∈ Req)
    (hmin : MinimalCommonActionObstruction (Good q) C M)
    (hk : k < M.card) :
    FiniteContractAudit.PassesLocalAudit
        (ActionabilityAudit.commonActionSat (Good q) C) k M ∧
      q ∉ Envelope Good (↑M : Set S) C (fun _ : S => ()) := by
  rcases SafeRepAudit.largeMinimalObstruction_gives_locallyAudited_unsafe_constantRep
      hC hmin hk with ⟨hpass, hunsafe⟩
  exact ⟨hpass, hunsafe⟩

end FiniteAudit

end FutureEnvelope

end InsacermoActionabilityInformation
