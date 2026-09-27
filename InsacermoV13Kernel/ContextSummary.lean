import InsacermoV13Kernel.SeparatorMessages

namespace InsacermoV13Kernel

universe uK uQ uW uA uM

/-- A context summary q : K → Q preserves only the portion of separator context
    needed to interpret message semantics. The encoder may still see the full
    context, but the decoder depends only on q(k) and the message. -/
def SummaryCertifiedProtocol
    {K : Type uK} {Q : Type uQ}
    {World : Type uW} {Action : Type uA}
    (Message : Type uM)
    (summary : K → Q)
    (available : Action → Prop)
    (admissible : K → World → Action → Prop) : Prop :=
  ∃ encode : K → World → Message,
    ∃ decode : Q → Message → Action,
      (∀ q m, available (decode q m)) ∧
      ∀ k x, admissible k x (decode (summary k) (encode k x))

/-- Exact lifting: a summary protocol becomes a global certified protocol by
    transmitting the summary value together with the local message. -/
theorem summaryProtocol_carries_summary
    {K : Type uK} {Q : Type uQ}
    {World : Type uW} {Action : Type uA}
    {Message : Type uM}
    {summary : K → Q}
    {available : Action → Prop}
    {admissible : K → World → Action → Prop}
    (h : SummaryCertifiedProtocol Message summary available admissible) :
    CertifiedProtocol
      available
      (ContextLiftAdmissible admissible)
      (Q × Message) := by
  rcases h with ⟨encode, decode, havail, hcert⟩
  refine
    ⟨(fun x => (summary x.1, encode x.1 x.2)),
     (fun qm => decode qm.1 qm.2),
     ?_,
     ?_⟩
  · intro qm
    exact havail qm.1 qm.2
  · intro x
    exact hcert x.1 x.2

/-- Identity summary recovers fully indexed separator semantics. -/
theorem summaryProtocol_of_indexed
    {K : Type uK} {World : Type uW} {Action : Type uA}
    {Message : Type uM}
    {available : Action → Prop}
    {admissible : K → World → Action → Prop}
    (h : IndexedCertifiedProtocol Message available admissible) :
    SummaryCertifiedProtocol Message (fun k : K => k) available admissible := by
  rcases h with ⟨encode, decode, havail, hcert⟩
  exact ⟨encode, decode, havail, hcert⟩

/-- Constant summary is exactly uniform semantics. -/
theorem summaryProtocol_of_uniform
    {K : Type uK} {World : Type uW} {Action : Type uA}
    {Message : Type uM}
    {available : Action → Prop}
    {admissible : K → World → Action → Prop}
    (h : UniformCertifiedProtocol Message available admissible) :
    SummaryCertifiedProtocol Message (fun _ : K => Unit.unit)
      available admissible := by
  rcases h with ⟨encode, decode, havail, hcert⟩
  refine
    ⟨encode,
     (fun _ m => decode m),
     ?_,
     ?_⟩
  · intro q m
    exact havail m
  · intro k x
    exact hcert k x

/-- If one summary refines another, every protocol using the coarser summary can
    be lifted to the finer summary by forgetting the extra detail. -/
theorem summaryProtocol_of_summary_refinement
    {K : Type uK} {QCoarse : Type uQ} {QFine : Type uM}
    {World : Type uW} {Action : Type uA}
    {Message : Type uM}
    {coarse : K → QCoarse} {fine : K → QFine}
    {available : Action → Prop}
    {admissible : K → World → Action → Prop}
    (hfactor : ∃ project : QFine → QCoarse, ∀ k, project (fine k) = coarse k)
    (h : SummaryCertifiedProtocol Message coarse available admissible) :
    SummaryCertifiedProtocol Message fine available admissible := by
  rcases hfactor with ⟨project, hproject⟩
  rcases h with ⟨encode, decode, havail, hcert⟩
  refine
    ⟨encode,
     (fun q m => decode (project q) m),
     ?_,
     ?_⟩
  · intro q m
    exact havail (project q) m
  · intro k x
    simpa [hproject k] using hcert k x

/-- The real operational meaning of a summary: if two contexts share the same
    summary value, the same message is decoded to the same action in both. -/
theorem equal_summary_equal_decoded_action
    {K : Type uK} {Q : Type uQ}
    {World : Type uW} {Action : Type uA}
    {Message : Type uM}
    {summary : K → Q}
    {available : Action → Prop}
    {admissible : K → World → Action → Prop}
    (h : SummaryCertifiedProtocol Message summary available admissible) :
    ∃ decode : Q → Message → Action,
      ∀ ⦃k₁ k₂ : K⦄, summary k₁ = summary k₂ →
        ∀ m, decode (summary k₁) m = decode (summary k₂) m := by
  rcases h with ⟨encode, decode, havail, hcert⟩
  refine ⟨decode, ?_⟩
  intro k₁ k₂ hq m
  simp [hq]

namespace PartialContextWitness

inductive Context
  | a0
  | a1
  | b0
  | b1

inductive Summary
  | A
  | B

inductive Action
  | alpha
  | beta

open Context Summary Action

def summary : Context → Summary
  | a0 | a1 => A
  | b0 | b1 => B

def available : Action → Prop := fun _ => True

def admissible : Context → Unit → Action → Prop
  | a0, _, alpha => True
  | a1, _, alpha => True
  | b0, _, beta => True
  | b1, _, beta => True
  | _, _, _ => False

def encode : Context → Unit → Fin 1 :=
  fun _ _ => 0

def decode : Summary → Fin 1 → Action
  | A, _ => alpha
  | B, _ => beta

theorem summary_one_message_protocol :
    SummaryCertifiedProtocol (Fin 1) summary available admissible := by
  refine ⟨encode, decode, ?_, ?_⟩
  · intro q m
    trivial
  · intro k x
    cases k <;> trivial

/-- The exact context is unnecessary: the two-bit physical context collapses to
    a two-class future-relevant summary. -/
theorem two_class_summary_suffices :
    CertifiedProtocol
      available
      (ContextLiftAdmissible admissible)
      (Summary × Fin 1) := by
  exact summaryProtocol_carries_summary summary_one_message_protocol

/-- Full context is strictly finer than the summary: distinct physical contexts
    can have the same future-relevant summary. -/
theorem summary_strictly_forgets_context :
    summary a0 = summary a1 ∧
    summary b0 = summary b1 ∧
    a0 ≠ a1 ∧
    b0 ≠ b1 := by
  decide

/-- Complete erasure is impossible: A-contexts require alpha and B-contexts
    require beta, so one context-free message cannot certify both. -/
theorem no_uniform_one_message :
    ¬ UniformCertifiedProtocol (Fin 1) available admissible := by
  rintro ⟨enc, dec, havail, hcert⟩
  have hsame :
      enc a0 () = enc b0 () :=
    Subsingleton.elim _ _
  have hA := hcert a0 ()
  have hB := hcert b0 ()
  have hdec :
      dec (enc a0 ()) = dec (enc b0 ()) := by
    rw [hsame]
  rw [← hdec] at hB
  cases hact : dec (enc a0 ()) with
  | alpha =>
      simpa [admissible, hact] using hB
  | beta =>
      simpa [admissible, hact] using hA

/-- Exact witness of partial context compression:
    full context is unnecessary, but total context erasure is impossible. -/
theorem partial_context_compression_strict :
    SummaryCertifiedProtocol (Fin 1) summary available admissible ∧
    ¬ UniformCertifiedProtocol (Fin 1) available admissible ∧
    summary a0 = summary a1 ∧
    summary b0 = summary b1 := by
  exact
    ⟨summary_one_message_protocol,
     no_uniform_one_message,
     rfl,
     rfl⟩

end PartialContextWitness

end InsacermoV13Kernel
