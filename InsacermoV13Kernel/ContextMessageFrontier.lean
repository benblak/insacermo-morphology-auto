import InsacermoV13Kernel.ContextSummary

namespace InsacermoV13Kernel

universe uK uW uA

/-- Finite context/message feasibility region.
    q counts summary symbols; m counts certified message symbols. -/
def ContextMessageBudget
    {K : Type uK} {World : Type uW} {Action : Type uA}
    (available : Action → Prop)
    (admissible : K → World → Action → Prop)
    (q m : Nat) : Prop :=
  ∃ summary : K → Fin q,
    SummaryCertifiedProtocol (Fin m) summary available admissible

/-- Any feasible (q,m) budget yields a global certified protocol whose message
    type is the product of summary and local-message alphabets. -/
theorem contextMessageBudget_carries_pair
    {K : Type uK} {World : Type uW} {Action : Type uA}
    {available : Action → Prop}
    {admissible : K → World → Action → Prop}
    {q m : Nat}
    (h : ContextMessageBudget available admissible q m) :
    CertifiedProtocol
      available
      (ContextLiftAdmissible admissible)
      (Fin q × Fin m) := by
  rcases h with ⟨summary, hsummary⟩
  exact summaryProtocol_carries_summary hsummary

/-- If an ordinary global m-message protocol exists, then one summary symbol is
    always sufficient: all context information can be shifted into the message.
    Therefore minimizing q alone, while leaving m unrestricted, is degenerate. -/
theorem one_summary_symbol_of_certifiedMessages
    {K : Type uK} {World : Type uW} {Action : Type uA}
    {available : Action → Prop}
    {admissible : K → World → Action → Prop}
    {m : Nat}
    (h :
      CertifiedMessages
        available
        (ContextLiftAdmissible admissible)
        m) :
    ContextMessageBudget available admissible 1 m := by
  rcases h with ⟨globalEncode, globalDecode, havail, hcert⟩
  let summary : K → Fin 1 := fun _ => 0
  refine ⟨summary, ?_⟩
  refine
    ⟨(fun k x => globalEncode (k, x)),
     (fun _ msg => globalDecode msg),
     ?_,
     ?_⟩
  · intro q msg
    exact havail msg
  · intro k x
    exact hcert (k, x)

/-- A coarser context summary and a larger local message alphabet can therefore
    trade information between the two channels. The right object is the joint
    feasibility region, not q in isolation. -/
def ContextMessageLe (p q : Nat × Nat) : Prop :=
  p.1 ≤ q.1 ∧ p.2 ≤ q.2

namespace ContextMessageTradeoffWitness

inductive Context
  | a0
  | a1
  | b0
  | b1

inductive Action
  | alpha
  | beta

open Context Action

def available : Action → Prop := fun _ => True

def admissible : Context → Unit → Action → Prop
  | a0, _, alpha => True
  | a1, _, alpha => True
  | b0, _, beta => True
  | b1, _, beta => True
  | _, _, _ => False

/-- Two summary symbols, one local message. -/
def summaryTwo : Context → Fin 2
  | a0 | a1 => 0
  | b0 | b1 => 1

def encodeOne : Context → Unit → Fin 1 :=
  fun _ _ => 0

def decodeTwoOne : Fin 2 → Fin 1 → Action :=
  fun q _ => if q.1 = 0 then alpha else beta

theorem budget_two_one :
    ContextMessageBudget available admissible 2 1 := by
  refine ⟨summaryTwo, ?_⟩
  refine ⟨encodeOne, decodeTwoOne, ?_, ?_⟩
  · intro q m
    trivial
  · intro k x
    cases k <;> simp [summaryTwo, encodeOne, decodeTwoOne, admissible]

/-- One summary symbol, two local messages: the message itself now carries the
    A/B distinction. -/
def summaryOne : Context → Fin 1 :=
  fun _ => 0

def encodeTwo : Context → Unit → Fin 2
  | a0, _ => 0
  | a1, _ => 0
  | b0, _ => 1
  | b1, _ => 1

def decodeOneTwo : Fin 1 → Fin 2 → Action :=
  fun _ m => if m.1 = 0 then alpha else beta

theorem budget_one_two :
    ContextMessageBudget available admissible 1 2 := by
  refine ⟨summaryOne, ?_⟩
  refine ⟨encodeTwo, decodeOneTwo, ?_, ?_⟩
  · intro q m
    trivial
  · intro k x
    cases k <;> simp [summaryOne, encodeTwo, decodeOneTwo, admissible]

/-- One summary symbol and one local message cannot distinguish A-contexts from
    B-contexts, so no single decoded action can certify all contexts. -/
theorem budget_one_one_impossible :
    ¬ ContextMessageBudget available admissible 1 1 := by
  rintro ⟨summary, encode, decode, havail, hcert⟩
  have hq : summary a0 = summary b0 := Subsingleton.elim _ _
  have hm : encode a0 () = encode b0 () := Subsingleton.elim _ _
  have hA := hcert a0 ()
  have hB := hcert b0 ()
  have hdec :
      decode (summary a0) (encode a0 ()) =
        decode (summary b0) (encode b0 ()) := by
    rw [hq, hm]
  rw [← hdec] at hB
  cases hact : decode (summary a0) (encode a0 ()) with
  | alpha =>
      simpa [admissible, hact] using hB
  | beta =>
      simpa [admissible, hact] using hA

/-- The two feasible budget points are incomparable in the coordinatewise
    resource order. -/
theorem budget_points_incomparable :
    ¬ ContextMessageLe (2, 1) (1, 2) ∧
    ¬ ContextMessageLe (1, 2) (2, 1) := by
  constructor
  · intro h
    exact (Nat.not_succ_le_self 1) h.1
  · intro h
    exact (Nat.not_succ_le_self 1) h.2

/-- Exact finite witness of a non-scalar context/message tradeoff:
    (2,1) is feasible, (1,2) is feasible, but their common lower-left point
    (1,1) is infeasible. -/
theorem strict_context_message_tradeoff :
    ContextMessageBudget available admissible 2 1 ∧
    ContextMessageBudget available admissible 1 2 ∧
    ¬ ContextMessageBudget available admissible 1 1 ∧
    (¬ ContextMessageLe (2, 1) (1, 2) ∧
     ¬ ContextMessageLe (1, 2) (2, 1)) := by
  exact
    ⟨budget_two_one,
     budget_one_two,
     budget_one_one_impossible,
     budget_points_incomparable⟩

end ContextMessageTradeoffWitness

end InsacermoV13Kernel
