import InsacermoV13Kernel.ContextMessageFrontier

namespace InsacermoV13Kernel

universe uK uW uA uK₁ uK₂ uW₁ uW₂ uA₁ uA₂ uQ₁ uQ₂ uM₁ uM₂

/-- Canonical embedding of a finite alphabet into any larger finite alphabet. -/
def FinEmbed {n n' : Nat} (h : n ≤ n') : Fin n → Fin n' :=
  fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 h⟩

theorem contextMessageLe_refl (p : Nat × Nat) :
    ContextMessageLe p p := by
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem contextMessageLe_trans
    {p q r : Nat × Nat}
    (hpq : ContextMessageLe p q)
    (hqr : ContextMessageLe q r) :
    ContextMessageLe p r := by
  exact
    ⟨Nat.le_trans hpq.1 hqr.1,
     Nat.le_trans hpq.2 hqr.2⟩

/-- The finite context/message feasibility region is upward closed whenever
    both context and local-world spaces are inhabited. Enlarging either
    alphabet cannot destroy a previously certified protocol. -/
theorem contextMessageBudget_upward
    {K : Type uK} {World : Type uW} {Action : Type uA}
    [Nonempty K] [Nonempty World]
    {available : Action → Prop}
    {admissible : K → World → Action → Prop}
    {q m q' m' : Nat}
    (hbudget : ContextMessageBudget available admissible q m)
    (hq : q ≤ q')
    (hm : m ≤ m') :
    ContextMessageBudget available admissible q' m' := by
  classical
  rcases hbudget with
    ⟨summary, encode, decode, havail, hcert⟩
  let k₀ : K := Classical.choice (inferInstance : Nonempty K)
  let x₀ : World := Classical.choice (inferInstance : Nonempty World)
  let q₀ : Fin q := summary k₀
  let m₀ : Fin m := encode k₀ x₀
  let fallback : Action := decode q₀ m₀
  let summary' : K → Fin q' :=
    fun k => FinEmbed hq (summary k)
  let encode' : K → World → Fin m' :=
    fun k x => FinEmbed hm (encode k x)
  let decode' : Fin q' → Fin m' → Action :=
    fun qi mi =>
      if hqi : qi.1 < q then
        if hmi : mi.1 < m then
          decode ⟨qi.1, hqi⟩ ⟨mi.1, hmi⟩
        else fallback
      else fallback
  refine ⟨summary', encode', decode', ?_, ?_⟩
  · intro qi mi
    dsimp [decode']
    split
    · rename_i hqi
      split
      · rename_i hmi
        exact havail ⟨qi.1, hqi⟩ ⟨mi.1, hmi⟩
      · exact havail q₀ m₀
    · exact havail q₀ m₀
  · intro k x
    dsimp [summary', encode', decode', FinEmbed]
    simp [(summary k).2, (encode k x).2]
    exact hcert k x

/-- Therefore the joint context/message feasibility predicate is an upper set
    in the coordinatewise resource order. -/
theorem contextMessageBudget_upperClosed
    {K : Type uK} {World : Type uW} {Action : Type uA}
    [Nonempty K] [Nonempty World]
    {available : Action → Prop}
    {admissible : K → World → Action → Prop} :
    UpperClosed
      (fun p : Nat × Nat =>
        ContextMessageBudget available admissible p.1 p.2)
      ContextMessageLe := by
  intro p r hp hpr
  exact contextMessageBudget_upward hp hpr.1 hpr.2

/-- Capability expansion preserves every point of the context/message
    feasibility region. -/
theorem contextMessageBudget_of_capability_expansion
    {K : Type uK} {World : Type uW} {Action : Type uA}
    {available₁ available₂ : Action → Prop}
    {admissible : K → World → Action → Prop}
    {q m : Nat}
    (hcap : ∀ ⦃a : Action⦄, available₁ a → available₂ a)
    (hbudget : ContextMessageBudget available₁ admissible q m) :
    ContextMessageBudget available₂ admissible q m := by
  rcases hbudget with
    ⟨summary, encode, decode, havail, hcert⟩
  exact
    ⟨summary, encode, decode,
     (fun qv mv => hcap (havail qv mv)),
     hcert⟩

/-- Contract weakening also preserves every feasible budget point. -/
theorem contextMessageBudget_of_contract_weakening
    {K : Type uK} {World : Type uW} {Action : Type uA}
    {available : Action → Prop}
    {strong weak : K → World → Action → Prop}
    {q m : Nat}
    (hcontract : ∀ ⦃k : K⦄ ⦃x : World⦄ ⦃a : Action⦄,
      strong k x a → weak k x a)
    (hbudget : ContextMessageBudget available strong q m) :
    ContextMessageBudget available weak q m := by
  rcases hbudget with
    ⟨summary, encode, decode, havail, hcert⟩
  refine ⟨summary, encode, decode, havail, ?_⟩
  intro k x
  exact hcontract (hcert k x)

/-- Pareto-minimal context/message budget: feasible, and no feasible budget
    weakly below it is strictly better in either coordinate. -/
def ParetoMinimalContextMessageBudget
    {K : Type uK} {World : Type uW} {Action : Type uA}
    (available : Action → Prop)
    (admissible : K → World → Action → Prop)
    (p : Nat × Nat) : Prop :=
  ContextMessageBudget available admissible p.1 p.2 ∧
    ∀ ⦃r : Nat × Nat⦄,
      ContextMessageBudget available admissible r.1 r.2 →
      ContextMessageLe r p →
      ContextMessageLe p r

/-- Pareto-minimal points form an antichain modulo equality of resource
    coordinates. -/
theorem paretoMinimal_contextMessage_antichain
    {K : Type uK} {World : Type uW} {Action : Type uA}
    {available : Action → Prop}
    {admissible : K → World → Action → Prop}
    {p r : Nat × Nat}
    (hp : ParetoMinimalContextMessageBudget available admissible p)
    (hr : ParetoMinimalContextMessageBudget available admissible r)
    (hpr : ContextMessageLe p r) :
    ContextMessageLe r p := by
  exact hr.2 hp.1 hpr

/-- Product admissibility for two context-indexed subsystems. -/
def ProductContextAdmissible
    {K₁ : Type uK₁} {K₂ : Type uK₂}
    {World₁ : Type uW₁} {World₂ : Type uW₂}
    {Action₁ : Type uA₁} {Action₂ : Type uA₂}
    (admissible₁ : K₁ → World₁ → Action₁ → Prop)
    (admissible₂ : K₂ → World₂ → Action₂ → Prop) :
    (K₁ × K₂) → (World₁ × World₂) → (Action₁ × Action₂) → Prop :=
  fun k x a =>
    admissible₁ k.1 x.1 a.1 ∧
      admissible₂ k.2 x.2 a.2

/-- Typed product composition of summary/message protocols.
    Independent systems combine by pairing context summaries and messages. -/
theorem summaryCertifiedProtocol_product
    {K₁ : Type uK₁} {K₂ : Type uK₂}
    {World₁ : Type uW₁} {World₂ : Type uW₂}
    {Action₁ : Type uA₁} {Action₂ : Type uA₂}
    {Q₁ : Type uQ₁} {Q₂ : Type uQ₂}
    {Message₁ : Type uM₁} {Message₂ : Type uM₂}
    {summary₁ : K₁ → Q₁} {summary₂ : K₂ → Q₂}
    {available₁ : Action₁ → Prop}
    {available₂ : Action₂ → Prop}
    {admissible₁ : K₁ → World₁ → Action₁ → Prop}
    {admissible₂ : K₂ → World₂ → Action₂ → Prop}
    (h₁ :
      SummaryCertifiedProtocol Message₁ summary₁
        available₁ admissible₁)
    (h₂ :
      SummaryCertifiedProtocol Message₂ summary₂
        available₂ admissible₂) :
    SummaryCertifiedProtocol
      (Message₁ × Message₂)
      (fun k : K₁ × K₂ => (summary₁ k.1, summary₂ k.2))
      (ProductAvailable available₁ available₂)
      (ProductContextAdmissible admissible₁ admissible₂) := by
  rcases h₁ with ⟨encode₁, decode₁, havail₁, hcert₁⟩
  rcases h₂ with ⟨encode₂, decode₂, havail₂, hcert₂⟩
  refine
    ⟨(fun k x => (encode₁ k.1 x.1, encode₂ k.2 x.2)),
     (fun q m => (decode₁ q.1 m.1, decode₂ q.2 m.2)),
     ?_,
     ?_⟩
  · intro q m
    exact
      ⟨havail₁ q.1 m.1,
       havail₂ q.2 m.2⟩
  · intro k x
    exact
      ⟨hcert₁ k.1 x.1,
       hcert₂ k.2 x.2⟩

namespace ContextMessageParetoWitness

open ContextMessageTradeoffWitness

/-- No inhabited context can be summarized into zero symbols. -/
theorem no_zero_summary_budget (m : Nat) :
    ¬ ContextMessageBudget available admissible 0 m := by
  rintro ⟨summary, hprotocol⟩
  exact Fin.elim0 (summary ContextMessageTradeoffWitness.Context.a0)

/-- With an inhabited local world, zero local messages are impossible. -/
theorem no_zero_message_budget (q : Nat) :
    ¬ ContextMessageBudget available admissible q 0 := by
  rintro ⟨summary, encode, decode, havail, hcert⟩
  exact Fin.elim0 (encode ContextMessageTradeoffWitness.Context.a0 ())

/-- (2,1) is not only feasible but Pareto-minimal. -/
theorem budget_two_one_pareto :
    ParetoMinimalContextMessageBudget available admissible (2, 1) := by
  refine ⟨budget_two_one, ?_⟩
  intro r hr hle
  rcases r with ⟨q, m⟩
  change ContextMessageLe (2, 1) (q, m)
  have hq : q ≤ 2 := hle.1
  have hm : m ≤ 1 := hle.2
  cases q with
  | zero =>
      exact False.elim (no_zero_summary_budget m hr)
  | succ q₁ =>
      cases q₁ with
      | zero =>
          cases m with
          | zero =>
              exact False.elim (no_zero_message_budget 1 hr)
          | succ m₁ =>
              cases m₁ with
              | zero =>
                  exact False.elim (budget_one_one_impossible hr)
              | succ m₂ =>
                  have : False := by simpa using hm
                  exact this.elim
      | succ q₂ =>
          cases q₂ with
          | zero =>
              cases m with
              | zero =>
                  exact False.elim (no_zero_message_budget 2 hr)
              | succ m₁ =>
                  cases m₁ with
                  | zero =>
                      exact contextMessageLe_refl (2, 1)
                  | succ m₂ =>
                      have : False := by simpa using hm
                      exact this.elim
          | succ q₃ =>
              have : False := by simpa using hq
              exact this.elim

/-- (1,2) is also Pareto-minimal. -/
theorem budget_one_two_pareto :
    ParetoMinimalContextMessageBudget available admissible (1, 2) := by
  refine ⟨budget_one_two, ?_⟩
  intro r hr hle
  rcases r with ⟨q, m⟩
  change ContextMessageLe (1, 2) (q, m)
  have hq : q ≤ 1 := hle.1
  have hm : m ≤ 2 := hle.2
  cases q with
  | zero =>
      exact False.elim (no_zero_summary_budget m hr)
  | succ q₁ =>
      cases q₁ with
      | zero =>
          cases m with
          | zero =>
              exact False.elim (no_zero_message_budget 1 hr)
          | succ m₁ =>
              cases m₁ with
              | zero =>
                  exact False.elim (budget_one_one_impossible hr)
              | succ m₂ =>
                  cases m₂ with
                  | zero =>
                      exact contextMessageLe_refl (1, 2)
                  | succ m₃ =>
                      have : False := by simpa using hm
                      exact this.elim
      | succ q₂ =>
          have : False := by simpa using hq
          exact this.elim

/-- The witness therefore has at least two distinct incomparable
    Pareto-minimal interface budgets. -/
theorem two_incomparable_pareto_minima :
    ParetoMinimalContextMessageBudget available admissible (2, 1) ∧
    ParetoMinimalContextMessageBudget available admissible (1, 2) ∧
    ¬ ContextMessageLe (2, 1) (1, 2) ∧
    ¬ ContextMessageLe (1, 2) (2, 1) := by
  exact
    ⟨budget_two_one_pareto,
     budget_one_two_pareto,
     budget_points_incomparable.1,
     budget_points_incomparable.2⟩

end ContextMessageParetoWitness

end InsacermoV13Kernel
