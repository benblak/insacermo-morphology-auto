import InsacermoV13Kernel.TreeContextCongruence

namespace InsacermoV13Kernel

universe uW uA uM uK

/-- Future-equivalence of two subtrees for a fixed protocol:
    every finite ancestor context sees the same root action and the same
    certification outcome after either subtree is plugged into the hole. -/
def TreeFutureEquivalent
    {World : Type uW} {Action : Type uA} {Message : Type uM}
    (available : Action → Prop)
    (admissible : World → ChildInterface Message → Action → Prop)
    (encode : World → ChildInterface Message → Message)
    (decode : Message → Action)
    (t₁ t₂ : CertTree World) : Prop :=
  ∀ ctx : TreeContext World,
    treeRootAction encode decode (plug ctx t₁) =
      treeRootAction encode decode (plug ctx t₂) ∧
    (TreeCertified available admissible encode decode (plug ctx t₁) ↔
      TreeCertified available admissible encode decode (plug ctx t₂))

theorem treeFutureEquivalent_refl
    {World : Type uW} {Action : Type uA} {Message : Type uM}
    {available : Action → Prop}
    {admissible : World → ChildInterface Message → Action → Prop}
    {encode : World → ChildInterface Message → Message}
    {decode : Message → Action}
    {t : CertTree World} :
    TreeFutureEquivalent available admissible encode decode t t := by
  intro ctx
  exact ⟨rfl, Iff.rfl⟩

theorem treeFutureEquivalent_symm
    {World : Type uW} {Action : Type uA} {Message : Type uM}
    {available : Action → Prop}
    {admissible : World → ChildInterface Message → Action → Prop}
    {encode : World → ChildInterface Message → Message}
    {decode : Message → Action}
    {t₁ t₂ : CertTree World}
    (h :
      TreeFutureEquivalent available admissible encode decode t₁ t₂) :
    TreeFutureEquivalent available admissible encode decode t₂ t₁ := by
  intro ctx
  rcases h ctx with ⟨ha, hc⟩
  exact ⟨ha.symm, hc.symm⟩

theorem treeFutureEquivalent_trans
    {World : Type uW} {Action : Type uA} {Message : Type uM}
    {available : Action → Prop}
    {admissible : World → ChildInterface Message → Action → Prop}
    {encode : World → ChildInterface Message → Message}
    {decode : Message → Action}
    {t₁ t₂ t₃ : CertTree World}
    (h₁₂ :
      TreeFutureEquivalent available admissible encode decode t₁ t₂)
    (h₂₃ :
      TreeFutureEquivalent available admissible encode decode t₂ t₃) :
    TreeFutureEquivalent available admissible encode decode t₁ t₃ := by
  intro ctx
  rcases h₁₂ ctx with ⟨ha12, hc12⟩
  rcases h₂₃ ctx with ⟨ha23, hc23⟩
  exact ⟨ha12.trans ha23, hc12.trans hc23⟩

/-- Equality of emitted interface messages is a sound future abstraction for
    certified subtrees: no finite ancestor context can distinguish them at the
    level of root action or whole-tree certification. -/
theorem treeMessage_eq_implies_futureEquivalent
    {World : Type uW} {Action : Type uA} {Message : Type uM}
    {available : Action → Prop}
    {admissible : World → ChildInterface Message → Action → Prop}
    {encode : World → ChildInterface Message → Message}
    {decode : Message → Action}
    {t₁ t₂ : CertTree World}
    (hmsg : treeMessage encode t₁ = treeMessage encode t₂)
    (ht₁ : TreeCertified available admissible encode decode t₁)
    (ht₂ : TreeCertified available admissible encode decode t₂) :
    TreeFutureEquivalent available admissible encode decode t₁ t₂ := by
  intro ctx
  exact
    ⟨treeRootAction_context_congruence hmsg ctx,
     treeCertified_context_equivalence hmsg ht₁ ht₂ ctx⟩

/-- A fixed interface-message map is future-sound when equal messages imply
    future-equivalence for all internally certified subtrees. -/
def FutureSoundTreeAbstraction
    {World : Type uW} {Action : Type uA} {Message : Type uM}
    (available : Action → Prop)
    (admissible : World → ChildInterface Message → Action → Prop)
    (encode : World → ChildInterface Message → Message)
    (decode : Message → Action) : Prop :=
  ∀ ⦃t₁ t₂ : CertTree World⦄,
    TreeCertified available admissible encode decode t₁ →
    TreeCertified available admissible encode decode t₂ →
    treeMessage encode t₁ = treeMessage encode t₂ →
    TreeFutureEquivalent available admissible encode decode t₁ t₂

theorem treeMessage_futureSound
    {World : Type uW} {Action : Type uA} {Message : Type uM}
    {available : Action → Prop}
    {admissible : World → ChildInterface Message → Action → Prop}
    {encode : World → ChildInterface Message → Message}
    {decode : Message → Action} :
    FutureSoundTreeAbstraction
      available admissible encode decode := by
  intro t₁ t₂ ht₁ ht₂ hmsg
  exact treeMessage_eq_implies_futureEquivalent hmsg ht₁ ht₂

/-- Closure theorem for the finite deterministic tree kernel.
    A single certified local rule induces:
      1. certification of every node of every finite tree;
      2. a future-sound interface abstraction for arbitrary finite ancestors.
    This is the local-to-global compositional closure of the current kernel. -/
theorem recursiveProtocol_totalClosure
    {World : Type uW} {Action : Type uA} {Message : Type uM}
    {available : Action → Prop}
    {admissible : World → ChildInterface Message → Action → Prop}
    (hlocal : RecursiveNodeProtocol Message available admissible) :
    ∃ encode : World → ChildInterface Message → Message,
      ∃ decode : Message → Action,
        (∀ t : CertTree World,
          TreeCertified available admissible encode decode t) ∧
        FutureSoundTreeAbstraction
          available admissible encode decode := by
  rcases recursiveTree_all_nodes_certified hlocal with
    ⟨encode, decode, hall⟩
  refine ⟨encode, decode, hall, ?_⟩
  intro t₁ t₂ ht₁ ht₂ hmsg
  exact treeMessage_eq_implies_futureEquivalent hmsg ht₁ ht₂

/-- Every feasible finite context/message budget produces an actual globally
    safe observation on the lifted context-world system. -/
theorem contextMessageBudget_globalSafe
    {K : Type uK} {World : Type uW} {Action : Type uA}
    {available : Action → Prop}
    {admissible : K → World → Action → Prop}
    {q m : Nat}
    (h : ContextMessageBudget available admissible q m) :
    ∃ obs : K × World → (Fin q × Fin m),
      GlobalSafe obs available (ContextLiftAdmissible admissible) := by
  have hprotocol :
      CertifiedProtocol
        available
        (ContextLiftAdmissible admissible)
        (Fin q × Fin m) :=
    contextMessageBudget_carries_pair h
  exact certifiedProtocol_globalSafe hprotocol

/-- Hence every Pareto-minimal context/message point is not merely an abstract
    resource point: it realizes a concrete globally safe observation. -/
theorem paretoMinimalBudget_realizes_globalSafe
    {K : Type uK} {World : Type uW} {Action : Type uA}
    {available : Action → Prop}
    {admissible : K → World → Action → Prop}
    {p : Nat × Nat}
    (hp :
      ParetoMinimalContextMessageBudget
        available admissible p) :
    ∃ obs : K × World → (Fin p.1 × Fin p.2),
      GlobalSafe obs available (ContextLiftAdmissible admissible) := by
  exact contextMessageBudget_globalSafe hp.1

namespace TotalClosureWitness

open RecursiveTreeWitness
open RecursiveTreeWitness.World

/-- Concrete closure witness: the explicit two-message local rule certifies
    every finite tree and its emitted message is future-sound under arbitrary
    ancestor replacement. -/
theorem recursive_witness_totalClosure :
    ∃ enc : World → ChildInterface (Fin 2) → Fin 2,
      ∃ dec : Fin 2 → Action,
        (∀ t : CertTree World,
          TreeCertified available admissible enc dec t) ∧
        FutureSoundTreeAbstraction
          available admissible enc dec := by
  exact recursiveProtocol_totalClosure local_rule_certified

/-- The earlier two Pareto-minimal interface budgets both realize GlobalSafe,
    while remaining incomparable. -/
theorem pareto_witness_both_realize_safe :
    (∃ obs :
        ContextMessageTradeoffWitness.Context × Unit →
          (Fin 2 × Fin 1),
      GlobalSafe
        obs
        ContextMessageTradeoffWitness.available
        (ContextLiftAdmissible
          ContextMessageTradeoffWitness.admissible)) ∧
    (∃ obs :
        ContextMessageTradeoffWitness.Context × Unit →
          (Fin 1 × Fin 2),
      GlobalSafe
        obs
        ContextMessageTradeoffWitness.available
        (ContextLiftAdmissible
          ContextMessageTradeoffWitness.admissible)) := by
  constructor
  · exact
      paretoMinimalBudget_realizes_globalSafe
        ContextMessageParetoWitness.budget_two_one_pareto
  · exact
      paretoMinimalBudget_realizes_globalSafe
        ContextMessageParetoWitness.budget_one_two_pareto

end TotalClosureWitness

end InsacermoV13Kernel
