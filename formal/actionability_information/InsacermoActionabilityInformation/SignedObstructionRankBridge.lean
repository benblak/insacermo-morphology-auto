import InsacermoActionabilityInformation.ObstructionRankLocalAudit
import InsacermoActionabilityInformation.SignedTopologicalMinimal

namespace InsacermoActionabilityInformation

open SimpleGraph

namespace SignedGraph

variable {V : Type*} (SG : SignedGraph V)

/-- The abstract finite-contract satisfiability predicate instantiated by a
selected signed-XOR edge family. -/
def signedSubcontractSat (F : Finset (Sym2 V)) : Prop :=
  ∃ x : V → Bool, SG.SatisfiesOn (F : Set (Sym2 V)) x

/-- The signed notion of inclusion-minimal UNSAT is literally the generic
finite-contract notion instantiated by `signedSubcontractSat`. -/
theorem isMinimalUnsat_iff_abstract
    {F : Finset (Sym2 V)} :
    SG.IsMinimalUnsat F ↔
      FiniteContractAudit.IsMinimalUnsat SG.signedSubcontractSat F := by
  rfl

/-- Exact structural bridge for obstruction rank in signed XOR.

Unlike `topologicalDepth`, which is the *least* size of an UNSAT subcontract,
this rank bounds *every* atomic contradiction.  Because the atomic
contradictions are exactly unbalanced simple cycles, obstruction rank at most
`k` is equivalent to every unbalanced cycle having length at most `k`. -/
theorem obstructionRankAtMost_iff_all_unbalancedCycles_length_le
    [DecidableEq V] (k : ℕ) :
    FiniteContractAudit.ObstructionRankAtMost SG.signedSubcontractSat k ↔
      ∀ {u : V} (p : SG.graph.Walk u u),
        SG.IsUnbalancedCycle p → p.length ≤ k := by
  classical
  constructor
  · intro hrank u p hp
    have hminSigned : SG.IsMinimalUnsat (SG.cycleEdgeFinset p) :=
      SG.unbalancedCycleEdges_isMinimalUnsat hp
    have hminAbstract :
        FiniteContractAudit.IsMinimalUnsat SG.signedSubcontractSat
          (SG.cycleEdgeFinset p) :=
      (SG.isMinimalUnsat_iff_abstract).mp hminSigned
    have hcard := hrank (SG.cycleEdgeFinset p) hminAbstract
    have hnodup : p.edges.Nodup := hp.1.isTrail.edges_nodup
    calc
      p.length = p.edges.length := by symm; exact p.length_edges
      _ = (SG.cycleEdgeFinset p).card := by
        simp [cycleEdgeFinset, List.toFinset_card_of_nodup hnodup]
      _ ≤ k := hcard
  · intro hcycles F hminAbstract
    have hminSigned : SG.IsMinimalUnsat F :=
      (SG.isMinimalUnsat_iff_abstract).mpr hminAbstract
    rcases SG.minimalUnsat_eq_unbalancedCycleEdges hminSigned with
      ⟨u, p, hp, hEq⟩
    have hlen : p.length ≤ k := hcycles p hp
    rw [← hEq]
    have hnodup : p.edges.Nodup := hp.1.isTrail.edges_nodup
    calc
      (SG.cycleEdgeFinset p).card = p.edges.length := by
        simp [cycleEdgeFinset, List.toFinset_card_of_nodup hnodup]
      _ = p.length := p.length_edges
      _ ≤ k := hlen

/-- Signed-XOR local-audit theorem.  Checking every selected edge subcontract
through size `k` is globally complete exactly when every atomic signed
contradiction (equivalently every unbalanced cycle) has length at most `k`. -/
theorem localAuditComplete_iff_all_unbalancedCycles_length_le
    [DecidableEq V] (k : ℕ) :
    FiniteContractAudit.LocalAuditComplete SG.signedSubcontractSat k ↔
      ∀ {u : V} (p : SG.graph.Walk u u),
        SG.IsUnbalancedCycle p → p.length ≤ k := by
  calc
    FiniteContractAudit.LocalAuditComplete SG.signedSubcontractSat k ↔
        FiniteContractAudit.ObstructionRankAtMost SG.signedSubcontractSat k :=
      (FiniteContractAudit.obstructionRankAtMost_iff_localAuditComplete
        SG.signedSubcontractSat k).symm
    _ ↔ ∀ {u : V} (p : SG.graph.Walk u u),
          SG.IsUnbalancedCycle p → p.length ≤ k :=
      SG.obstructionRankAtMost_iff_all_unbalancedCycles_length_le k

end SignedGraph

end InsacermoActionabilityInformation
