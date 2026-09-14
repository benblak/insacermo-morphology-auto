import InsacermoActionabilityInformation.SignedTopologicalDepth

namespace InsacermoActionabilityInformation

open SimpleGraph

namespace SignedGraph

variable {V : Type*} (SG : SignedGraph V)

/-- Restrict a signed graph to a selected family of unordered edges.  Edges not
already present in the underlying graph are ignored. -/
def restrictEdges (F : Set (Sym2 V)) : SignedGraph V where
  graph := SG.graph ⊓ SimpleGraph.fromEdgeSet F
  sign := SG.sign

@[simp]
theorem restrictEdges_sign (F : Set (Sym2 V)) (e : Sym2 V) :
    (SG.restrictEdges F).sign e = SG.sign e := rfl

/-- The restricted graph contains exactly the original edges selected by `F`. -/
theorem restrictEdges_adj_iff {F : Set (Sym2 V)} {u v : V} :
    (SG.restrictEdges F).graph.Adj u v ↔
      SG.graph.Adj u v ∧ s(u, v) ∈ F := by
  change (SG.graph.Adj u v ∧ (s(u, v) ∈ F ∧ u ≠ v)) ↔
    SG.graph.Adj u v ∧ s(u, v) ∈ F
  constructor
  · rintro ⟨hG, hF, _⟩
    exact ⟨hG, hF⟩
  · rintro ⟨hG, hF⟩
    exact ⟨hG, hF, hG.ne⟩

/-- Restricting the graph does not change the selected-edge satisfaction
problem: global satisfiability of the restricted signed graph is exactly
satisfiability of the selected subcontract in the original graph. -/
theorem restrictEdges_satisfiable_iff (F : Set (Sym2 V)) :
    (SG.restrictEdges F).Satisfiable ↔
      ∃ x : V → Bool, SG.SatisfiesOn F x := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro u v huv hF
    have hAdj : (SG.restrictEdges F).graph.Adj u v :=
      (SG.restrictEdges_adj_iff).2 ⟨huv, hF⟩
    have hEdge : s(u, v) ∈ (SG.restrictEdges F).graph.edgeSet := by
      simpa only [SimpleGraph.mem_edgeSet] using hAdj
    exact hx hAdj hEdge
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro u v huv _
    rcases (SG.restrictEdges_adj_iff).1 huv with ⟨hG, hF⟩
    exact hx hG hF

/-- The restricted underlying graph is a subgraph of the original one. -/
theorem restrictEdges_graph_le (F : Set (Sym2 V)) :
    (SG.restrictEdges F).graph ≤ SG.graph := by
  exact inf_le_left

/-- Transferring a restricted walk back to the original graph preserves its
signed parity because the edge list and sign function are unchanged. -/
theorem walkParity_transfer_restrictEdges
    {F : Set (Sym2 V)} {u v : V}
    (p : (SG.restrictEdges F).graph.Walk u v)
    (hp : ∀ e, e ∈ p.edges → e ∈ SG.graph.edgeSet) :
    SG.walkParity (p.transfer SG.graph hp) =
      (SG.restrictEdges F).walkParity p := by
  simp [walkParity, restrictEdges]

/-- Exact selected-subcontract theorem.  A selected edge family is
unsatisfiable exactly when it contains all edges of an unbalanced cycle of the
original signed graph. -/
theorem selected_unsat_iff_exists_unbalanced_cycle (F : Set (Sym2 V)) :
    (¬ ∃ x : V → Bool, SG.SatisfiesOn F x) ↔
      ∃ u : V, ∃ p : SG.graph.Walk u u,
        SG.IsUnbalancedCycle p ∧
          ∀ e, e ∈ p.edges → e ∈ F := by
  constructor
  · intro hunsat
    have hrestricted : ¬ (SG.restrictEdges F).Satisfiable := by
      intro hsat
      exact hunsat ((SG.restrictEdges_satisfiable_iff F).mp hsat)
    rcases ((SG.restrictEdges F).not_satisfiable_iff_exists_unbalanced_cycle.mp hrestricted) with
      ⟨u, q, hqcycle, hqun⟩
    have hle : (SG.restrictEdges F).graph ≤ SG.graph := SG.restrictEdges_graph_le F
    have hedges : ∀ e, e ∈ q.edges → e ∈ SG.graph.edgeSet := by
      intro e he
      exact SimpleGraph.edgeSet_mono hle (q.edges_subset_edgeSet he)
    let p : SG.graph.Walk u u := q.transfer SG.graph hedges
    refine ⟨u, p, ?_, ?_⟩
    · refine ⟨hqcycle.transfer hedges, ?_⟩
      unfold IsUnbalancedClosedWalk at hqun ⊢
      simpa [p, SG.walkParity_transfer_restrictEdges q hedges] using hqun
    · intro e he
      have heq : e ∈ q.edges := by
        simpa [p] using he
      have her : e ∈ (SG.restrictEdges F).graph.edgeSet :=
        q.edges_subset_edgeSet heq
      change e ∈ (SG.graph ⊓ SimpleGraph.fromEdgeSet F).edgeSet at her
      rw [SimpleGraph.edgeSet_inf, SimpleGraph.edgeSet_fromEdgeSet] at her
      exact her.2.1
  · rintro ⟨u, p, hp, hF⟩
    exact SG.unbalancedClosedWalk_blocks_selected_edges hF hp.2

end SignedGraph

end InsacermoActionabilityInformation
