import InsacermoActionabilityInformation.SignedTopologicalSubcontracts

namespace InsacermoActionabilityInformation

open SimpleGraph

namespace SignedGraph

variable {V : Type*} (SG : SignedGraph V)

/-- There is an unsatisfiable finite subcontract using at most `n` selected
edges.  This is the bounded form of INSACERMO topological obstruction depth. -/
def HasUnsatSubcontractAtMost (n : ℕ) : Prop :=
  ∃ F : Finset (Sym2 V),
    F.card ≤ n ∧
      ¬ ∃ x : V → Bool, SG.SatisfiesOn (F : Set (Sym2 V)) x

/-- There is an unbalanced cycle of length at most `n`. -/
def HasUnbalancedCycleAtMost (n : ℕ) : Prop :=
  ∃ u : V, ∃ p : SG.graph.Walk u u,
    SG.IsUnbalancedCycle p ∧ p.length ≤ n

/-- Every bounded unbalanced cycle yields an unsatisfiable subcontract of no
larger cardinality: simply select its distinct edges. -/
theorem hasUnbalancedCycleAtMost_implies_hasUnsatSubcontractAtMost
    {n : ℕ} (h : SG.HasUnbalancedCycleAtMost n) :
    SG.HasUnsatSubcontractAtMost n := by
  classical
  rcases h with ⟨u, p, hp, hlen⟩
  let F : Finset (Sym2 V) := p.edges.toFinset
  refine ⟨F, ?_, ?_⟩
  · have hnodup : p.edges.Nodup := hp.1.isTrail.edges_nodup
    calc
      F.card = p.edges.length := by
        simp [F, List.toFinset_card_of_nodup hnodup]
      _ = p.length := p.length_edges
      _ ≤ n := hlen
  · intro hsat
    exact SG.unbalancedClosedWalk_blocks_selected_edges
      (F := (F : Set (Sym2 V)))
      (p := p)
      (by
        intro e he
        simpa [F] using he)
      hp.2 hsat

/-- Conversely, every bounded unsatisfiable finite subcontract contains an
unbalanced cycle whose length is at most the subcontract cardinality. -/
theorem hasUnsatSubcontractAtMost_implies_hasUnbalancedCycleAtMost
    {n : ℕ} (h : SG.HasUnsatSubcontractAtMost n) :
    SG.HasUnbalancedCycleAtMost n := by
  classical
  rcases h with ⟨F, hcard, hunsat⟩
  rcases (SG.selected_unsat_iff_exists_unbalanced_cycle (F : Set (Sym2 V))).mp hunsat with
    ⟨u, p, hp, hF⟩
  refine ⟨u, p, hp, ?_⟩
  have hnodup : p.edges.Nodup := hp.1.isTrail.edges_nodup
  have hsubset : p.edges.toFinset ⊆ F := by
    intro e he
    have helist : e ∈ p.edges := by simpa using he
    exact hF e helist
  calc
    p.length = p.edges.length := by symm; exact p.length_edges
    _ = p.edges.toFinset.card := by
      symm
      exact List.toFinset_card_of_nodup hnodup
    _ ≤ F.card := Finset.card_le_card hsubset
    _ ≤ n := hcard

/-- Exact bounded-depth theorem: inspecting all subcontracts up to cardinality
`n` detects inconsistency exactly when an unbalanced cycle of length at most
`n` exists. -/
theorem hasUnsatSubcontractAtMost_iff_hasUnbalancedCycleAtMost (n : ℕ) :
    SG.HasUnsatSubcontractAtMost n ↔ SG.HasUnbalancedCycleAtMost n := by
  constructor
  · exact SG.hasUnsatSubcontractAtMost_implies_hasUnbalancedCycleAtMost
  · exact SG.hasUnbalancedCycleAtMost_implies_hasUnsatSubcontractAtMost

/-- Existence of some finite UNSAT subcontract is equivalent to existence of
an unbalanced cycle. -/
theorem exists_hasUnsatSubcontractAtMost_iff_exists_hasUnbalancedCycleAtMost :
    (∃ n, SG.HasUnsatSubcontractAtMost n) ↔
      ∃ n, SG.HasUnbalancedCycleAtMost n := by
  constructor <;> rintro ⟨n, hn⟩ <;>
    exact ⟨n, (SG.hasUnsatSubcontractAtMost_iff_hasUnbalancedCycleAtMost n).mp hn⟩

/-- When an obstruction exists, the least UNSAT subcontract cardinality is
exactly the least unbalanced-cycle length.  This is the formal finite version
of `κ_top = g_-`. -/
theorem topologicalDepth_eq_unbalancedGirth
    (hU : ∃ n, SG.HasUnsatSubcontractAtMost n) :
    Nat.find hU =
      Nat.find ((SG.exists_hasUnsatSubcontractAtMost_iff_exists_hasUnbalancedCycleAtMost).mp hU) := by
  let hC := (SG.exists_hasUnsatSubcontractAtMost_iff_exists_hasUnbalancedCycleAtMost).mp hU
  apply le_antisymm
  · have hspecC : SG.HasUnbalancedCycleAtMost (Nat.find hC) := Nat.find_spec hC
    have hspecU : SG.HasUnsatSubcontractAtMost (Nat.find hC) :=
      (SG.hasUnsatSubcontractAtMost_iff_hasUnbalancedCycleAtMost (Nat.find hC)).mpr hspecC
    exact Nat.find_min' hU hspecU
  · have hspecU : SG.HasUnsatSubcontractAtMost (Nat.find hU) := Nat.find_spec hU
    have hspecC : SG.HasUnbalancedCycleAtMost (Nat.find hU) :=
      (SG.hasUnsatSubcontractAtMost_iff_hasUnbalancedCycleAtMost (Nat.find hU)).mp hspecU
    exact Nat.find_min' hC hspecC

end SignedGraph

end InsacermoActionabilityInformation
