import InsacermoActionabilityInformation.SignedTopologicalDepthExact

namespace InsacermoActionabilityInformation

open SimpleGraph

namespace SignedGraph

variable {V : Type*} (SG : SignedGraph V)

/-- A finite selected subcontract is inclusion-minimal UNSAT when it is
unsatisfiable but every strict selected subfamily is satisfiable. -/
def IsMinimalUnsat (F : Finset (Sym2 V)) : Prop :=
  (¬ ∃ x : V → Bool, SG.SatisfiesOn (F : Set (Sym2 V)) x) ∧
    ∀ G : Finset (Sym2 V), G ⊂ F →
      ∃ x : V → Bool, SG.SatisfiesOn (G : Set (Sym2 V)) x

/-- Every inclusion-minimal finite UNSAT subcontract is exactly the distinct
edge set of an unbalanced cycle.  This identifies the atomic topological
obstructions on the UNSAT side. -/
theorem minimalUnsat_eq_unbalancedCycleEdges
    {F : Finset (Sym2 V)} (hmin : SG.IsMinimalUnsat F) :
    ∃ u : V, ∃ p : SG.graph.Walk u u,
      SG.IsUnbalancedCycle p ∧ p.edges.toFinset = F := by
  classical
  rcases (SG.selected_unsat_iff_exists_unbalanced_cycle (F : Set (Sym2 V))).mp hmin.1 with
    ⟨u, p, hp, hF⟩
  let C : Finset (Sym2 V) := p.edges.toFinset
  have hsubset : C ⊆ F := by
    intro e he
    have helist : e ∈ p.edges := by simpa [C] using he
    exact hF e helist
  have hCunsat : ¬ ∃ x : V → Bool, SG.SatisfiesOn (C : Set (Sym2 V)) x := by
    exact SG.unbalancedClosedWalk_blocks_selected_edges
      (F := (C : Set (Sym2 V)))
      (p := p)
      (by
        intro e he
        simpa [C] using he)
      hp.2
  have hEq : C = F := by
    by_contra hne
    have hproper : C ⊂ F := Finset.ssubset_iff_subset_ne.2 ⟨hsubset, hne⟩
    rcases hmin.2 C hproper with ⟨x, hx⟩
    exact hCunsat ⟨x, hx⟩
  exact ⟨u, p, hp, hEq⟩

end SignedGraph

end InsacermoActionabilityInformation
