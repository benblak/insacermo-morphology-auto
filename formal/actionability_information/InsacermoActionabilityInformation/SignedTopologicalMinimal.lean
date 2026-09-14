import InsacermoActionabilityInformation.SignedTopologicalDepthExact

namespace InsacermoActionabilityInformation

open SimpleGraph

namespace SignedGraph

variable {V : Type*} (SG : SignedGraph V)

/-- The distinct finite edge set of a walk, packaged noncomputably so theorem
statements do not require an artificial global `DecidableEq V` assumption. -/
noncomputable def cycleEdgeFinset {u v : V} (p : SG.graph.Walk u v) : Finset (Sym2 V) := by
  classical
  exact p.edges.toFinset

@[simp]
theorem mem_cycleEdgeFinset {u v : V} (p : SG.graph.Walk u v) (e : Sym2 V) :
    e ∈ SG.cycleEdgeFinset p ↔ e ∈ p.edges := by
  classical
  simp [cycleEdgeFinset]

/-- Every finite simple signed path is satisfiable.  Starting from the tail,
we assign the new endpoint exactly the Boolean value forced by the new edge.
Path simplicity guarantees that this endpoint does not occur later, so no
previously satisfied constraint is disturbed. -/
theorem pathEdgeFinset_satisfiable {u v : V} (p : SG.graph.Walk u v)
    (hp : p.IsPath) :
    ∃ x : V → Bool, SG.SatisfiesOn (SG.cycleEdgeFinset p : Set (Sym2 V)) x := by
  induction p with
  | nil =>
      refine ⟨fun _ => false, ?_⟩
      intro a b hab hmem
      have : s(a, b) ∈ (SimpleGraph.Walk.nil : SG.graph.Walk u u).edges :=
        (SG.mem_cycleEdgeFinset _ _).mp hmem
      simp at this
  | @cons u v w huv p ih =>
      have hpdata : p.IsPath ∧ u ∉ p.support :=
        (SimpleGraph.Walk.cons_isPath_iff huv p).mp hp
      rcases ih hpdata.1 with ⟨x, hx⟩
      let y : V → Bool := fun z =>
        if z = u then Bool.xor (SG.sign s(u, v)) (x v) else x z
      refine ⟨y, ?_⟩
      intro a b hab hmem
      have hlist : s(a, b) ∈ (SimpleGraph.Walk.cons huv p).edges :=
        (SG.mem_cycleEdgeFinset _ _).mp hmem
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at hlist
      rcases hlist with hhead | htail
      · rw [Sym2.mk_eq_mk_iff] at hhead
        rcases hhead with hsame | hswap
        · have ha : a = u := congrArg Prod.fst hsame
          have hb : b = v := congrArg Prod.snd hsame
          subst a
          subst b
          simp [y, huv.ne, Bool.xor_assoc]
        · have ha : a = v := congrArg Prod.fst hswap
          have hb : b = u := congrArg Prod.snd hswap
          subst a
          subst b
          simp [y, huv.ne, Bool.xor_assoc, Bool.xor_comm]
      · have hau : a ≠ u := by
          intro hau
          subst a
          exact hpdata.2 (p.fst_mem_support_of_mem_edges htail)
        have hbu : b ≠ u := by
          intro hbu
          subst b
          exact hpdata.2 (p.snd_mem_support_of_mem_edges htail)
        have htailmem : s(a, b) ∈ SG.cycleEdgeFinset p :=
          (SG.mem_cycleEdgeFinset p s(a, b)).2 htail
        have hsat := hx hab htailmem
        simpa [y, hau, hbu] using hsat

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
      SG.IsUnbalancedCycle p ∧ SG.cycleEdgeFinset p = F := by
  classical
  rcases (SG.selected_unsat_iff_exists_unbalanced_cycle (F : Set (Sym2 V))).mp hmin.1 with
    ⟨u, p, hp, hF⟩
  let C : Finset (Sym2 V) := SG.cycleEdgeFinset p
  have hsubset : C ⊆ F := by
    intro e he
    have helist : e ∈ p.edges := (SG.mem_cycleEdgeFinset p e).mp (by simpa [C] using he)
    exact hF e helist
  have hCunsat : ¬ ∃ x : V → Bool, SG.SatisfiesOn (C : Set (Sym2 V)) x := by
    exact SG.unbalancedClosedWalk_blocks_selected_edges
      (F := (C : Set (Sym2 V)))
      (p := p)
      (by
        intro e he
        have : e ∈ SG.cycleEdgeFinset p := (SG.mem_cycleEdgeFinset p e).2 he
        simpa [C] using this)
      hp.2
  have hEq : C = F := by
    by_contra hne
    have hproper : C ⊂ F := Finset.ssubset_iff_subset_ne.2 ⟨hsubset, hne⟩
    rcases hmin.2 C hproper with ⟨x, hx⟩
    exact hCunsat ⟨x, hx⟩
  exact ⟨u, p, hp, by simpa [C] using hEq⟩

end SignedGraph

end InsacermoActionabilityInformation
