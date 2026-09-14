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
  classical
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
      · have hpair : (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
          simpa only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] using hhead
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [y, huv.ne, huv.ne.symm, Bool.xor_assoc]
        · simp [y, huv.ne, huv.ne.symm, Bool.xor_assoc, Bool.xor_comm, Sym2.eq_swap]
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
        have hsat : Bool.xor (x a) (x b) = SG.sign s(a, b) := hx hab htailmem
        have hya : y a = x a := by simp [y, hau]
        have hyb : y b = x b := by simp [y, hbu]
        rw [hya, hyb]
        exact hsat

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

/-- A strict selected subfamily of the edge set of a simple cycle is
satisfiable.  Choose a missing edge, rotate the cycle to one endpoint, and
open the cycle at that edge.  If the edge is the final edge in the chosen
orientation, reverse the cycle first. -/
theorem strictSubset_cycleEdgeFinset_satisfiable
    {u : V} {p : SG.graph.Walk u u} (hp : p.IsCycle)
    {G : Finset (Sym2 V)} (hG : G ⊂ SG.cycleEdgeFinset p) :
    ∃ x : V → Bool, SG.SatisfiesOn (G : Set (Sym2 V)) x := by
  classical
  have hproper := Finset.ssubset_iff_subset_ne.mp hG
  have hmissing : ∃ e : Sym2 V, e ∈ SG.cycleEdgeFinset p ∧ e ∉ G := by
    by_contra hno
    have hreverse : SG.cycleEdgeFinset p ⊆ G := by
      intro e he
      by_contra heg
      exact hno ⟨e, he, heg⟩
    exact hproper.2 (Finset.Subset.antisymm hproper.1 hreverse)
  rcases hmissing with ⟨e, heC, heG⟩
  revert heC heG
  refine Sym2.inductionOn e ?_
  intro a b heC heG
  have heP : s(a, b) ∈ p.edges := (SG.mem_cycleEdgeFinset p _).mp heC
  have ha : a ∈ p.support := p.fst_mem_support_of_mem_edges heP
  let r : SG.graph.Walk a a := p.rotate a ha
  have hr : r.IsCycle := by
    simpa [r] using hp.rotate ha
  have heR : s(a, b) ∈ r.edges := by
    have hrot := (p.rotate_edges a ha).mem_iff.mpr heP
    simpa [r] using hrot
  have edge_of_G_mem_r : ∀ e' ∈ G, e' ∈ r.edges := by
    intro e' he'
    have he'C : e' ∈ SG.cycleEdgeFinset p := hproper.1 he'
    have he'P : e' ∈ p.edges := (SG.mem_cycleEdgeFinset p _).mp he'C
    have hrot := (p.rotate_edges a ha).mem_iff.mpr he'P
    simpa [r] using hrot
  have sat_of_head :
      ∀ (q : SG.graph.Walk a a), q.IsCycle →
        (∀ e' ∈ G, e' ∈ q.edges) →
        s(a, q.snd) = s(a, b) →
        ∃ x : V → Bool, SG.SatisfiesOn (G : Set (Sym2 V)) x := by
    intro q hq hqG hqhead
    rcases SG.pathEdgeFinset_satisfiable q.tail hq.isPath_tail with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro c d hcd hcdG
    apply hx hcd
    apply (SG.mem_cycleEdgeFinset q.tail _).2
    have hmemq : s(c, d) ∈ q.edges := hqG _ hcdG
    rw [← SimpleGraph.Walk.cons_tail_eq q hq.not_nil,
      SimpleGraph.Walk.edges_cons, List.mem_cons] at hmemq
    rcases hmemq with hfirst | htail
    · exfalso
      apply heG
      have hcdG' := hcdG
      rw [hfirst, hqhead] at hcdG'
      exact hcdG'
    · exact htail
  by_cases hhead : s(a, r.snd) = s(a, b)
  · exact sat_of_head r hr edge_of_G_mem_r hhead
  · have heTail : s(a, b) ∈ r.tail.edges := by
      have heR' := heR
      rw [← SimpleGraph.Walk.cons_tail_eq r hr.not_nil,
        SimpleGraph.Walk.edges_cons, List.mem_cons] at heR'
      rcases heR' with hfirst | htail
      · exact (hhead hfirst.symm).elim
      · exact htail
    have htailNonNil : ¬ r.tail.Nil := by
      intro hnil
      have hedgeNil : r.tail.edges = [] := SimpleGraph.Walk.edges_eq_nil.mpr hnil
      rw [hedgeNil] at heTail
      simp at heTail
    have hbpenTail : b = r.tail.penultimate :=
      hr.isPath_tail.eq_penultimate_of_mem_edges heTail
    have hpenTail : r.tail.penultimate = r.penultimate := by
      change r.tail.getVert (r.tail.length - 1) = r.getVert (r.length - 1)
      rw [SimpleGraph.Walk.getVert_tail]
      have hlen : r.tail.length + 1 = r.length :=
        r.length_tail_add_one hr.not_nil
      have hpos : 0 < r.tail.length :=
        SimpleGraph.Walk.not_nil_iff_lt_length.mp htailNonNil
      congr 1
      omega
    have hbpen : b = r.penultimate := hbpenTail.trans hpenTail
    have hrrev : r.reverse.IsCycle := hr.reverse
    have edge_of_G_mem_rev : ∀ e' ∈ G, e' ∈ r.reverse.edges := by
      intro e' he'
      have hmem := edge_of_G_mem_r e' he'
      simpa using hmem
    have hrevHead : s(a, r.reverse.snd) = s(a, b) := by
      rw [SimpleGraph.Walk.snd_reverse, ← hbpen]
    exact sat_of_head r.reverse hrrev edge_of_G_mem_rev hrevHead

/-- The edge set of every unbalanced simple cycle is inclusion-minimal UNSAT. -/
theorem unbalancedCycleEdges_isMinimalUnsat
    {u : V} {p : SG.graph.Walk u u} (hp : SG.IsUnbalancedCycle p) :
    SG.IsMinimalUnsat (SG.cycleEdgeFinset p) := by
  classical
  constructor
  · exact SG.unbalancedClosedWalk_blocks_selected_edges
      (F := (SG.cycleEdgeFinset p : Set (Sym2 V)))
      (p := p)
      (by
        intro e he
        exact (SG.mem_cycleEdgeFinset p e).2 he)
      hp.2
  · intro G hG
    exact SG.strictSubset_cycleEdgeFinset_satisfiable hp.1 hG

/-- Atomic classification of finite signed-XOR contradictions: a selected
subcontract is inclusion-minimal UNSAT if and only if it is exactly the edge
set of an unbalanced simple cycle. -/
theorem minimalUnsat_iff_exists_unbalancedCycleEdges
    {F : Finset (Sym2 V)} :
    SG.IsMinimalUnsat F ↔
      ∃ u : V, ∃ p : SG.graph.Walk u u,
        SG.IsUnbalancedCycle p ∧ SG.cycleEdgeFinset p = F := by
  constructor
  · exact SG.minimalUnsat_eq_unbalancedCycleEdges
  · rintro ⟨u, p, hp, rfl⟩
    exact SG.unbalancedCycleEdges_isMinimalUnsat hp

end SignedGraph

end InsacermoActionabilityInformation
