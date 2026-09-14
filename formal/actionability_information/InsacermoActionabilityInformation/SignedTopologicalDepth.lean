import Mathlib.Combinatorics.SimpleGraph.Paths

namespace InsacermoActionabilityInformation

open SimpleGraph

/-- A signed simple graph is represented by an ordinary simple graph together
with a Boolean label on every unordered pair of vertices.  Only labels on
actual graph edges matter.  `false` means equality across the edge and `true`
means inequality. -/
structure SignedGraph (V : Type*) where
  graph : SimpleGraph V
  sign : Sym2 V → Bool

namespace SignedGraph

variable {V : Type*} (SG : SignedGraph V)

/-- An assignment satisfies a selected set of signed edges. -/
def SatisfiesOn (F : Set (Sym2 V)) (x : V → Bool) : Prop :=
  ∀ ⦃u v : V⦄, SG.graph.Adj u v → s(u, v) ∈ F →
    Bool.xor (x u) (x v) = SG.sign s(u, v)

/-- Global satisfiability of the signed graph. -/
def Satisfiable : Prop :=
  ∃ x : V → Bool, SG.SatisfiesOn SG.graph.edgeSet x

/-- XOR parity accumulated along a graph walk. -/
def walkParity {u v : V} (p : SG.graph.Walk u v) : Bool :=
  p.edges.foldr (fun e acc => Bool.xor (SG.sign e) acc) false

@[simp]
theorem walkParity_nil {u : V} :
    SG.walkParity (SimpleGraph.Walk.nil : SG.graph.Walk u u) = false := by
  simp [walkParity]

@[simp]
theorem walkParity_cons {u v w : V} (h : SG.graph.Adj u v)
    (p : SG.graph.Walk v w) :
    SG.walkParity (SimpleGraph.Walk.cons h p) =
      Bool.xor (SG.sign s(u, v)) (SG.walkParity p) := by
  simp [walkParity]

/-- Fundamental telescoping lemma.  If every edge of a walk belongs to a
selected satisfiable sub-contract, then the XOR between endpoint labels is
exactly the signed parity accumulated along the walk. -/
theorem satisfiesOn_walkParity
    {F : Set (Sym2 V)} {x : V → Bool}
    (hx : SG.SatisfiesOn F x) {u v : V} (p : SG.graph.Walk u v)
    (hp : ∀ e, e ∈ p.edges → e ∈ F) :
    Bool.xor (x u) (x v) = SG.walkParity p := by
  induction p with
  | nil =>
      simp
  | @cons u v w huv p ih =>
      have hhead : s(u, v) ∈ F := hp _ (by simp)
      have htail : ∀ e, e ∈ p.edges → e ∈ F := by
        intro e he
        exact hp e (by simp [he])
      have hedge : Bool.xor (x u) (x v) = SG.sign s(u, v) := hx huv hhead
      have hrest : Bool.xor (x v) (x w) = SG.walkParity p := ih htail
      rw [SG.walkParity_cons huv p]
      rw [← hedge, ← hrest]
      simp [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

/-- Every globally satisfying assignment telescopes correctly along every
walk of the graph. -/
theorem satisfies_walkParity
    {x : V → Bool} (hx : SG.SatisfiesOn SG.graph.edgeSet x)
    {u v : V} (p : SG.graph.Walk u v) :
    Bool.xor (x u) (x v) = SG.walkParity p := by
  apply SG.satisfiesOn_walkParity hx p
  intro e he
  exact p.edges_subset_edgeSet he

/-- A closed walk is unbalanced when the XOR of its signed edges is `true`. -/
def IsUnbalancedClosedWalk {u : V} (p : SG.graph.Walk u u) : Prop :=
  SG.walkParity p = true

/-- An unbalanced cycle is a graph-theoretic cycle whose signed XOR is odd. -/
def IsUnbalancedCycle {u : V} (p : SG.graph.Walk u u) : Prop :=
  p.IsCycle ∧ SG.IsUnbalancedClosedWalk p

/-- Core obstruction theorem: an unbalanced closed walk is already a complete
certificate of global inconsistency. -/
theorem unbalancedClosedWalk_blocks_satisfiability
    {u : V} {p : SG.graph.Walk u u}
    (hp : SG.IsUnbalancedClosedWalk p) :
    ¬ SG.Satisfiable := by
  rintro ⟨x, hx⟩
  have htel : Bool.xor (x u) (x u) = SG.walkParity p :=
    SG.satisfies_walkParity hx p
  rw [hp] at htel
  simpa using htel

/-- In particular, every unbalanced cycle is an UNSAT certificate. -/
theorem unbalancedCycle_blocks_satisfiability
    {u : V} {p : SG.graph.Walk u u}
    (hp : SG.IsUnbalancedCycle p) :
    ¬ SG.Satisfiable :=
  SG.unbalancedClosedWalk_blocks_satisfiability hp.2

/-- Local version: if a selected edge set contains all edges of an unbalanced
closed walk, that selected sub-contract is itself unsatisfiable. -/
theorem unbalancedClosedWalk_blocks_selected_edges
    {F : Set (Sym2 V)} {u : V} {p : SG.graph.Walk u u}
    (hpF : ∀ e, e ∈ p.edges → e ∈ F)
    (hunbal : SG.IsUnbalancedClosedWalk p) :
    ¬ ∃ x : V → Bool, SG.SatisfiesOn F x := by
  rintro ⟨x, hx⟩
  have htel : Bool.xor (x u) (x u) = SG.walkParity p :=
    SG.satisfiesOn_walkParity hx p hpF
  rw [hunbal] at htel
  simpa using htel

/-- Every satisfiable signed graph has even parity on every closed walk. -/
theorem satisfiable_implies_all_closed_walks_balanced
    (hsat : SG.Satisfiable) {u : V} (p : SG.graph.Walk u u) :
    SG.walkParity p = false := by
  rcases hsat with ⟨x, hx⟩
  have htel : Bool.xor (x u) (x u) = SG.walkParity p :=
    SG.satisfies_walkParity hx p
  simpa using htel.symm

/-- Therefore satisfiability excludes every unbalanced cycle. -/
theorem satisfiable_implies_no_unbalanced_cycle
    (hsat : SG.Satisfiable) :
    ∀ {u : V} (p : SG.graph.Walk u u), ¬ SG.IsUnbalancedCycle p := by
  intro u p hp
  have hfalse := SG.satisfiable_implies_all_closed_walks_balanced hsat p
  rw [hp.2] at hfalse
  simp at hfalse

end SignedGraph

end InsacermoActionabilityInformation
