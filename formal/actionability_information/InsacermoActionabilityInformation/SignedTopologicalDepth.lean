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

variable {V : Type*} (Σ : SignedGraph V)

/-- An assignment satisfies a selected set of signed edges. -/
def SatisfiesOn (F : Set (Sym2 V)) (x : V → Bool) : Prop :=
  ∀ ⦃u v : V⦄, Σ.graph.Adj u v → s(u, v) ∈ F →
    Bool.xor (x u) (x v) = Σ.sign s(u, v)

/-- Global satisfiability of the signed graph. -/
def Satisfiable : Prop :=
  ∃ x : V → Bool, Σ.SatisfiesOn Σ.graph.edgeSet x

/-- XOR parity accumulated along a graph walk. -/
def walkParity {u v : V} (p : Σ.graph.Walk u v) : Bool :=
  p.edges.foldr (fun e acc => Bool.xor (Σ.sign e) acc) false

@[simp]
theorem walkParity_nil {u : V} :
    Σ.walkParity (SimpleGraph.Walk.nil : Σ.graph.Walk u u) = false := by
  simp [walkParity]

@[simp]
theorem walkParity_cons {u v w : V} (h : Σ.graph.Adj u v)
    (p : Σ.graph.Walk v w) :
    Σ.walkParity (SimpleGraph.Walk.cons h p) =
      Bool.xor (Σ.sign s(u, v)) (Σ.walkParity p) := by
  simp [walkParity]

/-- Fundamental telescoping lemma.  If every edge of a walk belongs to a
selected satisfiable sub-contract, then the XOR between endpoint labels is
exactly the signed parity accumulated along the walk. -/
theorem satisfiesOn_walkParity
    {F : Set (Sym2 V)} {x : V → Bool}
    (hx : Σ.SatisfiesOn F x) {u v : V} (p : Σ.graph.Walk u v)
    (hp : ∀ e, e ∈ p.edges → e ∈ F) :
    Bool.xor (x u) (x v) = Σ.walkParity p := by
  induction p with
  | nil =>
      simp
  | @cons u v w huv p ih =>
      have hhead : s(u, v) ∈ F := hp _ (by simp)
      have htail : ∀ e, e ∈ p.edges → e ∈ F := by
        intro e he
        exact hp e (by simp [he])
      have hedge : Bool.xor (x u) (x v) = Σ.sign s(u, v) := hx huv hhead
      have hrest : Bool.xor (x v) (x w) = Σ.walkParity p := ih htail
      rw [Σ.walkParity_cons huv p]
      rw [← hedge, ← hrest]
      simp [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

/-- Every globally satisfying assignment telescopes correctly along every
walk of the graph. -/
theorem satisfies_walkParity
    {x : V → Bool} (hx : Σ.SatisfiesOn Σ.graph.edgeSet x)
    {u v : V} (p : Σ.graph.Walk u v) :
    Bool.xor (x u) (x v) = Σ.walkParity p := by
  apply Σ.satisfiesOn_walkParity hx p
  intro e he
  exact p.edges_subset_edgeSet he

/-- A closed walk is unbalanced when the XOR of its signed edges is `true`. -/
def IsUnbalancedClosedWalk {u : V} (p : Σ.graph.Walk u u) : Prop :=
  Σ.walkParity p = true

/-- An unbalanced cycle is a graph-theoretic cycle whose signed XOR is odd. -/
def IsUnbalancedCycle {u : V} (p : Σ.graph.Walk u u) : Prop :=
  p.IsCycle ∧ Σ.IsUnbalancedClosedWalk p

/-- Core obstruction theorem: an unbalanced closed walk is already a complete
certificate of global inconsistency. -/
theorem unbalancedClosedWalk_blocks_satisfiability
    {u : V} {p : Σ.graph.Walk u u}
    (hp : Σ.IsUnbalancedClosedWalk p) :
    ¬ Σ.Satisfiable := by
  rintro ⟨x, hx⟩
  have htel : Bool.xor (x u) (x u) = Σ.walkParity p :=
    Σ.satisfies_walkParity hx p
  rw [hp] at htel
  simpa using htel

/-- In particular, every unbalanced cycle is an UNSAT certificate. -/
theorem unbalancedCycle_blocks_satisfiability
    {u : V} {p : Σ.graph.Walk u u}
    (hp : Σ.IsUnbalancedCycle p) :
    ¬ Σ.Satisfiable :=
  Σ.unbalancedClosedWalk_blocks_satisfiability hp.2

/-- Local version: if a selected edge set contains all edges of an unbalanced
closed walk, that selected sub-contract is itself unsatisfiable. -/
theorem unbalancedClosedWalk_blocks_selected_edges
    {F : Set (Sym2 V)} {u : V} {p : Σ.graph.Walk u u}
    (hpF : ∀ e, e ∈ p.edges → e ∈ F)
    (hunbal : Σ.IsUnbalancedClosedWalk p) :
    ¬ ∃ x : V → Bool, Σ.SatisfiesOn F x := by
  rintro ⟨x, hx⟩
  have htel : Bool.xor (x u) (x u) = Σ.walkParity p :=
    Σ.satisfiesOn_walkParity hx p hpF
  rw [hunbal] at htel
  simpa using htel

/-- Every satisfiable signed graph has even parity on every closed walk. -/
theorem satisfiable_implies_all_closed_walks_balanced
    (hsat : Σ.Satisfiable) {u : V} (p : Σ.graph.Walk u u) :
    Σ.walkParity p = false := by
  rcases hsat with ⟨x, hx⟩
  have htel : Bool.xor (x u) (x u) = Σ.walkParity p :=
    Σ.satisfies_walkParity hx p
  simpa using htel.symm

/-- Therefore satisfiability excludes every unbalanced cycle. -/
theorem satisfiable_implies_no_unbalanced_cycle
    (hsat : Σ.Satisfiable) :
    ∀ {u : V} (p : Σ.graph.Walk u u), ¬ Σ.IsUnbalancedCycle p := by
  intro u p hp
  have hfalse := Σ.satisfiable_implies_all_closed_walks_balanced hsat p
  rw [hp.2] at hfalse
  simp at hfalse

end SignedGraph

end InsacermoActionabilityInformation
