import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

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

@[simp]
theorem walkParity_append {u v w : V}
    (p : SG.graph.Walk u v) (q : SG.graph.Walk v w) :
    SG.walkParity (p.append q) = Bool.xor (SG.walkParity p) (SG.walkParity q) := by
  induction p with
  | nil => simp
  | cons h p ih =>
      simp [ih]

@[simp]
theorem walkParity_copy {u v u' v' : V} (p : SG.graph.Walk u v)
    (hu : u = u') (hv : v = v') :
    SG.walkParity (p.copy hu hv) = SG.walkParity p := by
  subst u'
  subst v'
  rfl

@[simp]
theorem walkParity_reverse {u v : V} (p : SG.graph.Walk u v) :
    SG.walkParity p.reverse = SG.walkParity p := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
      rw [SimpleGraph.Walk.reverse_cons, SG.walkParity_append]
      simp [ih, Bool.xor_comm, Sym2.eq_swap]

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

/-- A canonical representative of the connected component containing `v`.
This is used only to construct one satisfying assignment from balanced closed
walks; no graph-theoretic claim depends on which representative `Quot.out`
chooses. -/
noncomputable def componentRoot (v : V) : V :=
  Quot.out (SG.graph.connectedComponentMk v)

/-- The canonical component representative is reachable from the vertex. -/
theorem componentRoot_reachable (v : V) :
    SG.graph.Reachable (SG.componentRoot v) v := by
  apply SimpleGraph.ConnectedComponent.exact
  change SG.graph.connectedComponentMk (Quot.out (SG.graph.connectedComponentMk v)) =
    SG.graph.connectedComponentMk v
  exact Quot.out_eq _

/-- Adjacent vertices have the same canonical component representative. -/
theorem componentRoot_eq_of_adj {u v : V} (h : SG.graph.Adj u v) :
    SG.componentRoot u = SG.componentRoot v := by
  unfold componentRoot
  rw [SimpleGraph.ConnectedComponent.sound h.reachable]

/-- A chosen walk from the canonical representative of `v` to `v`. -/
noncomputable def componentPath (v : V) :
    SG.graph.Walk (SG.componentRoot v) v :=
  (SG.componentRoot_reachable v).some

/-- Converse kernel.  If every closed walk has even signed parity, the signed
graph admits a global satisfying Boolean assignment.  The assignment at `v`
is the parity of any fixed path from a representative of its connected
component to `v`; balanced closed walks make this path parity consistent across
edges. -/
theorem all_closed_walks_balanced_implies_satisfiable
    (hclosed : ∀ {u : V} (p : SG.graph.Walk u u), SG.walkParity p = false) :
    SG.Satisfiable := by
  refine ⟨fun v => SG.walkParity (SG.componentPath v), ?_⟩
  intro u v huv _
  let pu : SG.graph.Walk (SG.componentRoot u) u := SG.componentPath u
  let pv : SG.graph.Walk (SG.componentRoot v) v := SG.componentPath v
  have hroot : SG.componentRoot u = SG.componentRoot v := SG.componentRoot_eq_of_adj huv
  let pv' : SG.graph.Walk (SG.componentRoot u) v := pv.copy hroot.symm rfl
  let c : SG.graph.Walk (SG.componentRoot u) (SG.componentRoot u) :=
    (pu.concat huv).append pv'.reverse
  have hc : SG.walkParity c = false := hclosed c
  change Bool.xor (SG.walkParity pu) (SG.walkParity pv) = SG.sign s(u, v)
  cases hpu : SG.walkParity pu <;>
    cases hpv : SG.walkParity pv <;>
    cases hs : SG.sign s(u, v) <;>
    simp [c, pv', SimpleGraph.Walk.concat_eq_append, hpu, hpv, hs] at hc ⊢

/-- Exact closed-walk characterization of satisfiability. -/
theorem satisfiable_iff_all_closed_walks_balanced :
    SG.Satisfiable ↔
      ∀ {u : V} (p : SG.graph.Walk u u), SG.walkParity p = false := by
  constructor
  · exact fun hsat => SG.satisfiable_implies_all_closed_walks_balanced hsat
  · exact SG.all_closed_walks_balanced_implies_satisfiable

/-- Exact existential UNSAT certificate: a signed graph is inconsistent if and
only if some closed walk has odd signed parity. -/
theorem not_satisfiable_iff_exists_unbalanced_closed_walk :
    ¬ SG.Satisfiable ↔
      ∃ u : V, ∃ p : SG.graph.Walk u u, SG.IsUnbalancedClosedWalk p := by
  constructor
  · intro hunsat
    have hnot : ¬ (∀ {u : V} (p : SG.graph.Walk u u), SG.walkParity p = false) := by
      intro hclosed
      exact hunsat (SG.all_closed_walks_balanced_implies_satisfiable hclosed)
    push Not at hnot
    rcases hnot with ⟨u, p, hp⟩
    refine ⟨u, p, ?_⟩
    unfold IsUnbalancedClosedWalk
    cases h : SG.walkParity p <;> simp_all
  · rintro ⟨u, p, hp⟩
    exact SG.unbalancedClosedWalk_blocks_satisfiability hp

/-- An unbalanced closed walk in a simple graph has length at least three. -/
theorem three_le_length_of_unbalancedClosedWalk
    {u : V} {p : SG.graph.Walk u u}
    (hp : SG.IsUnbalancedClosedWalk p) :
    3 ≤ p.length := by
  cases p with
  | nil =>
      simp [IsUnbalancedClosedWalk] at hp
  | cons h q =>
      cases q with
      | nil =>
          simp at h
      | cons h' r =>
          cases r with
          | nil =>
              simp [IsUnbalancedClosedWalk, Sym2.eq_swap] at hp
          | cons h'' r' =>
              simp

/-- Removing a nontrivial balanced closed subwalk from the tail of a closed
walk preserves its parity and strictly shortens it. -/
theorem remove_balanced_closed_subwalk_of_tail
    {u : V} (p : SG.graph.Walk u u) (hpnon : ¬ p.Nil)
    {w : V} (q : SG.graph.Walk w w)
    (hqsub : q.IsSubwalk p.tail) (hqnon : ¬ q.Nil)
    (hqbal : SG.walkParity q = false) :
    ∃ r : SG.graph.Walk u u,
      r.length < p.length ∧ SG.walkParity r = SG.walkParity p := by
  rcases hqsub with ⟨ru, rv, hdec⟩
  let a : SG.graph.Walk u w := ru.cons (p.adj_snd hpnon)
  let r : SG.graph.Walk u u := a.append rv
  have hpdec : p = (a.append q).append rv := by
    rw [← p.cons_tail_eq hpnon, hdec]
    simp [a, SimpleGraph.Walk.append_assoc]
  refine ⟨r, ?_, ?_⟩
  · have hqpos : 0 < q.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp hqnon
    have hlen := congrArg (fun z => z.length) hpdec
    simp [r, a] at hlen ⊢
    omega
  · simp [r, hpdec, hqbal, Bool.xor_assoc]

/-- A length-minimal unbalanced closed walk cannot contain a removable closed
subwalk, hence it is a graph-theoretic cycle. -/
theorem minimal_unbalancedClosedWalk_isCycle
    {u : V} (p : SG.graph.Walk u u)
    (hp : SG.IsUnbalancedClosedWalk p)
    (hmin : ∀ {v : V} (q : SG.graph.Walk v v),
      q.length < p.length → ¬ SG.IsUnbalancedClosedWalk q) :
    p.IsCycle := by
  have hthree : 3 ≤ p.length := SG.three_le_length_of_unbalancedClosedWalk hp
  have hpnon : ¬ p.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_, hthree⟩
  rw [SimpleGraph.Walk.isPath_iff_isSubwalk_imp_nil]
  intro w q hqsub
  by_contra hqnon
  have htail_lt : p.tail.length < p.length := by
    rw [← p.length_tail_add_one hpnon]
    omega
  have hq_lt : q.length < p.length :=
    lt_of_le_of_lt (SimpleGraph.Walk.length_le_of_isSubwalk hqsub) htail_lt
  have hqbal : SG.walkParity q = false := by
    cases hpar : SG.walkParity q with
    | false => exact hpar
    | true =>
        exfalso
        exact (hmin q hq_lt) (by simpa [IsUnbalancedClosedWalk] using hpar)
  obtain ⟨r, hrlt, hrpar⟩ :=
    SG.remove_balanced_closed_subwalk_of_tail p hpnon q hqsub hqnon hqbal
  have hrun : SG.IsUnbalancedClosedWalk r := by
    unfold IsUnbalancedClosedWalk
    rw [hrpar, hp]
  exact (hmin r hrlt) hrun

/-- Every unbalanced closed walk contains an unbalanced cycle.  The proof
chooses a shortest odd closed walk and applies the preceding minimality lemma. -/
theorem unbalancedClosedWalk_contains_unbalancedCycle
    {u : V} (p : SG.graph.Walk u u)
    (hp : SG.IsUnbalancedClosedWalk p) :
    ∃ v : V, ∃ q : SG.graph.Walk v v, SG.IsUnbalancedCycle q := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ v : V, ∃ q : SG.graph.Walk v v,
      q.length = n ∧ SG.IsUnbalancedClosedWalk q
  have hP : ∃ n, P n := ⟨p.length, u, p, rfl, hp⟩
  let n := Nat.find hP
  have hn : P n := Nat.find_spec hP
  rcases hn with ⟨v, q, hqlen, hqun⟩
  have hmin : ∀ {w : V} (r : SG.graph.Walk w w),
      r.length < q.length → ¬ SG.IsUnbalancedClosedWalk r := by
    intro w r hlt hrun
    have hPr : P r.length := ⟨w, r, rfl, hrun⟩
    have hnle : n ≤ r.length := Nat.find_min' hP hPr
    rw [hqlen] at hlt
    omega
  refine ⟨v, q, ?_⟩
  exact ⟨SG.minimal_unbalancedClosedWalk_isCycle q hqun hmin, hqun⟩

/-- Exact cycle characterization: inconsistency is equivalent to the existence
of an unbalanced cycle. -/
theorem not_satisfiable_iff_exists_unbalanced_cycle :
    ¬ SG.Satisfiable ↔
      ∃ u : V, ∃ p : SG.graph.Walk u u, SG.IsUnbalancedCycle p := by
  constructor
  · intro hunsat
    rcases (SG.not_satisfiable_iff_exists_unbalanced_closed_walk.mp hunsat) with ⟨u, p, hp⟩
    exact SG.unbalancedClosedWalk_contains_unbalancedCycle p hp
  · rintro ⟨u, p, hp⟩
    exact SG.unbalancedCycle_blocks_satisfiability hp

end SignedGraph

end InsacermoActionabilityInformation
