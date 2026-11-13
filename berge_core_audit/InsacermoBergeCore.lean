/-
INSACERMO BERGE CORE AUDIT — Independent Lean 4.20 reconstruction.
This is NOT the original source authored by Claude.
Uses only Lean's core Init library (no Mathlib, no postulates).
Statements proved:
* finite decreasing-rank minimalization,
* minimal obstructions under enlarged action families,
* binary-observation feasibility equivalence,
* Berge's incremental minimal transversal update (up to predicate equivalence),
* strict-descent length is bounded by initial rank.
The phrase kappa <= |C| in Claude's original file is NOT asserted here;
its exact original definitions have not been provided.
-/
import Init

namespace InsacermoBergeCore

universe u v
variable {W : Type u}

abbrev Region (W : Type u) := W → Prop

def Sub (S T : Region W) : Prop := ∀ x, S x → T x
def Strict (S T : Region W) : Prop := Sub S T ∧ ¬ Sub T S
def Same (S T : Region W) : Prop := Sub S T ∧ Sub T S
def Add (S : Region W) (x : W) : Region W := fun y => S y ∨ y = x

theorem sub_refl (S : Region W) : Sub S S := by
  intro x hx
  exact hx

theorem sub_trans {S T U : Region W}
    (hST : Sub S T) (hTU : Sub T U) : Sub S U := by
  intro x hx
  exact hTU x (hST x hx)

/-- If strict inclusion decreases a natural-number rank, every inhabited
property has a minimal witness below the initial object. -/
theorem finite_descent
    (P : Region W → Prop)
    (rank : Region W → Nat)
    (hRank : ∀ S T : Region W, Strict S T → rank S < rank T)
    (B : Region W) (hB : P B) :
    ∃ M : Region W, Sub M B ∧ P M ∧
      ∀ S : Region W, Strict S M → ¬ P S := by
  have aux : ∀ fuel : Nat, ∀ T : Region W, rank T ≤ fuel → P T →
        ∃ M : Region W, Sub M T ∧ P M ∧
          ∀ S : Region W, Strict S M → ¬ P S := by
    intro fuel
    induction fuel with
    | zero =>
        intro T hBound hPT
        by_cases hSmaller : ∃ S : Region W, Strict S T ∧ P S
        · obtain ⟨S, hST, hPS⟩ := hSmaller
          have hImpossible : rank S < 0 := Nat.lt_of_lt_of_le (hRank S T hST) hBound
          exact False.elim (Nat.not_lt_zero _ hImpossible)
        · refine ⟨T, sub_refl T, hPT, ?_⟩
          intro S hST hPS
          exact hSmaller ⟨S, hST, hPS⟩
    | succ n ih =>
        intro T hBound hPT
        by_cases hSmaller : ∃ S : Region W, Strict S T ∧ P S
        · obtain ⟨S, hST, hPS⟩ := hSmaller
          have hLess : rank S < n + 1 :=
            Nat.lt_of_lt_of_le (hRank S T hST) hBound
          have hLe : rank S ≤ n := Nat.lt_succ_iff.mp hLess
          obtain ⟨M, hMS, hPM, hMin⟩ := ih S hLe hPS
          exact ⟨M, sub_trans hMS hST.1, hPM, hMin⟩
        · refine ⟨T, sub_refl T, hPT, ?_⟩
          intro S hST hPS
          exact hSmaller ⟨S, hST, hPS⟩
  exact aux (rank B) B (Nat.le_refl _) hB

def Feasible (actions : List (Region W)) (B : Region W) : Prop :=
  ∃ a : Region W, a ∈ actions ∧ Sub B a

def MinimalObstruction (actions : List (Region W)) (B : Region W) : Prop :=
  ¬ Feasible actions B ∧
    ∀ S : Region W, Strict S B → Feasible actions S

/-- No new minimal obstruction appears without containing an old minimal
obstruction. This does not claim old obstructions persist. -/
theorem new_obstruction_contains_old
    (oldActions newActions : List (Region W))
    (hExpand : ∀ a : Region W, a ∈ oldActions → a ∈ newActions)
    (rank : Region W → Nat)
    (hRank : ∀ S T : Region W, Strict S T → rank S < rank T)
    (B : Region W)
    (hNew : MinimalObstruction newActions B) :
    ∃ M : Region W, Sub M B ∧ MinimalObstruction oldActions M := by
  have hOld : ¬ Feasible oldActions B := by
    intro h
    apply hNew.1
    obtain ⟨a, ha, hBa⟩ := h
    exact ⟨a, hExpand a ha, hBa⟩
  obtain ⟨M, hMB, hObs, hMin⟩ :=
    finite_descent (fun S => ¬ Feasible oldActions S) rank hRank B hOld
  refine ⟨M, hMB, ⟨hObs, ?_⟩⟩
  intro S hSM
  exact Classical.byContradiction (fun hNot => hMin S hSM hNot)

def Fiber (B : Region W) (p : W → Bool) (r : Bool) : Region W :=
  fun x => B x ∧ p x = r

def ObservationFeasible (actions : List (Region W))
    (B : Region W) (p : W → Bool) : Prop :=
  ∀ r : Bool, ∃ a : Region W, a ∈ actions ∧
    ∀ x : W, B x → p x = r → a x

theorem obs_feas_iff
    (actions : List (Region W))
    (B : Region W) (p : W → Bool) :
    ObservationFeasible actions B p ↔
      ∀ r : Bool, Feasible actions (Fiber B p r) := by
  constructor
  · intro h r
    obtain ⟨a, ha, hw⟩ := h r
    exact ⟨a, ha, fun x hx => hw x hx.1 hx.2⟩
  · intro h r
    obtain ⟨a, ha, hs⟩ := h r
    exact ⟨a, ha, fun x hx hp => hs x ⟨hx, hp⟩⟩

def Hit (S E : Region W) : Prop := ∃ x : W, S x ∧ E x

def Hits (H : List (Region W)) (S : Region W) : Prop :=
  ∀ E : Region W, E ∈ H → Hit S E

def MinimalHits (H : List (Region W)) (T : Region W) : Prop :=
  Hits H T ∧ ∀ S : Region W, Strict S T → ¬ Hits H S

theorem hits_mono (H : List (Region W))
    {S T : Region W} (hST : Sub S T) (hs : Hits H S) :
    Hits H T := by
  intro E hE
  obtain ⟨x, hxS, hxE⟩ := hs E hE
  exact ⟨x, hST x hxS, hxE⟩

theorem hits_tail (H : List (Region W)) (E : Region W)
    {T : Region W} (h : Hits (E :: H) T) : Hits H T := by
  intro F hF
  apply h F
  exact List.mem_cons_of_mem E hF

theorem hits_add (H : List (Region W)) (E T : Region W) (x : W)
    (hT : Hits H T) (hEx : E x) :
    Hits (E :: H) (Add T x) := by
  intro F hF
  rcases List.mem_cons.mp hF with hEq | hTail
  · subst F
    exact ⟨x, Or.inr rfl, hEx⟩
  · obtain ⟨y, hyT, hyF⟩ := hT F hTail
    exact ⟨y, Or.inl hyT, hyF⟩

/-- One application of Berge's construction: start with a minimal
transversal of H and add a vertex in the new edge E. -/
def BergeCandidate (H : List (Region W))
    (E T : Region W) : Prop :=
  ∃ U : Region W, ∃ x : W,
    MinimalHits H U ∧ E x ∧ Same T (Add U x)

def BergeMinimalCandidate (H : List (Region W))
    (E T : Region W) : Prop :=
  BergeCandidate H E T ∧
    ∀ S : Region W, BergeCandidate H E S → Sub S T → Sub T S

theorem candidate_hits
    (H : List (Region W)) (E T : Region W)
    (hc : BergeCandidate H E T) : Hits (E :: H) T := by
  obtain ⟨U, x, hU, hEx, hSame⟩ := hc
  apply hits_mono (E :: H) hSame.2
  exact hits_add H E U x hU.1 hEx

theorem minimal_hits_candidate
    (H : List (Region W)) (E T : Region W)
    (rank : Region W → Nat)
    (hRank : ∀ S U : Region W, Strict S U → rank S < rank U)
    (hT : MinimalHits (E :: H) T) :
    BergeCandidate H E T := by
  have hH : Hits H T := hits_tail H E hT.1
  obtain ⟨U, hUT, hHits, hMin⟩ :=
    finite_descent (Hits H) rank hRank T hH
  obtain ⟨x, hxT, hxE⟩ := hT.1 E (List.Mem.head _)
  have hST : Sub (Add U x) T := by
    intro y hy
    cases hy with
    | inl hUy => exact hUT y hUy
    | inr hxy =>
        subst y
        exact hxT
  have hTS : Sub T (Add U x) := by
    apply Classical.byContradiction
    intro hNot
    exact hT.2 (Add U x) ⟨hST, hNot⟩
      (hits_add H E U x hHits hxE)
  exact ⟨U, x, ⟨hHits, hMin⟩, hxE, ⟨hTS, hST⟩⟩

/-- Berge's one-edge update theorem (conditional only on a well-founded rank).
Minimal hitting sets of E :: H are exactly the inclusion-minimal members
of the generated candidates, modulo extensional equality of regions. -/
theorem berge_update_iff
    (H : List (Region W)) (E T : Region W)
    (rank : Region W → Nat)
    (hRank : ∀ S U : Region W, Strict S U → rank S < rank U) :
    MinimalHits (E :: H) T ↔ BergeMinimalCandidate H E T := by
  constructor
  · intro ht
    refine ⟨minimal_hits_candidate H E T rank hRank ht, ?_⟩
    intro S hc hST
    apply Classical.byContradiction
    intro hNot
    exact ht.2 S ⟨hST, hNot⟩ (candidate_hits H E S hc)
  · intro hc
    refine ⟨candidate_hits H E T hc.1, ?_⟩
    intro S hST hS
    have hH : Hits H S := hits_tail H E hS
    obtain ⟨U, hUS, hUH, hUMin⟩ :=
      finite_descent (Hits H) rank hRank S hH
    obtain ⟨x, hxS, hxE⟩ := hS E (List.Mem.head _)
    have hRS : Sub (Add U x) S := by
      intro y hy
      rcases hy with hUy | hyx
      · exact hUS y hUy
      · subst y
        exact hxS
    have hRT : Sub (Add U x) T := sub_trans hRS hST.1
    have hCandidate : BergeCandidate H E (Add U x) :=
      ⟨U, x, ⟨hUH, hUMin⟩, hxE,
        ⟨sub_refl (Add U x), sub_refl (Add U x)⟩⟩
    have hTR : Sub T (Add U x) := hc.2 (Add U x) hCandidate hRT
    exact hST.2 (sub_trans hTR hRS)

/-- A chain of strict rank descents, with length n. -/
inductive RankDescent (rank : Region W → Nat) :
    Nat → Region W → Prop where
  | zero (B : Region W) : RankDescent rank 0 B
  | next (B S : Region W) (n : Nat)
      (hDrop : rank S < rank B) (hRest : RankDescent rank n S) :
      RankDescent rank (n + 1) B

theorem finite_descent_length_bound
    (rank : Region W → Nat) {n : Nat} {B : Region W}
    (h : RankDescent rank n B) : n ≤ rank B := by
  induction h with
  | zero B =>
      exact Nat.zero_le _
  | next B S n hDrop hRest ih =>
      exact Nat.le_trans (Nat.succ_le_succ ih) hDrop

#print axioms finite_descent
#print axioms new_obstruction_contains_old
#print axioms obs_feas_iff
#print axioms berge_update_iff
#print axioms finite_descent_length_bound

end InsacermoBergeCore
