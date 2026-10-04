import Std
import EffectiveStateBoundV1

/-!
INSACERMO — Semantic Complexity Law Kernel V1

Two independent ceilings govern a finite deterministic adaptive plan after an
exact semantic quotient:

1. semantic ceiling:
   n effective classes admit an explicit belief-signature cover of size 2^n;

2. prospective ceiling:
   if every probe has at most m occurring branches and planning depth is at
   most d, a plan tree has at most
     G(m,0)=1
     G(m,d+1)=1+m*G(m,d)
   nodes.

A quantity K that is independently known to be bounded by both ceilings is
therefore bounded by their minimum.

This file does NOT claim wall-clock runtime is equal to this bound. It isolates
a semantic/prospective state-space ceiling. Implementation overhead, probe
evaluation, certificate construction, and search order remain separate.
-/

namespace InsacermoSemanticComplexity

/-- Maximum node count of a full m-ary adaptive tree of depth at most d. -/
def prospectiveNodes (m : Nat) : Nat → Nat
  | 0 => 1
  | d + 1 => 1 + m * prospectiveNodes m d

/-- Minimal tree model needed for the structural counting theorem. -/
inductive PlanTree where
  | act : PlanTree
  | probe : List PlanTree → PlanTree
deriving Repr

open PlanTree

def nodeCount : PlanTree → Nat
  | act => 1
  | probe children => 1 + (children.map nodeCount).sum

/--
A plan stays within depth d and has at most m children at every probe node.
At depth zero, only ACT is allowed.
-/
def TreeWithin (m : Nat) : Nat → PlanTree → Prop
  | 0, act => True
  | 0, probe _ => False
  | d + 1, act => True
  | d + 1, probe children =>
      children.length ≤ m ∧
      ∀ child ∈ children, TreeWithin m d child

theorem sum_map_le_length_mul
    {α : Type}
    (xs : List α)
    (f : α → Nat)
    (bound : Nat)
    (h : ∀ x ∈ xs, f x ≤ bound) :
    (xs.map f).sum ≤ xs.length * bound := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : f x ≤ bound := h x (by simp)
      have htail : ∀ y ∈ xs, f y ≤ bound := by
        intro y hy
        exact h y (by simp [hy])
      have hi := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        f x + (xs.map f).sum ≤ bound + xs.length * bound :=
          Nat.add_le_add hx hi
        _ = (xs.length + 1) * bound := by
          simp [Nat.add_mul, Nat.add_comm]

/--
Prospective tree theorem: branching m and depth d alone bound the number of
nodes of every admissible adaptive plan.
-/
theorem treeWithin_nodeCount_le
    (m : Nat) :
    ∀ d : Nat, ∀ t : PlanTree,
      TreeWithin m d t →
      nodeCount t ≤ prospectiveNodes m d := by
  intro d
  induction d with
  | zero =>
      intro t ht
      cases t with
      | act =>
          simp [nodeCount, prospectiveNodes]
      | probe children =>
          simp [TreeWithin] at ht
  | succ d ih =>
      intro t ht
      cases t with
      | act =>
          simp [nodeCount, prospectiveNodes]
      | probe children =>
          have hstruct :
              children.length ≤ m ∧
              ∀ child ∈ children, TreeWithin m d child := by
            simpa [TreeWithin] using ht
          have hchild :
              ∀ child ∈ children,
                nodeCount child ≤ prospectiveNodes m d := by
            intro child hmem
            exact ih child (hstruct.2 child hmem)
          have hsum :
              (children.map nodeCount).sum ≤
                children.length * prospectiveNodes m d :=
            sum_map_le_length_mul children nodeCount
              (prospectiveNodes m d) hchild
          have hmul :
              children.length * prospectiveNodes m d ≤
                m * prospectiveNodes m d :=
            Nat.mul_le_mul_right (prospectiveNodes m d) hstruct.1
          simp only [nodeCount, prospectiveNodes]
          omega

/-- The semantic belief-signature ceiling inherited from EffectiveStateBoundV1. -/
def semanticCeiling (effectiveClasses : Nat) : Nat :=
  2 ^ effectiveClasses

/-- The two independent ceilings combined conservatively. -/
def combinedCeiling
    (effectiveClasses branching depth : Nat) : Nat :=
  if semanticCeiling effectiveClasses ≤ prospectiveNodes branching depth then
    semanticCeiling effectiveClasses
  else
    prospectiveNodes branching depth

/--
Arithmetic composition law:
if a planner-state quantity K is separately bounded by the semantic and
prospective ceilings, then it is bounded by their minimum.
-/
theorem semantic_complexity_law
    (K effectiveClasses branching depth : Nat)
    (hsemantic : K ≤ semanticCeiling effectiveClasses)
    (hprospective : K ≤ prospectiveNodes branching depth) :
    K ≤ combinedCeiling effectiveClasses branching depth := by
  unfold combinedCeiling
  split
  · exact hsemantic
  · exact hprospective

/--
Direct plan corollary for the prospective half of the law.
-/
theorem plan_respects_prospective_ceiling
    (effectiveClasses branching depth : Nat)
    (t : PlanTree)
    (ht : TreeWithin branching depth t) :
    nodeCount t ≤ prospectiveNodes branching depth := by
  exact treeWithin_nodeCount_le branching depth t ht

/--
The previously verified semantic enumeration has exactly the semantic ceiling
length. This bridges the naming in this file to EffectiveStateBoundV1.
-/
theorem semantic_cover_length
    (effectiveClasses : Nat) :
    (InsacermoEffectiveStateBound.bitBeliefs effectiveClasses).length =
      semanticCeiling effectiveClasses := by
  simpa [semanticCeiling] using
    InsacermoEffectiveStateBound.bitBeliefs_length effectiveClasses

/-- Concrete arithmetic checkpoint for the ternary depth-8 stress family. -/
theorem ternary_depth8_node_ceiling :
    prospectiveNodes 3 8 = 9841 := by
  decide

/-- A full ternary depth-8 tree has 3^8 = 6561 leaf positions. -/
theorem ternary_depth8_leaf_positions :
    3 ^ 8 = 6561 := by
  decide

#print axioms sum_map_le_length_mul
#print axioms treeWithin_nodeCount_le
#print axioms semantic_complexity_law
#print axioms plan_respects_prospective_ceiling
#print axioms semantic_cover_length
#print axioms ternary_depth8_node_ceiling
#print axioms ternary_depth8_leaf_positions

end InsacermoSemanticComplexity
