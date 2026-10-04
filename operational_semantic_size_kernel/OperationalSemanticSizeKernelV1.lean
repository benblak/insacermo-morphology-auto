import Std
import EffectiveStateBoundV1
import SemanticComplexityLawKernelV1
import ReachableBeliefKernelV1
import FiniteReachableBeliefBoundV1

/-!
INSACERMO — Operational Semantic Size Kernel V1

This file is the explicit final composition layer for the finite deterministic /
passive regime formalized by the preceding kernels.

Three independently certified ceilings act on the SAME quantity K, interpreted
as a certified count of distinct visited beliefs:

  semantic ceiling     = 2^N_eff
  reachable ceiling    = (M+1)^P
  prospective ceiling  = G(M,d) = 1 + M + ... + M^d

The operational ceiling is their minimum.

Important precision:
- This is a semantic/state-space theorem, not a wall-clock runtime theorem.
- K must be a distinct-belief count certified against all three interfaces.
- A plan trace records one belief occurrence per plan node; a distinct count is
  only required to be <= the number of occurrences, so revisits are not counted
  as new beliefs.
- The finite reachable-belief catalogue may contain duplicate beliefs; its
  length is therefore a rigorous cover, not an equality with the number of
  distinct reachable beliefs.
- No claim is made here about stochastic/dynamic probes, multiplicity-sensitive
  statistics, Python/JavaScript correctness, or dataset provenance.
-/

namespace InsacermoOperationalSemanticSize

open InsacermoSemanticComplexity
open InsacermoFiniteReachableBelief

/-- Semantic ceiling inherited from the effective-state kernel. -/
def semanticBound (effectiveClasses : Nat) : Nat :=
  2 ^ effectiveClasses

/-- Reachable-history ceiling inherited from the finite canonical catalogue. -/
def reachableBound (probeCount outcomeBound : Nat) : Nat :=
  (outcomeBound + 1) ^ probeCount

/-- Prospective plan-tree ceiling inherited from the semantic-complexity kernel. -/
def prospectiveBound (branching depth : Nat) : Nat :=
  prospectiveNodes branching depth

/-- Small Std-only minimum helper. -/
def minNat (a b : Nat) : Nat :=
  if a ≤ b then a else b

/-- The three-way operational semantic ceiling. -/
def operationalCeiling
    (effectiveClasses probeCount outcomeBound branching depth : Nat) : Nat :=
  minNat (semanticBound effectiveClasses)
    (minNat (reachableBound probeCount outcomeBound)
      (prospectiveBound branching depth))

theorem le_minNat
    (k a b : Nat)
    (ha : k ≤ a)
    (hb : k ≤ b) :
    k ≤ minNat a b := by
  unfold minNat
  split
  · exact ha
  · exact hb

/--
Final arithmetic composition law:
one certified distinct-visited-belief count K bounded by all three independently
verified ceilings is bounded by their three-way minimum.
-/
theorem operational_semantic_size_law
    (K effectiveClasses probeCount outcomeBound branching depth : Nat)
    (hsemantic : K ≤ semanticBound effectiveClasses)
    (hreachable : K ≤ reachableBound probeCount outcomeBound)
    (hprospective : K ≤ prospectiveBound branching depth) :
    K ≤ operationalCeiling effectiveClasses probeCount outcomeBound
      branching depth := by
  unfold operationalCeiling
  apply le_minNat
  · exact hsemantic
  · exact le_minNat K
      (reachableBound probeCount outcomeBound)
      (prospectiveBound branching depth)
      hreachable hprospective

/--
A plan trace pairs the plan tree with a list containing exactly one belief
occurrence per plan node. The beliefs may repeat.
-/
structure PlanTrace (S : Type) where
  tree : PlanTree
  visits : List S
  one_visit_per_node : visits.length = nodeCount tree

/--
Every occurrence in a plan trace is bounded by the prospective tree bound.
-/
theorem planTrace_occurrences_le
    {S : Type}
    (branching depth : Nat)
    (trace : PlanTrace S)
    (hwithin : TreeWithin branching depth trace.tree) :
    trace.visits.length ≤ prospectiveBound branching depth := by
  rw [trace.one_visit_per_node]
  exact treeWithin_nodeCount_le branching depth trace.tree hwithin

/--
Any certified number of distinct visited beliefs is no larger than the
prospective ceiling if it is no larger than the trace occurrence count.
This keeps revisits separate from genuinely new semantic states.
-/
theorem distinct_visits_le_prospective
    {S : Type}
    (K branching depth : Nat)
    (trace : PlanTrace S)
    (hdistinct_le_occurrences : K ≤ trace.visits.length)
    (hwithin : TreeWithin branching depth trace.tree) :
    K ≤ prospectiveBound branching depth := by
  exact Nat.le_trans hdistinct_le_occurrences
    (planTrace_occurrences_le branching depth trace hwithin)

/--
The effective-state catalogue has exactly the semantic ceiling number of slots.
-/
theorem semantic_catalogue_slot_count
    (effectiveClasses : Nat) :
    (InsacermoEffectiveStateBound.bitBeliefs effectiveClasses).length =
      semanticBound effectiveClasses := by
  simpa [semanticBound] using
    InsacermoEffectiveStateBound.bitBeliefs_length effectiveClasses

/--
The decoded finite reachable-belief catalogue has exactly the reachable ceiling
number of slots. It may contain duplicate beliefs.
-/
theorem reachable_catalogue_slot_count
    {W : Type}
    (observe : Nat → W → Nat)
    (B : InsacermoReachableBelief.Belief W)
    (probeCount outcomeBound : Nat) :
    (beliefCatalogue observe B probeCount outcomeBound).length =
      reachableBound probeCount outcomeBound := by
  simpa [reachableBound] using
    beliefCatalogue_length observe B probeCount outcomeBound

/--
Every realizable bounded passive deterministic history lands in the explicit
reachable-belief catalogue whose slot count is the reachable ceiling.
-/
theorem reachable_history_lands_in_operational_catalogue
    {W : Type}
    (observe : Nat → W → Nat)
    (B : InsacermoReachableBelief.Belief W)
    (probeCount outcomeBound : Nat)
    (history : List NatConstraint)
    (hreal : InsacermoReachableBelief.RealizableHistory observe B history)
    (hbound : BoundedHistory probeCount outcomeBound history) :
    runHistory observe B history ∈
      beliefCatalogue observe B probeCount outcomeBound := by
  exact every_reachable_belief_mem_catalogue
    observe B probeCount outcomeBound history hreal hbound

/--
Certificate joining the SAME distinct visited-belief count to all three bounds.
The fields are deliberately explicit: each side of the final minimum must be
independently justified rather than inferred from a slogan.
-/
structure OperationalSemanticCertificate where
  distinctVisited : Nat
  effectiveClasses : Nat
  probeCount : Nat
  outcomeBound : Nat
  branching : Nat
  depth : Nat
  semantic_ok :
    distinctVisited ≤ semanticBound effectiveClasses
  reachable_ok :
    distinctVisited ≤ reachableBound probeCount outcomeBound
  prospective_ok :
    distinctVisited ≤ prospectiveBound branching depth

theorem certificate_respects_operational_ceiling
    (cert : OperationalSemanticCertificate) :
    cert.distinctVisited ≤
      operationalCeiling cert.effectiveClasses cert.probeCount
        cert.outcomeBound cert.branching cert.depth := by
  exact operational_semantic_size_law
    cert.distinctVisited
    cert.effectiveClasses
    cert.probeCount
    cert.outcomeBound
    cert.branching
    cert.depth
    cert.semantic_ok
    cert.reachable_ok
    cert.prospective_ok

/--
Build the final certificate when the semantic and reachable bounds have been
certified and the prospective side comes from an actual bounded plan trace.
-/
def certificateFromPlanTrace
    {S : Type}
    (K effectiveClasses probeCount outcomeBound branching depth : Nat)
    (trace : PlanTrace S)
    (hdistinct_le_occurrences : K ≤ trace.visits.length)
    (hwithin : TreeWithin branching depth trace.tree)
    (hsemantic : K ≤ semanticBound effectiveClasses)
    (hreachable : K ≤ reachableBound probeCount outcomeBound) :
    OperationalSemanticCertificate :=
  {
    distinctVisited := K
    effectiveClasses := effectiveClasses
    probeCount := probeCount
    outcomeBound := outcomeBound
    branching := branching
    depth := depth
    semantic_ok := hsemantic
    reachable_ok := hreachable
    prospective_ok :=
      distinct_visits_le_prospective K branching depth trace
        hdistinct_le_occurrences hwithin
  }

/--
End-to-end final theorem for a bounded plan trace.
-/
theorem operational_semantic_size_from_plan
    {S : Type}
    (K effectiveClasses probeCount outcomeBound branching depth : Nat)
    (trace : PlanTrace S)
    (hdistinct_le_occurrences : K ≤ trace.visits.length)
    (hwithin : TreeWithin branching depth trace.tree)
    (hsemantic : K ≤ semanticBound effectiveClasses)
    (hreachable : K ≤ reachableBound probeCount outcomeBound) :
    K ≤ operationalCeiling effectiveClasses probeCount outcomeBound
      branching depth := by
  let cert :=
    certificateFromPlanTrace K effectiveClasses probeCount outcomeBound
      branching depth trace hdistinct_le_occurrences hwithin
      hsemantic hreachable
  exact certificate_respects_operational_ceiling cert

/-- Concrete checkpoint matching the ternary depth-8 adversarial family. -/
theorem ternary_depth8_prospective_bound :
    prospectiveBound 3 8 = 9841 := by
  decide

#print axioms le_minNat
#print axioms operational_semantic_size_law
#print axioms planTrace_occurrences_le
#print axioms distinct_visits_le_prospective
#print axioms semantic_catalogue_slot_count
#print axioms reachable_catalogue_slot_count
#print axioms reachable_history_lands_in_operational_catalogue
#print axioms certificate_respects_operational_ceiling
#print axioms operational_semantic_size_from_plan
#print axioms ternary_depth8_prospective_bound

end InsacermoOperationalSemanticSize
