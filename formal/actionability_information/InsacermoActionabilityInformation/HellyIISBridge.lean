import InsacermoActionabilityInformation.CertificatePreAuditDepth
import InsacermoActionabilityInformation.StructuralAuditKernel
import Mathlib

namespace InsacermoActionabilityInformation

namespace HellyIISBridge

open FutureRobustness
open StructuralAuditKernel
open CertificatePreAudit

variable {Q X : Type*} [DecidableEq Q]

/-- The conflict hypergraph of an arbitrary finite-bundle feasibility family:
its hyperedges are exactly the inclusion-minimal failed bundles.

This is the generic INSACERMO object corresponding to MUS/IIS/conflict
hyperedges in the classical literatures. -/
def ConflictHypergraph
    (P : FeasibilityFamily Q) : Set (Finset Q) :=
  {F | MinimalFailure P F}

/-- Rank-at-most statement for the conflict hypergraph. -/
def ConflictRankAtMost
    (P : FeasibilityFamily Q) (r : ℕ) : Prop :=
  ∀ F : Finset Q, F ∈ ConflictHypergraph P → F.card ≤ r

/-- INSACERMO actual obstruction-depth upper bounds are definitionally the same
as rank upper bounds on the minimal-conflict hypergraph. -/
theorem actualDepthAtMost_iff_conflictRankAtMost
    {P : FeasibilityFamily Q} {r : ℕ} :
    ActualDepthAtMost P r ↔ ConflictRankAtMost P r := by
  rfl

/-- Feasibility induced by a finite family of sets: a bundle of requirements
is feasible exactly when all corresponding sets have a common point. -/
def IntersectionFeasible
    (K : Q → Set X) (F : Finset Q) : Prop :=
  ∃ x : X, ∀ q, q ∈ F → x ∈ K q

/-- Intersection feasibility is downward closed. -/
theorem intersectionFeasible_downward
    (K : Q → Set X)
    {F G : Finset Q}
    (hF : IntersectionFeasible K F)
    (hGF : G ⊆ F) :
    IntersectionFeasible K G := by
  rcases hF with ⟨x, hx⟩
  exact ⟨x, fun q hq => hx q (hGF hq)⟩

/-- Every set family induces a future-contract complex by nonempty
intersection. -/
def intersectionContract
    (K : Q → Set X) : ContractComplex Q where
  feasible := IntersectionFeasible K
  downward := by
    intro F G hF hGF
    exact intersectionFeasible_downward K hF hGF

/-- Finite Helly property with number at most r:
if every subfamily of cardinality at most r has nonempty intersection,
then the whole finite family has nonempty intersection. -/
def FiniteHellyAtMost
    (K : Q → Set X) (r : ℕ) : Prop :=
  ∀ F : Finset Q,
    (∀ G : Finset Q, G ⊆ F → G.card ≤ r →
      IntersectionFeasible K G) →
    IntersectionFeasible K F

/-- A failed contract in a downward-closed finite contract complex contains an
inclusion-minimal failed sub-contract. -/
theorem exists_minimalNonface_subset_of_failure
    {K : ContractComplex Q} {F : Finset Q}
    (hbad : ¬ K.feasible F) :
    ∃ G : Finset Q, G ⊆ F ∧ MinimalNonface K G := by
  classical
  induction F using Finset.strongInductionOn with
  | H F ih =>
      by_cases hdel : ∀ q, q ∈ F → K.feasible (F.erase q)
      · refine ⟨F, Finset.Subset.rfl, hbad, ?_⟩
        intro G hGF
        have hnot : ¬ F ⊆ G := hGF.2
        push_neg at hnot
        rcases hnot with ⟨q, hqF, hqG⟩
        have hGdel : G ⊆ F.erase q := by
          intro x hxG
          exact Finset.mem_erase.mpr ⟨by
            intro hxq
            subst x
            exact hqG hxG, hGF.1 hxG⟩
        exact K.downward (hdel q hqF) hGdel
      · push_neg at hdel
        rcases hdel with ⟨q, hqF, hbadDel⟩
        have hcard : (F.erase q).card < F.card :=
          Finset.card_erase_lt_of_mem hqF
        rcases ih (F.erase q) hcard hbadDel with ⟨G, hGF, hmin⟩
        exact ⟨G, hGF.trans (Finset.erase_subset q F), hmin⟩

/-- For downward-closed contract complexes, the generic bounded-bad-witness
property is equivalent to saying that every minimal obstruction has size at
most r.  The forward implication already existed in StructuralAuditKernel;
the reverse implication uses finiteness to descend to a minimal obstruction. -/
theorem badWitnessAtMost_iff_minimalNonface_card_le
    {K : ContractComplex Q} {r : ℕ} :
    BadWitnessAtMost K r ↔
      ∀ F : Finset Q, MinimalNonface K F → F.card ≤ r := by
  constructor
  · intro hcert F hmin
    exact minimalNonface_card_le_of_boundedWitness hcert hmin
  · intro hmin F hbad
    rcases exists_minimalNonface_subset_of_failure hbad with ⟨G, hGF, hGmin⟩
    exact ⟨G, hGF, hmin G hGmin, hGmin.1⟩

/-- In the intersection model, a Helly bound is exactly the bounded-witness
property: every empty finite intersection already has an empty subintersection
of size at most r. -/
theorem finiteHellyAtMost_iff_badWitnessAtMost
    {K : Q → Set X} {r : ℕ} :
    FiniteHellyAtMost K r ↔
      BadWitnessAtMost (intersectionContract K) r := by
  constructor
  · intro hHelly F hbad
    by_contra hno
    push_neg at hno
    have hall :
        ∀ G : Finset Q, G ⊆ F → G.card ≤ r →
          IntersectionFeasible K G := by
      intro G hGF hcard
      by_contra hGbad
      exact hno G hGF hcard hGbad
    exact hbad (hHelly F hall)
  · intro hbad F hall
    by_contra hFbad
    rcases hbad F hFbad with ⟨G, hGF, hcard, hGbad⟩
    exact hGbad (hall G hGF hcard)

/-- MinimalFailure and MinimalNonface coincide for any ContractComplex. -/
theorem minimalFailure_iff_minimalNonface
    {K : ContractComplex Q} {F : Finset Q} :
    MinimalFailure K.feasible F ↔ MinimalNonface K F := by
  rfl

/-- Therefore, in a finite intersection semantics, a Helly-number upper bound
is exactly an INSACERMO actual minimal-obstruction-depth upper bound.

This theorem is deliberately a literature bridge: it records that this part
of INSACERMO specializes to classical Helly-style critical-family depth and
should not be claimed as a new invariant. -/
theorem finiteHellyAtMost_iff_actualDepthAtMost
    {K : Q → Set X} {r : ℕ} :
    FiniteHellyAtMost K r ↔
      ActualDepthAtMost (IntersectionFeasible K) r := by
  rw [finiteHellyAtMost_iff_badWitnessAtMost]
  rw [badWitnessAtMost_iff_minimalNonface_card_le]
  constructor
  · intro h F hmin
    exact h F ((minimalFailure_iff_minimalNonface).mp hmin)
  · intro h F hmin
    exact h F ((minimalFailure_iff_minimalNonface).mpr hmin)

/-- Corollary: in intersection models, the conflict-hypergraph rank bound,
Helly bound, and INSACERMO actual obstruction-depth bound are the same
statement. -/
theorem finiteHellyAtMost_iff_conflictRankAtMost
    {K : Q → Set X} {r : ℕ} :
    FiniteHellyAtMost K r ↔
      ConflictRankAtMost (IntersectionFeasible K) r := by
  rw [← actualDepthAtMost_iff_conflictRankAtMost]
  exact finiteHellyAtMost_iff_actualDepthAtMost

end HellyIISBridge

end InsacermoActionabilityInformation
