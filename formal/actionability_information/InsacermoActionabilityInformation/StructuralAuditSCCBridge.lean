import InsacermoActionabilityInformation.StructuralAuditKernel

namespace InsacermoActionabilityInformation

namespace StructuralAuditSCCBridge

open FutureRobustness
open StructuralAuditKernel

/-- Pairwise comparability of all distinct goals in a finite bundle under a
directed reachability-style relation. -/
def PairwiseComparableOn
    {Q : Type*} [DecidableEq Q]
    (Rel : Q → Q → Prop) (F : Finset Q) : Prop :=
  ∀ q, q ∈ F → ∀ r, r ∈ F → q ≠ r → (Rel q r ∨ Rel r q)

/-- Abstract state-goal chain characterization.
A bundle is feasible exactly when every goal is individually reachable and all
distinct goals are pairwise comparable in the eventual reachability order.

For directed graphs with state-valued goals, this is the proposition supplied
by the SCC-condensation characterization. -/
def StateGoalChainCharacterization
    {Q : Type*} [DecidableEq Q]
    (K : ContractComplex Q)
    (Reach : Q → Prop)
    (Rel : Q → Q → Prop) : Prop :=
  ∀ F : Finset Q,
    K.feasible F ↔
      (∀ q, q ∈ F → Reach q) ∧ PairwiseComparableOn Rel F

/-- The chain characterization immediately yields a complete singleton/pair
failure certificate: every failed bundle already contains a failed singleton
or pair. -/
theorem badWitnessAtMostTwo_of_chainCharacterization
    {Q : Type*} [DecidableEq Q]
    {K : ContractComplex Q}
    {Reach : Q → Prop}
    {Rel : Q → Q → Prop}
    (hchar : StateGoalChainCharacterization K Reach Rel) :
    BadWitnessAtMostTwo K := by
  classical
  intro F hbad
  by_cases hreach : ∀ q, q ∈ F → Reach q
  · by_cases hpair : PairwiseComparableOn Rel F
    · exact False.elim (hbad ((hchar F).2 ⟨hreach, hpair⟩))
    · unfold PairwiseComparableOn at hpair
      push_neg at hpair
      rcases hpair with ⟨q, hq, r, hr, hqr, hinc⟩
      refine ⟨{q, r}, ?_, ?_, ?_⟩
      · intro z hz
        simp at hz
        rcases hz with rfl | rfl
        · exact hq
        · exact hr
      · by_cases hqr' : q = r
        · subst r
          simp
        · simp [hqr']
      · intro hfeas
        have hc := (hchar ({q, r} : Finset Q)).1 hfeas
        have hcomp := hc.2 q (by simp) r (by simp) hqr
        exact hinc hcomp
  · push_neg at hreach
    rcases hreach with ⟨q, hq, hqbad⟩
    refine ⟨{q}, ?_, ?_, ?_⟩
    · intro z hz
      simpa using hq
    · simp
    · intro hfeas
      have hc := (hchar ({q} : Finset Q)).1 hfeas
      exact hqbad (hc.1 q (by simp))

/-- Therefore every minimal obstruction in a state-goal chain system has
cardinality at most two. -/
theorem minimalNonface_card_le_two_of_chainCharacterization
    {Q : Type*} [DecidableEq Q]
    {K : ContractComplex Q}
    {Reach : Q → Prop}
    {Rel : Q → Q → Prop}
    (hchar : StateGoalChainCharacterization K Reach Rel)
    {F : Finset Q}
    (hmin : MinimalNonface K F) :
    F.card ≤ 2 := by
  exact minimalNonface_card_le_two
    (badWitnessAtMostTwo_of_chainCharacterization hchar) hmin

end StructuralAuditSCCBridge

end InsacermoActionabilityInformation
