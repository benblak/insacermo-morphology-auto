import InsacermoActionabilityInformation.ObstructionRankLocalAudit
import InsacermoActionabilityInformation.HypergraphActionability

namespace InsacermoActionabilityInformation

namespace ActionabilityAudit

variable {S A : Type*} [DecidableEq S]

/-- The abstract finite-contract satisfiability predicate instantiated by
common-action feasibility: a finite family of worlds is satisfiable exactly
when one currently available action is good for all of them. -/
def commonActionSat (Good : S → A → Prop) (C : Set A) (F : Finset S) : Prop :=
  HasCommonActionOn Good C F

/-- When at least one capability is available, INSACERMO's minimal
common-action obstruction is exactly the generic finite-contract minimal UNSAT
notion.  Nonemptiness of `C` matters only for the empty subcontract. -/
theorem minimalCommonActionObstruction_iff_abstract
    {Good : S → A → Prop} {C : Set A} (hC : C.Nonempty)
    {F : Finset S} :
    MinimalCommonActionObstruction Good C F ↔
      FiniteContractAudit.IsMinimalUnsat (commonActionSat Good C) F := by
  constructor
  · intro hmin
    constructor
    · exact hmin.1.2
    · intro G hGF
      by_cases hG : G.Nonempty
      · exact hmin.2 G hGF hG
      · rcases hC with ⟨a, haC⟩
        refine ⟨a, haC, ?_⟩
        intro s hs
        exact (hG ⟨s, hs⟩).elim
  · intro hmin
    have hFne : F.Nonempty := by
      by_contra hF
      have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      rcases hC with ⟨a, haC⟩
      apply hmin.1
      subst F
      refine ⟨a, haC, ?_⟩
      intro s hs
      simp at hs
    refine ⟨⟨hFne, hmin.1⟩, ?_⟩
    intro G hGF hGne
    exact hmin.2 G hGF

/-- Capability-relative obstruction rank at most `k`: every minimal family of
worlds with no common available good action has cardinality at most `k`. -/
def CommonActionObstructionRankAtMost
    (Good : S → A → Prop) (C : Set A) (k : ℕ) : Prop :=
  ∀ F : Finset S, MinimalCommonActionObstruction Good C F → F.card ≤ k

/-- Under nonempty capability, the actionability-specific obstruction rank is
exactly the abstract finite-contract obstruction rank. -/
theorem commonActionObstructionRankAtMost_iff_abstract
    {Good : S → A → Prop} {C : Set A} (hC : C.Nonempty) (k : ℕ) :
    CommonActionObstructionRankAtMost Good C k ↔
      FiniteContractAudit.ObstructionRankAtMost (commonActionSat Good C) k := by
  constructor
  · intro hrank F hmin
    exact hrank F ((minimalCommonActionObstruction_iff_abstract hC).mpr hmin)
  · intro hrank F hmin
    exact hrank F ((minimalCommonActionObstruction_iff_abstract hC).mp hmin)

/-- Exact actionability local-audit theorem: bounded size of all minimal
common-action obstructions is equivalent to completeness of checking every
world-subcontract through that same size. -/
theorem commonActionObstructionRankAtMost_iff_localAuditComplete
    {Good : S → A → Prop} {C : Set A} (hC : C.Nonempty) (k : ℕ) :
    CommonActionObstructionRankAtMost Good C k ↔
      FiniteContractAudit.LocalAuditComplete (commonActionSat Good C) k := by
  calc
    CommonActionObstructionRankAtMost Good C k ↔
        FiniteContractAudit.ObstructionRankAtMost (commonActionSat Good C) k :=
      commonActionObstructionRankAtMost_iff_abstract hC k
    _ ↔ FiniteContractAudit.LocalAuditComplete (commonActionSat Good C) k :=
      FiniteContractAudit.obstructionRankAtMost_iff_localAuditComplete
        (commonActionSat Good C) k

/-- If minimal common-action obstructions are unbounded, no fixed finite audit
of world-subcontract cardinality can certify global common-action feasibility. -/
theorem unboundedCommonActionObstructions_implies_no_fixed_localAudit
    {Good : S → A → Prop} {C : Set A} (hC : C.Nonempty)
    (hunbounded :
      ∀ k : ℕ, ∃ F : Finset S,
        MinimalCommonActionObstruction Good C F ∧ k < F.card) :
    ∀ k : ℕ,
      ¬ FiniteContractAudit.LocalAuditComplete (commonActionSat Good C) k := by
  apply FiniteContractAudit.unboundedMinimalObstructions_implies_no_fixed_localAudit
  intro k
  rcases hunbounded k with ⟨F, hmin, hk⟩
  exact ⟨F, (minimalCommonActionObstruction_iff_abstract hC).mp hmin, hk⟩

end ActionabilityAudit

end InsacermoActionabilityInformation
