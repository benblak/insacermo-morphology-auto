import Mathlib.Data.Finset.Card

namespace InsacermoActionabilityInformation

namespace FiniteContractAudit

variable {α : Type*} [DecidableEq α]

/-- A finite subcontract is inclusion-minimal UNSAT when it is itself
unsatisfiable but every strict finite subfamily is satisfiable. -/
def IsMinimalUnsat (Sat : Finset α → Prop) (F : Finset α) : Prop :=
  ¬ Sat F ∧ ∀ G : Finset α, G ⊂ F → Sat G

/-- Obstruction rank at most `k`: every minimal UNSAT core has cardinality at
most `k`. -/
def ObstructionRankAtMost (Sat : Finset α → Prop) (k : ℕ) : Prop :=
  ∀ F : Finset α, IsMinimalUnsat Sat F → F.card ≤ k

/-- A depth-`k` local audit of a finite contract `F`: every selected
subcontract of size at most `k` is satisfiable. -/
def PassesLocalAudit (Sat : Finset α → Prop) (k : ℕ) (F : Finset α) : Prop :=
  ∀ G : Finset α, G ⊆ F → G.card ≤ k → Sat G

/-- Local audit completeness at depth `k`: passing every local check through
cardinality `k` forces global satisfiability. -/
def LocalAuditComplete (Sat : Finset α → Prop) (k : ℕ) : Prop :=
  ∀ F : Finset α, PassesLocalAudit Sat k F → Sat F

/-- Every finite UNSAT contract contains an inclusion-minimal UNSAT
subcontract.  This is a pure finiteness fact; no monotonicity hypothesis on
`Sat` is required. -/
theorem exists_minimalUnsat_subset (Sat : Finset α → Prop)
    {F : Finset α} (hunsat : ¬ Sat F) :
    ∃ M : Finset α, M ⊆ F ∧ IsMinimalUnsat Sat M := by
  classical
  induction F using Finset.strongInductionOn with
  | _ F ih =>
      by_cases hex : ∃ G : Finset α, G ⊂ F ∧ ¬ Sat G
      · rcases hex with ⟨G, hGF, hGunsat⟩
        rcases ih G hGF hGunsat with ⟨M, hMG, hMmin⟩
        exact ⟨M, hMG.trans hGF.1, hMmin⟩
      · refine ⟨F, Finset.Subset.rfl, hunsat, ?_⟩
        intro G hGF
        by_contra hGunsat
        exact hex ⟨G, hGF, hGunsat⟩

/-- Bounded obstruction rank makes depth-`k` local auditing complete. -/
theorem obstructionRankAtMost_implies_localAuditComplete
    (Sat : Finset α → Prop) (k : ℕ)
    (hrank : ObstructionRankAtMost Sat k) :
    LocalAuditComplete Sat k := by
  intro F haudit
  by_contra hunsat
  rcases exists_minimalUnsat_subset Sat hunsat with ⟨M, hMF, hMmin⟩
  have hcard : M.card ≤ k := hrank M hMmin
  exact hMmin.1 (haudit M hMF hcard)

/-- If depth-`k` local auditing is complete, then no minimal UNSAT core can be
larger than `k`.  Otherwise that core itself would pass every depth-`k` audit
while remaining globally UNSAT. -/
theorem localAuditComplete_implies_obstructionRankAtMost
    (Sat : Finset α → Prop) (k : ℕ)
    (hauditComplete : LocalAuditComplete Sat k) :
    ObstructionRankAtMost Sat k := by
  intro F hmin
  by_contra hnotle
  have hklt : k < F.card := Nat.lt_of_not_ge hnotle
  have hpass : PassesLocalAudit Sat k F := by
    intro G hGF hcard
    have hne : G ≠ F := by
      intro hEq
      subst G
      exact (Nat.not_lt_of_ge hcard) hklt
    have hproper : G ⊂ F := Finset.ssubset_iff_subset_ne.2 ⟨hGF, hne⟩
    exact hmin.2 G hproper
  exact hmin.1 (hauditComplete F hpass)

/-- Exact abstract duality: a finite contract theory has obstruction rank at
most `k` if and only if checking all subcontracts through cardinality `k`
completely decides global satisfiability. -/
theorem obstructionRankAtMost_iff_localAuditComplete
    (Sat : Finset α → Prop) (k : ℕ) :
    ObstructionRankAtMost Sat k ↔ LocalAuditComplete Sat k := by
  constructor
  · exact obstructionRankAtMost_implies_localAuditComplete Sat k
  · exact localAuditComplete_implies_obstructionRankAtMost Sat k

/-- Exact No Local Auditor witness.  Any minimal UNSAT core whose size exceeds
`k` passes every local audit of depth `k` although the whole contract is
unsatisfiable. -/
theorem minimalUnsat_large_is_localAudit_blindSpot
    (Sat : Finset α → Prop) {k : ℕ} {F : Finset α}
    (hmin : IsMinimalUnsat Sat F) (hk : k < F.card) :
    PassesLocalAudit Sat k F ∧ ¬ Sat F := by
  constructor
  · intro G hGF hcard
    have hne : G ≠ F := by
      intro hEq
      subst G
      exact (Nat.not_lt_of_ge hcard) hk
    exact hmin.2 G (Finset.ssubset_iff_subset_ne.2 ⟨hGF, hne⟩)
  · exact hmin.1

/-- An unbounded family of minimal obstructions defeats every fixed finite
local audit depth. -/
def UnboundedMinimalObstructions (Sat : Finset α → Prop) : Prop :=
  ∀ k : ℕ, ∃ F : Finset α, IsMinimalUnsat Sat F ∧ k < F.card

/-- If minimal obstructions are unbounded, no fixed finite audit depth can be
complete. -/
theorem unboundedMinimalObstructions_implies_no_fixed_localAudit
    (Sat : Finset α → Prop)
    (hunbounded : UnboundedMinimalObstructions Sat) :
    ∀ k : ℕ, ¬ LocalAuditComplete Sat k := by
  intro k hcomplete
  rcases hunbounded k with ⟨F, hmin, hk⟩
  rcases minimalUnsat_large_is_localAudit_blindSpot Sat hmin hk with ⟨hpass, hunsat⟩
  exact hunsat (hcomplete F hpass)

end FiniteContractAudit

end InsacermoActionabilityInformation
