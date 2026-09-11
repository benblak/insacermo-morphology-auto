import InsacermoActionabilityInformation.HigherOrderObstructions

namespace InsacermoActionabilityInformation

/-- A finite common-action obstruction that is entirely contained in one
realized observation fiber. -/
def FiberContainsFiniteObstruction {S A Y : Type*} [DecidableEq S]
    (Good : S → A → Prop) (B : Set S) (C : Set A) (h : S → Y) : Prop :=
  ∃ F : Finset S, ∃ y : Y,
    CommonActionObstruction Good C F ∧
    (∀ s, s ∈ F → s ∈ B) ∧
    (∀ s, s ∈ F → h s = y)

/-- A minimal common-action obstruction entirely contained in one observation
fiber. These are the hyperedges of the minimal obstruction hypergraph. -/
def FiberContainsMinimalObstruction {S A Y : Type*} [DecidableEq S]
    (Good : S → A → Prop) (B : Set S) (C : Set A) (h : S → Y) : Prop :=
  ∃ F : Finset S, ∃ y : Y,
    MinimalCommonActionObstruction Good C F ∧
    (∀ s, s ∈ F → s ∈ B) ∧
    (∀ s, s ∈ F → h s = y)

/-- On a finite world space, `SafeRep` is equivalent to absence of any finite
common-action obstruction inside a realized observation fiber. -/
theorem safeRep_iff_no_finite_fiber_obstruction
    {S A Y : Type*} [Fintype S] [DecidableEq S]
    {Good : S → A → Prop} {B : Set S} {C : Set A} {h : S → Y} :
    SafeRep Good B C h ↔ ¬ FiberContainsFiniteObstruction Good B C h := by
  classical
  constructor
  · intro hsafe hobs
    rcases hobs with ⟨F, y, hFobs, hFB, hFy⟩
    exact finiteObstruction_inside_fiber_blocks_safeRep hFobs hFB hFy hsafe
  · intro hno
    by_contra hsafe
    have hcriterion :
        ¬ (∀ y, RealizedFiber B h y →
          (FiberCommonActions Good B h y ∩ C).Nonempty) := by
      intro hall
      exact hsafe (safeRep_iff_fiberCommonActions_intersects.mpr hall)
    push_neg at hcriterion
    rcases hcriterion with ⟨y, hyreal, hnone⟩
    let F : Finset S := Finset.univ.filter (fun s => s ∈ B ∧ h s = y)
    have hFne : F.Nonempty := by
      rcases hyreal with ⟨s0, hs0B, hs0y⟩
      refine ⟨s0, ?_⟩
      simp [F, hs0B, hs0y]
    have hFobs : CommonActionObstruction Good C F := by
      refine ⟨hFne, ?_⟩
      intro hcommon
      rcases hcommon with ⟨a, haC, hall⟩
      apply hnone
      refine ⟨a, ?_, haC⟩
      intro s hsB hsy
      apply hall s
      simp [F, hsB, hsy]
    apply hno
    refine ⟨F, y, hFobs, ?_, ?_⟩
    · intro s hsF
      simpa [F] using hsF
    · intro s hsF
      simpa [F] using hsF

/-- Every finite obstruction contains a minimal obstruction. -/
theorem obstruction_contains_minimal
    {S A : Type*} [DecidableEq S]
    {Good : S → A → Prop} {C : Set A} {F : Finset S}
    (hobs : CommonActionObstruction Good C F) :
    ∃ M : Finset S, M ⊆ F ∧ MinimalCommonActionObstruction Good C M := by
  classical
  revert hobs
  refine Finset.strongInduction F ?_
  intro F ih hobs
  by_cases hmin : MinimalCommonActionObstruction Good C F
  · exact ⟨F, Finset.Subset.rfl, hmin⟩
  · have hnotall :
        ¬ ∀ G : Finset S, G ⊂ F → G.Nonempty → HasCommonActionOn Good C G := by
      intro hall
      exact hmin ⟨hobs, hall⟩
    push_neg at hnotall
    rcases hnotall with ⟨G, hGF, hGne, hGbad⟩
    have hGobs : CommonActionObstruction Good C G := ⟨hGne, hGbad⟩
    rcases ih G hGF hGobs with ⟨M, hMG, hMmin⟩
    exact ⟨M, Finset.Subset.trans hMG hGF.1, hMmin⟩

/-- Existence of an arbitrary finite fiber obstruction is equivalent to
existence of a minimal one. -/
theorem fiberContainsFiniteObstruction_iff_minimal
    {S A Y : Type*} [DecidableEq S]
    {Good : S → A → Prop} {B : Set S} {C : Set A} {h : S → Y} :
    FiberContainsFiniteObstruction Good B C h ↔
      FiberContainsMinimalObstruction Good B C h := by
  classical
  constructor
  · rintro ⟨F, y, hFobs, hFB, hFy⟩
    rcases obstruction_contains_minimal hFobs with ⟨M, hMF, hMmin⟩
    refine ⟨M, y, hMmin, ?_, ?_⟩
    · intro s hsM
      exact hFB s (hMF hsM)
    · intro s hsM
      exact hFy s (hMF hsM)
  · rintro ⟨F, y, hFmin, hFB, hFy⟩
    exact ⟨F, y, hFmin.1, hFB, hFy⟩

/-- Hypergraph characterization of actionability on finite world spaces:
`SafeRep` holds exactly when no realized observation fiber contains a minimal
common-action obstruction. -/
theorem safeRep_iff_no_minimal_fiber_obstruction
    {S A Y : Type*} [Fintype S] [DecidableEq S]
    {Good : S → A → Prop} {B : Set S} {C : Set A} {h : S → Y} :
    SafeRep Good B C h ↔ ¬ FiberContainsMinimalObstruction Good B C h := by
  rw [safeRep_iff_no_finite_fiber_obstruction,
      fiberContainsFiniteObstruction_iff_minimal]

/-- The minimal-obstruction hypergraph of a capability-relative contract. -/
def MinimalObstructionHypergraph {S A : Type*} [DecidableEq S]
    (Good : S → A → Prop) (C : Set A) : Set (Finset S) :=
  {F | MinimalCommonActionObstruction Good C F}

/-- A representation is hypergraph-safe when no hyperedge is collapsed inside
one admissible observation fiber. -/
def HypergraphSafe {S A Y : Type*} [DecidableEq S]
    (Good : S → A → Prop) (B : Set S) (C : Set A) (h : S → Y) : Prop :=
  ∀ F, F ∈ MinimalObstructionHypergraph Good C →
    ¬ ∃ y, (∀ s, s ∈ F → s ∈ B) ∧ (∀ s, s ∈ F → h s = y)

/-- Exact finite equivalence between `SafeRep` and hypergraph safety. -/
theorem safeRep_iff_hypergraphSafe
    {S A Y : Type*} [Fintype S] [DecidableEq S]
    {Good : S → A → Prop} {B : Set S} {C : Set A} {h : S → Y} :
    SafeRep Good B C h ↔ HypergraphSafe Good B C h := by
  rw [safeRep_iff_no_minimal_fiber_obstruction]
  constructor
  · intro hno F hF hcollapse
    apply hno
    rcases hcollapse with ⟨y, hFB, hFy⟩
    exact ⟨F, y, hF, hFB, hFy⟩
  · intro hhyper hmin
    rcases hmin with ⟨F, y, hF, hFB, hFy⟩
    exact hhyper F hF ⟨y, hFB, hFy⟩

end InsacermoActionabilityInformation
