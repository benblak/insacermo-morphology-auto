/-
INSACERMO -- certified one-probe obstruction separation (2026-11-13)
Independent extension. No Mathlib. Does not modify the frozen INSACERMO engine.
Reliable binary probes only; no adversarial lies in these statements.
-/
import InsacermoBergeCore

namespace InsacermoProbeCriterion
open InsacermoBergeCore
universe u
variable {W : Type u}

/-- All worlds in a set return the same answer to the probe. -/
def Monochromatic (p : W → Bool) (B : Region W) : Prop :=
  ∃ r : Bool, ∀ x : W, B x → p x = r

def ObservationObstruction (actions : List (Region W))
    (p : W → Bool) (B : Region W) : Prop :=
  ¬ ObservationFeasible actions B p

def MinimalObservationObstruction (actions : List (Region W))
    (p : W → Bool) (B : Region W) : Prop :=
  ObservationObstruction actions p B ∧
    ∀ S : Region W, Strict S B → ObservationFeasible actions S p

theorem obs_feasible_mono
    (actions : List (Region W)) (p : W → Bool)
    {S T : Region W} (hST : Sub S T)
    (h : ObservationFeasible actions T p) :
    ObservationFeasible actions S p := by
  intro r
  obtain ⟨a, ha, hWorks⟩ := h r
  exact ⟨a, ha, fun x hx hr => hWorks x (hST x hx) hr⟩

theorem obs_feasible_of_feasible
    (actions : List (Region W)) (p : W → Bool)
    (B : Region W) (h : Feasible actions B) :
    ObservationFeasible actions B p := by
  obtain ⟨a, ha, hWorks⟩ := h
  intro r
  exact ⟨a, ha, fun x hx _ => hWorks x hx⟩

theorem monochromatic_obstruction_is_obstruction
    (actions : List (Region W)) (p : W → Bool)
    (M : Region W) (hOld : ¬ Feasible actions M)
    (hMono : Monochromatic p M) :
    ObservationObstruction actions p M := by
  intro hObs
  obtain ⟨r, hMr⟩ := hMono
  obtain ⟨a, ha, hAction⟩ := hObs r
  apply hOld
  exact ⟨a, ha, fun x hx => hAction x hx (hMr x hx)⟩

/-- If observing p cannot guarantee an action, a finite-rank minimal old
obstruction exists entirely inside one observation fiber. -/
theorem obstruction_contains_monochromatic_minimal
    (actions : List (Region W)) (p : W → Bool)
    (rank : Region W → Nat)
    (hRank : ∀ S T : Region W, Strict S T → rank S < rank T)
    (B : Region W) (hObs : ObservationObstruction actions p B) :
    ∃ M : Region W, Sub M B ∧
      MinimalObstruction actions M ∧ Monochromatic p M := by
  have hNot : ¬ (∀ r : Bool, Feasible actions (Fiber B p r)) := by
    intro hFeas
    exact hObs ((obs_feas_iff actions B p).mpr hFeas)
  have hExists : ∃ r : Bool, ¬ Feasible actions (Fiber B p r) := by
    apply Classical.byContradiction
    intro hNo
    apply hNot
    intro r
    apply Classical.byContradiction
    intro hr
    exact hNo ⟨r, hr⟩
  obtain ⟨r, hFiberBad⟩ := hExists
  obtain ⟨M, hMF, hMNot, hMin⟩ :=
    finite_descent (fun S => ¬ Feasible actions S) rank hRank
      (Fiber B p r) hFiberBad
  have hMinimal : MinimalObstruction actions M := by
    refine ⟨hMNot, ?_⟩
    intro S hSM
    apply Classical.byContradiction
    intro hNotFeas
    exact hMin S hSM hNotFeas
  have hMB : Sub M B := by
    intro x hx
    exact (hMF x hx).1
  have hMono : Monochromatic p M := by
    refine ⟨r, ?_⟩
    intro x hx
    exact (hMF x hx).2
  exact ⟨M, hMB, hMinimal, hMono⟩

/-- A failed one-probe contract has a monochromatic old minimal obstruction,
and conversely such a witness suffices to prove failure. -/
theorem obs_obstruction_iff_witness
    (actions : List (Region W)) (p : W → Bool)
    (rank : Region W → Nat)
    (hRank : ∀ S T : Region W, Strict S T → rank S < rank T)
    (B : Region W) :
    ObservationObstruction actions p B ↔
      ∃ M : Region W, Sub M B ∧
        MinimalObstruction actions M ∧ Monochromatic p M := by
  constructor
  · intro hBad
    exact obstruction_contains_monochromatic_minimal
      actions p rank hRank B hBad
  · intro hWitness
    obtain ⟨M, hMB, hMinimal, hMono⟩ := hWitness
    intro hObs
    have hObsM := obs_feasible_mono actions p hMB hObs
    exact monochromatic_obstruction_is_obstruction
      actions p M hMinimal.1 hMono hObsM

/-- Exact characterization, not just order monotonicity:
the MINIMAL post-observation obstructions are precisely those old minimal
obstructions that are monochromatic for p. -/
theorem obs_minimal_iff_old_minimal_monochromatic
    (actions : List (Region W)) (p : W → Bool)
    (rank : Region W → Nat)
    (hRank : ∀ S T : Region W, Strict S T → rank S < rank T)
    (B : Region W) :
    MinimalObservationObstruction actions p B ↔
      MinimalObstruction actions B ∧ Monochromatic p B := by
  constructor
  · intro hNew
    obtain ⟨M, hMB, hOld, hMono⟩ :=
      (obs_obstruction_iff_witness actions p rank hRank B).mp hNew.1
    have hBM : Sub B M := by
      apply Classical.byContradiction
      intro hNot
      have hStrict : Strict M B := ⟨hMB, hNot⟩
      have hObsM := hNew.2 M hStrict
      exact monochromatic_obstruction_is_obstruction
        actions p M hOld.1 hMono hObsM
    have hMonoB : Monochromatic p B := by
      obtain ⟨r, hMonoMr⟩ := hMono
      exact ⟨r, fun x hx => hMonoMr x (hBM x hx)⟩
    have hNotFeasB : ¬ Feasible actions B := by
      intro hFeasible
      exact hNew.1 (obs_feasible_of_feasible actions p B hFeasible)
    have hAllSmaller : ∀ S : Region W,
        Strict S B → Feasible actions S := by
      intro S hSB
      obtain ⟨r, hBr⟩ := hMonoB
      obtain ⟨a, ha, hAction⟩ := hNew.2 S hSB r
      exact ⟨a, ha, fun x hx =>
        hAction x hx (hBr x (hSB.1 x hx))⟩
    exact ⟨⟨hNotFeasB, hAllSmaller⟩, hMonoB⟩
  · intro hOldMono
    obtain ⟨hOld, hMono⟩ := hOldMono
    refine ⟨monochromatic_obstruction_is_obstruction
      actions p B hOld.1 hMono, ?_⟩
    intro S hSB
    exact obs_feasible_of_feasible actions p S (hOld.2 S hSB)

/-- All old minimal obstructions of rank <= k are separated by p. -/
def SplitsAllCritical
    (actions : List (Region W)) (p : W → Bool)
    (rank : Region W → Nat) (k : Nat) : Prop :=
  ∀ M : Region W, MinimalObstruction actions M →
    rank M ≤ k → ¬ Monochromatic p M

/-- After a probe, no minimal obstruction of rank <= k remains. -/
def NoSmallObstructionAfter
    (actions : List (Region W)) (p : W → Bool)
    (rank : Region W → Nat) (k : Nat) : Prop :=
  ∀ M : Region W, MinimalObservationObstruction actions p M →
    ¬ rank M ≤ k

/-- Exact criterion for strict increase in minimum obstruction order
(with the convention that no obstructions means order infinity). -/
theorem raises_order_iff_splits_critical
    (actions : List (Region W)) (p : W → Bool)
    (rank : Region W → Nat)
    (hRank : ∀ S T : Region W, Strict S T → rank S < rank T)
    (k : Nat) :
    NoSmallObstructionAfter actions p rank k ↔
      SplitsAllCritical actions p rank k := by
  constructor
  · intro hNo M hMinimal hBound hMono
    have hAfter : MinimalObservationObstruction actions p M :=
      (obs_minimal_iff_old_minimal_monochromatic
        actions p rank hRank M).mpr ⟨hMinimal, hMono⟩
    exact hNo M hAfter hBound
  · intro hSplit M hMinObs hBound
    obtain ⟨hOld, hMono⟩ :=
      (obs_minimal_iff_old_minimal_monochromatic
        actions p rank hRank M).mp hMinObs
    exact hSplit M hOld hBound hMono

/-- Certified library-level non-improvement witness:
each permitted probe leaves at least one small monochromatic obstruction. -/
theorem library_blockage_certificate
    (actions : List (Region W)) (library : List (W → Bool))
    (rank : Region W → Nat)
    (hRank : ∀ S T : Region W, Strict S T → rank S < rank T)
    (k : Nat)
    (hWitness : ∀ p : W → Bool, p ∈ library →
      ∃ M : Region W, MinimalObstruction actions M ∧
        rank M ≤ k ∧ Monochromatic p M) :
    ∀ p : W → Bool, p ∈ library →
      ¬ NoSmallObstructionAfter actions p rank k := by
  intro p hp hRaise
  obtain ⟨M, hOld, hBound, hMono⟩ := hWitness p hp
  have hSplit :=
    (raises_order_iff_splits_critical actions p rank hRank k).mp hRaise
  exact hSplit M hOld hBound hMono

#print axioms obstruction_contains_monochromatic_minimal
#print axioms obs_minimal_iff_old_minimal_monochromatic
#print axioms raises_order_iff_splits_critical
#print axioms library_blockage_certificate

end InsacermoProbeCriterion
