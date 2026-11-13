/-
INSACERMO — Independent Berge audit reconstruction, 2026-11-13.
NOT the original file written by Claude.
Finite worlds, finite action-success regions, and one binary observation.
This file is intentionally isolated from the frozen INSACERMO engine.
-/
import Mathlib.Data.Finset.Card

namespace InsacermoBergeAudit

variable {W : Type*} [DecidableEq W]

/-- A single action must succeed on every still-possible world. -/
def Feasible (actions : Finset (Finset W)) (B : Finset W) : Prop :=
  ∃ a ∈ actions, B ⊆ a

/-- No declared action can guarantee the contract on this set of worlds. -/
def Obstruction (actions : Finset (Finset W)) (B : Finset W) : Prop :=
  ¬ Feasible actions B

/-- Infeasible, while each strict subset is feasible. -/
def MinimalObstruction (actions : Finset (Finset W)) (B : Finset W) : Prop :=
  Obstruction actions B ∧
    ∀ C : Finset W, C ⊂ B → Feasible actions C

/-- A finite obstruction always contains a minimal obstruction. -/
private theorem extract_minimal_obstruction
    (actions : Finset (Finset W)) :
    ∀ B : Finset W, Obstruction actions B →
      ∃ M : Finset W, M ⊆ B ∧ MinimalObstruction actions M := by
  classical
  intro B
  apply Finset.strongInductionOn B
  intro B ih hB
  by_cases hsmaller :
      ∃ C : Finset W, C ⊂ B ∧ Obstruction actions C
  · obtain ⟨C, hCB, hC⟩ := hsmaller
    obtain ⟨M, hMC, hM⟩ := ih C hCB hC
    exact ⟨M, hMC.trans (le_of_lt hCB), hM⟩
  · refine ⟨B, Finset.Subset.rfl, ⟨hB, ?_⟩⟩
    intro C hCB
    by_contra hnot
    exact hsmaller ⟨C, hCB, hnot⟩

/--
Increasing the available action regions cannot introduce a minimal obstruction
without an old minimal obstruction contained in it.
-/
theorem new_obstruction_contains_old
    (oldActions newActions : Finset (Finset W))
    (hExpand : oldActions ⊆ newActions)
    (B : Finset W)
    (hNew : MinimalObstruction newActions B) :
    ∃ M : Finset W, M ⊆ B ∧ MinimalObstruction oldActions M := by
  classical
  have hOld : Obstruction oldActions B := by
    intro hF
    apply hNew.1
    obtain ⟨a, ha, hBa⟩ := hF
    exact ⟨a, hExpand ha, hBa⟩
  exact extract_minimal_obstruction oldActions B hOld

/-- Numerical consequence for each new minimal obstruction. -/
theorem old_obstruction_card_le_new
    (oldActions newActions : Finset (Finset W))
    (hExpand : oldActions ⊆ newActions)
    (B : Finset W)
    (hNew : MinimalObstruction newActions B) :
    ∃ M : Finset W,
      MinimalObstruction oldActions M ∧ M.card ≤ B.card := by
  obtain ⟨M, hsub, hmin⟩ :=
    new_obstruction_contains_old oldActions newActions hExpand B hNew
  exact ⟨M, hmin, Finset.card_le_card hsub⟩

/-- Binary observation followed by one action selected per observation result. -/
def ObservationFeasible
    (B : Finset W) (p : W → Bool)
    (actions : Finset (Finset W)) : Prop :=
  ∀ r : Bool, ∃ a ∈ actions,
    ∀ w ∈ B, p w = r → w ∈ a

/-- Set of worlds consistent with a particular observation result. -/
def Fiber (B : Finset W) (p : W → Bool) (r : Bool) : Finset W :=
  B.filter (fun w => p w = r)

/--
Exact observation criterion:
a binary probe followed by an action guarantees the contract if and only if
each observation fiber is feasible under one fixed action.
-/
theorem obs_feas_iff
    (B : Finset W) (p : W → Bool)
    (actions : Finset (Finset W)) :
    ObservationFeasible B p actions ↔
      ∀ r : Bool, Feasible actions (Fiber B p r) := by
  classical
  constructor
  · intro h r
    obtain ⟨a, ha, hWorks⟩ := h r
    refine ⟨a, ha, ?_⟩
    intro w hw
    have hPair := Finset.mem_filter.mp hw
    exact hWorks w hPair.1 hPair.2
  · intro h r
    obtain ⟨a, ha, hSub⟩ := h r
    refine ⟨a, ha, ?_⟩
    intro w hw hp
    apply hSub
    exact Finset.mem_filter.mpr ⟨hw, hp⟩

#print axioms InsacermoBergeAudit.new_obstruction_contains_old
#print axioms InsacermoBergeAudit.old_obstruction_card_le_new
#print axioms InsacermoBergeAudit.obs_feas_iff
end InsacermoBergeAudit
