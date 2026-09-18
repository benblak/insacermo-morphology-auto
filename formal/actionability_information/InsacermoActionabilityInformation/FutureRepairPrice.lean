import InsacermoActionabilityInformation.EventualObstructionRank

namespace InsacermoActionabilityInformation

namespace FutureRepairPrice

open TemporalObstructionPersistence
open FutureDepthSpectrum
open EventualFutureGeometry
open EventualObstructionRank

/-- A repair action of cost at most `budget` makes bundle `F` eventually
recoverable when applying that repair to the current state produces a finite
future depth.  The repair language itself is left abstract. -/
def EventualRepairWithinBudget
    {Q X Repair : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (applyRepair : Repair → X → X) (cost : Repair → ℕ)
    (x : X) (F : Finset Q) (budget : ℕ) : Prop :=
  ∃ r : Repair,
    cost r ≤ budget ∧
    (EventualFutureComplex Avail Step (applyRepair r x)).feasible F

/-- Deadline repair: after a repair of cost at most `budget`, the future
bundle has joint recovery depth at most `H`. -/
def DeadlineRepairWithinBudget
    {Q X Repair : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (applyRepair : Repair → X → X) (cost : Repair → ℕ)
    (x : X) (F : Finset Q) (H budget : ℕ) : Prop :=
  ∃ r : Repair,
    cost r ≤ budget ∧
    DepthAtMost (Spectrum Avail Step (applyRepair r x) F) H

/-- Increasing the repair budget cannot destroy eventual repairability. -/
theorem eventualRepairWithinBudget_mono
    {Q X Repair : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X} {cost : Repair → ℕ}
    {x : X} {F : Finset Q} {b b' : ℕ}
    (hbb : b ≤ b')
    (h : EventualRepairWithinBudget Avail Step applyRepair cost x F b) :
    EventualRepairWithinBudget Avail Step applyRepair cost x F b' := by
  rcases h with ⟨r, hcost, hfeas⟩
  exact ⟨r, Nat.le_trans hcost hbb, hfeas⟩

/-- Increasing the repair budget cannot destroy deadline repairability. -/
theorem deadlineRepairWithinBudget_mono
    {Q X Repair : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X} {cost : Repair → ℕ}
    {x : X} {F : Finset Q} {H b b' : ℕ}
    (hbb : b ≤ b')
    (h : DeadlineRepairWithinBudget Avail Step applyRepair cost x F H b) :
    DeadlineRepairWithinBudget Avail Step applyRepair cost x F H b' := by
  rcases h with ⟨r, hcost, hdepth⟩
  exact ⟨r, Nat.le_trans hcost hbb, hdepth⟩

/-- Existence of some finite-cost repair restoring eventual recoverability. -/
def HasEventualRepair
    {Q X Repair : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (applyRepair : Repair → X → X) (cost : Repair → ℕ)
    (x : X) (F : Finset Q) : Prop :=
  ∃ budget, EventualRepairWithinBudget
    Avail Step applyRepair cost x F budget

/-- Existence of some finite-cost repair restoring the bundle by deadline H. -/
def HasDeadlineRepair
    {Q X Repair : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (applyRepair : Repair → X → X) (cost : Repair → ℕ)
    (x : X) (F : Finset Q) (H : ℕ) : Prop :=
  ∃ budget, DeadlineRepairWithinBudget
    Avail Step applyRepair cost x F H budget

/-- Exact minimum finite cost required to make a future bundle eventually
recoverable, provided some finite-cost repair exists. -/
noncomputable def EventualRepairPrice
    {Q X Repair : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (applyRepair : Repair → X → X) (cost : Repair → ℕ)
    (x : X) (F : Finset Q)
    (hrepair : HasEventualRepair Avail Step applyRepair cost x F) : ℕ := by
  classical
  exact Nat.find hrepair

/-- Exact minimum finite cost required to recover a bundle by deadline H. -/
noncomputable def DeadlineRepairPrice
    {Q X Repair : Type*} [DecidableEq Q]
    (Avail : X → Set Q) (Step : X → X → Prop)
    (applyRepair : Repair → X → X) (cost : Repair → ℕ)
    (x : X) (F : Finset Q) (H : ℕ)
    (hrepair : HasDeadlineRepair Avail Step applyRepair cost x F H) : ℕ := by
  classical
  exact Nat.find hrepair

/-- The eventual repair price is itself a sufficient repair budget. -/
theorem eventualRepairPrice_spec
    {Q X Repair : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X} {cost : Repair → ℕ}
    {x : X} {F : Finset Q}
    (hrepair : HasEventualRepair Avail Step applyRepair cost x F) :
    EventualRepairWithinBudget Avail Step applyRepair cost x F
      (EventualRepairPrice Avail Step applyRepair cost x F hrepair) := by
  classical
  unfold EventualRepairPrice
  exact Nat.find_spec hrepair

/-- No smaller budget than the eventual repair price can restore the bundle. -/
theorem eventualRepairPrice_minimal
    {Q X Repair : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X} {cost : Repair → ℕ}
    {x : X} {F : Finset Q}
    (hrepair : HasEventualRepair Avail Step applyRepair cost x F)
    {b : ℕ}
    (hb : EventualRepairWithinBudget Avail Step applyRepair cost x F b) :
    EventualRepairPrice Avail Step applyRepair cost x F hrepair ≤ b := by
  classical
  unfold EventualRepairPrice
  exact Nat.find_min' hrepair hb

/-- The deadline repair price is itself a sufficient deadline budget. -/
theorem deadlineRepairPrice_spec
    {Q X Repair : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X} {cost : Repair → ℕ}
    {x : X} {F : Finset Q} {H : ℕ}
    (hrepair : HasDeadlineRepair Avail Step applyRepair cost x F H) :
    DeadlineRepairWithinBudget Avail Step applyRepair cost x F H
      (DeadlineRepairPrice Avail Step applyRepair cost x F H hrepair) := by
  classical
  unfold DeadlineRepairPrice
  exact Nat.find_spec hrepair

/-- No smaller budget than the deadline repair price can recover by H. -/
theorem deadlineRepairPrice_minimal
    {Q X Repair : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X} {cost : Repair → ℕ}
    {x : X} {F : Finset Q} {H : ℕ}
    (hrepair : HasDeadlineRepair Avail Step applyRepair cost x F H)
    {b : ℕ}
    (hb : DeadlineRepairWithinBudget Avail Step applyRepair cost x F H b) :
    DeadlineRepairPrice Avail Step applyRepair cost x F H hrepair ≤ b := by
  classical
  unfold DeadlineRepairPrice
  exact Nat.find_min' hrepair hb

/-- Any deadline repair is automatically an eventual repair at the same budget. -/
theorem deadlineRepair_implies_eventualRepair
    {Q X Repair : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X} {cost : Repair → ℕ}
    {x : X} {F : Finset Q} {H b : ℕ}
    (h : DeadlineRepairWithinBudget Avail Step applyRepair cost x F H b) :
    EventualRepairWithinBudget Avail Step applyRepair cost x F b := by
  rcases h with ⟨r, hcost, hdepth⟩
  refine ⟨r, hcost, ?_⟩
  exact (eventualFutureComplex_feasible_iff_spectrum_finite).2
    (by
      cases hs : Spectrum Avail Step (applyRepair r x) F with
      | finite d =>
          exact ⟨d, hs⟩
      | infinite =>
          rw [hs] at hdepth
          simp [DepthAtMost] at hdepth)

/-- Therefore existence of a deadline repair implies existence of an eventual
repair. -/
theorem hasDeadlineRepair_implies_hasEventualRepair
    {Q X Repair : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X} {cost : Repair → ℕ}
    {x : X} {F : Finset Q} {H : ℕ}
    (h : HasDeadlineRepair Avail Step applyRepair cost x F H) :
    HasEventualRepair Avail Step applyRepair cost x F := by
  rcases h with ⟨b, hb⟩
  exact ⟨b, deadlineRepair_implies_eventualRepair hb⟩

/-- Meeting a deadline can never be cheaper than merely restoring eventual
recoverability, whenever both exact minima are instantiated from the same
deadline-repair witness. -/
theorem eventualRepairPrice_le_deadlineRepairPrice
    {Q X Repair : Type*} [DecidableEq Q]
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X} {cost : Repair → ℕ}
    {x : X} {F : Finset Q} {H : ℕ}
    (hdeadline : HasDeadlineRepair Avail Step applyRepair cost x F H) :
    let heventual :=
      hasDeadlineRepair_implies_hasEventualRepair hdeadline
    EventualRepairPrice Avail Step applyRepair cost x F heventual ≤
      DeadlineRepairPrice Avail Step applyRepair cost x F H hdeadline := by
  intro heventual
  apply eventualRepairPrice_minimal heventual
  exact deadlineRepair_implies_eventualRepair
    (deadlineRepairPrice_spec hdeadline)

end FutureRepairPrice

end InsacermoActionabilityInformation
