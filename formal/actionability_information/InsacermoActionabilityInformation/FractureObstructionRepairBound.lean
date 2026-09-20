import InsacermoActionabilityInformation.FirstFractureRepairLaw
import InsacermoActionabilityInformation.WeightedHittingActionability

namespace InsacermoActionabilityInformation
namespace FractureObstructionRepairBound

open FutureRobustness
open FutureDepthSpectrum
open EventualFutureGeometry
open FutureRepairPrice

structure CertifiedFractureFamily
    {Q : Type*} [DecidableEq Q]
    (before after : ContractComplex Q)
    (target : Finset Q) where
  obstructions : Finset (Finset Q)
  subset_target :
    ∀ F, F ∈ obstructions → F ⊆ target
  newly_minimal :
    ∀ F, F ∈ obstructions →
      before.feasible F ∧ MinimalNonface after F

def HitsFractureFamily
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    (canResolve : Finset Q → Finset I)
    (H : Finset I) : Prop :=
  ∀ F, F ∈ family.obstructions →
    ∃ i, i ∈ H ∧ i ∈ canResolve F

def FractureTransversalWithinBudget
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    (canResolve : Finset Q → Finset I)
    (atomCost : I → Nat)
    (budget : Nat) : Prop :=
  ∃ H : Finset I,
    SelectionCost atomCost H ≤ budget ∧
    HitsFractureFamily family canResolve H

def HasFractureTransversal
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    (canResolve : Finset Q → Finset I)
    (atomCost : I → Nat) : Prop :=
  ∃ budget, FractureTransversalWithinBudget
    family canResolve atomCost budget

noncomputable def FractureTransversalPrice
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    (canResolve : Finset Q → Finset I)
    (atomCost : I → Nat)
    (h : HasFractureTransversal family canResolve atomCost) : Nat := by
  classical
  exact Nat.find h

theorem fractureTransversalPrice_spec
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    (canResolve : Finset Q → Finset I)
    (atomCost : I → Nat)
    (h : HasFractureTransversal family canResolve atomCost) :
    FractureTransversalWithinBudget family canResolve atomCost
      (FractureTransversalPrice family canResolve atomCost h) := by
  classical
  unfold FractureTransversalPrice
  exact Nat.find_spec h

theorem fractureTransversalPrice_minimal
    {Q I : Type*} [DecidableEq Q] [DecidableEq I]
    {before after : ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    (canResolve : Finset Q → Finset I)
    (atomCost : I → Nat)
    (h : HasFractureTransversal family canResolve atomCost)
    {b : Nat}
    (hb : FractureTransversalWithinBudget family canResolve atomCost b) :
    FractureTransversalPrice family canResolve atomCost h ≤ b := by
  classical
  unfold FractureTransversalPrice
  exact Nat.find_min' h hb

def RepairAtomsSoundForFracture
    {Q I X Repair : Type*}
    [DecidableEq Q] [DecidableEq I]
    {before after : ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    (Avail : X → Set Q) (Step : X → X → Prop)
    (applyRepair : Repair → X → X)
    (xAfter : X)
    (support : Repair → Finset I)
    (canResolve : Finset Q → Finset I) : Prop :=
  ∀ r F, F ∈ family.obstructions →
    (EventualFutureComplex Avail Step (applyRepair r xAfter)).feasible F →
    ∃ i, i ∈ support r ∧ i ∈ canResolve F

theorem successful_target_repair_hits_fracture_family
    {Q I X Repair : Type*}
    [DecidableEq Q] [DecidableEq I]
    {before after : ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X}
    {xAfter : X}
    {support : Repair → Finset I}
    {canResolve : Finset Q → Finset I}
    (hsound :
      RepairAtomsSoundForFracture
        family Avail Step applyRepair xAfter support canResolve)
    {r : Repair}
    (hrepair :
      (EventualFutureComplex Avail Step (applyRepair r xAfter)).feasible target) :
    HitsFractureFamily family canResolve (support r) := by
  intro F hF
  have hFfeas :
      (EventualFutureComplex Avail Step (applyRepair r xAfter)).feasible F := by
    exact (EventualFutureComplex Avail Step (applyRepair r xAfter)).downward
      hrepair (family.subset_target F hF)
  exact hsound r F hF hFfeas

theorem successful_repair_yields_transversal_budget
    {Q I X Repair : Type*}
    [DecidableEq Q] [DecidableEq I]
    {before after : ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X}
    {xAfter : X}
    {support : Repair → Finset I}
    {canResolve : Finset Q → Finset I}
    {atomCost : I → Nat}
    {repairCost : Repair → Nat}
    (hsound :
      RepairAtomsSoundForFracture
        family Avail Step applyRepair xAfter support canResolve)
    (hcost :
      ∀ r, SelectionCost atomCost (support r) ≤ repairCost r)
    {r : Repair}
    (hrepair :
      (EventualFutureComplex Avail Step (applyRepair r xAfter)).feasible target) :
    FractureTransversalWithinBudget
      family canResolve atomCost (repairCost r) := by
  refine ⟨support r, hcost r, ?_⟩
  exact successful_target_repair_hits_fracture_family family hsound hrepair

theorem hasFractureTransversal_of_hasEventualRepair
    {Q I X Repair : Type*}
    [DecidableEq Q] [DecidableEq I]
    {before after : ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X}
    {repairCost : Repair → Nat}
    {xAfter : X}
    {support : Repair → Finset I}
    {canResolve : Finset Q → Finset I}
    {atomCost : I → Nat}
    (hrepair :
      HasEventualRepair Avail Step applyRepair repairCost xAfter target)
    (hsound :
      RepairAtomsSoundForFracture
        family Avail Step applyRepair xAfter support canResolve)
    (hcost :
      ∀ r, SelectionCost atomCost (support r) ≤ repairCost r) :
    HasFractureTransversal family canResolve atomCost := by
  rcases hrepair with ⟨budget, r, hrcost, hrfeas⟩
  refine ⟨budget, ?_⟩
  exact successful_repair_yields_transversal_budget
    family hsound hcost hrfeas

theorem fractureTransversalPrice_le_eventualRepairPrice
    {Q I X Repair : Type*}
    [DecidableEq Q] [DecidableEq I]
    {before after : ContractComplex Q}
    {target : Finset Q}
    (family : CertifiedFractureFamily before after target)
    {Avail : X → Set Q} {Step : X → X → Prop}
    {applyRepair : Repair → X → X}
    {repairCost : Repair → Nat}
    {xAfter : X}
    {support : Repair → Finset I}
    {canResolve : Finset Q → Finset I}
    {atomCost : I → Nat}
    (hrepair :
      HasEventualRepair Avail Step applyRepair repairCost xAfter target)
    (hsound :
      RepairAtomsSoundForFracture
        family Avail Step applyRepair xAfter support canResolve)
    (hcost :
      ∀ r, SelectionCost atomCost (support r) ≤ repairCost r) :
    let htrans :=
      hasFractureTransversal_of_hasEventualRepair
        family hrepair hsound hcost
    FractureTransversalPrice family canResolve atomCost htrans ≤
      EventualRepairPrice
        Avail Step applyRepair repairCost xAfter target hrepair := by
  intro htrans
  have hprice :=
    eventualRepairPrice_spec
      (Avail := Avail) (Step := Step)
      (applyRepair := applyRepair) (cost := repairCost)
      (x := xAfter) (F := target) hrepair
  rcases hprice with ⟨r, hrcost, hrfeas⟩
  apply fractureTransversalPrice_minimal
    family canResolve atomCost htrans
  exact ⟨support r,
    Nat.le_trans (hcost r) hrcost,
    successful_target_repair_hits_fracture_family family hsound hrfeas⟩

end FractureObstructionRepairBound
end InsacermoActionabilityInformation
