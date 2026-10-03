import Std
import CostlyProbeMinimal
import SafeProbeTheorem
import ProbeRepairKernel
import ProbePriceKernel

/-!
INSACERMO — Probe / Reserve-Debt Bridge V1

This file connects the certified probe-repair price layer to the existing strict
reserve/debt admissibility rule.

Interpretation:
- rho0  : initial reserve
- debt  : already certified accumulated debt D_t
- price : certified additional repair price Pi for the contemplated probe

The probe remains admissible exactly when the total certified debt after paying
the repair price is still strictly below reserve:

    debt + price < rho0

No weakening from strict (<) to non-strict (≤) is introduced here.
-/

namespace InsacermoProbeReserveDebt

/-- Strict reserve/debt admissibility after accounting for the probe repair price. -/
def ProbeAffordable (rho0 debt price : Nat) : Prop :=
  debt + price < rho0

/-- Existing temporal safety rule before paying any additional probe price. -/
def DebtSafe (rho0 debt : Nat) : Prop :=
  debt < rho0

/--
A zero-price probe preserves the existing strict reserve/debt criterion exactly.
-/
theorem zero_price_iff_existing_safe
    (rho0 debt : Nat) :
    ProbeAffordable rho0 debt 0 ↔ DebtSafe rho0 debt := by
  simp [ProbeAffordable, DebtSafe]

/--
Any affordable priced probe was already debt-safe before the probe.
-/
theorem affordable_implies_existing_safe
    (rho0 debt price : Nat)
    (h : ProbeAffordable rho0 debt price) :
    DebtSafe rho0 debt := by
  unfold ProbeAffordable at h
  unfold DebtSafe
  omega

/--
The price is literally additional certified debt in this bridge.
-/
theorem post_probe_debt_is_debt_plus_price
    (debt price : Nat) :
    debt + price = debt + price := by
  rfl

/--
Strictness is preserved: equality with the reserve is not admissible.
-/
theorem equality_to_reserve_is_refused
    (rho0 debt price : Nat)
    (h : debt + price = rho0) :
    ¬ ProbeAffordable rho0 debt price := by
  unfold ProbeAffordable
  omega

/--
If the contemplated repair price alone exhausts or exceeds the remaining reserve margin,
the probe must be refused by the strict rule.
-/
theorem price_exhausting_margin_is_refused
    (rho0 debt price : Nat)
    (h : rho0 ≤ debt + price) :
    ¬ ProbeAffordable rho0 debt price := by
  unfold ProbeAffordable
  omega

/--
If the total post-probe debt is strictly below reserve, the strict temporal rule is satisfied.
-/
theorem affordable_exactly_strict_post_debt
    (rho0 debt price : Nat) :
    ProbeAffordable rho0 debt price ↔ debt + price < rho0 := by
  rfl

inductive ProbeDecision where
  | probe
  | repairProbe
  | refuse
deriving DecidableEq, Repr

/--
Decision rule:
- price = 0 and affordable: PROBE
- price > 0 and affordable: REPAIR + PROBE
- otherwise: REFUSE
-/
def decideProbe (rho0 debt price : Nat) : ProbeDecision :=
  if h : debt + price < rho0 then
    if price = 0 then .probe else .repairProbe
  else
    .refuse

theorem decision_probe_sound
    (rho0 debt price : Nat)
    (h : decideProbe rho0 debt price = .probe) :
    ProbeAffordable rho0 debt price ∧ price = 0 := by
  unfold decideProbe at h
  split at h
  next ha =>
    split at h
    next hp =>
      exact ⟨ha, hp⟩
    next hp =>
      simp at h
  next ha =>
    simp at h

theorem decision_repair_probe_sound
    (rho0 debt price : Nat)
    (h : decideProbe rho0 debt price = .repairProbe) :
    ProbeAffordable rho0 debt price ∧ price ≠ 0 := by
  unfold decideProbe at h
  split at h
  next ha =>
    split at h
    next hp =>
      simp at h
    next hp =>
      exact ⟨ha, hp⟩
  next ha =>
    simp at h

theorem decision_refuse_sound
    (rho0 debt price : Nat)
    (h : decideProbe rho0 debt price = .refuse) :
    ¬ ProbeAffordable rho0 debt price := by
  unfold decideProbe at h
  split at h
  next ha =>
    split at h <;> simp at h
  next ha =>
    exact ha

/--
Complete operational trichotomy for the bridge.
-/
theorem decision_complete
    (rho0 debt price : Nat) :
    (decideProbe rho0 debt price = .probe ∧
      ProbeAffordable rho0 debt price ∧ price = 0) ∨
    (decideProbe rho0 debt price = .repairProbe ∧
      ProbeAffordable rho0 debt price ∧ price ≠ 0) ∨
    (decideProbe rho0 debt price = .refuse ∧
      ¬ ProbeAffordable rho0 debt price) := by
  by_cases ha : debt + price < rho0
  · by_cases hp : price = 0
    · left
      have hdebt : debt < rho0 := by
        simpa [hp] using ha
      refine ⟨?_, ?_, hp⟩
      · simp [decideProbe, hp, hdebt]
      · unfold ProbeAffordable
        simpa [hp] using ha
    · right
      left
      refine ⟨?_, ?_, hp⟩
      · simp [decideProbe, ha, hp]
      · unfold ProbeAffordable
        exact ha
  · right
    right
    refine ⟨?_, ?_⟩
    · simp [decideProbe, ha]
    · unfold ProbeAffordable
      exact ha

#print axioms zero_price_iff_existing_safe
#print axioms affordable_implies_existing_safe
#print axioms equality_to_reserve_is_refused
#print axioms price_exhausting_margin_is_refused
#print axioms affordable_exactly_strict_post_debt
#print axioms decision_probe_sound
#print axioms decision_repair_probe_sound
#print axioms decision_refuse_sound
#print axioms decision_complete

end InsacermoProbeReserveDebt
