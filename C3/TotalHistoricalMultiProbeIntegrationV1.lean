import C3.LegacyTemporalRepairIntegrationV1
import ProofCarryingMultiProbeRuntimeKernelV1

/-!
INSACERMO TRUE HISTORICAL MULTI-PROBE × C3 × REPAIR (2026-10-11).
Actual October 4 kernels imported unmodified. A recursive TraceAffordable
follows EVERY possible probe outcome of a C3 plan. Costs are extracted
from the actual C3 probePrice. Strict reserve is required on each leaf.
The contracts/transformations and debt bounds are declared, not inferred.
-/
namespace INSACERMO.TotalHistoricalMulti
open INSACERMO.LegacyC3Repair
open INSACERMO.TotalRepairFuture
open INSACERMO.RecursiveC3
open INSACERMO.C3PP
open InsacermoMultiProbeBudget
open INSACERMO.ProofCarryingMultiProbeRuntimeV1
universe u v w z
variable {Scenario : Type u} {Probe : Type v} {Outcome : Type w} {State : Type z}

/-- On each terminal trace, the *actual C3 probe cost* is paid. -/
def StrictTraceReserve (M : DynamicProblem Scenario Recipe Probe Outcome)
    (rho : Nat) :
    Nat → (Scenario → Prop) → Nat → Plan Recipe Probe Outcome → Prop
  | 0, _, debt, .act _ => debt < rho
  | 0, _, _, .probe _ _ => False
  | _ + 1, _, debt, .act _ => debt < rho
  | k + 1, X, debt, .probe q next =>
      ∀ o, StrictTraceReserve M rho k (AfterDynamic M q X o)
        (debt + M.base.probeCost q) (next o)

/-- A global upper envelope of actual possible branch costs. -/
def PriceEnvelope (M : DynamicProblem Scenario Recipe Probe Outcome) :
    Nat → (Scenario → Prop) → Plan Recipe Probe Outcome → Nat → Prop
  | 0, _, .act _, _ => True
  | 0, _, .probe _ _, _ => False
  | _ + 1, _, .act _, _ => True
  | k + 1, X, .probe q next, ceiling =>
      M.base.probeCost q ≤ ceiling ∧
      ∀ o, PriceEnvelope M k (AfterDynamic M q X o)
        (next o) (ceiling - M.base.probeCost q)

/-- Sound envelope: if every branch costs at most ceiling and total debt
    plus ceiling is below reserve, no possible C3 branch can exceed reserve.
    The strict inequality is exactly the original 2026-10-04 policy. -/
theorem envelope_implies_strict_reserve
    (M : DynamicProblem Scenario Recipe Probe Outcome)
    (rho : Nat) (depth : Nat) :
    ∀ (X : Scenario → Prop) (t : Plan Recipe Probe Outcome)
      (debt ceiling : Nat),
      PriceEnvelope M depth X t ceiling →
      debt + ceiling < rho →
      StrictTraceReserve M rho depth X debt t := by
  induction depth with
  | zero =>
      intro X t debt ceiling henv hlt
      cases t with
      | act p => exact Nat.lt_of_le_of_lt (Nat.le_add_right debt ceiling) hlt
      | probe q next => exact False.elim henv
  | succ k ih =>
      intro X t debt ceiling henv hlt
      cases t with
      | act p => exact Nat.lt_of_le_of_lt (Nat.le_add_right debt ceiling) hlt
      | probe q next =>
          rcases henv with ⟨hprice, hchildren⟩
          intro o
          apply ih _ (next o) (debt + M.base.probeCost q)
            (ceiling - M.base.probeCost q) (hchildren o)
          have heq : debt + M.base.probeCost q + (ceiling - M.base.probeCost q) =
              debt + ceiling := by omega
          rw [heq]
          exact hlt

/-- The original multiprobe budget predicate remains exactly equivalent to
    the strict envelope budget when the envelope is represented as one
    certified price (no accidental weakening to ≤). -/
theorem original_multi_budget_one_envelope
    (rho debt ceiling : Nat) :
    PlanAffordable rho debt [ceiling] ↔ debt + ceiling < rho := by
  simp [PlanAffordable, debtAfterPlan]

/-- Fully joint statement. Future temporal safety from original 2026 kernel,
    direct recovery of bad-state exclusion, AND accumulated cost strictly
    under original multiprobe reserve on ALL recursively reachable branches. -/
theorem ALL_BRANCHES_FUTURE_AND_RESERVE
    (m n : Nat) (A : Nat → Nat → Nat) (rhs : Nat → Nat)
    (allowed : Nat → Bool)
    (probeOK : Probe → Prop) (probePrice : Probe → Nat)
    (observes : Probe → Scenario → Outcome → Prop)
    (transform : Probe → Outcome → Scenario → Scenario)
    (bad0 badt : State → Prop) (d : State → State → Nat)
    (D U : Nat) (state : Scenario → Recipe → State)
    (hdebt : ∀ b, badt b → ∃ b0, bad0 b0 ∧ d b b0 ≤ D)
    (hDU : D ≤ U)
    (rho debt ceiling depth budget : Nat)
    (X : Scenario → Prop) (t : Plan Recipe Probe Outcome)
    (hplan : PlanValid
      (repairModel m n A rhs allowed (HistoricalFuture bad0 d U state)
        probeOK probePrice observes transform) depth budget X t)
    (henvelope : PriceEnvelope
      (repairModel m n A rhs allowed (HistoricalFuture bad0 d U state)
        probeOK probePrice observes transform)
      depth X t ceiling)
    (hreserve : PlanAffordable rho debt [ceiling]) :
    NoBadAtLeaves
      (repairModel m n A rhs allowed (HistoricalFuture bad0 d U state)
        probeOK probePrice observes transform)
      badt state depth X t ∧
    StrictTraceReserve
      (repairModel m n A rhs allowed (HistoricalFuture bad0 d U state)
        probeOK probePrice observes transform)
      rho depth X debt t := by
  constructor
  · exact verified_future_repair_excludes_badt
      m n A rhs allowed probeOK probePrice observes transform
      bad0 badt d D U state hdebt hDU depth budget X t hplan
  · exact envelope_implies_strict_reserve _ rho depth X t debt ceiling
      henvelope ((original_multi_budget_one_envelope rho debt ceiling).mp hreserve)

end INSACERMO.TotalHistoricalMulti
