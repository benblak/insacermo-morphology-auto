import C3.TotalRepairFutureBridgeV1
import LegacyTemporalValidityKernelV1
import LegacyCertifiedOnlineDebtKernelV1
import LegacyFinalIntegrationKernelV1

/-! Historical kernel sources are byte-for-byte copied from commit
a24bd8841a6b507dc82758cf68ac2c8aa523e3e1,
and imported as separate modules. New statements reuse original definitions.
No equivalence to an entire prior MAX TOTAL binary is claimed. -/
namespace INSACERMO.LegacyC3Repair
open INSACERMO.TotalRepairFuture
open INSACERMO.RecursiveC3
open INSACERMO.C3PP
open INSACERMO.TemporalValidityV1
open INSACERMO.CertifiedOnlineDebtV1
open INSACERMO.FinalIntegrationV1
universe u v w z
variable {Scenario : Type u} {Probe : Type v} {Outcome : Type w} {State : Type z}

/-- The ORIGINAL temporal kernel is used as the precise future obligation
on each reachable state after C3 transformations and final REPAIR. -/
def HistoricalFuture
    (bad0 : State → Prop) (d : State → State → Nat)
    (upper : Nat) (state : Scenario → Recipe → State) :
    Scenario → Recipe → Prop :=
  fun s p => INSACERMO.TemporalValidityV1.Safe bad0 d upper (state s p)

/-- Safety of every leaf, not only of the first repair. -/
def NoBadAtLeaves
    (M : DynamicProblem Scenario Recipe Probe Outcome)
    (badt : State → Prop) (state : Scenario → Recipe → State) :
    Nat → (Scenario → Prop) → Plan Recipe Probe Outcome → Prop
  | 0, X, .act p => ∀ s, X s → ¬ badt (state s p)
  | 0, _, .probe _ _ => False
  | _ + 1, X, .act p => ∀ s, X s → ¬ badt (state s p)
  | k + 1, X, .probe q next =>
      ∀ o, NoBadAtLeaves M badt state k (AfterDynamic M q X o) (next o)

/-- This uses the ACTUAL historical debt upper-bound theorem. -/
theorem old_temporal_safety_from_bound
    (bad0 badt : State → Prop) (d : State → State → Nat)
    (D U : Nat) (s : State)
    (hdebt : ∀ b, badt b → ∃ b0, bad0 b0 ∧ d b b0 ≤ D)
    (hDU : D ≤ U)
    (hsafe : INSACERMO.TemporalValidityV1.Safe bad0 d U s) :
    ¬ badt s :=
  INSACERMO.CertifiedOnlineDebtV1.safe_of_certified_upper_bound
    bad0 badt d D U s hdebt hDU hsafe

/-- The original strict runtime gate proves debt < reserve; equality fails. -/
theorem original_strict_reserve_gate
    (b : VerifiedBound) (h : RuntimeGate b) :
    b.trueDebt < b.reserve :=
  verified_bound_plus_runtime_gate_is_safe b h

/-- Composition theorem: C3-valid REPAIR policy + future obligation in the
actual temporal Safe predicate + sound debt upper bound → every terminal
reachable scenario is outside the declared time-dependent bad set. -/
theorem verified_future_repair_excludes_badt
    (m n : Nat) (A : Nat → Nat → Nat) (rhs : Nat → Nat)
    (allowed : Nat → Bool)
    (probeOK : Probe → Prop) (probePrice : Probe → Nat)
    (observes : Probe → Scenario → Outcome → Prop)
    (transform : Probe → Outcome → Scenario → Scenario)
    (bad0 badt : State → Prop) (d : State → State → Nat)
    (D U : Nat) (state : Scenario → Recipe → State)
    (hdebt : ∀ b, badt b → ∃ b0, bad0 b0 ∧ d b b0 ≤ D)
    (hDU : D ≤ U)
    (depth : Nat) :
    ∀ (budget : Nat) (X : Scenario → Prop)
      (t : Plan Recipe Probe Outcome),
      PlanValid
        (repairModel m n A rhs allowed (HistoricalFuture bad0 d U state)
          probeOK probePrice observes transform)
        depth budget X t →
      NoBadAtLeaves
        (repairModel m n A rhs allowed (HistoricalFuture bad0 d U state)
          probeOK probePrice observes transform)
        badt state depth X t := by
  intro budget X t hv
  have hf := verified_plan_preserves_all_declared_futures
    m n A rhs allowed (HistoricalFuture bad0 d U state)
    probeOK probePrice observes transform depth budget X t hv
  induction depth generalizing budget X t with
  | zero =>
      cases t with
      | act p =>
          intro s hs
          exact old_temporal_safety_from_bound bad0 badt d D U (state s p)
            hdebt hDU (hf s hs)
      | probe q next => exact False.elim hf
  | succ k ih =>
      cases t with
      | act p =>
          intro s hs
          exact old_temporal_safety_from_bound bad0 badt d D U (state s p)
            hdebt hDU (hf s hs)
      | probe q next =>
          intro o
          exact ih _ _ (next o) (hv.2.2.2 o) (hf o)

end INSACERMO.LegacyC3Repair
