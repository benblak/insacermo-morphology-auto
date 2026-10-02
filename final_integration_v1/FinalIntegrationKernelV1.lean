import Lean.Elab.Tactic.Omega

namespace INSACERMO.FinalIntegrationV1

structure VerifiedBound where
  trueDebt : Nat
  upperBound : Nat
  reserve : Nat
  sound : trueDebt ≤ upperBound

def RuntimeGate (b : VerifiedBound) : Prop :=
  b.upperBound < b.reserve

theorem verified_bound_plus_runtime_gate_is_safe
    (b : VerifiedBound)
    (hgate : RuntimeGate b) :
    b.trueDebt < b.reserve := by
  unfold RuntimeGate at hgate
  omega

theorem equality_never_passes_strict_gate
    (U rho : Nat)
    (h : U = rho) :
    ¬ U < rho := by
  omega

inductive FinalVerdict where
  | act
  | probe
  | repair
  | refuse
deriving DecidableEq

def SafeVerdict (D rho : Nat) : FinalVerdict → Prop
  | .act => D < rho
  | .probe => True
  | .repair => True
  | .refuse => True

theorem fail_closed_non_act_is_safe
    (D rho : Nat)
    (v : FinalVerdict)
    (h : v ≠ .act) :
    SafeVerdict D rho v := by
  cases v <;> simp_all [SafeVerdict]

#print axioms verified_bound_plus_runtime_gate_is_safe
#print axioms equality_never_passes_strict_gate
#print axioms fail_closed_non_act_is_safe

end INSACERMO.FinalIntegrationV1
