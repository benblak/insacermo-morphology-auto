/-!
Automatically generated FROM ORIGINAL parsed NOAA GZIP, with independent
byte-level data auditor. These are EXACT FINITE COMPUTATIONS, not a proof that
the external data provider is infallible or that all hidden waves are known.
-/
namespace InsacermoIntegratedEvidence
def observedLeftDm : Nat := 74
def observedRightDm : Nat := 80
theorem observed_net_change_ge_five :
    observedRightDm >= observedLeftDm + 5 := by decide
theorem exact_observed_change :
    observedRightDm - observedLeftDm = 6 := by decide
def measured (present : Bool) (height : Nat) : Option Nat :=
  if present then some height else none
theorem missing_center_is_not_identified :
    measured false 0 = measured false 1 ∧ (0 : Nat) ≠ 1 := by decide
theorem zero_one_two_clock :
    ((List.range 3).filter (fun k => k % 3 == 1)).length = 1 := by decide
end InsacermoIntegratedEvidence
