import ExactRepairDualKernelV1

/-!
INSACERMO REPAIR: reusable executable certificate checker.
A single proof connects finite Boolean checks to the general duality kernel.
Any new numeric LP instance can supply data; no new mathematical proofs.
-/
namespace InsacermoExactRepair
variable {m n : Nat}

/-- Check each declared nonnegative dual constraint in the allowed grammar. -/
def checkDual (m n : Nat) (A : Nat → Nat → Nat)
    (allowed : Nat → Bool) (y : Nat → Nat) (E : Nat) : Bool :=
  (List.range n).all (fun j =>
    (!allowed j) || decide (sumN m (fun i => A i j * y i) ≤ 10 * E))

/-- Check admissibility of each nonzero primal action and each requirement. -/
def checkPrimal (m n : Nat) (A : Nat → Nat → Nat)
    (b : Nat → Nat) (allowed : Nat → Bool) (x : Nat → Nat) (D : Nat) : Bool :=
  ((List.range n).all (fun j => decide (x j = 0) || allowed j)) &&
  ((List.range m).all (fun i =>
    decide (b i * D ≤ sumN n (fun j => A i j * x j))))

theorem checked_dual_sound
    (m n : Nat) (A : Nat → Nat → Nat) (allowed : Nat → Bool)
    (y : Nat → Nat) (E : Nat)
    (h : checkDual m n A allowed y E = true) :
    DualValid (m := m) (n := n) A allowed y E := by
  intro j hj ha
  have hrow := (List.all_eq_true.mp h) j (List.mem_range.mpr hj)
  have hreduced : decide (sumN m (fun i => A i j * y i) ≤ 10 * E) = true := by
    simpa [checkDual, ha] using hrow
  exact of_decide_eq_true hreduced

theorem checked_primal_sound
    (m n : Nat) (A : Nat → Nat → Nat) (b : Nat → Nat)
    (allowed : Nat → Bool) (x : Nat → Nat) (D : Nat)
    (h : checkPrimal m n A b allowed x D = true) :
    PrimalValid (m := m) (n := n) A b allowed x D := by
  obtain ⟨hall, hreq⟩ := Bool.and_eq_true.mp h
  constructor
  · intro j hj hx
    have hrow := (List.all_eq_true.mp hall) j (List.mem_range.mpr hj)
    have hn : decide (x j = 0) = false := by
      exact decide_eq_false hx
    have ha : allowed j = true := by
      simpa [hn] using hrow
    exact ha
  · intro i hi
    have hrow := (List.all_eq_true.mp hreq) i (List.mem_range.mpr hi)
    exact of_decide_eq_true hrow

theorem checked_budget_impossible
    (m n : Nat) (A : Nat → Nat → Nat) (b : Nat → Nat)
    (allowed : Nat → Bool) (y : Nat → Nat) (E : Nat)
    (hdual : checkDual m n A allowed y E = true)
    (hgap : 40 * (10 * E) < 365 * sumN m (fun i => b i * y i))
    (D : Nat) (hD : D > 0) (x : Nat → Nat)
    (hp : PrimalValid (m := m) (n := n) A b allowed x D) :
    ¬ (365 * sumN n x ≤ 40 * D) :=
  dual_budget_impossible A b allowed y E
    (checked_dual_sound m n A allowed y E hdual) hgap D hD x hp

end InsacermoExactRepair
