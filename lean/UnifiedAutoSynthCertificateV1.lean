import ExactRepairCheckerV1

/-! One generic kernel, one compiled instance per previously unseen contract.
    The future has an explicit finite list of allowed resources in each world.
    Read-only robust constructions may use only their intersection.
    This DOES NOT assert infeasibility for outcome-contingent C3 policies. -/
namespace INSACERMO.AutoSynthCert
open InsacermoExactRepair

def worldAllowed (worlds : List (List Bool)) (w j : Nat) : Bool :=
  (((worlds[w]?).getD [])[j]?).getD false

def checkFuture (n : Nat) (worlds : List (List Bool)) (x : Nat → Nat) : Bool :=
  (List.range worlds.length).all (fun w =>
    (List.range n).all (fun j =>
      decide (x j = 0) || worldAllowed worlds w j))

/-- Soundness for ALL finite future worlds, not just the selected one. -/
theorem checked_future_sound
    (n : Nat) (worlds : List (List Bool)) (x : Nat → Nat)
    (h : checkFuture n worlds x = true) :
    ∀ w, w < worlds.length → ∀ j, j < n →
      x j ≠ 0 → worldAllowed worlds w j = true := by
  intro w hw j hj hx
  have hout : (List.range worlds.length).all (fun w =>
      (List.range n).all (fun j =>
        decide (x j = 0) || worldAllowed worlds w j)) = true := by
    simpa [checkFuture] using h
  have hinner := (List.all_eq_true.mp hout) w (List.mem_range.mpr hw)
  have hrow := (List.all_eq_true.mp hinner) j (List.mem_range.mpr hj)
  have hn : decide (x j = 0) = false := decide_eq_false hx
  simpa [hn] using hrow

/-- Full constructive certificate, with the *existing* primal theorem. -/
theorem certified_future_construction
    (m n : Nat) (A : Nat → Nat → Nat) (b : Nat → Nat)
    (allowed : Nat → Bool) (worlds : List (List Bool))
    (x : Nat → Nat) (D : Nat)
    (hp : checkPrimal m n A b allowed x D = true)
    (hf : checkFuture n worlds x = true)
    (hprice : 365 * sumN n x ≤ 40 * D) :
    PrimalValid (m := m) (n := n) A b allowed x D ∧
    (∀ w, w < worlds.length → ∀ j, j < n →
      x j ≠ 0 → worldAllowed worlds w j = true) ∧
    365 * sumN n x ≤ 40 * D := by
  exact ⟨checked_primal_sound m n A b allowed x D hp,
    checked_future_sound n worlds x hf, hprice⟩

/-- The direct no-go is only for the declared fixed shared-action LP grammar. -/
theorem certified_no_robust_single_construction
    (m n : Nat) (A : Nat → Nat → Nat) (b : Nat → Nat)
    (allowed : Nat → Bool) (y : Nat → Nat) (E : Nat)
    (hd : checkDual m n A allowed y E = true)
    (hg : 40 * (10 * E) < 365 * sumN m (fun i => b i * y i)) :
    ∀ D, D > 0 → ∀ x,
      PrimalValid (m := m) (n := n) A b allowed x D →
      ¬ (365 * sumN n x ≤ 40 * D) := by
  intro D hD x hp
  exact checked_budget_impossible m n A b allowed y E hd hg D hD x hp

end INSACERMO.AutoSynthCert
