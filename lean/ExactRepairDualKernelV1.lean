import Std

/-!
INSACERMO REPAIR: generic exact nonnegative linear-program dual certificate.
All numeric quantities are Nat. A and b are original decimals scaled by 10.
Primal x and dual y can be represented as Nat numerators over denominators
D and E. The generic inequality has no numerical instance hardcoded.
-/
namespace InsacermoExactRepair
open scoped BigOperators
variable {m n : Nat}

def PrimalValid (A : Fin m → Fin n → Nat) (b : Fin m → Nat)
    (allowed : Fin n → Bool) (x : Fin n → Nat) (D : Nat) : Prop :=
  (∀ j, x j ≠ 0 → allowed j = true) ∧
  ∀ i, b i * D ≤ ∑ j : Fin n, A i j * x j

def DualValid (A : Fin m → Fin n → Nat)
    (allowed : Fin n → Bool) (y : Fin m → Nat) (E : Nat) : Prop :=
  ∀ j, allowed j = true →
    (∑ i : Fin m, A i j * y i) ≤ 10 * E

theorem weak_duality
    (A : Fin m → Fin n → Nat) (b : Fin m → Nat)
    (allowed : Fin n → Bool) (x : Fin n → Nat) (D : Nat)
    (y : Fin m → Nat) (E : Nat)
    (hp : PrimalValid A b allowed x D)
    (hd : DualValid A allowed y E) :
    (∑ i : Fin m, b i * y i) * D ≤
      (10 * E) * (∑ j : Fin n, x j) := by
  have h1 :
      (∑ i : Fin m, b i * y i) * D =
      ∑ i : Fin m, (b i * D) * y i := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ac_rfl
  have h2 :
      (∑ i : Fin m, (b i * D) * y i) ≤
      ∑ i : Fin m, (∑ j : Fin n, A i j * x j) * y i := by
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.mul_le_mul_right (y i) (hp.2 i)
  have h3 :
      (∑ i : Fin m, (∑ j : Fin n, A i j * x j) * y i) =
      ∑ j : Fin n, (∑ i : Fin m, A i j * y i) * x j := by
    calc
      _ = ∑ i : Fin m, ∑ j : Fin n, (A i j * x j) * y i := by
        simp only [Finset.sum_mul]
      _ = ∑ j : Fin n, ∑ i : Fin m, (A i j * x j) * y i := by
        rw [Finset.sum_comm]
      _ = ∑ j : Fin n, ∑ i : Fin m, (A i j * y i) * x j := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        ac_rfl
      _ = ∑ j : Fin n, (∑ i : Fin m, A i j * y i) * x j := by
        simp only [Finset.sum_mul]
  have h4 :
      (∑ j : Fin n, (∑ i : Fin m, A i j * y i) * x j) ≤
      ∑ j : Fin n, (10 * E) * x j := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hz : x j = 0
    · simp [hz]
    · have ha : allowed j = true := hp.1 j hz
      exact Nat.mul_le_mul_right (x j) (hd j ha)
  calc
    _ = _ := h1
    _ ≤ _ := h2
    _ = _ := h3
    _ ≤ _ := h4
    _ = _ := by rw [Finset.mul_sum]

/-- If the checked dual bound strictly exceeds the $40/year budget,
    no feasible mixture of admitted foods exists under this budget. -/
theorem dual_budget_impossible
    (A : Fin m → Fin n → Nat) (b : Fin m → Nat)
    (allowed : Fin n → Bool) (y : Fin m → Nat) (E : Nat)
    (hd : DualValid A allowed y E)
    (hstrict : 40 * (10 * E) < 365 * (∑ i : Fin m, b i * y i)) :
    ∀ D : Nat, D > 0 → ∀ x : Fin n → Nat,
      PrimalValid A b allowed x D →
      ¬ (365 * (∑ j : Fin n, x j) ≤ 40 * D) := by
  intro D hD x hp hb
  have hweak := weak_duality A b allowed x D y E hp hd
  have h1 :
      (365 * (∑ i : Fin m, b i * y i)) * D ≤
        (10 * E) * (365 * (∑ j : Fin n, x j)) := by
    calc
      _ = ((∑ i : Fin m, b i * y i) * D) * 365 := by ac_rfl
      _ ≤ ((10 * E) * (∑ j : Fin n, x j)) * 365 :=
        Nat.mul_le_mul_right 365 hweak
      _ = _ := by ac_rfl
  have h2 :
      (10 * E) * (365 * (∑ j : Fin n, x j)) ≤
        (40 * (10 * E)) * D := by
    calc
      _ ≤ (10 * E) * (40 * D) := Nat.mul_le_mul_left (10 * E) hb
      _ = _ := by ac_rfl
  have h3 :
      (40 * (10 * E)) * D <
        (365 * (∑ i : Fin m, b i * y i)) * D :=
    Nat.mul_lt_mul_of_pos_right hstrict hD
  exact (Nat.not_lt_of_ge (Nat.le_trans h1 h2)) h3

end InsacermoExactRepair
