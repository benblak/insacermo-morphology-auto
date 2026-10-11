import Std

/-!
INSACERMO REPAIR. Standalone Lean 4.33.1 generic weak duality,
using primitive recursive Nat sums instead of unavailable Finset/mathlib.
A,b are integers (decimal source * 10). x,y are nonnegative
rational numerators with natural denominators D,E.
No axioms, no hidden LP solver, no sensor assumptions.
-/

namespace InsacermoExactRepair

/-- Total of first n entries, purely in Lean core. -/
def sumN : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumN n f + f n

theorem sumN_zero (n : Nat) : sumN n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumN, ih]

theorem sumN_congr (n : Nat) (f g : Nat → Nat)
    (h : ∀ i, i < n → f i = g i) : sumN n f = sumN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [sumN]
      rw [ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)))]
      rw [h n (Nat.lt_succ_self n)]

theorem sumN_le (n : Nat) (f g : Nat → Nat)
    (h : ∀ i, i < n → f i ≤ g i) : sumN n f ≤ sumN n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
      simp only [sumN]
      exact Nat.add_le_add
        (ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n))))
        (h n (Nat.lt_succ_self n))

theorem sumN_add (n : Nat) (f g : Nat → Nat) :
    sumN n (fun i => f i + g i) = sumN n f + sumN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [sumN]
      rw [ih]
      omega

theorem sumN_mul_right (n : Nat) (f : Nat → Nat) (k : Nat) :
    sumN n (fun i => f i * k) = sumN n f * k := by
  induction n with
  | zero => simp [sumN]
  | succ n ih =>
      simp only [sumN]
      rw [ih, Nat.add_mul]

theorem sumN_comm (m n : Nat) (f : Nat → Nat → Nat) :
    sumN m (fun i => sumN n (fun j => f i j)) =
    sumN n (fun j => sumN m (fun i => f i j)) := by
  induction m with
  | zero =>
      simpa only [sumN] using (sumN_zero n).symm
  | succ m ih =>
      calc
        sumN (m+1) (fun i => sumN n (fun j => f i j)) =
          sumN m (fun i => sumN n (fun j => f i j)) +
          sumN n (fun j => f m j) := rfl
        _ = sumN n (fun j => sumN m (fun i => f i j)) +
            sumN n (fun j => f m j) := by rw [ih]
        _ = sumN n (fun j => sumN m (fun i => f i j) + f m j) :=
          (sumN_add n (fun j => sumN m (fun i => f i j))
            (fun j => f m j)).symm
        _ = sumN n (fun j => sumN (m+1) (fun i => f i j)) := by
          apply sumN_congr
          intro j hj
          rfl

variable {m n : Nat}

def PrimalValid (A : Nat → Nat → Nat) (b : Nat → Nat)
    (allowed : Nat → Bool) (x : Nat → Nat) (D : Nat) : Prop :=
  (∀ j, j < n → x j ≠ 0 → allowed j = true) ∧
  ∀ i, i < m → b i * D ≤ sumN n (fun j => A i j * x j)

def DualValid (A : Nat → Nat → Nat)
    (allowed : Nat → Bool) (y : Nat → Nat) (E : Nat) : Prop :=
  ∀ j, j < n → allowed j = true →
    sumN m (fun i => A i j * y i) ≤ 10 * E

theorem weak_duality
    (A : Nat → Nat → Nat) (b : Nat → Nat)
    (allowed : Nat → Bool) (x : Nat → Nat) (D : Nat)
    (y : Nat → Nat) (E : Nat)
    (hp : PrimalValid (m := m) (n := n) A b allowed x D)
    (hd : DualValid (m := m) (n := n) A allowed y E) :
    sumN m (fun i => b i * y i) * D ≤
      (10 * E) * sumN n x := by
  calc
    sumN m (fun i => b i * y i) * D =
        sumN m (fun i => (b i * y i) * D) :=
          (sumN_mul_right m (fun i => b i * y i) D).symm
    _ = sumN m (fun i => (b i * D) * y i) := by
      apply sumN_congr
      intro i hi
      ac_rfl
    _ ≤ sumN m (fun i => (sumN n (fun j => A i j * x j)) * y i) := by
      apply sumN_le
      intro i hi
      exact Nat.mul_le_mul_right (y i) (hp.2 i hi)
    _ = sumN m (fun i => sumN n (fun j => (A i j * x j) * y i)) := by
      apply sumN_congr
      intro i hi
      exact (sumN_mul_right n (fun j => A i j * x j) (y i)).symm
    _ = sumN n (fun j => sumN m (fun i => (A i j * x j) * y i)) :=
      sumN_comm m n (fun i j => (A i j * x j) * y i)
    _ = sumN n (fun j => sumN m (fun i => (A i j * y i) * x j)) := by
      apply sumN_congr
      intro j hj
      apply sumN_congr
      intro i hi
      ac_rfl
    _ = sumN n (fun j => (sumN m (fun i => A i j * y i)) * x j) := by
      apply sumN_congr
      intro j hj
      exact sumN_mul_right m (fun i => A i j * y i) (x j)
    _ ≤ sumN n (fun j => (10 * E) * x j) := by
      apply sumN_le
      intro j hj
      by_cases hx : x j = 0
      · simp [hx]
      · exact Nat.mul_le_mul_right (x j) (hd j hj (hp.1 j hj hx))
    _ = (10 * E) * sumN n x := by
      have hsum : sumN n (fun j => x j * (10 * E)) = sumN n x * (10 * E) :=
        sumN_mul_right n x (10 * E)
      calc
        _ = sumN n (fun j => x j * (10 * E)) := by
          apply sumN_congr
          intro j hj
          ac_rfl
        _ = sumN n x * (10 * E) := hsum
        _ = _ := by ac_rfl

theorem dual_budget_impossible
    (A : Nat → Nat → Nat) (b : Nat → Nat)
    (allowed : Nat → Bool) (y : Nat → Nat) (E : Nat)
    (hd : DualValid (m := m) (n := n) A allowed y E)
    (hstrict : 40 * (10 * E) < 365 * sumN m (fun i => b i * y i)) :
    ∀ D : Nat, D > 0 → ∀ x : Nat → Nat,
      PrimalValid (m := m) (n := n) A b allowed x D →
      ¬ (365 * sumN n x ≤ 40 * D) := by
  intro D hD x hp hb
  have hweak := weak_duality A b allowed x D y E hp hd
  have h1 :
      (365 * sumN m (fun i => b i * y i)) * D ≤
        (10 * E) * (365 * sumN n x) := by
    calc
      _ = (sumN m (fun i => b i * y i) * D) * 365 := by ac_rfl
      _ ≤ ((10 * E) * sumN n x) * 365 :=
        Nat.mul_le_mul_right 365 hweak
      _ = _ := by ac_rfl
  have h2 :
      (10 * E) * (365 * sumN n x) ≤
        (40 * (10 * E)) * D := by
    calc
      _ ≤ (10 * E) * (40 * D) := Nat.mul_le_mul_left (10 * E) hb
      _ = _ := by ac_rfl
  have h3 :
      (40 * (10 * E)) * D <
        (365 * sumN m (fun i => b i * y i)) * D :=
    Nat.mul_lt_mul_of_pos_right hstrict hD
  exact (Nat.not_lt_of_ge (Nat.le_trans h1 h2)) h3

end InsacermoExactRepair
