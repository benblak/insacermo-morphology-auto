import Lean

/-!
Core arithmetic of a trustless Farkas certificate verifier.
This file does not assert that n=736 was globally solved.
All weighted sums are mathematical integers. Solver-produced data is
untrusted and can only satisfy the final theorem via a kernel proof.
-/
namespace INSACERMO.Proof736

def sumOn (l : List Nat) (f : Nat → Int) : Int :=
  (l.map f).sum

theorem sumOn_add (l : List Nat) (f g : Nat → Int) :
    sumOn l (fun i => f i + g i) = sumOn l f + sumOn l g := by
  induction l with
  | nil => simp [sumOn]
  | cons a t ih =>
    simp only [sumOn, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem sumOn_mul (l : List Nat) (k : Int) (f : Nat → Int) :
    sumOn l (fun i => k * f i) = k * sumOn l f := by
  induction l with
  | nil => simp [sumOn]
  | cons a t ih =>
    simp only [sumOn, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Int.mul_add]

theorem sumOn_mono (l : List Nat) (f g : Nat → Int)
    (h : ∀ i ∈ l, f i ≤ g i) :
    sumOn l f ≤ sumOn l g := by
  induction l with
  | nil => simp [sumOn]
  | cons a t ih =>
    have ha : f a ≤ g a := h a (by simp)
    have ht : ∀ i ∈ t, f i ≤ g i := by
      intro i hi
      exact h i (by simp [hi])
    have hs := ih ht
    simp only [sumOn] at hs
    simp only [sumOn, List.map_cons, List.sum_cons]
    omega

def eval (n : Nat) (c x : Nat → Int) : Int :=
  sumOn (List.range n) (fun i => c i * x i)

theorem eval_add (n : Nat) (c d x : Nat → Int) :
    eval n (fun i => c i + d i) x = eval n c x + eval n d x := by
  unfold eval
  simp only [Int.add_mul]
  exact sumOn_add (List.range n) (fun i => c i * x i) (fun i => d i * x i)

theorem eval_mul (n : Nat) (k : Int) (c x : Nat → Int) :
    eval n (fun i => k * c i) x = k * eval n c x := by
  unfold eval
  simp only [Int.mul_assoc]
  exact sumOn_mul (List.range n) k (fun i => c i * x i)

structure Row where
  coeff : Nat → Int
  minimum : Int
  weight : Nat

def combined (rs : List Row) (i : Nat) : Int :=
  (rs.map (fun r => (r.weight : Int) * r.coeff i)).sum

def rhs (rs : List Row) : Int :=
  (rs.map (fun r => (r.weight : Int) * r.minimum)).sum

theorem eval_combined (n : Nat) (rs : List Row) (x : Nat → Int) :
    eval n (combined rs) x =
      (rs.map (fun r => (r.weight : Int) * eval n r.coeff x)).sum := by
  induction rs with
  | nil =>
    have z (l : List Nat) : sumOn l (fun _ => (0 : Int)) = 0 := by
      induction l with
      | nil => rfl
      | cons a t ih =>
        change (0 : Int) + sumOn t (fun _ => (0 : Int)) = 0
        omega
    change sumOn (List.range n) (fun i => (0 : Int) * x i) = 0
    simpa using (z (List.range n))
  | cons r rs ih =>
    have hfun : combined (r :: rs) =
        (fun i => (r.weight : Int) * r.coeff i + combined rs i) := by
      funext i
      simp [combined]
    rw [hfun, eval_add, eval_mul, ih]
    simp

theorem weighted_sound (n : Nat) (rs : List Row) (x : Nat → Int)
    (h : ∀ r ∈ rs, r.minimum ≤ eval n r.coeff x) :
    rhs rs ≤ eval n (combined rs) x := by
  rw [eval_combined]
  induction rs with
  | nil => simp [rhs]
  | cons r rs ih =>
    have hr : r.minimum ≤ eval n r.coeff x :=
      h r (by simp)
    have ht : ∀ s ∈ rs, s.minimum ≤ eval n s.coeff x := by
      intro s hs
      exact h s (by simp [hs])
    have hw : (r.weight : Int) * r.minimum ≤
        (r.weight : Int) * eval n r.coeff x := by
      induction r.weight with
      | zero => simp
      | succ k ihw =>
        have cast_eq : ((Nat.succ k : Nat) : Int) = ((k : Int) + 1) := by omega
        rw [cast_eq, Int.add_mul, Int.add_mul]
        simp only [Int.one_mul]
        omega
    have rest := ih ht
    simp only [rhs, List.map_cons, List.sum_cons] at *
    omega


/-!
The integer slack term is exact, including *negative* slack on branch
vertices fixed to 1. This is why the arithmetic checker can certify
a global lower bound using small 57-leaf Farkas dual certificates.
-/

def fixedOK (f : Option Bool) (x : Nat) : Prop :=
  match f with
  | none => True
  | some false => x = 0
  | some true => x = 1

def slack (c : Int) (K : Nat) (f : Option Bool) : Int :=
  match f with
  | none => if (K : Int) ≤ c then c - (K : Int) else 0
  | some false => 0
  | some true => c - (K : Int)

theorem integer_weight_le (k : Nat) (a b : Int) (hab : a ≤ b) :
    (k : Int) * a ≤ (k : Int) * b := by
  induction k with
  | zero => simp
  | succ k ih =>
    have cast_eq : ((Nat.succ k : Nat) : Int) = ((k : Int) + 1) := by omega
    rw [cast_eq, Int.add_mul, Int.add_mul]
    simp only [Int.one_mul]
    omega

theorem point_upper (c : Int) (K x : Nat) (hx : x ≤ 1)
    (f : Option Bool) (hf : fixedOK f x) :
    c * (x : Int) ≤ (K : Int) * (x : Int) + slack c K f := by
  cases f with
  | none =>
    have h01 : x = 0 ∨ x = 1 := by omega
    rcases h01 with hz | ho
    · subst x
      by_cases hc : (K : Int) ≤ c <;> simp [slack, hc] <;> omega
    · subst x
      by_cases hc : (K : Int) ≤ c <;> simp [slack, hc] <;> omega
  | some b =>
    cases b with
    | false =>
      have hz : x = 0 := hf
      subst x
      simp [slack]
    | true =>
      have ho : x = 1 := hf
      subst x
      simp [slack] <;> omega

def xInt (x : Nat → Nat) (i : Nat) : Int := (x i : Int)

theorem eval_upper (n : Nat) (c : Nat → Int) (x : Nat → Nat)
    (K : Nat) (fixes : Nat → Option Bool)
    (hx : ∀ i < n, x i ≤ 1)
    (hf : ∀ i < n, fixedOK (fixes i) (x i)) :
    eval n c (xInt x) ≤
      (K : Int) * sumOn (List.range n) (xInt x) +
        sumOn (List.range n) (fun i => slack (c i) K (fixes i)) := by
  have h := sumOn_mono (List.range n)
    (fun i => c i * xInt x i)
    (fun i => (K : Int) * xInt x i + slack (c i) K (fixes i))
    (by
      intro i hi
      have hv : i < n := List.mem_range.mp hi
      exact point_upper (c i) K (x i) (hx i hv) (fixes i) (hf i hv))
  rw [sumOn_add, sumOn_mul] at h
  exact h

theorem leaf_sound (n K B : Nat)
    (rs : List Row) (x : Nat → Nat) (fixes : Nat → Option Bool)
    (hx : ∀ i < n, x i ≤ 1)
    (hf : ∀ i < n, fixedOK (fixes i) (x i))
    (hrows : ∀ r ∈ rs, r.minimum ≤ eval n r.coeff (xInt x))
    (hbudget : sumOn (List.range n) (xInt x) ≤ (B : Int))
    (hcertificate :
      (K : Int) * (B : Int) +
        sumOn (List.range n) (fun i => slack (combined rs i) K (fixes i))
          < rhs rs) : False := by
  have hlower := weighted_sound n rs (xInt x) hrows
  have hupper := eval_upper n (combined rs) x K fixes hx hf
  have hmul := integer_weight_le K
    (sumOn (List.range n) (xInt x)) (B : Int) hbudget
  omega

end INSACERMO.Proof736
