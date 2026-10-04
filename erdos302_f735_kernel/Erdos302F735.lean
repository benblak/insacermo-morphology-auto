import Std

/-!
Erdős Problem 302 — structural transfer from n = 734 to n = 735.

This file deliberately avoids a quadratic brute-force witness check inside Lean.
Instead it kernel-checks the only new endpoint c = 735, proves that the only
new reciprocal triples are {210,294,735} and {294,490,735}, and proves a
generic transfer theorem:

* any admissible 734-set that omits 294 can safely add 735;
* any 735-set has cardinality at most the 734 cardinality plus one;
* therefore, given a 608-element admissible 734 witness omitting 294 and the
  upper bound f(734) <= 608, the exact value at 735 is 609.

The concrete 608-element public witness is independently integer-verified in
verify_f735.py; its admissibility is not smuggled into Lean as an axiom.
-/

namespace Erdos302F735

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def Admissible (n : Nat) (S : Nat → Bool) : Prop :=
  (∀ x, S x → 0 < x ∧ x ≤ n) ∧
  (∀ a b c, a < b → b < c → S a → S b → S c →
    a * (b + c) ≠ b * c)

def cardinal734 (S : Nat → Bool) : Nat :=
  ((List.range 735).filter (fun x => 0 < x && S x)).length

def cardinal735 (S : Nat → Bool) : Nat :=
  cardinal734 S + (S 735).toNat

/-- Small exact certificate for the only genuinely new endpoint. -/
def endpoint735Check : Bool :=
  (List.range 735).all (fun b =>
    !(0 < b && b < 735) ||
      (if b * 735 % (b + 735) = 0 then
        (b == 294 || b == 490)
       else true))

theorem endpoint735_check : endpoint735Check = true := by
  decide +kernel

/-- Every ordered positive reciprocal triple whose largest entry is 735
    is one of the two explicit triples. -/
theorem new_triples_with_735
    (a b : Nat)
    (ha : 0 < a) (hab : a < b) (hb735 : b < 735)
    (hrel : a * (b + 735) = b * 735) :
    (a = 210 ∧ b = 294) ∨ (a = 294 ∧ b = 490) := by
  have hrow :=
    List.all_eq_true.mp endpoint735_check b (List.mem_range.mpr hb735)
  have hbpos : 0 < b := by omega
  have hdiv : (b + 735) ∣ b * 735 := by
    exact ⟨a, by simpa [Nat.mul_comm] using hrel.symm⟩
  have hmod : b * 735 % (b + 735) = 0 :=
    Nat.mod_eq_zero_of_dvd hdiv
  have hbclass : b = 294 ∨ b = 490 := by
    simpa [endpoint735Check, hbpos, hb735, hmod] using hrow
  rcases hbclass with rfl | rfl
  · left
    constructor <;> omega
  · right
    constructor <;> omega

def add735 (S : Nat → Bool) (x : Nat) : Bool :=
  if x = 735 then true else S x

def trim734 (S : Nat → Bool) (x : Nat) : Bool :=
  S x && decide (x ≤ 734)

theorem add735_support
    (S : Nat → Bool) (hS : Admissible 734 S)
    (x : Nat) (hx : add735 S x) :
    0 < x ∧ x ≤ 735 := by
  by_cases h : x = 735
  · omega
  · have hsx : S x := by simpa [add735, h] using hx
    have hh := hS.1 x hsx
    omega

/-- The key structural fact: omitting 294 is sufficient to append 735 safely. -/
theorem add735_admissible
    (S : Nat → Bool) (hS : Admissible 734 S)
    (h294 : S 294 = false) :
    Admissible 735 (add735 S) := by
  have support : ∀ x, add735 S x → 0 < x ∧ x ≤ 735 :=
    add735_support S hS
  refine ⟨support, ?_⟩
  intro a b c hab hbc ha hb hc hrel
  by_cases hc734 : c ≤ 734
  · have hna : a ≠ 735 := by omega
    have hnb : b ≠ 735 := by omega
    have hnc : c ≠ 735 := by omega
    have sa : S a := by simpa [add735, hna] using ha
    have sb : S b := by simpa [add735, hnb] using hb
    have sc : S c := by simpa [add735, hnc] using hc
    exact hS.2 a b c hab hbc sa sb sc hrel
  · have hc735 : c = 735 := by
      have hc' := (support c hc).2
      omega
    subst c
    have hclass :=
      new_triples_with_735 a b (by have := (support a ha).1; omega)
        hab hbc hrel
    rcases hclass with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hs294 : S 294 := by simpa [add735] using hb
      simp [h294] at hs294
    · have hs294 : S 294 := by simpa [add735] using ha
      simp [h294] at hs294

theorem trim734_admissible
    (S : Nat → Bool) (hS : Admissible 735 S) :
    Admissible 734 (trim734 S) := by
  constructor
  · intro x hx
    simp [trim734] at hx
    exact ⟨(hS.1 x hx.1).1, hx.2⟩
  · intro a b c hab hbc ha hb hc hrel
    simp [trim734] at ha hb hc
    exact hS.2 a b c hab hbc ha.1 hb.1 hc.1 hrel

theorem add735_cardinal734 (S : Nat → Bool) :
    cardinal734 (add735 S) = cardinal734 S := by
  unfold cardinal734
  apply congrArg List.length
  apply List.filter_congr
  intro x hx
  have hxlt : x < 735 := List.mem_range.mp hx
  have hne : x ≠ 735 := by omega
  simp [add735, hne]

theorem add735_cardinal (S : Nat → Bool) :
    cardinal735 (add735 S) = cardinal734 S + 1 := by
  simp [cardinal735, add735, add735_cardinal734]

theorem trim734_cardinal (S : Nat → Bool) :
    cardinal734 (trim734 S) = cardinal734 S := by
  unfold cardinal734
  apply congrArg List.length
  apply List.filter_congr
  intro x hx
  have hxlt : x < 735 := List.mem_range.mp hx
  have hxle : x ≤ 734 := by omega
  simp [trim734, hxle]

theorem cardinal735_upper_one (S : Nat → Bool) :
    cardinal735 S ≤ cardinal734 S + 1 := by
  unfold cardinal735
  cases h : S 735 <;> simp [h]

theorem upper_735_from_734
    (h734 : ∀ S : Nat → Bool, Admissible 734 S → cardinal734 S ≤ 608)
    (S : Nat → Bool) (hS : Admissible 735 S) :
    cardinal735 S ≤ 609 := by
  have htrim := h734 (trim734 S) (trim734_admissible S hS)
  rw [trim734_cardinal] at htrim
  have hu := cardinal735_upper_one S
  omega

def ExactMaximum735 (k : Nat) : Prop :=
  (∃ S : Nat → Bool, Admissible 735 S ∧ cardinal735 S = k) ∧
  (∀ S : Nat → Bool, Admissible 735 S → cardinal735 S ≤ k)

/-- Exact finite transfer. The two explicit premises are intentionally visible:
    an upper bound at 734 and an admissible 608-witness at 734 omitting 294. -/
theorem exact_735_from_734
    (h734 : ∀ S : Nat → Bool, Admissible 734 S → cardinal734 S ≤ 608)
    (W : Nat → Bool)
    (hW : Admissible 734 W)
    (hWcard : cardinal734 W = 608)
    (hW294 : W 294 = false) :
    ExactMaximum735 609 := by
  constructor
  · refine ⟨add735 W, add735_admissible W hW hW294, ?_⟩
    rw [add735_cardinal, hWcard]
  · exact upper_735_from_734 h734

#print axioms endpoint735_check
#print axioms new_triples_with_735
#print axioms add735_admissible
#print axioms upper_735_from_734
#print axioms exact_735_from_734

end Erdos302F735
