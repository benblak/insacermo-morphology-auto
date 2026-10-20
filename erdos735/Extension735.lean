import Extension734

/-! Independent extension from 734 to 735 for Erdős #302.
The archived Lean 734 sources are vendored unchanged on this isolated branch.
The numerical value at 731 is an explicit theorem premise. -/

namespace Erdos302Extension735
open Erdos302Finite Erdos302Extension734
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

def excluded : List Nat := [
  6,10,12,18,20,23,26,28,34,36,40,42,48,50,56,60,66,68,70,72,
  76,78,84,88,90,96,100,102,108,110,112,114,120,124,126,128,
  130,132,134,138,140,142,144,146,148,150,154,156,158,162,164,
  166,168,172,174,176,178,180,182,184,186,188,190,194,195,198,
  200,202,204,206,208,210,212,214,216,218,220,222,226,228,234,
  236,238,240,244,246,247,252,258,260,264,270,272,276,282,286,
  288,294,300,308,318,320,323,330,336,342,348,352,354,366,378,
  442,460,462,480,510,560,580,588,600,630,660,680,690,726,728]

def W (x : Nat) : Bool := decide (0 < x ∧ x ≤ 734 ∧ x ∉ excluded)

theorem W_294 : W 294 = false := by decide +kernel

theorem W_cardinal : fullCardinal W = 608 := by decide +kernel

theorem W_bound (x : Nat) (hx : W x) : 0 < x ∧ x ≤ 734 := by
  simpa [W] using hx

theorem W_pair_certificate :
  ∀ b : Fin 735, ∀ c : Fin 735,
    b.val < c.val → W b.val → W c.val →
    (b.val + c.val) ∣ b.val * c.val →
    W (b.val * c.val / (b.val + c.val)) →
    b.val * c.val / (b.val + c.val) < b.val → False := by
  decide +kernel

theorem W_admissible : Admissible 734 W := by
  constructor
  · intro x hx
    exact W_bound x hx
  · intro a b c hab hbc ha hb hc hrel
    have hbnd := W_bound b hb
    have hcnd := W_bound c hc
    have hdiv : b + c ∣ b * c := ⟨a, by simpa [Nat.mul_comm] using hrel.symm⟩
    have hq : a = b * c / (b + c) := by
      calc
        a = ((b + c) * a) / (b + c) := by
          exact (Nat.mul_div_cancel_left a (by omega)).symm
        _ = (b * c) / (b + c) := by rw [Nat.mul_comm (b + c) a, hrel]
    exact W_pair_certificate ⟨b, by omega⟩ ⟨c, by omega⟩
      hbc hb hc hdiv (by simpa [← hq] using ha) (by simpa [← hq] using hab)

def endpoint735Check : Bool :=
  (List.range 736).all (fun b =>
    !(0 < b && b < 735 && b != 294 && b != 490) ||
      b * 735 % (b + 735) != 0)

theorem endpoint735_certificate : endpoint735Check = true := by decide +kernel

theorem new_triplet_uses_294 (a b : Nat)
    (ha : 0 < a) (hab : a < b) (hbc : b < 735)
    (hrel : a * (b + 735) = b * 735) : a = 294 ∨ b = 294 := by
  have hbound : b < 736 := by omega
  have hrow := List.all_eq_true.mp endpoint735_certificate b (List.mem_range.mpr hbound)
  by_cases hb294 : b = 294
  · exact Or.inr hb294
  by_cases hb490 : b = 490
  · left
    subst b
    omega
  have hnonzero : b * 735 % (b + 735) ≠ 0 := by
    simpa [show 0 < b by omega, hbc, hb294, hb490] using hrow
  have hdiv : (b + 735) ∣ b * 735 := ⟨a, by simpa [Nat.mul_comm] using hrel.symm⟩
  exact False.elim (hnonzero (Nat.mod_eq_zero_of_dvd hdiv))

def add735 (S : Nat → Bool) (x : Nat) : Bool := if x = 735 then true else S x
def erase735 (S : Nat → Bool) (x : Nat) : Bool := if x = 735 then false else S x
def cardinal735 (S : Nat → Bool) : Nat := fullCardinal S + (S 735).toNat

theorem base_cardinal_add735 (S : Nat → Bool) : cardinal (add735 S) = cardinal S := by
  apply base_cardinal_congr
  intro x _ hx
  have h : x ≠ 735 := by omega
  simp [add735, h]

theorem base_cardinal_erase735 (S : Nat → Bool) : cardinal (erase735 S) = cardinal S := by
  apply base_cardinal_congr
  intro x _ hx
  have h : x ≠ 735 := by omega
  simp [erase735, h]

theorem card_add735 (S : Nat → Bool) : cardinal735 (add735 S) = fullCardinal S + 1 := by
  simp [cardinal735, fullCardinal, base_cardinal_add735, add735]

theorem card_erase735 (S : Nat → Bool) : cardinal735 S ≤ fullCardinal (erase735 S) + 1 := by
  have h733 : erase735 S 733 = S 733 := by simp [erase735]
  have h734 : erase735 S 734 = S 734 := by simp [erase735]
  unfold cardinal735 fullCardinal
  rw [base_cardinal_erase735, h733, h734]
  cases h : S 735 <;> simp [h]

theorem erase735_admissible (S : Nat → Bool) (hS : Admissible 735 S) :
    Admissible 734 (erase735 S) := by
  constructor
  · intro x hx
    by_cases heq : x = 735
    · simp [erase735, heq] at hx
    · have hsx : S x := by simpa [erase735, heq] using hx
      have hh := hS.1 x hsx
      omega
  · intro a b c hab hbc ha hb hc heq
    have sub : ∀ x, erase735 S x → S x := by
      intro x hx
      by_cases h : x = 735 <;> simp_all [erase735]
    exact hS.2 a b c hab hbc (sub a ha) (sub b hb) (sub c hc) heq

theorem add735_admissible (S : Nat → Bool)
    (hS : Admissible 734 S) (h294 : S 294 = false) :
    Admissible 735 (add735 S) := by
  have support : ∀ x, add735 S x → 0 < x ∧ x ≤ 735 := by
    intro x hx
    by_cases h : x = 735
    · omega
    · have hsx : S x := by simpa [add735, h] using hx
      have hh := hS.1 x hsx
      omega
  refine ⟨support, ?_⟩
  intro a b c hab hbc ha hb hc heq
  by_cases hc735 : c = 735
  · subst c
    have hh := new_triplet_uses_294 a b (support a ha).1 hab hbc heq
    rcases hh with ha294 | hb294
    · subst a
      have hs294 : S 294 := by simpa [add735] using ha
      simp [h294] at hs294
    · subst b
      have hs294 : S 294 := by simpa [add735] using hb
      simp [h294] at hs294
  · have ca : a ≠ 735 := by omega
    have cb : b ≠ 735 := by omega
    have sa : S a := by simpa [add735, ca] using ha
    have sb : S b := by simpa [add735, cb] using hb
    have sc : S c := by simpa [add735, hc735] using hc
    exact hS.2 a b c hab hbc sa sb sc heq

def ExactMaximum735 (k : Nat) : Prop :=
  (∃ S : Nat → Bool, Admissible 735 S ∧ cardinal735 S = k) ∧
  (∀ S : Nat → Bool, Admissible 735 S → cardinal735 S ≤ k)

theorem numerical_735_from_731 (h731 : ExactMaximum 731 606) : ExactMaximum735 609 := by
  have h734 : FullExactMaximum 734 608 := numerical_734_from_731 h731
  constructor
  · refine ⟨add735 W, add735_admissible W W_admissible W_294, ?_⟩
    simpa [W_cardinal] using card_add735 W
  · intro S hS
    have hu := h734.2 (erase735 S) (erase735_admissible S hS)
    have hc := card_erase735 S
    omega

#print axioms W_pair_certificate
#print axioms W_admissible
#print axioms endpoint735_certificate
#print axioms new_triplet_uses_294
#print axioms numerical_735_from_731

end Erdos302Extension735
