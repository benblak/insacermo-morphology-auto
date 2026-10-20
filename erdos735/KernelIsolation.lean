import Std

namespace Erdos302Kernel

def inGNat (x : Nat) : Bool :=
 x == 122 || x == 183 || x == 244 || x == 366 || x == 732

def Expected (a b c : Nat) : Prop :=
 (a = 122 ∧ b = 183 ∧ c = 366) ∨
 (a = 183 ∧ b = 244 ∧ c = 732) ∨
 (a = 244 ∧ b = 366 ∧ c = 732)
instance (a b c : Nat) : Decidable (Expected a b c) := by
 unfold Expected
 infer_instance

def quotient (a b : Nat) : Nat := a * b / (b - a)

theorem third_eq_quotient (a b c : Nat) (hab : a < b)
 (hrel : a * (b + c) = b * c) : c = quotient a b := by
 have hm : (b-a)*c = a*b := by
  rw [Nat.mul_sub_right_distrib]
  have hh : a*b + a*c = b*c := by simpa [Nat.mul_add] using hrel
  omega
 unfold quotient
 rw [← hm, Nat.mul_div_cancel_left c (by omega)]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem first_certificate :
 ∀ a ∈ [122,183,244,366,732], ∀ b : Fin 733,
   a < b.val → b.val < quotient a b.val → quotient a b.val ≤ 732 →
   a * (b.val + quotient a b.val) = b.val * quotient a b.val →
   Expected a b.val (quotient a b.val) := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem second_certificate :
 ∀ b ∈ [122,183,244,366,732], ∀ a : Fin 733,
   0 < a.val → a.val < b → b < quotient a.val b → quotient a.val b ≤ 732 →
   a.val * (b + quotient a.val b) = b * quotient a.val b →
   Expected a.val b (quotient a.val b) := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
theorem third_certificate :
 ∀ c ∈ [122,183,244,366,732], ∀ a : Fin 733,
   0 < a.val → a.val < quotient a.val c → quotient a.val c < c →
   a.val * (quotient a.val c + c) = quotient a.val c * c →
   Expected a.val (quotient a.val c) c := by decide +kernel

theorem isolated_nat (a b c : Nat)
 (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : c ≤ 732)
 (hrel : a * (b + c) = b * c)
 (hG : inGNat a || inGNat b || inGNat c) :
 (a = 122 ∧ b = 183 ∧ c = 366) ∨
 (a = 183 ∧ b = 244 ∧ c = 732) ∨
 (a = 244 ∧ b = 366 ∧ c = 732) := by
 have membership (x : Nat) (hx : inGNat x = true) :
     x ∈ [122,183,244,366,732] := by simpa [inGNat, or_assoc] using hx
 have split : inGNat a = true ∨ inGNat b = true ∨ inGNat c = true := by
  simpa [Bool.or_eq_true, or_assoc] using hG
 rcases split with haG | hbG | hcG
 · have eqc := third_eq_quotient a b c hab hrel
   have ht := first_certificate a (membership a haG) ⟨b, by omega⟩ hab
    (by simpa [← eqc] using hbc) (by simpa [← eqc] using hc)
    (by simpa [← eqc] using hrel)
   simpa [Expected, ← eqc] using ht
 · have eqc := third_eq_quotient a b c hab hrel
   have ht := second_certificate b (membership b hbG) ⟨a, by omega⟩ ha hab
    (by simpa [← eqc] using hbc) (by simpa [← eqc] using hc)
    (by simpa [← eqc] using hrel)
   simpa [Expected, ← eqc] using ht
 · have eqb := third_eq_quotient a c b (by omega)
    (by simpa [Nat.add_comm, Nat.mul_comm] using hrel)
   have ht := third_certificate c (membership c hcG) ⟨a, by omega⟩ ha
    (by simpa [← eqb] using hab) (by simpa [← eqb] using hbc)
    (by simpa [← eqb] using hrel)
   simpa [Expected, ← eqb] using ht

#print axioms isolated_nat
#print axioms third_eq_quotient
#print axioms first_certificate
#print axioms second_certificate
#print axioms third_certificate
end Erdos302Kernel
