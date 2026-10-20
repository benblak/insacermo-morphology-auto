import Plateau302
import KernelEndpoints734

/-! Exact maximum transfers through 734. The numerical corollaries retain an explicit external baseline. -/

namespace Erdos302Extension734
open Erdos302Finite

theorem no_new_triples (a b c : Nat)
 (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : c ≤ 734)
 (hrel : a * (b + c) = b * c) : c ≤ 732 := by
 exact Erdos302KernelEndpoints734.no_new_triples a b c ha hab hbc hc hrel

def fullCardinal (S : Nat → Bool) : Nat :=
 cardinal S + (S 733).toNat + (S 734).toNat

def fullDomain : List Nat := (outside ++ gadget) ++ [733,734]

theorem full_domain_membership (x : Nat) :
 x ∈ fullDomain ↔ 0 < x ∧ x ≤ 734 := by
 rw [fullDomain, List.mem_append, domain_membership]
 simp only [List.mem_cons, List.mem_nil_iff, or_false]
 omega

theorem full_domain_nodup : fullDomain.Nodup := by
 apply List.nodup_append.mpr
 refine ⟨domain_nodup, by decide, ?_⟩
 intro a ha b hb heq
 have hbnd := (domain_membership a).mp ha
 simp at hb
 omega

theorem full_cardinal_domain (S : Nat → Bool) :
 fullCardinal S = (fullDomain.filter S).length := by
 cases h1 : S 733 <;> cases h2 : S 734 <;> simp [fullCardinal, fullDomain, cardinal, h1, h2] <;> omega

theorem base_cardinal_congr (S T : Nat → Bool)
 (h : ∀ x, 0 < x → x ≤ 732 → S x = T x) : cardinal S = cardinal T := by
 rw [cardinal_eq_domain_count, cardinal_eq_domain_count]
 apply congrArg List.length
 apply List.filter_congr
 intro x hx
 have hh := (domain_membership x).mp hx
 exact h x hh.1 hh.2

def trim (S : Nat → Bool) (x : Nat) : Bool := S x && decide (x ≤ 732)
def liftTo (S : Nat → Bool) (n x : Nat) : Bool :=
 if x ≤ 732 then S x else (x == 733 || x == 734) && decide (x ≤ n)

theorem trim_cardinal (S : Nat → Bool) : cardinal (trim S) = cardinal S := by
 apply base_cardinal_congr
 intro x _ hx
 simp [trim, hx]

theorem lift_cardinal (S : Nat → Bool) (n : Nat) :
 cardinal (liftTo S n) = cardinal S := by
 apply base_cardinal_congr
 intro x _ hx
 simp [liftTo, hx]

theorem trim_admissible (S : Nat → Bool) (n : Nat) (hS : Admissible n S) :
 Admissible 732 (trim S) := by
 constructor
 · intro x hx
   simp [trim] at hx
   exact ⟨(hS.1 x hx.1).1,hx.2⟩
 · intro a b c hab hbc ha hb hc heq
   simp [trim] at ha hb hc
   exact hS.2 a b c hab hbc ha.1 hb.1 hc.1 heq

theorem lift_admissible (S : Nat → Bool) (n : Nat)
 (hnlo : 732 ≤ n) (hnhi : n ≤ 734) (hS : Admissible 732 S) :
 Admissible n (liftTo S n) := by
 have support : ∀ x, liftTo S n x → 0 < x ∧ x ≤ n := by
  intro x hx
  by_cases h : x ≤ 732
  · have hsx : S x := by simpa [liftTo, h] using hx
    have hh := hS.1 x hsx
    omega
  · simp [liftTo, h] at hx
    omega
 refine ⟨support, ?_⟩
 intro a b c hab hbc ha hb hc heq
 have ca : 0 < a := (support a ha).1
 have cc : c ≤ 734 := by have hh := (support c hc).2; omega
 have cb := no_new_triples a b c ca hab hbc cc heq
 have ab : a ≤ 732 := by omega
 have bb : b ≤ 732 := by omega
 have sa : S a := by simpa [liftTo, ab] using ha
 have sb : S b := by simpa [liftTo, bb] using hb
 have sc : S c := by simpa [liftTo, cb] using hc
 exact hS.2 a b c hab hbc sa sb sc heq

theorem full_lift_733 (S : Nat → Bool) :
 fullCardinal (liftTo S 733) = cardinal S + 1 := by
 simp [fullCardinal, lift_cardinal, liftTo]

theorem full_lift_734 (S : Nat → Bool) :
 fullCardinal (liftTo S 734) = cardinal S + 2 := by
 simp [fullCardinal, lift_cardinal, liftTo]

theorem upper_full_733 (S : Nat → Bool) (hS : Admissible 733 S) :
 fullCardinal S ≤ cardinal S + 1 := by
 have h734 : S 734 = false := by
  cases h : S 734
  · rfl
  · have hh := (hS.1 734 h).2
    omega
 cases h733 : S 733 <;> simp [fullCardinal, h733, h734]

theorem upper_full_734 (S : Nat → Bool) : fullCardinal S ≤ cardinal S + 2 := by
 cases h733 : S 733 <;> cases h734 : S 734 <;> simp [fullCardinal, h733, h734] <;> omega

def FullExactMaximum (n k : Nat) : Prop :=
 (∃ S : Nat → Bool, Admissible n S ∧ fullCardinal S = k) ∧
 (∀ S : Nat → Bool, Admissible n S → fullCardinal S ≤ k)

theorem exact_maximum_733_transfer (k : Nat) (h : ExactMaximum 732 k) :
 FullExactMaximum 733 (k + 1) := by
 constructor
 · rcases h.1 with ⟨S,hS,hcard⟩
   exact ⟨liftTo S 733, lift_admissible S 733 (by decide) (by decide) hS,
    by rw [full_lift_733,hcard]⟩
 · intro S hS
   have hh := h.2 (trim S) (trim_admissible S 733 hS)
   rw [trim_cardinal] at hh
   have hu := upper_full_733 S hS
   omega

theorem exact_maximum_734_transfer (k : Nat) (h : ExactMaximum 732 k) :
 FullExactMaximum 734 (k + 2) := by
 constructor
 · rcases h.1 with ⟨S,hS,hcard⟩
   exact ⟨liftTo S 734, lift_admissible S 734 (by decide) (by decide) hS,
    by rw [full_lift_734,hcard]⟩
 · intro S hS
   have hh := h.2 (trim S) (trim_admissible S 734 hS)
   rw [trim_cardinal] at hh
   have hu := upper_full_734 S
   omega

-- These numerical conclusions have an explicit external 731 baseline premise.
theorem numerical_733_from_731 (h : ExactMaximum 731 606) :
 FullExactMaximum 733 607 :=
 exact_maximum_733_transfer 606 (exact_maximum_transfer 606 h)

theorem numerical_734_from_731 (h : ExactMaximum 731 606) :
 FullExactMaximum 734 608 :=
 exact_maximum_734_transfer 606 (exact_maximum_transfer 606 h)

#print axioms no_new_triples
#print axioms full_domain_nodup
#print axioms exact_maximum_733_transfer
#print axioms exact_maximum_734_transfer
#print axioms numerical_734_from_731



def add734 (S : Nat → Bool) (x : Nat) : Bool := if x = 734 then true else S x
def erase734 (S : Nat → Bool) (x : Nat) : Bool := if x = 734 then false else S x

theorem add734_base_cardinal (S : Nat → Bool) : cardinal (add734 S) = cardinal S := by
 apply base_cardinal_congr
 intro x _ hx
 have hh : x ≠ 734 := by omega
 simp [add734,hh]

theorem erase734_base_cardinal (S : Nat → Bool) : cardinal (erase734 S) = cardinal S := by
 apply base_cardinal_congr
 intro x _ hx
 have hh : x ≠ 734 := by omega
 simp [erase734,hh]

theorem erase734_admissible (S : Nat → Bool) (hS : Admissible 734 S) :
 Admissible 733 (erase734 S) := by
 constructor
 · intro x hx
   by_cases heq : x = 734
   · simp [erase734,heq] at hx
   · have hsx : S x := by simpa [erase734,heq] using hx
     have hh := hS.1 x hsx
     omega
 · intro a b c hab hbc ha hb hc heq
   have sub : ∀ x, erase734 S x → S x := by
    intro x hx
    by_cases h : x = 734 <;> simp_all [erase734]
   exact hS.2 a b c hab hbc (sub a ha) (sub b hb) (sub c hc) heq

theorem add734_admissible (S : Nat → Bool) (hS : Admissible 733 S) :
 Admissible 734 (add734 S) := by
 have support : ∀ x, add734 S x → 0 < x ∧ x ≤ 734 := by
  intro x hx
  by_cases h : x = 734
  · omega
  · have hsx : S x := by simpa [add734,h] using hx
    have hh := hS.1 x hsx
    omega
 refine ⟨support,?_⟩
 intro a b c hab hbc ha hb hc heq
 have hh := no_new_triples a b c (support a ha).1 hab hbc (support c hc).2 heq
 have an : a ≠ 734 := by omega
 have bn : b ≠ 734 := by omega
 have cn : c ≠ 734 := by omega
 have sa : S a := by simpa [add734,an] using ha
 have sb : S b := by simpa [add734,bn] using hb
 have sc : S c := by simpa [add734,cn] using hc
 exact hS.2 a b c hab hbc sa sb sc heq

theorem add734_cardinal (S : Nat → Bool) (hS : Admissible 733 S) :
 fullCardinal (add734 S) = fullCardinal S + 1 := by
 have hz : S 734 = false := by
  cases h : S 734
  · rfl
  · have hh := (hS.1 734 h).2
    omega
 simp [fullCardinal,add734_base_cardinal,add734,hz]

theorem erase734_cardinal (S : Nat → Bool) :
 fullCardinal S ≤ fullCardinal (erase734 S) + 1 := by
 cases hh : S 734 <;> simp [fullCardinal,erase734_base_cardinal,erase734,hh]

theorem exact_maximum_734_from_733 (k : Nat) (h : FullExactMaximum 733 k) :
 FullExactMaximum 734 (k + 1) := by
 constructor
 · rcases h.1 with ⟨S,hS,hc⟩
   exact ⟨add734 S,add734_admissible S hS, by rw [add734_cardinal S hS,hc]⟩
 · intro S hS
   have h1 := h.2 (erase734 S) (erase734_admissible S hS)
   have h2 := erase734_cardinal S
   omega

#print axioms exact_maximum_734_from_733

end Erdos302Extension734
