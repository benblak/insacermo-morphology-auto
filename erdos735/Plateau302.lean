import KernelIsolation
import Init.Data.Rat

/-!
Finite plateau for the reciprocal-triple-free extremal function in Erdős problem 302.

The main theorem `plateau_732` says that the attainable cardinality thresholds for
subsets of {1,...,732} and {1,...,731} are identical. It does not assume a numerical
value for either extremal function. `exact_maximum_transfer` explicitly assumes
a numerical baseline at 731 and transfers it to 732.

The OEIS A390395 b-file, accessed 2026-09-07, ends with 731 606. Combining that
external baseline with this transition gives 732 606. The baseline is not
formalized in this file. This does not solve the asymptotic Erdős conjecture.

The finite isolation proof now uses exact quotient tables evaluated by the Lean
kernel. The earlier native bv_decide version remains in the publication history.
The current theorem has only ordinary Lean logical axioms; dependencies are printed below.
-/

namespace Erdos302Finite

-- Exact bridge to the original unit-fraction equation, using Lean core rationals.
theorem unit_fraction_equivalence (a b c : Nat) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
   (1 : Rat) / (↑a : Rat) = (1 : Rat) / (↑b : Rat) + (1 : Rat) / (↑c : Rat) ↔
   a * (b + c) = b * c := by
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  change ((↑(1 : Int) : Rat) / (↑a : Rat) = (↑(1 : Int) : Rat) / (↑b : Rat) + (↑(1 : Int) : Rat) / (↑c : Rat)) ↔ _
  rw [← Rat.mkRat_eq_div, ← Rat.mkRat_eq_div, ← Rat.mkRat_eq_div]
  rw [Rat.mkRat_add_mkRat 1 1 hb0 hc0]
  rw [Rat.mkRat_eq_iff ha0 (Nat.mul_ne_zero hb0 hc0)]
  simp only [Int.one_mul]
  simp only [← Int.natCast_add, ← Int.natCast_mul, Int.ofNat_inj]
  simp [Nat.add_comm, Nat.mul_comm, eq_comm]

def inGNat (x : Nat) : Bool :=
 x == 122 || x == 183 || x == 244 || x == 366 || x == 732

theorem isolated_nat (a b c : Nat)
 (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : c ≤ 732)
 (hrel : a * (b + c) = b * c)
 (hG : inGNat a || inGNat b || inGNat c) :
 (a = 122 ∧ b = 183 ∧ c = 366) ∨
 (a = 183 ∧ b = 244 ∧ c = 732) ∨
 (a = 244 ∧ b = 366 ∧ c = 732) := by
 exact Erdos302Kernel.isolated_nat a b c ha hab hbc hc hrel hG

def gadget : List Nat := [122, 183, 244, 366, 732]
def outside : List Nat := (List.range 733).filter (fun x => 0 < x && !inGNat x)

def cardinal (S : Nat → Bool) : Nat :=
 (outside.filter S).length + (gadget.filter S).length

def Admissible (n : Nat) (S : Nat → Bool) : Prop :=
 (∀ x, S x → 0 < x ∧ x ≤ n) ∧
 (∀ a b c, a < b → b < c → S a → S b → S c → a * (b + c) ≠ b * c)

def replacement (S : Nat → Bool) (x : Nat) : Bool :=
 if inGNat x then x == 122 || x == 183 || x == 244 else S x

theorem replacement_bound (S : Nat → Bool) (hS : Admissible 732 S) :
 ∀ x, replacement S x → 0 < x ∧ x ≤ 731 := by
 intro x hx
 by_cases hG : inGNat x = true
 · simp [replacement, hG] at hx
   omega
 · have hnot : inGNat x = false := by cases h : inGNat x <;> simp_all
   have hsx : S x := by simpa [replacement, hnot] using hx
   have hb := hS.1 x hsx
   have : x ≠ 732 := by intro he; subst x; simp [inGNat] at hnot
   omega

theorem replacement_admissible (S : Nat → Bool) (hS : Admissible 732 S) :
 Admissible 731 (replacement S) := by
 have hbound := replacement_bound S hS
 refine ⟨hbound, ?_⟩
 intro a b c hab hbc ha hb hc heq
 have haa := (hbound a ha).1
 have hcc : c ≤ 732 := by have := (hbound c hc).2; omega
 by_cases hG : (inGNat a || inGNat b || inGNat c) = true
 · have hg := isolated_nat a b c haa hab hbc hcc heq hG
   rcases hg with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
   all_goals simp [replacement, inGNat] at ha hb hc
 · have hz : inGNat a = false ∧ inGNat b = false ∧ inGNat c = false := by
    simpa [and_assoc] using hG
   have sa : S a := by simpa [replacement, hz.1] using ha
   have sb : S b := by simpa [replacement, hz.2.1] using hb
   have sc : S c := by simpa [replacement, hz.2.2] using hc
   exact hS.2 a b c hab hbc sa sb sc heq

theorem local_cardinal_bound (S : Nat → Bool) (hS : Admissible 732 S) :
 (gadget.filter S).length ≤ 3 := by
 have h1 : ¬(S 122 = true ∧ S 183 = true ∧ S 366 = true) := by
  intro ⟨ha,hb,hc⟩
  exact hS.2 122 183 366 (by decide) (by decide) ha hb hc (by decide)
 have h2 : ¬(S 183 = true ∧ S 244 = true ∧ S 732 = true) := by
  intro ⟨ha,hb,hc⟩
  exact hS.2 183 244 732 (by decide) (by decide) ha hb hc (by decide)
 have h3 : ¬(S 244 = true ∧ S 366 = true ∧ S 732 = true) := by
  intro ⟨ha,hb,hc⟩
  exact hS.2 244 366 732 (by decide) (by decide) ha hb hc (by decide)
 cases ha : S 122 <;> cases hb : S 183 <;> cases hc : S 244 <;>
  cases hd : S 366 <;> cases he : S 732 <;> simp_all [gadget]

theorem replacement_cardinal (S : Nat → Bool) (hS : Admissible 732 S) :
 cardinal S ≤ cardinal (replacement S) := by
 have hs : outside.filter S = outside.filter (replacement S) := by
  apply List.filter_congr
  intro x hx
  have hxg : inGNat x = false := by
   have h := (List.mem_filter.mp hx).2
   simp_all [outside]
  simp [replacement, hxg]
 have hg : (gadget.filter (replacement S)).length = 3 := by
  simp [gadget, replacement, inGNat]
 have hb := local_cardinal_bound S hS
 unfold cardinal
 rw [← hs, hg]
 omega

theorem plateau_732 (k : Nat) :
 (∃ S : Nat → Bool, Admissible 732 S ∧ k ≤ cardinal S) ↔
 (∃ S : Nat → Bool, Admissible 731 S ∧ k ≤ cardinal S) := by
 constructor
 · rintro ⟨S,hS,hk⟩
   exact ⟨replacement S, replacement_admissible S hS,
      Nat.le_trans hk (replacement_cardinal S hS)⟩
 · rintro ⟨S,hS,hk⟩
   refine ⟨S, ⟨?_,hS.2⟩,hk⟩
   intro x hx
   have hb := hS.1 x hx
   omega

#print axioms plateau_732



-- This domain is a permutation of 1,...,732, so `cardinal` is ordinary set cardinality.
theorem domain_membership (x : Nat) :
 x ∈ (outside ++ gadget) ↔ 0 < x ∧ x ≤ 732 := by
 simp [outside, gadget, inGNat]
 omega

theorem domain_nodup : (outside ++ gadget).Nodup := by
 apply List.nodup_append.mpr
 refine ⟨List.Pairwise.filter _ List.nodup_range, by decide, ?_⟩
 intro a ha b hb heq
 subst b
 have hout := (List.mem_filter.mp ha).2
 simp [gadget] at hb
 simp [inGNat] at hout
 omega

theorem cardinal_eq_domain_count (S : Nat → Bool) :
 cardinal S = ((outside ++ gadget).filter S).length := by
 simp [cardinal]

def ExactMaximum (n k : Nat) : Prop :=
 (∃ S : Nat → Bool, Admissible n S ∧ cardinal S = k) ∧
 (∀ S : Nat → Bool, Admissible n S → cardinal S ≤ k)

-- The numerical 731 baseline is an explicit premise, not an axiom or an unproved assertion.
theorem exact_maximum_transfer (k : Nat) (h : ExactMaximum 731 k) :
 ExactMaximum 732 k := by
 refine ⟨?_, ?_⟩
 · rcases h.1 with ⟨S,hS,hcard⟩
   refine ⟨S, ⟨?_,hS.2⟩,hcard⟩
   intro x hx
   have hb := hS.1 x hx
   omega
 · intro S hS
   exact Nat.le_trans (replacement_cardinal S hS)
     (h.2 (replacement S) (replacement_admissible S hS))

#print axioms domain_membership
#print axioms domain_nodup
#print axioms exact_maximum_transfer



-- The same admissibility condition stated with exact rational unit fractions.
def RatAdmissible (n : Nat) (S : Nat → Bool) : Prop :=
 (∀ x, S x → 0 < x ∧ x ≤ n) ∧
 (∀ a b c, a < b → b < c → S a → S b → S c →
   (1 : Rat) / (↑a : Rat) ≠ (1 : Rat) / (↑b : Rat) + (1 : Rat) / (↑c : Rat))

theorem admissible_iff_rat (n : Nat) (S : Nat → Bool) :
 Admissible n S ↔ RatAdmissible n S := by
 constructor
 · intro h
   refine ⟨h.1, ?_⟩
   intro a b c hab hbc ha hb hc hrel
   exact h.2 a b c hab hbc ha hb hc
     ((unit_fraction_equivalence a b c (h.1 a ha).1 (h.1 b hb).1 (h.1 c hc).1).mp hrel)
 · intro h
   refine ⟨h.1, ?_⟩
   intro a b c hab hbc ha hb hc hrel
   exact h.2 a b c hab hbc ha hb hc
     ((unit_fraction_equivalence a b c (h.1 a ha).1 (h.1 b hb).1 (h.1 c hc).1).mpr hrel)

theorem rat_plateau_732 (k : Nat) :
 (∃ S : Nat → Bool, RatAdmissible 732 S ∧ k ≤ cardinal S) ↔
 (∃ S : Nat → Bool, RatAdmissible 731 S ∧ k ≤ cardinal S) := by
 simp only [← admissible_iff_rat]
 exact plateau_732 k

#print axioms unit_fraction_equivalence
#print axioms admissible_iff_rat
#print axioms rat_plateau_732

end Erdos302Finite
