import Std

/-!
Erdős Problem 302 — finite frontier at n = 735.

This file proves:
* an explicit 609-element subset of {1,...,735} is admissible;
* every admissible subset of {1,...,735} has size at most 609,
  assuming the finite upper-bound premise f(734) ≤ 608.

Thus the numerical conclusion f(735)=609 is kernel-checked conditional only on
that explicit finite premise. No asymptotic claim is made.
-/

namespace Erdos302F735

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

def Admissible (n : Nat) (S : Nat → Bool) : Prop :=
  (∀ x, S x → 0 < x ∧ x ≤ n) ∧
  (∀ a b c, a < b → b < c → S a → S b → S c →
    a * (b + c) ≠ b * c)

def countUpTo (n : Nat) (S : Nat → Bool) : Nat :=
  ((List.range (n + 1)).filter (fun x => 0 < x && S x)).length

def witnessList : List Nat := [
1,2,3,4,5,7,8,9,11,13,14,15,16,17,19,21,22,24,25,27,29,30,31,32,33,35,37,38,39,41,43,44,45,46,47,49,51,52,53,54,55,57,58,59,61,62,63,64,65,67,69,71,73,74,75,76,77,79,80,81,82,83,85,86,87,89,91,93,94,97,98,99,101,103,104,105,106,107,109,111,113,115,116,117,118,119,121,122,123,125,127,129,131,133,135,136,137,139,141,143,147,149,151,152,153,155,157,160,161,163,165,167,169,170,171,173,175,177,179,181,183,185,187,189,191,192,193,196,197,199,201,203,205,207,209,211,213,215,217,219,221,223,224,225,227,229,230,231,232,233,235,237,239,241,242,243,245,247,248,249,250,251,253,254,255,256,257,259,261,262,263,265,266,267,268,269,271,273,274,275,276,277,278,279,280,281,283,284,285,287,289,290,291,292,293,295,296,297,298,299,301,302,303,304,305,306,307,309,310,311,312,313,314,315,316,317,318,319,321,322,324,325,326,327,328,329,331,332,333,334,335,337,338,339,340,341,343,344,345,346,347,349,350,351,353,355,356,357,358,359,360,361,362,363,364,365,367,368,369,370,371,372,373,374,375,376,377,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,461,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,481,482,483,484,485,486,487,488,489,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,581,582,583,584,585,586,587,589,590,591,592,593,594,595,596,597,598,599,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,681,682,683,684,685,686,687,688,689,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,727,729,730,731,732,733,734,735]

def witness (x : Nat) : Bool := witnessList.contains x

def boundsCheck (n : Nat) (L : List Nat) : Bool :=
  L.all (fun x => 0 < x && x ≤ n)

def pairSafe (S : Nat → Bool) (b c : Nat) : Bool :=
  if b < c then
    if b * c % (b + c) = 0 then
      !(S (b * c / (b + c)) && S b && S c)
    else true
  else true

def tripleFreeCheck (n : Nat) (S : Nat → Bool) : Bool :=
  (List.range (n + 1)).all (fun b =>
    (List.range (n + 1)).all (fun c => pairSafe S b c))

theorem witness_nodup : witnessList.Nodup := by decide +kernel
theorem witness_bounds_check : boundsCheck 735 witnessList = true := by decide +kernel
theorem witness_count : countUpTo 735 witness = 609 := by decide +kernel
theorem witness_triple_check : tripleFreeCheck 735 witness = true := by decide +kernel

theorem witness_support (x : Nat) (hx : witness x) : 0 < x ∧ x ≤ 735 := by
  have hmem : x ∈ witnessList := by
    simpa [witness] using hx
  have hall := List.all_eq_true.mp witness_bounds_check x hmem
  simpa [boundsCheck] using hall

theorem witness_admissible : Admissible 735 witness := by
  constructor
  · exact witness_support
  · intro a b c hab hbc ha hb hc hrel
    have hbnd : b < 736 := by
      have h := (witness_support b hb).2
      omega
    have hcnd : c < 736 := by
      have h := (witness_support c hc).2
      omega
    have hrow := List.all_eq_true.mp witness_triple_check b (List.mem_range.mpr hbnd)
    have hcell := List.all_eq_true.mp hrow c (List.mem_range.mpr hcnd)
    have hdiv : (b + c) ∣ b * c := ⟨a, by simpa [Nat.mul_comm] using hrel.symm⟩
    have hmod : b * c % (b + c) = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hden : 0 < b + c := by omega
    have hq : b * c / (b + c) = a := by
      rw [← hrel]
      exact Nat.mul_div_right a hden
    simp [pairSafe, hbc, hmod, hq, ha, hb, hc] at hcell

def trim734 (S : Nat → Bool) (x : Nat) : Bool :=
  S x && decide (x ≤ 734)

theorem trim734_admissible (S : Nat → Bool) (hS : Admissible 735 S) :
    Admissible 734 (trim734 S) := by
  constructor
  · intro x hx
    simp [trim734] at hx
    exact ⟨(hS.1 x hx.1).1, hx.2⟩
  · intro a b c hab hbc ha hb hc hrel
    simp [trim734] at ha hb hc
    exact hS.2 a b c hab hbc ha.1 hb.1 hc.1 hrel

theorem count735_split (S : Nat → Bool) :
    countUpTo 735 S = countUpTo 734 S + (S 735).toNat := by
  simp [countUpTo, List.range_succ]

theorem count_trim734 (S : Nat → Bool) :
    countUpTo 734 (trim734 S) = countUpTo 734 S := by
  apply congrArg List.length
  apply List.filter_congr
  intro x hx
  have hxlt : x < 735 := List.mem_range.mp hx
  have hxle : x ≤ 734 := by omega
  simp [trim734, hxle]

theorem upper_735_from_734
    (h734 : ∀ S : Nat → Bool, Admissible 734 S → countUpTo 734 S ≤ 608)
    (S : Nat → Bool) (hS : Admissible 735 S) :
    countUpTo 735 S ≤ 609 := by
  have htrim := h734 (trim734 S) (trim734_admissible S hS)
  rw [count_trim734] at htrim
  rw [count735_split]
  have hbit : (S 735).toNat ≤ 1 := by
    cases h : S 735 <;> simp [h]
  omega

def ExactMaximum (n k : Nat) : Prop :=
  (∃ S : Nat → Bool, Admissible n S ∧ countUpTo n S = k) ∧
  (∀ S : Nat → Bool, Admissible n S → countUpTo n S ≤ k)

theorem exact_735_from_upper_734
    (h734 : ∀ S : Nat → Bool, Admissible 734 S → countUpTo 734 S ≤ 608) :
    ExactMaximum 735 609 := by
  constructor
  · exact ⟨witness, witness_admissible, witness_count⟩
  · exact upper_735_from_734 h734

#print axioms witness_nodup
#print axioms witness_count
#print axioms witness_triple_check
#print axioms witness_admissible
#print axioms upper_735_from_734
#print axioms exact_735_from_upper_734

end Erdos302F735
