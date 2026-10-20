import Std

namespace Erdos302KernelEndpoints734

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def endpointCheck (c : Nat) : Bool :=
 (List.range 735).all (fun b => !(0 < b && b < c) || b * c % (b + c) != 0)

theorem endpoint733_check : endpointCheck 733 = true := by decide +kernel
theorem endpoint734_check : endpointCheck 734 = true := by decide +kernel

theorem endpoint_impossible (a b c : Nat)
 (hb : 0 < b) (hbc : b < c) (hc : c = 733 ∨ c = 734)
 (hrel : a * (b + c) = b * c) : False := by
 have htab : endpointCheck c = true := by
  rcases hc with rfl | rfl
  · exact endpoint733_check
  · exact endpoint734_check
 have hbound : b < 735 := by omega
 have hrow := List.all_eq_true.mp htab b (List.mem_range.mpr hbound)
 have hnonzero : b * c % (b + c) ≠ 0 := by
  simpa [hb,hbc] using hrow
 have hdiv : (b + c) ∣ b * c := ⟨a, by simpa [Nat.mul_comm] using hrel.symm⟩
 exact hnonzero (Nat.mod_eq_zero_of_dvd hdiv)

theorem no_new_triples (a b c : Nat)
 (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : c ≤ 734)
 (hrel : a * (b + c) = b * c) : c ≤ 732 := by
 by_cases h : c ≤ 732
 · exact h
 · have hend : c = 733 ∨ c = 734 := by omega
   exact False.elim (endpoint_impossible a b c (by omega) hbc hend hrel)

#print axioms endpoint733_check
#print axioms endpoint734_check
#print axioms no_new_triples

end Erdos302KernelEndpoints734
