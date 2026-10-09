import Std

/-! A generic proof over a declared finite metric, including Hamming distance:
if opposite-class reference signatures differ in at least 3 coordinates,
and each new observation differs in at most 1 coordinate from its reference,
the two observed signatures cannot be identical.
The numerical inequality follows by metric triangle inequalities.
This lemma does NOT verify CSV decoding or the 7-pixel minimization.
-/
namespace INSACERMO.RadiusOne

theorem separation_under_one_error
    {α : Type} (distance : α → α → Nat)
    (triangle : ∀ a b c, distance a c ≤ distance a b + distance b c)
    (zero : ∀ a, distance a a = 0)
    (origin0 origin1 new0 new1 : α)
    (h0 : distance origin0 new0 ≤ 1)
    (h1 : distance new1 origin1 ≤ 1)
    (hReference : 3 ≤ distance origin0 origin1) :
    new0 ≠ new1 := by
  intro hEqual
  have hLeft := triangle origin0 new0 origin1
  have hRight := triangle new0 new1 origin1
  rw [hEqual, zero] at hRight
  omega

end INSACERMO.RadiusOne
