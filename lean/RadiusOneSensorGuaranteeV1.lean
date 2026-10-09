import Std

/-! Finite classification under one arbitrary altered sensor reading in EACH
image. A reference image has a stable origin label. The signature of each
altered image lies in a radius-one Hamming ball around its original signature.
Opposite-label balls are disjoint if reference signatures differ in >=3
coordinates. This is not a universal handwriting recognition guarantee. -/
namespace INSACERMO.RadiusOne

def hamming (xs ys : List Nat) : Nat :=
  (List.zip xs ys).filter (fun xy => xy.1 != xy.2) |>.length

theorem robust_binary_signatures_separated
    (reference0 reference1 altered0 altered1 : List Nat)
    (h0 : hamming reference0 altered0 ≤ 1)
    (h1 : hamming reference1 altered1 ≤ 1)
    (hDistinct : 3 ≤ hamming reference0 reference1)
    (hTriangleLeft : hamming reference0 reference1 ≤
      hamming reference0 altered0 + hamming altered0 reference1)
    (hTriangleRight : hamming altered0 reference1 ≤
      hamming altered0 altered1 + hamming altered1 reference1)
    (hSymmetric : hamming altered1 reference1 = hamming reference1 altered1) :
    altered0 ≠ altered1 := by
  intro heq
  subst altered1
  have := Nat.le_trans hDistinct (Nat.le_trans hTriangleLeft
    (Nat.add_le_add_left hTriangleRight _))
  simp only [hamming, List.zip_self, List.filter_false, List.length_nil] at this
  omega

end INSACERMO.RadiusOne
