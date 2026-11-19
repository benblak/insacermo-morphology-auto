import Lean

/-!
INSACERMO -- SAME isolated neutrino CP laboratory, 2026-11-19.
The PRELIMINARY Bari 2026.a global fit (2026-10-15) quotes 1D
profiled delta_CP intervals: https://global-nu.org/results.html
Here all coordinates are in TENTHS of degrees.
A = 1980..2250; B = 50..400 or 3200..3550.
NO confidence sets: 1sigma 1890..2412, 2sigma 1656..2970,
3sigma 1422..3510.
Only interval arithmetic is verified, NOT scientific data quality,
likelihood calibration, a true baryogenesis model, or the old C3.
The original engine and formal kernel remain unchanged.
-/

namespace INSACERMO.Bari2026a

def Overlap (l u a b : Int) : Prop := l ≤ b ∧ a ≤ u

theorem one_sigma_A : Overlap 1890 2412 1980 2250 := by
  unfold Overlap
  decide

theorem one_sigma_no_B :
    ¬ Overlap 1890 2412 50 400 ∧
    ¬ Overlap 1890 2412 3200 3550 := by
  unfold Overlap
  decide

theorem two_sigma_A : Overlap 1656 2970 1980 2250 := by
  unfold Overlap
  decide

theorem two_sigma_no_B :
    ¬ Overlap 1656 2970 50 400 ∧
    ¬ Overlap 1656 2970 3200 3550 := by
  unfold Overlap
  decide

theorem three_sigma_A_and_B_high :
    Overlap 1422 3510 1980 2250 ∧
    Overlap 1422 3510 3200 3550 := by
  unfold Overlap
  decide

theorem three_sigma_no_B_low :
    ¬ Overlap 1422 3510 50 400 := by
  unfold Overlap
  decide

theorem B_high_witness :
    (3200 : Int) ≥ 1422 ∧ 3200 ≤ 3510 ∧ 3200 ≥ 3200 ∧ 3200 ≤ 3550 := by decide

end INSACERMO.Bari2026a
