import NuFIT61GridCertification

/-!
INSACERMO / SAME frozen C3 laboratory / 2026-11-20.
An exact, CONDITIONAL sensitivity calculation, not a new detector model.
Source of tabulated NO NuFIT v6.1 CP values is SHA-256 pinned in the
source-derived NuFIT61GridCertification module, generated from 73 rows.
Chi-square quantities are exact integers, scaled by 10^12.
Nominal decision conventions: 2sigma <=4, 3sigma <=9.
The NuFIT 2025 tabulated grid differs from Bari 2026.a preliminary
intervals. No inference about a calibrated confidence level, physical
detector sensitivity, or unobserved continuously varying likelihood.
The + and - perturbations represent HYPOTHETICAL changes in the MINIMA
of the respective NuFIT high/low-B regions. No causal response model
is provided. C3 original code and original Lean kernel stay frozen.
-/

namespace INSACERMO.JointSensitivityMargins
open INSACERMO.NuFIT61RealGrid

def highMin : Nat := 3690221000000
def lowMin : Nat := 9048116000000
def cutoff2 : Nat := 4000000000000
def cutoff3 : Nat := 9000000000000
def highMargin : Nat := 309779000000
def lowMargin : Nat := 48116000000

theorem observed_high_witness : (320, highMin) ∈ grid := by
  exact witnessed_B_high

theorem observed_low_witness : (5, lowMin) ∈ grid := by
  exact witnessed_B_low

theorem high_margin_exact :
    highMin + highMargin = cutoff2 := by
  decide

theorem high_min_still_inside_for_every_shift_at_most_margin
    (shift : Nat) (h : shift ≤ highMargin) :
    highMin + shift ≤ cutoff2 := by
  unfold highMin highMargin cutoff2 at *
  omega

theorem high_min_outside_when_shift_exceeds_margin
    (shift : Nat) (h : highMargin < shift) :
    cutoff2 < highMin + shift := by
  unfold highMin highMargin cutoff2 at *
  omega

theorem low_margin_exact :
    lowMin - lowMargin = cutoff3 := by
  decide

theorem low_min_stays_outside_for_every_decrease_below_margin
    (decrease : Nat) (h : decrease < lowMargin) :
    cutoff3 < lowMin - decrease := by
  unfold lowMin lowMargin cutoff3 at *
  omega

theorem low_min_boundary_is_admissible :
    lowMin - lowMargin ≤ cutoff3 := by
  decide

theorem both_verdicts_stable_under_declared_minimum_changes
    (increaseHigh decreaseLow : Nat)
    (hHigh : increaseHigh ≤ highMargin)
    (hLow : decreaseLow < lowMargin) :
    highMin + increaseHigh ≤ cutoff2 ∧
    cutoff3 < lowMin - decreaseLow := by
  constructor
  · exact high_min_still_inside_for_every_shift_at_most_margin increaseHigh hHigh
  · exact low_min_stays_outside_for_every_decrease_below_margin decreaseLow hLow

end INSACERMO.JointSensitivityMargins
