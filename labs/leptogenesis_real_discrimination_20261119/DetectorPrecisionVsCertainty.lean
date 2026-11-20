import Lean

/-!
INSACERMO — SAME isolated A/B neutrino CP phase laboratory, 2026-11-20.
Models from two distinct published theoretical works:
A [198°,225°]; B [5°,40°] or [320°,355°] (circle 360°).
This file proves conditional INTEGER ANGLE geometry for radii
54° (2*27), 44° (2*22), 40° (2*20), 36° (2*18).
27/22/18° are published DUNE benchmark phase precisions at
specific true phases/exposures; 20° is a Hyper-K 1sigma forecast.
Using ANY of these as a symmetric 1-sigma Gaussian standard
deviation uniform in true delta is an ILLUSTRATIVE PROXY only.
A 2sigma interval is NEVER an absolute experimental error bound.
No statistical coverage or detector response is certified here.
Only conditional geometry is proven. Original C3 is UNMODIFIED.
-/

namespace INSACERMO.DetectorPrecisionVsCertainty

def PredictA (p : Int) : Prop := 198 ≤ p ∧ p ≤ 225
def PredictB (p : Int) : Prop :=
  (5 ≤ p ∧ p ≤ 40) ∨ (320 ≤ p ∧ p ≤ 355)

/-- Signed shifts implement circular errors at angles 0..359,
    sufficient for the radii considered here. -/
def CircleError (p z r : Int) : Prop :=
  (p-r ≤ z ∧ z ≤ p+r) ∨
  (p-r ≤ z+360 ∧ z+360 ≤ p+r) ∨
  (p-r ≤ z-360 ∧ z-360 ≤ p+r)

theorem radius54_can_confuse :
    PredictA 225 ∧ PredictB 320 ∧
    CircleError 225 272 54 ∧ CircleError 320 272 54 := by
  simp [PredictA, PredictB, CircleError]

theorem radius44_cannot_confuse (a b z : Int)
    (ha : PredictA a) (hb : PredictB b)
    (hz : 0 ≤ z ∧ z < 360)
    (ea : CircleError a z 44) (eb : CircleError b z 44) : False := by
  unfold PredictA at ha
  unfold PredictB at hb
  unfold CircleError at ea eb
  omega

theorem radius40_cannot_confuse (a b z : Int)
    (ha : PredictA a) (hb : PredictB b)
    (hz : 0 ≤ z ∧ z < 360)
    (ea : CircleError a z 40) (eb : CircleError b z 40) : False := by
  unfold PredictA at ha
  unfold PredictB at hb
  unfold CircleError at ea eb
  omega

theorem radius36_cannot_confuse (a b z : Int)
    (ha : PredictA a) (hb : PredictB b)
    (hz : 0 ≤ z ∧ z < 360)
    (ea : CircleError a z 36) (eb : CircleError b z 36) : False := by
  unfold PredictA at ha
  unfold PredictB at hb
  unfold CircleError at ea eb
  omega

-- A measurement z=272° with a hypothetical ABSOLUTE radius 44°
-- would be compatible with NEITHER of the two model families.
theorem radius44_at_272_excludes_A (p : Int)
    (h : PredictA p) : ¬ CircleError p 272 44 := by
  unfold PredictA at h
  unfold CircleError
  omega

theorem radius44_at_272_excludes_B (p : Int)
    (h : PredictB p) : ¬ CircleError p 272 44 := by
  unfold PredictB at h
  unfold CircleError
  omega

-- The closest predicted true phases are at 225° and 320°.
-- At the halfway OBSERVED angle 272.5°, both fixed-mean
-- symmetric equal-variance Gaussian toy likelihoods are equal.
-- This is just an EXACT DISTANCE IDENTITY, not a Gaussian theorem.
theorem closest_pair_halfway_equaldistance_tenths :
    (2725 : Int) - 2250 = 3200 - 2725 := by omega

theorem closest_pair_halfway_equal_squared_distance_tenths :
    ((2725 : Int)-2250)*((2725 : Int)-2250) =
    ((3200 : Int)-2725)*((3200 : Int)-2725) := by
  decide

end INSACERMO.DetectorPrecisionVsCertainty
