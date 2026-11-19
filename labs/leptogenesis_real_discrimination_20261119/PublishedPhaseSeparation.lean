import Lean

namespace INSACERMO.PublishedLeptogenesisDiscrimination

/-!
This is an independent CONDITIONAL theorem about two PUBLISHED
neutrino CP phase prediction intervals under specific models.
It is not a proof that any baryogenesis mechanism is true.
The error bound is DETERMINISTIC and deliberately idealized;
it is NOT a published DUNE/Hyper-K experimental confidence interval.
-/

/-- Two leptogenesis studies predict (under their individual assumptions):
    A: 198-225 degrees.
    B: 5-40 OR 320-355 degrees.
    These are ANGLES on a circle of length 360 degrees. -/
def PredictA (p : Int) : Prop := 198 ≤ p ∧ p ≤ 225
def PredictB (p : Int) : Prop :=
  (5 ≤ p ∧ p ≤ 40) ∨ (320 ≤ p ∧ p ≤ 355)

/-- An ideal bounded-error measurement z in [0,360).
    Three shifts cover all possible wrap-around coincidences for
    p in [0,360) and error <= 48 degrees. -/
def CircularError (p z error : Int) : Prop :=
  (p-error ≤ z ∧ z ≤ p+error) ∨
  (p-error ≤ z+360 ∧ z+360 ≤ p+error) ∨
  (p-error ≤ z-360 ∧ z-360 ≤ p+error)

/-- With a certified maximum absolute circular measurement error
    of 47 degrees, a measurement cannot be compatible with BOTH
    published prediction families. Conditional on one family being
    correct, the measurement discriminates them. -/
theorem forty_seven_degree_bound_separates
    (pA pB z : Int)
    (hA : PredictA pA) (hB : PredictB pB)
    (hz : 0 ≤ z ∧ z < 360)
    (eA : CircularError pA z 47)
    (eB : CircularError pB z 47) : False := by
  unfold PredictA at hA
  unfold PredictB at hB
  unfold CircularError at eA eB
  omega

/-- The 47 degree guarantee is sharp (as an integer bound):
    At 48 degrees, A phase 225 and B phase 320
    are both compatible with measured phase 272. -/
theorem forty_eight_degree_counterexample :
    PredictA 225 ∧ PredictB 320 ∧
    CircularError 225 272 48 ∧ CircularError 320 272 48 := by
  decide

/-- The closest points between A and B in the published intervals
    have circular angular distance 95 degrees. -/
theorem minimal_circular_gap_ge_95
    (a b : Int) (ha : PredictA a) (hb : PredictB b) :
    (95 ≤ b-a ∧ b-a ≤ 360-95) ∨
    (95 ≤ a-b ∧ a-b ≤ 360-95) := by
  unfold PredictA at ha
  unfold PredictB at hb
  omega

/-- A limiting pair attains the 95 degree separation. -/
theorem minimal_gap_attained :
    PredictA 225 ∧ PredictB 320 ∧ (320:Int)-225=95 := by
  decide

/-- If the true physical mechanism is outside the two published
    models, discriminating A from B alone DOES NOT identify it. -/
def FamilyCorrect (w : Fin 3) (a : Fin 3) : Prop := w=a
def OurTwoClassSensor (w : Fin 3) : Bool := w.val != 1

theorem an_unmodelled_rival_blocks_classification :
    ¬ INSACERMO.RefusEspoir.Safe FamilyCorrect OurTwoClassSensor := by
  apply INSACERMO.RefusEspoir.collision_forces_refusal
    FamilyCorrect OurTwoClassSensor (0 : Fin 3) (2 : Fin 3)
  · decide
  · intro a h
    have ha : (0 : Fin 3) = a := h.1
    have hb : (2 : Fin 3) = a := h.2
    have hneq : (0 : Fin 3) ≠ (2 : Fin 3) := by decide
    exact hneq (ha.trans hb.symm)

end INSACERMO.PublishedLeptogenesisDiscrimination
