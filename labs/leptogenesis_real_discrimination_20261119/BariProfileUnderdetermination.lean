import Lean

/-!
INSACERMO / Bari 2026.a : finite-knot non-uniqueness.
Published NO 1,2,3 sigma endpoints correspond to delta chi2 1,4,9.
Two constructed piecewise-linear profiles have identical reported
boundary knots, but DIFFERENT intermediate chi2 at 320 degrees.
Full 0.1-degree profiles are independently checked in Python.
This theorem does NOT certify Bari's unpublished likelihood data.
The original C3 and all older Lean results remain unchanged.
-/
namespace INSACERMO.BariProfileUnderdetermination

-- Angle in 0.1-degree units, and delta chi2 in unit increments.
def profile5 : List (Int × Int) :=
  [(0,20),(1422,9),(1656,4),(1890,1),(2142,0),
   (2412,1),(2970,4),(3200,5),(3510,9),(3600,20)]

def profile8 : List (Int × Int) :=
  [(0,20),(1422,9),(1656,4),(1890,1),(2142,0),
   (2412,1),(2970,4),(3200,8),(3510,9),(3600,20)]

def ReportedKnots (p : List (Int × Int)) : Prop :=
  (0,20) ∈ p ∧ (1422,9) ∈ p ∧ (1656,4) ∈ p ∧
  (1890,1) ∈ p ∧ (2142,0) ∈ p ∧ (2412,1) ∈ p ∧
  (2970,4) ∈ p ∧ (3510,9) ∈ p ∧ (3600,20) ∈ p

theorem both_witnesses_match_reported_knots :
    ReportedKnots profile5 ∧ ReportedKnots profile8 := by
  unfold ReportedKnots profile5 profile8
  decide

theorem values_at_B_high_start_are_distinct :
    (3200,5) ∈ profile5 ∧ (3200,8) ∈ profile8 ∧
    (3200,8) ∉ profile5 ∧ (3200,5) ∉ profile8 := by
  unfold profile5 profile8
  decide

theorem both_candidates_inside_same_published_bracket :
    4 < (5 : Int) ∧ (5 : Int) < 9 ∧
    4 < (8 : Int) ∧ (8 : Int) < 9 := by omega

theorem no_unique_integer_value_from_just_the_bracket :
    ¬ ∃ t : Int, ∀ v : Int, 4 < v → v < 9 → v = t := by
  intro h
  obtain ⟨t, ht⟩ := h
  have h5 : (5 : Int) = t := ht 5 (by omega) (by omega)
  have h8 : (8 : Int) = t := ht 8 (by omega) (by omega)
  omega

end INSACERMO.BariProfileUnderdetermination
