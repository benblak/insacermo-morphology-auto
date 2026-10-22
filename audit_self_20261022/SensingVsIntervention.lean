import C3.PortableExactSearchV1

/-!
INSACERMO self-audit: why observation and intervention must be distinguished.

This module uses the historical PortableC3 verifier unchanged.  The
counterexamples were found by a complete finite enumeration in an external
Python lab, then transcribed to this independent Lean source.

There are three world states:
  world 0: action 0 is allowed;
  world 1: action 1 is allowed;
  world 2: no action is allowed.
Initial uncertainty is [0,1]. Depth=1, budget=1.

These are finite semantic counterexamples, not new laws of nature.
-/
namespace INSACERMO.SensingVsIntervention
open PortableC3

def baseGood : List (List Bool) :=
  [[true,false],[false,true],[false,false]]
def start : List Nat := [0,1]

-- A completely ambiguous observation: both outcomes permitted in every world.
def blindNoChange : Model := {
  worldCount := 3
  actionCount := 2
  probeCount := 1
  good := baseGood
  sense := [[3,3,3]]
  nextFalse := [[0,1,2]]
  nextTrue := [[0,1,2]]
  actionCost := [0,0]
  probeCost := [1]
}

-- Same observations and actions. The observation ALSO drives any world to 0.
def blindWithReset : Model := {
  worldCount := 3
  actionCount := 2
  probeCount := 1
  good := baseGood
  sense := [[3,3,3]]
  nextFalse := [[0,0,0]]
  nextTrue := [[0,0,0]]
  actionCost := [0,0]
  probeCost := [1]
}

-- Perfectly distinguishes initially possible worlds 0 and 1, without changing state.
def distinguishingNoChange : Model := {
  worldCount := 3
  actionCount := 2
  probeCount := 1
  good := baseGood
  sense := [[1,2,1]]
  nextFalse := [[0,1,2]]
  nextTrue := [[0,1,2]]
  actionCost := [0,0]
  probeCost := [1]
}

-- Exactly the same observation, but the true branch damages state 1 to state 2.
def distinguishingDamages : Model := {
  worldCount := 3
  actionCount := 2
  probeCount := 1
  good := baseGood
  sense := [[1,2,1]]
  nextFalse := [[0,0,0]]
  nextTrue := [[0,2,0]]
  actionCost := [0,0]
  probeCost := [1]
}

set_option maxRecDepth 8192
set_option maxHeartbeats 100000000

theorem all_models_well_formed :
  wellFormed blindNoChange start = true ∧
  wellFormed blindWithReset start = true ∧
  wellFormed distinguishingNoChange start = true ∧
  wellFormed distinguishingDamages start = true := by
  decide +kernel

-- Distinguishing observations alone would have no effect in this case.
theorem information_free_measurement_cannot_help :
    canFinite blindNoChange 1 1 start = false := by
  decide +kernel

-- An identical information channel becomes actionable by changing the state.
theorem information_free_intervention_can_help :
    canFinite blindWithReset 1 1 start = true := by
  decide +kernel

theorem information_free_intervention_is_a_verified_plan :
    checkTree blindWithReset 1 1 start
      (.probe 0 (.act 0) (.act 0)) = true := by
  decide +kernel

theorem information_free_intervention_safe :
    Safe blindWithReset 1 1 start (.probe 0 (.act 0) (.act 0)) :=
  accepted_certificate_sound _ _ _ _ _
    information_free_intervention_is_a_verified_plan

-- When the measurement does not change the state, its information is enough.
theorem informative_noninvasive_measurement_succeeds :
    canFinite distinguishingNoChange 1 1 start = true := by
  decide +kernel

theorem informative_noninvasive_tree_check :
    checkTree distinguishingNoChange 1 1 start
      (.probe 0 (.act 0) (.act 1)) = true := by
  decide +kernel

theorem informative_noninvasive_tree_safe :
    Safe distinguishingNoChange 1 1 start
      (.probe 0 (.act 0) (.act 1)) :=
  accepted_certificate_sound _ _ _ _ _
    informative_noninvasive_tree_check

-- Same informational discrimination; damaged world is not actionable.
theorem informative_destructive_measurement_fails :
    canFinite distinguishingDamages 1 1 start = false := by
  decide +kernel

-- This exclusion covers *all* policy trees at depth one and budget one.
theorem damaging_probe_precludes_every_safe_plan (t : Tree) :
    checkTree distinguishingDamages 1 1 start t = false :=
  impossible_budget_rejects_every_plan _ _ _ _
    informative_destructive_measurement_fails t

end INSACERMO.SensingVsIntervention
