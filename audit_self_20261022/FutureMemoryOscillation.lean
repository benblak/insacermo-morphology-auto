import C3.PortableExactSearchV1

/-!
INSACERMO laboratory: an exact-future-horizon contract need not stay
monotone as the system moves. Old C3/Portable* files are unchanged.

These examples concern finite declared deterministic transitions, not
a proof of a novel law of physical time.  A probe is used only as the
existing C3 transition interface; observations are maximally
uninformative and both branches have identical transitions.
-/
namespace INSACERMO.FutureMemory
open PortableC3

def start : List Nat := [0, 1]

def canLoseAndRegain : Model := {
  worldCount := 3
  actionCount := 2
  probeCount := 1
  good := [[true, false], [true, false], [false, false]]
  sense := [[3, 3, 3]]
  nextFalse := [[0, 2, 0]]
  nextTrue := [[0, 2, 0]]
  actionCost := [0, 0]
  probeCost := [0]
}

def canGainAndLose : Model := {
  worldCount := 3
  actionCount := 2
  probeCount := 1
  good := [[true, false], [false, false], [true, false]]
  sense := [[3, 3, 3]]
  nextFalse := [[0, 2, 1]]
  nextTrue := [[0, 2, 1]]
  actionCost := [0, 0]
  probeCost := [0]
}

def tick (m : Model) (X : List Nat) : List Nat := after m X 0 false
def terminalCanAct (m : Model) (X : List Nat) : Bool := direct m 0 X

set_option maxRecDepth 8192
set_option maxHeartbeats 100000000

theorem both_models_well_formed :
    wellFormed canLoseAndRegain start = true ∧
    wellFormed canGainAndLose start = true := by
  decide +kernel

theorem lose_and_regain_exact_horizon :
    terminalCanAct canLoseAndRegain start = true ∧
    terminalCanAct canLoseAndRegain (tick canLoseAndRegain start) = false ∧
    terminalCanAct canLoseAndRegain
      (tick canLoseAndRegain (tick canLoseAndRegain start)) = true := by
  decide +kernel

theorem gain_and_lose_exact_horizon :
    terminalCanAct canGainAndLose start = false ∧
    terminalCanAct canGainAndLose (tick canGainAndLose start) = true ∧
    terminalCanAct canGainAndLose
      (tick canGainAndLose (tick canGainAndLose start)) = false := by
  decide +kernel

theorem two_period_state_uncertainty :
    tick canGainAndLose start = [0, 2] ∧
    tick canGainAndLose [0, 2] = start := by
  decide +kernel

def assignments (width alphabet : Nat) : List (List Nat) :=
  (List.range width).foldl
    (fun acc _ => acc.flatMap (fun xs =>
      (List.range alphabet).map (fun v => xs ++ [v]))) [[]]

def maskRow (v : Nat) : List Bool :=
  [v == 1 || v == 3, v == 2 || v == 3]

def constructedModel (n : Nat) (transition masks : List Nat) : Model := {
  worldCount := n
  actionCount := 2
  probeCount := 1
  good := masks.map maskRow
  sense := [List.replicate n 3]
  nextFalse := [transition]
  nextTrue := [transition]
  actionCost := [0, 0]
  probeCost := [0]
}

def profile (m : Model) : Bool × Bool × Bool :=
  (direct m 0 start,
   direct m 0 (tick m start),
   direct m 0 (tick m (tick m start)))

def patternCount (n : Nat) (wanted : Bool × Bool × Bool) : Nat :=
  ((assignments n n).flatMap (fun transition =>
    (assignments n 4).map (fun masks =>
      profile (constructedModel n transition masks) == wanted))).count true

theorem no_three_step_reversal_with_two_worlds :
    patternCount 2 (true, false, true) = 0 ∧
    patternCount 2 (false, true, false) = 0 := by
  decide +kernel

theorem exhaustive_three_world_counts :
    patternCount 3 (true, false, true) = 70 ∧
    patternCount 3 (false, true, false) = 64 := by
  decide +kernel

end INSACERMO.FutureMemory
