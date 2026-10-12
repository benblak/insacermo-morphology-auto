-- INSACERMO external numerical audit, 2026-10-12.
-- Recompute all reserves from the 4 physical routes. No axiom/sorry/admit.
import Init

set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace InsacermoFuturs

def admissibleMasks (unlockedRoutes : List Nat) : List Nat :=
  (List.range 32).filter (fun failure =>
    unlockedRoutes.any (fun route => Nat.land failure route == 0))

def step (masks weights : List Nat) : List Nat :=
  masks.map (fun current =>
    (masks.zip weights).foldl (fun total pair =>
      if Nat.land current pair.1 == 0 then total + pair.2 else total) 0)

def countHistories (routes : List Nat) (h : Nat) : Nat :=
  let masks := admissibleMasks routes
  let first := masks.map (fun _ => 1)
  let last := (List.range (h - 1)).foldl (fun weights _ => step masks weights) first
  last.foldl (· + ·) 0

-- 5-link network, with S→T path masks 9,18,21,14.
def discoveryStage1 : List Nat := [9,21]
def discoveryStage2 : List Nat := [9,21,14]
def preserveStage1 : List Nat := [9,18]
def preserveStage2 : List Nat := [9,18,21]

def discoveryReserve4 : Nat :=
  countHistories discoveryStage1 4 + countHistories discoveryStage2 4
def preserveReserve4 : Nat :=
  countHistories preserveStage1 4 + countHistories preserveStage2 4
def discoveryReserve12 : Nat :=
  countHistories discoveryStage1 12 + countHistories discoveryStage2 12
def preserveReserve12 : Nat :=
  countHistories preserveStage1 12 + countHistories preserveStage2 12

theorem discovery_h4 : discoveryReserve4 = 6742 := by decide
theorem preserve_h4 : preserveReserve4 = 16503 := by decide
theorem discovery_h12 : discoveryReserve12 = 59159887786 := by decide
theorem preserve_h12 : preserveReserve12 = 472801220590 := by decide

theorem concrete_conflict : discoveryReserve4 < preserveReserve4 := by
  rw [discovery_h4, preserve_h4]
  decide

theorem threshold_10000 :
    discoveryReserve4 < 10000 ∧ 10000 ≤ preserveReserve4 := by
  rw [discovery_h4, preserve_h4]
  decide

def allSixReserves4 : List Nat := [
  countHistories [9,21] 4 + countHistories [9,21,14] 4,
  countHistories [9,14] 4 + countHistories [9,14,21] 4,
  countHistories [9,21] 4 + countHistories [9,21,18] 4,
  countHistories [9,14] 4 + countHistories [9,14,18] 4,
  countHistories [9,18] 4 + countHistories [9,18,21] 4,
  countHistories [9,18] 4 + countHistories [9,18,14] 4
]

theorem all_six_reserves :
    allSixReserves4 = [6742,6742,10855,10855,16503,16503] := by decide

theorem impossible_threshold_20000 :
    allSixReserves4.all (fun x => x < 20000) = true := by
  rw [all_six_reserves]
  decide

-- These scores are outputs of the frozen Discovery Planner, NOT Lean-derived.
def plannerScores : List Nat := [7,7,6,6,6,6]
theorem no_order_maximizes_both :
    (plannerScores.zip allSixReserves4).all
      (fun p => !(p.1 == 7 && p.2 == 16503)) = true := by
  rw [all_six_reserves]
  decide

#print axioms InsacermoFuturs.discovery_h4
#print axioms InsacermoFuturs.preserve_h4
#print axioms InsacermoFuturs.discovery_h12
#print axioms InsacermoFuturs.preserve_h12
#print axioms InsacermoFuturs.no_order_maximizes_both

end InsacermoFuturs
