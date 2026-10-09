import Std

/-!
INSACERMO MAX: finite, exact, non-ML operator synthesis certificate.

Exactly one failed critical edge among 4, or OTHER (index 4).
Every probe is a nonempty OR over critical edge status, cost 1.
Each repair fixes exactly one critical edge, cost 2.
All observations are perfect. ACT iff all possible critical failed
edges have been repaired. A finite budget is an upper bound on *every*
branch's total probe/repair cost.

This is the precise "pooled probe + unit repair" 5-world model from
the frozen V1.5 Python experiment. It is NOT a proof about all
possible scientific operators or the full INSACERMO runtime.
-/
namespace INSACERMO.MaxExact

def faulty (world : Nat) (repairMask : Nat) : Bool :=
  world < 4 && !(repairMask.testBit world)

def safe (belief repairMask : Nat) : Bool :=
  (List.range 4).all (fun w => !((belief.testBit w) && faulty w repairMask))

def downBranch (belief repairMask probeMask : Nat) : Nat :=
  (List.range 4).foldl (fun acc w =>
    if belief.testBit w && faulty w repairMask && probeMask.testBit w
    then acc + 2^w else acc) 0

def allBelief : Nat := 31

/-- Exhaustive feasibility recursion, exact under the stated
    grammar. Every recursive call has strictly less remaining cost.
    REPAIR is only an individual 2-unit operation.
    No trained parameters or search heuristic are involved. -/
def feasible : Nat → Nat → Nat → Bool
  | 0, belief, repairs => safe belief repairs
  | budget + 1, belief, repairs =>
    if safe belief repairs then true
    else
      let probes := (List.range 15).any (fun i =>
        let mask := i+1
        let yes := downBranch belief repairs mask
        let no := belief - yes
        yes != 0 && no != 0 &&
          feasible budget yes repairs &&
          feasible budget no repairs)
      let fixes :=
        match budget with
        | 0 => false
        | previous + 1 =>
          (List.range 4).any (fun i =>
            let mask := 2^i
            (belief.testBit i) && !(repairs.testBit i) &&
              feasible previous belief (repairs + mask))
      probes || fixes
termination_by budget => budget

/-- The exact optimum worst-case cost is at most four abstract units. -/
theorem four_suffices : feasible 4 allBelief 0 = true := by
  decide +kernel

/-- There is no guaranteed policy costing at most three units. -/
theorem three_insufficient : feasible 3 allBelief 0 = false := by
  decide +kernel

theorem exact_minimax_cost_four :
    feasible 4 allBelief 0 = true ∧ feasible 3 allBelief 0 = false :=
  ⟨four_suffices, three_insufficient⟩

end INSACERMO.MaxExact
