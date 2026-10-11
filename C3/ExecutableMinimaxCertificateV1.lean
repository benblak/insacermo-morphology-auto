import C3.RecursiveTotalPlanKernelV1
import Std

/- INSACERMO executable FINITE audit. This does not prove the generic
   PlanValid predicate. Both witness and lower bound are independently
   recomputed by kernel reduction from a finite declared model. -/
namespace INSACERMO.TotalExecutable

open INSACERMO.RecursiveC3

abbrev St := Fin 4 × Bool
abbrev ActId := Fin 4
abbrev ProbeId := Fin 4

def states : List St :=
  [(0, false), (1, false), (2, false), (3, false),
   (0, true), (1, true), (2, true), (3, true)]

def initial : List St :=
  [(0, false), (1, false), (2, false), (3, false)]

def good (p : ActId) (s : St) : Bool :=
  s.2 && (p == s.1)

def sense (q : ProbeId) (s : St) (o : Bool) : Bool :=
  if q.val == 0 then o == (s.1.val % 2 == 1)
  else if q.val == 1 then o == (s.1.val / 2 == 1)
  else if q.val == 2 then !o
  else true

def step (q : ProbeId) (_o : Bool) (s : St) : St :=
  if q.val == 2 then (s.1, true) else s

def after (X : List St) (q : ProbeId) (o : Bool) : List St :=
  (X.filter (fun s => sense q s o)).map (step q o)

def direct (X : List St) : Bool :=
  (List.finRange 4).any
    (fun p => X.all (good p))

def canFinite : Nat → Nat → List St → Bool
  | 0, _, X => direct X
  | n+1, b, X =>
      direct X ||
      (b > 0 && (List.finRange 4).any (fun q =>
          (canFinite n (b-1) (after X q false)) &&
          (canFinite n (b-1) (after X q true))))

/-- A tree made of the same actions and outcomes as the Python emitter. -/
def emitted : Plan ActId ProbeId Bool :=
  .probe 0 (fun o =>
    .probe 1 (fun o2 =>
      .probe 2 (fun _ =>
        .act (if o then (if o2 then 3 else 1)
              else (if o2 then 2 else 0)))))


def checkTree : Nat → Nat → List St → Plan ActId ProbeId Bool → Bool
  | 0, _, X, .act p => X.all (good p)
  | 0, _, _, .probe _ _ => false
  | _+1, _, X, .act p => X.all (good p)
  | n+1, b, X, .probe q next =>
      b > 0 &&
      checkTree n (b-1) (after X q false) (next false) &&
      checkTree n (b-1) (after X q true) (next true)

/- Compare generated tree against independent interpreter. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
theorem emitted_tree_passes : checkTree 3 3 initial emitted = true := by
  decide +kernel

/-- Independent complete enumeration of *all* 4 probes, 4 terminal actions
    and both sensor outcomes for up to 3 observations and a budget of 2. -/
theorem budget_two_impossible : canFinite 3 2 initial = false := by
  decide +kernel

theorem budget_three_exists : canFinite 3 3 initial = true := by
  decide +kernel

theorem exact_finite_minimax :
    checkTree 3 3 initial emitted = true ∧
    canFinite 3 2 initial = false ∧
    canFinite 3 3 initial = true :=
  ⟨emitted_tree_passes, budget_two_impossible, budget_three_exists⟩


end INSACERMO.TotalExecutable
