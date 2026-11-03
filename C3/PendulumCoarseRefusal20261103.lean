import C3.PortableExactSearchV1

namespace PortableC3.PendulumCoarseRefusal

/- Public experimental pendulum periods compressed to two fitted candidate laws.
   Declared error bound 15ms, NOT a certified physical tolerance.
   Both threshold probes admit both outcomes in both possible worlds. -/
def model : PortableC3.Model := {
  worldCount := 2
  actionCount := 2
  probeCount := 2
  good := [[true, false], [false, true]]
  sense := [[3, 3], [3, 3]]
  nextFalse := [[0, 1], [0, 1]]
  nextTrue := [[0, 1], [0, 1]]
  actionCost := [0, 0]
  probeCost := [1, 1]
}

def start : List Nat := [0, 1]
def depth : Nat := 4
set_option maxRecDepth 8192
set_option maxHeartbeats 25000000

theorem model_valid : PortableC3.wellFormed model start = true := by decide +kernel

theorem no_unique_identification_at_budget_five :
    PortableC3.canFinite model depth 5 start = false := by decide +kernel

theorem no_unique_identification_at_any_budget_le_five
    (b : Nat) (hb : b ≤ 5) :
    PortableC3.canFinite model depth b start = false :=
  PortableC3.one_infeasible_budget_excludes_all_cheaper
    model depth 5 start no_unique_identification_at_budget_five b hb

theorem any_candidate_tree_rejected (b : Nat) (hb : b ≤ 5)
    (t : PortableC3.Tree) :
    PortableC3.checkTree model depth b start t = false :=
  PortableC3.impossible_budget_rejects_every_plan
    model depth b start (no_unique_identification_at_any_budget_le_five b hb) t

#print axioms no_unique_identification_at_budget_five
#print axioms any_candidate_tree_rejected
end PortableC3.PendulumCoarseRefusal
