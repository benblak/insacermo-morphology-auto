import Std

/-!
INSACERMO — Effective Semantic State Bound V1

Once raw worlds are replaced by n effective semantic classes, any finite belief
carried by an exact planner is a subset of those n classes.

Therefore the complete semantic belief universe contains exactly 2^n possible
beliefs. Any actually reachable belief family is a subfamily of that powerset,
so its cardinality is at most 2^n.

This is a semantic-state bound, not a wall-clock runtime theorem.
It does not claim every subset is reachable, nor that the solver must visit all
2^n beliefs.
-/

namespace InsacermoEffectiveStateBound

def BeliefUniverse {Q : Type} [DecidableEq Q]
    (worlds : Finset Q) : Finset (Finset Q) :=
  worlds.powerset

theorem belief_universe_card
    {Q : Type} [DecidableEq Q]
    (worlds : Finset Q) :
    (BeliefUniverse worlds).card = 2 ^ worlds.card := by
  simp [BeliefUniverse]

theorem reachable_beliefs_le_two_pow
    {Q : Type} [DecidableEq Q]
    (worlds : Finset Q)
    (reachable : Finset (Finset Q))
    (hsub : reachable ⊆ BeliefUniverse worlds) :
    reachable.card ≤ 2 ^ worlds.card := by
  have hcard : reachable.card ≤ (BeliefUniverse worlds).card :=
    Finset.card_le_card hsub
  simpa [belief_universe_card] using hcard

theorem depth_indexed_state_bound
    {Q : Type} [DecidableEq Q]
    (worlds : Finset Q)
    (reachable : Finset (Finset Q))
    (hsub : reachable ⊆ BeliefUniverse worlds)
    (depth : Nat) :
    reachable.card * (depth + 1) ≤
      (2 ^ worlds.card) * (depth + 1) := by
  exact Nat.mul_le_mul_right (depth + 1)
    (reachable_beliefs_le_two_pow worlds reachable hsub)

theorem raw_multiplicity_absent_after_quotient
    {Raw Q : Type} [DecidableEq Q]
    (raw : Finset Raw)
    (classes : Finset Q)
    (reachable : Finset (Finset Q))
    (hsub : reachable ⊆ BeliefUniverse classes) :
    reachable.card ≤ 2 ^ classes.card := by
  exact reachable_beliefs_le_two_pow classes reachable hsub

theorem memo_key_upper_bound
    {Q : Type} [DecidableEq Q]
    (classes : Finset Q)
    (memoBeliefs : Finset (Finset Q))
    (hsub : memoBeliefs ⊆ BeliefUniverse classes)
    (depth : Nat) :
    memoBeliefs.card * (depth + 1) ≤
      2 ^ classes.card * (depth + 1) := by
  exact depth_indexed_state_bound classes memoBeliefs hsub depth

#print axioms belief_universe_card
#print axioms reachable_beliefs_le_two_pow
#print axioms depth_indexed_state_bound
#print axioms raw_multiplicity_absent_after_quotient
#print axioms memo_key_upper_bound

end InsacermoEffectiveStateBound
