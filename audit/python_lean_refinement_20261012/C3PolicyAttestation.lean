-- INSACERMO C3: external verified receipt boundary.
-- This file does not modify C3 or interpret arbitrary Python source.
import C3.PortableExactSearchV1

namespace PortableC3

/-- Read-only policy list obtained from the contract's declared Must/May grammar. -/
def allActionsAllowed (allowed : List Nat) : Tree → Bool
  | .act a => allowed.contains a
  | .probe _ no yes =>
      allActionsAllowed allowed no && allActionsAllowed allowed yes

/-- Declarative property: every terminal action of a conditional plan belongs
    to the contract's declared policy universe, including empty branches. -/
def PolicyTree (allowed : List Nat) : Tree → Prop
  | .act a => a ∈ allowed
  | .probe _ no yes => PolicyTree allowed no ∧ PolicyTree allowed yes

theorem allActionsAllowed_sound (allowed : List Nat) (t : Tree)
    (h : allActionsAllowed allowed t = true) : PolicyTree allowed t := by
  induction t with
  | act a =>
      simpa [allActionsAllowed, PolicyTree] using h
  | probe q no yes ihNo ihYes =>
      simp only [allActionsAllowed, Bool.and_eq_true] at h
      exact ⟨ihNo h.1, ihYes h.2⟩

/-- An independent *verifier*, not the Python solver: certificate acceptance
    requires Lean semantics AND a syntactic policy-universe check. -/
def attestPolicyTree (m : Model) (allowed : List Nat) (depth budget : Nat)
    (worlds : List Nat) (t : Tree) : Bool :=
  checkTree m depth budget worlds t && allActionsAllowed allowed t

/-- Generic proof for ALL finite models, all budgets, all policy trees:
    an accepted serialized witness is safe and uses only allowed actions. -/
theorem attested_tree_sound_and_authorized
    (m : Model) (allowed : List Nat) (depth budget : Nat)
    (worlds : List Nat) (t : Tree)
    (h : attestPolicyTree m allowed depth budget worlds t = true) :
    Safe m depth budget worlds t ∧ PolicyTree allowed t := by
  have ⟨hc, hp⟩ : checkTree m depth budget worlds t = true ∧ allActionsAllowed allowed t = true := by
    simpa only [attestPolicyTree, Bool.and_eq_true] using h
  exact ⟨accepted_certificate_sound m depth budget worlds t hc,
         allActionsAllowed_sound allowed t hp⟩

/-- A verdict denying an admissible plan can be justified using the exhaustive
    finite search theorem, not by trusting Python's word for impossibility. -/
theorem rejected_search_blocks_all_policy_trees
    (m : Model) (allowed : List Nat) (depth budget : Nat)
    (worlds : List Nat)
    (h : canFinite m depth budget worlds = false)
    (t : Tree) :
    attestPolicyTree m allowed depth budget worlds t = false := by
  cases ht : attestPolicyTree m allowed depth budget worlds t with
  | false => rfl
  | true =>
    have hs := (attested_tree_sound_and_authorized m allowed depth budget worlds t ht).1
    have hc : checkTree m depth budget worlds t = true :=
      (checkTree_iff_safe m depth budget worlds t).mpr hs
    have impossible : checkTree m depth budget worlds t = false :=
      impossible_budget_rejects_every_plan m depth budget worlds h t
    simp [impossible] at hc

/-- Demonstrates that masks alone cannot certify a forbidden terminal action
    on an unreachable empty branch; explicit policy checking is necessary. -/
def emptyExample : Model := {
  worldCount := 1, actionCount := 2, probeCount := 1,
  good := [[true, false]], sense := [[1]],
  nextFalse := [[0]], nextTrue := [[0]],
  actionCost := [0, 0], probeCost := [0]
}

theorem empty_branch_refuses_forbidden_action :
    attestPolicyTree emptyExample [0] 0 0 [] (.act 1) = false := by decide

#print axioms PortableC3.allActionsAllowed_sound
#print axioms PortableC3.attested_tree_sound_and_authorized
#print axioms PortableC3.rejected_search_blocks_all_policy_trees
#print axioms PortableC3.empty_branch_refuses_forbidden_action

end PortableC3
