import Std

/-!
INSACERMO — HIGHER-ORDER ACTIONABILITY OBSTRUCTION V1

A finite declared world w : Fin n is compatible with action a : Fin n
exactly when w ≠ a. A declared belief is specified by the predicate present.

Result: every proper belief (one or more worlds missing) admits a
common certified action; the full belief admits none. In particular,
minimal actionability obstructions of arbitrary finite size exist.

This is a rigorous structural result in a declared deterministic model,
NOT a claim of a new theorem in all of mathematics and NOT a proof about
an arbitrary Python runtime or physical intervention.

No AI model, statistical training, learned parameters, sorry, admit,
custom axioms or oracle.
-/

namespace INSACERMO.HigherOrderObstruction

def permitted {n : Nat} (w a : Fin n) : Prop := w ≠ a

def canAct {n : Nat} (present : Fin n → Prop) : Prop :=
  ∃ a : Fin n, ∀ w : Fin n, present w → permitted w a

/-- If one world is absent from the belief, the corresponding action
    simultaneously works for all the remaining worlds. -/
theorem missing_world_gives_action {n : Nat}
    (present : Fin n → Prop)
    (missing : Fin n)
    (hAbsent : ¬ present missing) :
    canAct present := by
  refine ⟨missing, ?_⟩
  intro w hw hEq
  apply hAbsent
  simpa [hEq] using hw

/-- Entirely general proper-subbelief guarantee. -/
theorem every_proper_belief_acts {n : Nat}
    (present : Fin n → Prop)
    (hProper : ∃ missing : Fin n, ¬ present missing) :
    canAct present := by
  obtain ⟨missing, hm⟩ := hProper
  exact missing_world_gives_action present missing hm

/-- A full belief cannot choose even one action valid in every world:
    given a candidate action, the matching world invalidates it. -/
theorem full_belief_refuses (n : Nat) :
    ¬ canAct (fun _ : Fin n => True) := by
  intro h
  obtain ⟨a, hAll⟩ := h
  exact (hAll a True.intro) rfl

/-- Minimal obstruction of size n: removing ANY one world
    permits ACT, yet retaining all n worlds makes ACT impossible. -/
theorem arbitrary_order_minimal_obstruction (n : Nat) :
    (∀ missing : Fin n,
      canAct (fun w : Fin n => w ≠ missing))
    ∧ ¬ canAct (fun _ : Fin n => True) := by
  constructor
  · intro missing
    apply missing_world_gives_action
    intro h
    exact h rfl
  · exact full_belief_refuses n

/-- Exhaustive finite check that for all DISTINCT pairs of worlds,
    there exists a compatible action. This condition is insufficient
    for global ACT starting from three worlds. -/
def allPairsCompatible (n : Nat) : Bool :=
  (List.range n).all fun w =>
    (List.range n).all fun z =>
      if w == z then true
      else (List.range n).any (fun a => (w != a) && (z != a))

theorem every_pair_compatible_3 : allPairsCompatible 3 = true := by
  decide +kernel

theorem every_pair_compatible_4 : allPairsCompatible 4 = true := by
  decide +kernel

theorem every_pair_compatible_7 : allPairsCompatible 7 = true := by
  decide +kernel

theorem three_worlds_refuse_despite_pairwise_compatibility :
    allPairsCompatible 3 = true ∧
    ¬ canAct (fun _ : Fin 3 => True) :=
  ⟨every_pair_compatible_3, full_belief_refuses 3⟩

theorem eleven_worlds_have_a_minimal_order_eleven_obstruction :
    (∀ missing : Fin 11,
      canAct (fun w : Fin 11 => w ≠ missing))
    ∧ ¬ canAct (fun _ : Fin 11 => True) :=
  arbitrary_order_minimal_obstruction 11

end INSACERMO.HigherOrderObstruction
