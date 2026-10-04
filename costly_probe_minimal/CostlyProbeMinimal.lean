import Std

/-!
INSACERMO — minimal costly-probe witness.

The point is deliberately narrow:

* Free information cannot reduce guaranteed actionability, because it may be ignored.
* A probe that changes the action/capability relation can reduce guaranteed actionability
  even while preserving the number of locally feasible actions in every world.
* Under the stated assumptions, two worlds are insufficient for this phenomenon when
  a strict binary observation distinguishes them and every post-probe world retains an action.
* One action is also insufficient if every world retains that action.
* A concrete 3-world / 2-action witness exists.

No machine learning and no statistical approximation are involved.
-/

namespace InsacermoCostlyProbeMinimal

/-- If information is free and does not change feasibility, simply ignore it. -/
theorem free_information_cannot_hurt
    {W A O : Type}
    (feasible : W → A → Prop)
    (observe : W → O)
    (h : ∃ a : A, ∀ w : W, feasible w a) :
    ∃ policy : O → A, ∀ w : W, feasible w (policy (observe w)) := by
  rcases h with ⟨a, ha⟩
  exact ⟨fun _ => a, ha⟩

/-- With only one action, retaining one feasible action in every world prevents collapse. -/
theorem one_action_cannot_fail
    {W O : Type}
    (feasible : W → Unit → Prop)
    (observe : W → O)
    (hlocal : ∀ w : W, feasible w ()) :
    ∃ policy : O → Unit, ∀ w : W, feasible w (policy (observe w)) := by
  exact ⟨fun _ => (), hlocal⟩

/--
For two worlds and a binary observation, strict information is perfect information.
If every post-probe world still has at least one feasible action, a contingent policy exists.
-/
theorem two_worlds_strict_information_cannot_fail
    {A : Type}
    (feasible : Bool → A → Prop)
    (observe : Bool → Bool)
    (hinfo : observe false ≠ observe true)
    (h0 : ∃ a : A, feasible false a)
    (h1 : ∃ a : A, feasible true a) :
    ∃ policy : Bool → A, ∀ w : Bool, feasible w (policy (observe w)) := by
  rcases h0 with ⟨a0, ha0⟩
  rcases h1 with ⟨a1, ha1⟩
  let policy : Bool → A := fun z => if z = observe false then a0 else a1
  refine ⟨policy, ?_⟩
  intro w
  cases w with
  | false =>
      simpa [policy] using ha0
  | true =>
      have hn : observe true ≠ observe false := Ne.symm hinfo
      simpa [policy, hn] using ha1

abbrev World := Fin 3
abbrev Action := Bool
abbrev Observation := Bool

/-- Before probing, action false is feasible in all three worlds. -/
def beforeFeasible (_w : World) (a : Action) : Prop :=
  a = false

/--
After probing, every world still has exactly one feasible action.
Worlds 0 and 1 keep action false; world 2 requires action true.
-/
def afterFeasible (w : World) (a : Action) : Prop :=
  if w.val = 2 then a = true else a = false

/--
The probe is informative but incomplete:
world 1 is separated, while worlds 0 and 2 remain observationally merged.
-/
def probeObservation (w : World) : Observation :=
  w.val == 1

theorem before_is_actionable :
    ∃ a : Action, ∀ w : World, beforeFeasible w a := by
  exact ⟨false, by intro w; rfl⟩

theorem probe_is_strictly_informative :
    probeObservation (0 : World) ≠ probeObservation (1 : World) ∧
    probeObservation (0 : World) = probeObservation (2 : World) := by
  decide

/--
No local capability count is lost: before and after the probe,
every world has exactly one feasible action.
-/
theorem local_capacity_is_preserved :
    ∀ w : World,
      (∃ a : Action, beforeFeasible w a ∧ ∀ b : Action, beforeFeasible w b → b = a) ∧
      (∃ a : Action, afterFeasible w a ∧ ∀ b : Action, afterFeasible w b → b = a) := by
  intro w
  constructor
  · refine ⟨false, rfl, ?_⟩
    intro y hy
    exact hy
  · by_cases h : w.val = 2
    · refine ⟨true, by simp [afterFeasible, h], ?_⟩
      intro y hy
      simpa [afterFeasible, h] using hy
    · refine ⟨false, by simp [afterFeasible, h], ?_⟩
      intro y hy
      simpa [afterFeasible, h] using hy

/--
Despite the information gain and preservation of local action count,
there is no observation-contingent policy that guarantees feasibility in every world.
-/
theorem after_probe_not_guaranteed :
    ¬ ∃ policy : Observation → Action,
        ∀ w : World, afterFeasible w (policy (probeObservation w)) := by
  intro h
  rcases h with ⟨policy, hp⟩
  have h0 := hp (0 : World)
  have h2 := hp (2 : World)
  have ha : policy false = false := by
    simpa [afterFeasible, probeObservation] using h0
  have hb : policy false = true := by
    simpa [afterFeasible, probeObservation] using h2
  simp [ha] at hb

theorem minimal_costly_probe_witness :
    (∃ a : Action, ∀ w : World, beforeFeasible w a) ∧
    (probeObservation (0 : World) ≠ probeObservation (1 : World)) ∧
    (∀ w : World,
      (∃ a : Action, beforeFeasible w a ∧ ∀ b : Action, beforeFeasible w b → b = a) ∧
      (∃ a : Action, afterFeasible w a ∧ ∀ b : Action, afterFeasible w b → b = a)) ∧
    ¬ ∃ policy : Observation → Action,
        ∀ w : World, afterFeasible w (policy (probeObservation w)) := by
  exact ⟨before_is_actionable,
    probe_is_strictly_informative.1,
    local_capacity_is_preserved,
    after_probe_not_guaranteed⟩

#print axioms free_information_cannot_hurt
#print axioms one_action_cannot_fail
#print axioms two_worlds_strict_information_cannot_fail
#print axioms before_is_actionable
#print axioms probe_is_strictly_informative
#print axioms local_capacity_is_preserved
#print axioms after_probe_not_guaranteed
#print axioms minimal_costly_probe_witness

end InsacermoCostlyProbeMinimal
