import Std
import costly_probe_minimal.CostlyProbeMinimal

/-!
INSACERMO — Safe Probe Theorem V1

General characterization of when an observation/probe preserves guaranteed actionability.

A probe is safe iff, for every observation value that can occur, all worlds in that
observation fiber share at least one post-probe feasible action.

This theorem is purely extensional and finite/infinite agnostic: no cardinality assumptions,
no machine learning, no optimization oracle.
-/

namespace InsacermoSafeProbe

/-- There exists an observation-contingent policy that is feasible in every world. -/
def SafeProbe {W A O : Type}
    (feasible : W → A → Prop)
    (observe : W → O) : Prop :=
  ∃ policy : O → A, ∀ w : W, feasible w (policy (observe w))

/-- Every nonempty observation fiber has at least one action shared by all worlds in that fiber. -/
def FiberCommonAction {W A O : Type}
    (feasible : W → A → Prop)
    (observe : W → O) : Prop :=
  ∀ o : O, (∃ w : W, observe w = o) →
    ∃ a : A, ∀ w : W, observe w = o → feasible w a

/--
Main theorem: a probe is safe exactly when each observable fiber has a common action.
-/
theorem safe_probe_iff_fiber_common_action
    {W A O : Type}
    (feasible : W → A → Prop)
    (observe : W → O) :
    SafeProbe feasible observe ↔ FiberCommonAction feasible observe := by
  constructor
  · rintro ⟨policy, hp⟩
    intro o ho
    refine ⟨policy o, ?_⟩
    intro w hw
    simpa [hw] using hp w
  · intro hf
    classical
    choose witness hWitness using fun o : O =>
      Classical.propComplete (∃ w : W, observe w = o)
    let policy : O → A := fun o =>
      if ho : ∃ w : W, observe w = o then
        Classical.choose (hf o ho)
      else
        Classical.choice (show Nonempty A from ?_)
    · refine ⟨policy, ?_⟩
      intro w
      have ho : ∃ u : W, observe u = observe w := ⟨w, rfl⟩
      simp only [policy, dif_pos ho]
      exact Classical.choose_spec (hf (observe w) ho) w rfl
    · rcases hf (observe w) ⟨w, rfl⟩ with ⟨a, _⟩
      exact ⟨a⟩

/--
Equivalent failure criterion: a probe is unsafe iff no contingent policy works.
This exposes the obstruction as an observation fiber with no common feasible action.
-/
theorem unsafe_of_bad_fiber
    {W A O : Type}
    (feasible : W → A → Prop)
    (observe : W → O)
    (o : O)
    (hoccurs : ∃ w : W, observe w = o)
    (hbad : ¬ ∃ a : A, ∀ w : W, observe w = o → feasible w a) :
    ¬ SafeProbe feasible observe := by
  intro hs
  have hf := (safe_probe_iff_fiber_common_action feasible observe).mp hs
  exact hbad (hf o hoccurs)

/-- Free information is safe whenever one action was globally feasible already. -/
theorem free_information_safe
    {W A O : Type}
    (feasible : W → A → Prop)
    (observe : W → O)
    (hglobal : ∃ a : A, ∀ w : W, feasible w a) :
    SafeProbe feasible observe := by
  rcases hglobal with ⟨a, ha⟩
  exact ⟨fun _ => a, ha⟩

/-- The 3×2 witness from V1 is unsafe because the false-observation fiber has no common action. -/
theorem minimal_witness_exhibits_bad_fiber :
    ¬ FiberCommonAction
      InsacermoCostlyProbeMinimal.afterFeasible
      InsacermoCostlyProbeMinimal.probeObservation := by
  intro hf
  have hocc :
      ∃ w : InsacermoCostlyProbeMinimal.World,
        InsacermoCostlyProbeMinimal.probeObservation w = false := by
    exact ⟨(0 : InsacermoCostlyProbeMinimal.World), by decide⟩
  rcases hf false hocc with ⟨a, ha⟩
  have h0 := ha (0 : InsacermoCostlyProbeMinimal.World) (by decide)
  have h2 := ha (2 : InsacermoCostlyProbeMinimal.World) (by decide)
  have ha0 : a = false := by
    simpa [InsacermoCostlyProbeMinimal.afterFeasible] using h0
  have ha1 : a = true := by
    simpa [InsacermoCostlyProbeMinimal.afterFeasible] using h2
  simp [ha0] at ha1

theorem minimal_witness_unsafe_by_general_theorem :
    ¬ SafeProbe
      InsacermoCostlyProbeMinimal.afterFeasible
      InsacermoCostlyProbeMinimal.probeObservation := by
  intro hs
  exact minimal_witness_exhibits_bad_fiber
    ((safe_probe_iff_fiber_common_action
      InsacermoCostlyProbeMinimal.afterFeasible
      InsacermoCostlyProbeMinimal.probeObservation).mp hs)

#print axioms safe_probe_iff_fiber_common_action
#print axioms unsafe_of_bad_fiber
#print axioms free_information_safe
#print axioms minimal_witness_exhibits_bad_fiber
#print axioms minimal_witness_unsafe_by_general_theorem

end InsacermoSafeProbe
