import Lean

/-!
INSACERMO external laboratory, 2026-11-05.
This file certifies ONLY algebraic identifiability and integer interval arithmetic.
It does NOT certify physical sensor bounds or a particular pendulum geometry.
-/

namespace InsacermoEnergyLab

-- In the energy-balance equation, net observed work can be split
-- between unobserved dissipation and other external work.
def workBalance (net friction external : Int) : Prop :=
  net = friction + external

theorem arbitrary_friction_is_compatible (net friction : Int) :
    ∃ external : Int, workBalance net friction external := by
  refine ⟨net - friction, ?_⟩
  unfold workBalance
  omega

-- A strict energy loss admits two physically distinct sign-compatible
-- explanations: all dissipative versus all other external work.
theorem two_distinct_mechanisms_for_loss (net : Int) (hneg : net < 0) :
    ∃ frictionA externalA frictionB externalB : Int,
      workBalance net frictionA externalA ∧
      workBalance net frictionB externalB ∧
      frictionA ≤ 0 ∧ frictionB ≤ 0 ∧
      frictionA ≠ frictionB := by
  refine ⟨net, 0, 0, net, ?_, ?_, ?_, ?_, ?_⟩
  · simp [workBalance]
  · simp [workBalance]
  · omega
  · omega
  · omega

-- A whole finite series of energy changes does not remove this
-- ambiguity if external work remains unconstrained at every step.
theorem every_finite_energy_trace_has_any_drag_explanation
    (observed proposedDrag : List Int)
    (hlen : observed.length = proposedDrag.length) :
    ∃ external : List Int,
       observed = List.zipWith (· + ·) proposedDrag external := by
  induction observed generalizing proposedDrag with
  | nil =>
    cases proposedDrag with
    | nil => exact ⟨[], rfl⟩
    | cons _ _ => simp at hlen
  | cons v vs ih =>
    cases proposedDrag with
    | nil => simp at hlen
    | cons f fs =>
      have hlen' : vs.length = fs.length := by simpa using hlen
      obtain ⟨ext, hext⟩ := ih fs hlen'
      refine ⟨(v - f) :: ext, ?_⟩
      calc
        v :: vs = (f + (v - f)) :: vs := by
          congr 1
          omega
        _ = (f + (v - f)) :: List.zipWith (· + ·) fs ext := by rw [←hext]
        _ = List.zipWith (· + ·) (f :: fs) ((v - f) :: ext) := by rfl

-- Observed-data interval certificate, in integer micro-J/kg.
-- Hypotheses are externally computed numeric bounds, NOT
-- derived from original sensors or trigonometry inside Lean.
theorem measured_interval_forces_loss
    (before after : Int)
    (hbefore : 618785 ≤ before)
    (hafter : after ≤ 205000) :
    after + 413785 ≤ before := by
  omega

theorem energy_conservation_excluded_under_bounds
    (before after : Int)
    (hbefore : 618785 ≤ before)
    (hafter : after ≤ 205000) :
    before ≠ after := by
  have h := measured_interval_forces_loss before after hbefore hafter
  omega

end InsacermoEnergyLab

#print axioms InsacermoEnergyLab.arbitrary_friction_is_compatible
#print axioms InsacermoEnergyLab.two_distinct_mechanisms_for_loss
#print axioms InsacermoEnergyLab.every_finite_energy_trace_has_any_drag_explanation
#print axioms InsacermoEnergyLab.measured_interval_forces_loss
#print axioms InsacermoEnergyLab.energy_conservation_excluded_under_bounds
