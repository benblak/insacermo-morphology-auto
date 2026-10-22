import C3.PortableExactSearchV1

/-!
INSACERMO self-criticism laboratory.
The original C3/Portable* libraries remain untouched.

One world, one safe action, zero sensors.  The policy checker and its
soundness theorem accept an immediate action, and exhaustive feasibility
accepts it, yet the input wellFormed gate rejects the very same model.
Providing an unused artificial probe makes wellFormed accept it.

This establishes a mismatch for the zero-probe corner case, not a failure
of the theorem checkTree_iff_safe nor of physically grounded decisions.
-/
namespace InsacermoSelfAudit
open PortableC3

def sensorless : Model := {
  worldCount := 1
  actionCount := 1
  probeCount := 0
  good := [[true]]
  sense := []
  nextFalse := []
  nextTrue := []
  actionCost := [0]
  probeCost := []
}

def phantomSensor : Model := {
  worldCount := 1
  actionCount := 1
  probeCount := 1
  good := [[true]]
  sense := [[3]]
  nextFalse := [[0]]
  nextTrue := [[0]]
  actionCost := [0]
  probeCost := [0]
}

theorem safe_act_without_any_sensor :
    checkTree sensorless 0 0 [0] (.act 0) = true := by
  decide +kernel

theorem sound_act_without_any_sensor :
    Safe sensorless 0 0 [0] (.act 0) :=
  accepted_certificate_sound sensorless 0 0 [0] (.act 0)
    safe_act_without_any_sensor

theorem feasible_without_any_sensor :
    canFinite sensorless 0 0 [0] = true := by
  decide +kernel

theorem original_input_gate_rejects_sensorless :
    wellFormed sensorless [0] = false := by
  decide +kernel

theorem artificial_sensor_passes_gate :
    wellFormed phantomSensor [0] = true := by
  decide +kernel

theorem action_still_identical :
    checkTree phantomSensor 0 0 [0] (.act 0) = true := by
  decide +kernel

end InsacermoSelfAudit
