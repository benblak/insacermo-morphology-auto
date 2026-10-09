import RuntimeVerdictProjectionCheckerV1
namespace INSACERMO.GeneratedRuntimeVerdicts
open INSACERMO.RuntimeVerdictProjection
def case_ACT : FiniteCase := {
  valid := true
  good := [[true], [true]]
  probes := []
  repairs := []
  depth := 1
}
def claimed_ACT : Verdict := Verdict.act
theorem from_frozen_runtime_act :
    computed case_ACT = claimed_ACT := by decide +kernel
def case_PROBE : FiniteCase := {
  valid := true
  good := [[true, false], [false, true]]
  probes := [[0, 1]]
  repairs := []
  depth := 1
}
def claimed_PROBE : Verdict := Verdict.probe
theorem from_frozen_runtime_probe :
    computed case_PROBE = claimed_PROBE := by decide +kernel
def case_REPAIR : FiniteCase := {
  valid := true
  good := [[true, false], [false, true]]
  probes := []
  repairs := [[true, true]]
  depth := 1
}
def claimed_REPAIR : Verdict := Verdict.repair
theorem from_frozen_runtime_repair :
    computed case_REPAIR = claimed_REPAIR := by decide +kernel
def case_REFUSE : FiniteCase := {
  valid := true
  good := [[true, false], [false, true]]
  probes := []
  repairs := []
  depth := 1
}
def claimed_REFUSE : Verdict := Verdict.refuse
theorem from_frozen_runtime_refuse :
    computed case_REFUSE = claimed_REFUSE := by decide +kernel
def case_OUTSIDE_ENVELOPE : FiniteCase := {
  valid := false
  good := [[true], [true]]
  probes := []
  repairs := []
  depth := 1
}
def claimed_OUTSIDE_ENVELOPE : Verdict := Verdict.refuse
theorem from_frozen_runtime_outside_envelope :
    computed case_OUTSIDE_ENVELOPE = claimed_OUTSIDE_ENVELOPE := by decide +kernel
theorem forged_refuse_for_act_rejected : computed case_ACT != Verdict.refuse := by decide +kernel
theorem forged_act_for_probe_rejected : computed case_PROBE != Verdict.act := by decide +kernel
theorem forged_probe_for_repair_rejected : computed case_REPAIR != Verdict.probe := by decide +kernel
theorem forged_act_for_refuse_rejected : computed case_REFUSE != Verdict.act := by decide +kernel
theorem invalid_envelope_blocks_act : computed case_OUTSIDE_ENVELOPE = Verdict.refuse := by decide +kernel
end INSACERMO.GeneratedRuntimeVerdicts
