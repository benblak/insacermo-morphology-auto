import FiniteDecisionCertificateCheckerV2
import MaxExactOperatorOptimumV1

namespace INSACERMO.EmittedOpenFlightsV2
open INSACERMO.FiniteCertV2

def sourcePayloadSha256 : String := "6207c4fb2e1b26f1d29e177ca2cf406d2b77076ea2a42598efd02fb181115524"
def historicalDatasetSha256 : String := "bd373706238134f619c624c606dccc74c05c2582a977c489c81de501735f2390"

def allowed : List Operator := [
  ⟨0,1,1⟩,⟨0,2,1⟩,⟨0,3,1⟩,⟨0,4,1⟩,⟨0,5,1⟩,⟨0,6,1⟩,⟨0,7,1⟩,
  ⟨0,8,1⟩,⟨0,9,1⟩,⟨0,10,1⟩,⟨0,11,1⟩,⟨0,12,1⟩,⟨0,13,1⟩,⟨0,14,1⟩,⟨0,15,1⟩,
  ⟨1,1,2⟩,⟨1,2,2⟩,⟨1,4,2⟩,⟨1,8,2⟩
]

def plan : Policy :=
  .probe 3 1
    (.probe 1 1 (.repair 1 2 .act) (.repair 2 2 .act))
    (.probe 4 1 (.repair 4 2 .act) (.repair 8 2 .act))

def contract : Contract := ⟨5,4,5,0,true,"REACHABILITY_ONE_OUTAGE"⟩
def exhaustedReserve : Contract := ⟨5,4,4,0,true,"REACHABILITY_ONE_OUTAGE"⟩
def debtAtLimit : Contract := ⟨5,4,5,1,true,"REACHABILITY_ONE_OUTAGE"⟩
def invalidEnvelope : Contract := ⟨5,4,5,0,false,"REACHABILITY_ONE_OUTAGE"⟩

def forgedProbePrice : Policy :=
  match plan with
  | .probe mask _ yes no => .probe mask 99 yes no
  | x => x
def forgedRepair : Policy := .repair 16 2 plan

theorem emitted_grammar_matches_full_reference : allowed = referenceGrammar := by decide +kernel
theorem emitted_plan_valid_and_strictly_funded : accepts contract allowed plan = true := by decide +kernel
theorem emitted_max_cost_four : worstCost 5 plan = 4 := by decide +kernel
theorem equality_with_reserve_rejected : accepts exhaustedReserve allowed plan = false := by decide +kernel
theorem debt_at_reserve_rejected : accepts debtAtLimit allowed plan = false := by decide +kernel
theorem invalid_envelope_rejected : accepts invalidEnvelope allowed plan = false := by decide +kernel
theorem forged_operator_price_rejected : accepts contract allowed forgedProbePrice = false := by decide +kernel
theorem illegal_repair_rejected : accepts contract allowed forgedRepair = false := by decide +kernel
theorem unsafe_act_rejected : accepts contract allowed .act = false := by decide +kernel
theorem unsupported_refuse_not_mislabelled_act : accepts contract allowed .refuse = false := by decide +kernel
theorem auto_emitted_plan_exact_minimax :
    accepts contract allowed plan = true ∧
    worstCost 5 plan = 4 ∧
    MaxExact.feasible 3 MaxExact.allBelief 0 = false := by
  exact ⟨emitted_plan_valid_and_strictly_funded, emitted_max_cost_four, MaxExact.three_insufficient⟩
end INSACERMO.EmittedOpenFlightsV2
