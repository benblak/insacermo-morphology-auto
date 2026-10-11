from proof_carrying_multi_probe_runtime_v1.multi_probe_runtime_v2 import *
from final_integration_v1.final_integration_v1 import (
    CanonicalIntegration, make_base_receipt
)
from certified_online_debt_v1.online_debt_v1 import (
    AuthorityPolicy, DebtVerifier, DebtClaim
)

NOW="2026-10-02T08:00:00+00:00"
C="contract-multi-probe"
O="observer-multi-probe"
SIG=[3,5,8]

policy=AuthorityPolicy("current","CURRENT_CERTIFIED_BOUND",C,O)
integration=CanonicalIntegration(
    contract_hash=C,
    observer_hash=O,
    debt_verifier=DebtVerifier([policy]),
)
base=make_base_receipt(
    contract_hash=C,
    observer_hash=O,
    verdict="ACT",
    selected_action="A",
    core_reference="CORE_INTERFACE_RECEIPT",
    signature=SIG,
)
claim=DebtClaim(
    "current","A",C,O,"TOTAL",2,
    "2026-10-02T07:59:00+00:00","E0","CURRENT_CERTIFIED_BOUND",
    {"current_upper_bound":2},None,None
)
bound=integration.verify_claim(claim,now=NOW)
base_cert=integration.evaluate_verified(
    base_receipt=base,
    signature=SIG,
    rho0=20,
    verified_bound=bound,
    now=NOW,
)
assert CanonicalIntegration.verify_integration_certificate(base_cert)["valid"]

runtime=ProofCarryingMultiProbeRuntime(contract_hash=C)

candidates=[
    PlanCandidate("p3",(3,4),C,"contract-receipt"),
    PlanCandidate("p1",(1,2),C,"contract-receipt"),
    PlanCandidate("p2",(2,2),C,"contract-receipt"),
]
cert=runtime.evaluate(
    base_integration_certificate=base_cert,
    candidates=candidates,
    rho0=20,
    debt_before=5,
)
assert cert["chosen_plan"]["plan_id"]=="p1"
assert cert["total_price"]==3
assert cert["debt_after"]==8
assert cert["reserve_left"]==12
assert cert["verdict"]=="EXECUTE"
assert cert["proof_obligations"]["strict_reserve_rule"] is True
assert runtime.verify(cert)["valid"]

refuse_candidates=[
    PlanCandidate("r2",(6,),C,"contract-receipt"),
    PlanCandidate("r1",(5,),C,"contract-receipt"),
    PlanCandidate("r3",(9,),C,"contract-receipt"),
]
refuse=runtime.evaluate(
    base_integration_certificate=base_cert,
    candidates=refuse_candidates,
    rho0=10,
    debt_before=5,
)
assert refuse["chosen_plan"]["plan_id"]=="r1"
assert refuse["total_price"]==5
assert refuse["debt_after"]==10
assert refuse["verdict"]=="REFUSE"
assert refuse["proof_obligations"]["strict_reserve_rule"] is False
assert refuse["proof_obligations"]["refuse_excludes_all_audited_candidates"] is True
assert runtime.verify(refuse)["valid"]

tampered=dict(cert)
tampered["reserve_left"]=999
assert not runtime.verify(tampered)["valid"]

bad_candidates=[PlanCandidate("bad",(1,), "wrong-contract","contract-receipt")]
try:
    runtime.evaluate(
        base_integration_certificate=base_cert,
        candidates=bad_candidates,
        rho0=20,
        debt_before=5,
    )
except MultiProbeRuntimeError as e:
    assert str(e)=="CANDIDATE_CONTRACT_MISMATCH"
else:
    raise AssertionError("contract mismatch candidate accepted")

try:
    runtime.evaluate(
        base_integration_certificate=base_cert,
        candidates=[],
        rho0=20,
        debt_before=5,
    )
except MultiProbeRuntimeError as e:
    assert str(e)=="NO_AUDITED_CANDIDATES"
else:
    raise AssertionError("empty candidate set accepted")

print("PROOF_CARRYING_MULTI_PROBE_RUNTIME_V2_TESTS: PASS 5")
