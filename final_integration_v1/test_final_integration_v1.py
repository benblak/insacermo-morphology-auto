from final_integration_v1 import *
from certified_online_debt_v1.online_debt_v1 import *
from minimum_proof_acquisition_v1.proof_acquisition_v1 import AbsoluteBoundOffer
from temporal_runtime.temporal_runtime_v1 import DebtEvidence, FractureRegistry

NOW="2026-10-02T08:00:00+00:00"
C="contract-final"
O="observer-final"
SIG=[7,11]

policies=[
    AuthorityPolicy("fresh_probe","FRESH_PROBE_BOUND",C,O,max_age_steps=1),
    AuthorityPolicy("current_authority","CURRENT_CERTIFIED_BOUND",C,O),
]
verifier=DebtVerifier(policies)
integration=CanonicalIntegration(contract_hash=C,observer_hash=O,debt_verifier=verifier)
base=make_base_receipt(contract_hash=C,observer_hash=O,verdict="ACT",
                       selected_action="A",core_reference="CORE_INTERFACE_RECEIPT",signature=SIG)

offers=[
    AbsoluteBoundOffer("fresh_probe",1,5,"fresh_probe"),
    AbsoluteBoundOffer("expensive",10,3,"current_authority"),
]
claim=DebtClaim(
    "fresh_probe","A",C,O,"TOTAL",5,
    "2026-10-02T07:59:00+00:00","E0","FRESH_PROBE_BOUND",
    {"probe_upper_bound":5,"age_steps":0},
    "2026-10-02T08:05:00+00:00",None
)
out=plan_then_verify_then_decide(
    reserve=10,baseline_upper_bound=13,offers=offers,selected_claim=claim,now=NOW,
    integration=integration,base_receipt=base,signature=SIG)
assert out["plan"]["selected_sources"]==("fresh_probe",)
assert out["certificate"]["temporal_verdict"]=="ACT"
assert CanonicalIntegration.verify_integration_certificate(out["certificate"])["valid"]

equal_claim=DebtClaim(
    "current_authority","A",C,O,"TOTAL",10,
    "2026-10-02T07:59:00+00:00","E1","CURRENT_CERTIFIED_BOUND",
    {"current_upper_bound":10},None,None
)
equal_bound=integration.verify_claim(equal_claim,now=NOW)
eq=integration.evaluate_verified(base_receipt=base,signature=SIG,rho0=10,
                                 verified_bound=equal_bound,now=NOW)
assert eq["temporal_verdict"]=="PROBE"

raw=DebtEvidence("A",1,C,O,"raw","2026-10-02T07:59:00+00:00","E2",None,True)
try:
    verified_bound_to_evidence(raw,contract_hash=C,observer_hash=O)
except IntegrationError as e:
    assert str(e)=="VERIFIED_DEBT_BOUND_REQUIRED"
else:
    raise AssertionError("raw DebtEvidence bypassed verifier")

forged=DebtClaim(
    "fresh_probe","A",C,O,"TOTAL",2,
    "2026-10-02T07:59:00+00:00","E3","FRESH_PROBE_BOUND",
    {"probe_upper_bound":5,"age_steps":0},None,None
)
try:
    integration.verify_claim(forged,now=NOW)
except DebtVerificationError as e:
    assert str(e)=="CLAIMED_BOUND_NOT_RECOMPUTABLE"
else:
    raise AssertionError("forged claim accepted")

expired=DebtClaim(
    "fresh_probe","A",C,O,"TOTAL",5,
    "2026-10-02T07:00:00+00:00","E4","FRESH_PROBE_BOUND",
    {"probe_upper_bound":5,"age_steps":0},"2026-10-02T07:30:00+00:00",None
)
try:
    integration.verify_claim(expired,now=NOW)
except DebtVerificationError as e:
    assert str(e)=="CLAIM_EXPIRED"
else:
    raise AssertionError("expired claim accepted")

badbase=dict(base); badbase["selected_action"]="B"
try:
    integration.evaluate_verified(base_receipt=badbase,signature=SIG,rho0=10,
                                  verified_bound=equal_bound,now=NOW)
except IntegrationError as e:
    assert str(e)=="BASE_RECEIPT_HASH_MISMATCH"
else:
    raise AssertionError("tampered base receipt accepted")

fresh_bound=integration.verify_claim(claim,now=NOW)
fr=FractureRegistry(); assert fr.record(SIG,"0",{"t":0}) is None
w=fr.record(SIG,"1",{"t":1}); assert w
fract=integration.evaluate_verified(base_receipt=base,signature=SIG,rho0=100,
                                    verified_bound=fresh_bound,now=NOW,
                                    fracture=w,probe=False,repair=True)
assert fract["temporal_verdict"]=="REPAIR"

missing=integration.evaluate_verified(base_receipt=base,signature=SIG,rho0=10,
                                      verified_bound=None,now=NOW)
assert missing["temporal_verdict"]=="PROBE"

tampered=dict(out["certificate"]); tampered["residual_reserve"]=999
assert not CanonicalIntegration.verify_integration_certificate(tampered)["valid"]

bad_selected=DebtClaim(
    "current_authority","A",C,O,"TOTAL",3,
    "2026-10-02T07:59:00+00:00","E5","CURRENT_CERTIFIED_BOUND",
    {"current_upper_bound":3},None,None
)
try:
    plan_then_verify_then_decide(
        reserve=10,baseline_upper_bound=13,offers=offers,selected_claim=bad_selected,now=NOW,
        integration=integration,base_receipt=base,signature=SIG)
except IntegrationError as e:
    assert str(e)=="CLAIM_NOT_SELECTED_BY_PROOF_PLAN"
else:
    raise AssertionError("unselected authority claim accepted")

print("FINAL_INTEGRATION_V1_TESTS: PASS 10")
