"""Executable end-to-end V3 regression over unchanged October 4 debt/runtime modules."""
from copy import deepcopy
from unified_runtime_v3 import Contract, decide, verify, UnifiedError
from final_integration_v1.final_integration_v1 import CanonicalIntegration, make_base_receipt
from certified_online_debt_v1.online_debt_v1 import AuthorityPolicy, DebtVerifier, DebtClaim
from proof_carrying_multi_probe_runtime_v1.multi_probe_runtime_v2 import ProofCarryingMultiProbeRuntime
NOW="2026-10-02T08:00:00+00:00"
C=Contract(A=((10,10),),b=(1,),future_worlds=((False,True),),annual_limit=40)
H=C.contract_hash
O="observer-unified-v3"
SIGNATURE=[3,5,8]
integrator=CanonicalIntegration(contract_hash=H,observer_hash=O,
    debt_verifier=DebtVerifier([AuthorityPolicy("current","CURRENT_CERTIFIED_BOUND",H,O)]))
receipt=make_base_receipt(contract_hash=H,observer_hash=O,verdict="ACT",
    selected_action="A",core_reference="CORE_INTERFACE_RECEIPT",signature=SIGNATURE)
claim=DebtClaim("current","A",H,O,"TOTAL",2,
    "2026-10-02T07:59:00+00:00","E0","CURRENT_CERTIFIED_BOUND",
    {"current_upper_bound":2},None,None)
bound=integrator.verify_claim(claim,now=NOW)
base=integrator.evaluate_verified(base_receipt=receipt,signature=SIGNATURE,
    rho0=20,verified_bound=bound,now=NOW)
assert CanonicalIntegration.verify_integration_certificate(base)["valid"]

# Both satisfy EXACT same current contract, future only permits second action.
bad={"id":"cheap_bad_future","recipe":["1/10","0"],"prices":[1]}
good={"id":"safe_future","recipe":["0","1/10"],"prices":[3]}
args=dict(contract=C,base_certificate=base,proposals=[bad,good],rho0=20,debt_before=5)
cert=decide(**args)
assert cert["verdict"]=="EXECUTE" and cert["selected"]=="safe_future"
assert all(row["check"]["current_valid"] for row in cert["audited"])
assert not cert["audited"][0]["check"]["future_valid"]
assert cert["audited"][1]["check"]["future_valid"]
assert cert["historical_certificate"]["debt_after"]==8
assert ProofCarryingMultiProbeRuntime.verify(cert["historical_certificate"])["valid"]
assert verify(**args,certificate=cert)
print("PASS: future-safe choice over cheaper destructive alternative")

# No future-safe offer → refuse, not a hidden relaxation of future requirement.
none=dict(args,proposals=[bad])
refused=decide(**none)
assert refused["verdict"]=="REFUSE_FUTURE_OR_PRESENT"
assert verify(**none,certificate=refused)
print("PASS: future contract prevents unsafe repair")

# At equality, historical strictly reserved bound must refuse.
equal=dict(args,rho0=8)
cert_equal=decide(**equal)
assert cert_equal["verdict"]=="REFUSE"
assert verify(**equal,certificate=cert_equal)
print("PASS: strict reserve rejects equality")

# Budget crossing and invalid claims must never permit EXECUTE.
over=Contract(A=((10,10),),b=(1,),future_worlds=((False,True),),annual_limit=30)
assert not verify(**args,certificate={**cert,"verdict":"EXECUTE","certificate_hash":"fake"})
mutated=deepcopy(cert);mutated["audited"][0]["check"]["future_valid"]=True
assert not verify(**args,certificate=mutated)
mutated2=deepcopy(cert);mutated2["historical_certificate"]["reserve_left"]=999
assert not verify(**args,certificate=mutated2)
try:
    decide(**dict(args,contract=over))
except UnifiedError as e: assert str(e)=="CONTRACT_MISMATCH"
else: raise AssertionError("contract hash bypassed")
print("PASS: contract mismatch and certificate tampering rejected")
print("INSACERMO_V3_REAL_LEGACY_RUNTIME_INTEGRATION: SUCCESS 4 SCENARIOS")
