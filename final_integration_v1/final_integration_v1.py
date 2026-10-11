from __future__ import annotations
from dataclasses import dataclass, asdict
from typing import Any
import hashlib, json

from certified_online_debt_v1.online_debt_v1 import (
    DebtClaim, DebtVerifier, VerifiedDebtBound
)
from temporal_runtime.temporal_runtime_v1 import Runtime, DebtEvidence
from minimum_proof_acquisition_v1.proof_acquisition_v1 import plan_same_debt_absolute

VERSION="INSACERMO_FINAL_INTEGRATION_V1"

def h(obj: Any) -> str:
    return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(",",":"),ensure_ascii=False).encode()).hexdigest()

class IntegrationError(ValueError):
    pass

@dataclass(frozen=True)
class BaseReceipt:
    contract_hash: str
    observer_hash: str
    verdict: str
    selected_action: str | None
    core_reference: str
    signature_hash: str
    def payload(self):
        d=asdict(self)
        d["receipt_hash"]=h(d)
        return d

def make_base_receipt(*,contract_hash:str,observer_hash:str,verdict:str,
                      selected_action:str|None,core_reference:str,signature:list[int]) -> dict:
    if verdict=="ACT" and not selected_action:
        raise IntegrationError("ACT_REQUIRES_ACTION")
    return BaseReceipt(contract_hash,observer_hash,verdict,selected_action,
                       core_reference,h(signature)).payload()

def verify_base_receipt(receipt:dict,*,contract_hash:str,observer_hash:str,signature:list[int]) -> None:
    rec=receipt.get("receipt_hash")
    body={k:v for k,v in receipt.items() if k!="receipt_hash"}
    if rec!=h(body):
        raise IntegrationError("BASE_RECEIPT_HASH_MISMATCH")
    if receipt.get("contract_hash")!=contract_hash:
        raise IntegrationError("BASE_RECEIPT_CONTRACT_MISMATCH")
    if receipt.get("observer_hash")!=observer_hash:
        raise IntegrationError("BASE_RECEIPT_OBSERVER_MISMATCH")
    if receipt.get("signature_hash")!=h(signature):
        raise IntegrationError("BASE_RECEIPT_SIGNATURE_MISMATCH")
    if receipt.get("verdict")=="ACT" and not receipt.get("selected_action"):
        raise IntegrationError("BASE_RECEIPT_ACT_WITHOUT_ACTION")

def verified_bound_to_evidence(bound:VerifiedDebtBound,*,contract_hash:str,observer_hash:str) -> DebtEvidence:
    if not isinstance(bound,VerifiedDebtBound):
        raise IntegrationError("VERIFIED_DEBT_BOUND_REQUIRED")
    if bound.contract_hash!=contract_hash:
        raise IntegrationError("VERIFIED_BOUND_CONTRACT_MISMATCH")
    if bound.observer_hash!=observer_hash:
        raise IntegrationError("VERIFIED_BOUND_OBSERVER_MISMATCH")
    source_id=f"{bound.authority_id}:{bound.payload()['verified_bound_hash']}"
    return DebtEvidence(
        action=bound.action,
        upper_bound=float(bound.upper_bound),
        contract_hash=bound.contract_hash,
        observer_hash=bound.observer_hash,
        source_id=source_id,
        issued_at=bound.issued_at,
        epoch=bound.epoch,
        valid_until=bound.valid_until,
        certified_upper_bound=True,
    )

class CanonicalIntegration:
    def __init__(self,*,contract_hash:str,observer_hash:str,debt_verifier:DebtVerifier):
        self.contract_hash=contract_hash
        self.observer_hash=observer_hash
        self.debt_verifier=debt_verifier
        self.runtime=Runtime(contract_hash,observer_hash)

    def verify_claim(self,claim:DebtClaim,*,now:str)->VerifiedDebtBound:
        return self.debt_verifier.verify(claim,now=now)

    def evaluate_verified(self,*,base_receipt:dict,signature:list[int],rho0:float,
                          verified_bound:VerifiedDebtBound|None,now:str,
                          fracture=None,probe:bool=True,repair:bool=True)->dict:
        verify_base_receipt(base_receipt,contract_hash=self.contract_hash,
                            observer_hash=self.observer_hash,signature=signature)
        evidence=None if verified_bound is None else verified_bound_to_evidence(
            verified_bound,contract_hash=self.contract_hash,observer_hash=self.observer_hash)
        core_receipt={"verdict":base_receipt["verdict"],
                      "selected_action":base_receipt["selected_action"]}
        cert=self.runtime.evaluate(
            base_receipt=core_receipt,signature=signature,rho0=rho0,
            evidence=evidence,now=now,fracture=fracture,probe=probe,repair=repair)
        cert["integration_version"]=VERSION
        cert["base_receipt_hash"]=base_receipt["receipt_hash"]
        cert["integration_hash"]=h(cert)
        return cert

    @staticmethod
    def verify_integration_certificate(cert:dict)->dict:
        failures=[]
        integ=cert.get("integration_hash")
        body={k:v for k,v in cert.items() if k!="integration_hash"}
        if integ!=h(body):
            failures.append("INTEGRATION_HASH_MISMATCH")
        temporal={k:v for k,v in cert.items()
                  if k not in ("integration_version","base_receipt_hash","integration_hash")}
        tv=Runtime.verify(temporal)
        failures.extend("TEMPORAL:"+x for x in tv["failures"])
        return {"valid":not failures,"failures":failures}

def plan_then_verify_then_decide(*,reserve:int,baseline_upper_bound:int,offers,
                                 selected_claim:DebtClaim,now:str,
                                 integration:CanonicalIntegration,
                                 base_receipt:dict,signature:list[int]) -> dict:
    plan=plan_same_debt_absolute(
        reserve=reserve,baseline_upper_bound=baseline_upper_bound,offers=offers)
    if not plan.restores_act:
        return {"plan":asdict(plan),"verified_bound":None,"certificate":
            integration.evaluate_verified(base_receipt=base_receipt,signature=signature,
                                          rho0=reserve,verified_bound=None,now=now)}
    if selected_claim.authority_id not in plan.selected_sources:
        raise IntegrationError("CLAIM_NOT_SELECTED_BY_PROOF_PLAN")
    bound=integration.verify_claim(selected_claim,now=now)
    cert=integration.evaluate_verified(
        base_receipt=base_receipt,signature=signature,rho0=reserve,
        verified_bound=bound,now=now)
    return {"plan":asdict(plan),"verified_bound":bound.payload(),"certificate":cert}
