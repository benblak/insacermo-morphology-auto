from __future__ import annotations
from dataclasses import dataclass, asdict
from datetime import datetime
import hashlib, json

VERSION = "INSACERMO_PROOF_CARRYING_TEMPORAL_RUNTIME_V1"

def h(obj):
    return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(",",":"),ensure_ascii=False).encode()).hexdigest()

def _dt(s):
    return None if s is None else datetime.fromisoformat(str(s).replace("Z","+00:00"))

@dataclass(frozen=True)
class KernelRef:
    run_id:int=36969985558
    commit:str="cdfdb91780286d6cf80a33d5007b0a8bbe091fd6"
    artifact_id:int=11211017962
    artifact_sha256:str="31c749851b0dfba8245b44aff34d43281b1b55845a06e76aea1534a756122e06"
    lean_version:str="4.19.0"

@dataclass(frozen=True)
class DebtEvidence:
    action:str
    upper_bound:float
    contract_hash:str
    observer_hash:str
    source_id:str
    issued_at:str
    epoch:str
    valid_until:str|None=None
    certified_upper_bound:bool=True
    def payload(self):
        d=asdict(self); d["evidence_hash"]=h(d); return d

class Runtime:
    def __init__(self,contract_hash,observer_hash,kernel=KernelRef()):
        self.contract_hash=str(contract_hash); self.observer_hash=str(observer_hash); self.kernel=kernel
        self.last_debt={}
    def _fallback(self,probe,repair,reason):
        return ("PROBE" if probe else "REPAIR" if repair else "REFUSE",reason)
    def evaluate(self,*,base_receipt,signature,rho0,evidence,now,fracture=None,probe=True,repair=True):
        action=base_receipt.get("selected_action"); base=base_receipt.get("verdict")
        po={"contract_hash_match":None,"observer_hash_match":None,"certified_upper_bound":None,
            "debt_nonnegative":None,"evidence_not_expired":None,"debt_nondecreasing":None,
            "strict_reserve_gt_debt":None,"observer_fracture_absent":fracture is None}
        verdict=base; reason="Base decision is not ACT; temporal layer cannot elevate it."; residual=None
        if base!="ACT" or not action:
            pass
        elif fracture is not None:
            verdict,reason=self._fallback(False,repair,"Observer fracture: identical observation supports incompatible required actions.")
        elif rho0 is None or rho0<0:
            verdict,reason=self._fallback(probe,repair,"No nonnegative static reserve.")
        elif evidence is None:
            verdict,reason=self._fallback(probe,repair,"Temporal debt unknown: ACT cannot be reused.")
        else:
            po["contract_hash_match"]=evidence.contract_hash==self.contract_hash
            po["observer_hash_match"]=evidence.observer_hash==self.observer_hash
            po["certified_upper_bound"]=bool(evidence.certified_upper_bound)
            po["debt_nonnegative"]=evidence.upper_bound>=0
            po["evidence_not_expired"]=evidence.valid_until is None or _dt(now)<=_dt(evidence.valid_until)
            key=(str(action),str(evidence.epoch)); prev=self.last_debt.get(key)
            po["debt_nondecreasing"]=prev is None or evidence.upper_bound>=prev
            if not all(po[k] for k in ("contract_hash_match","observer_hash_match","certified_upper_bound","debt_nonnegative","evidence_not_expired","debt_nondecreasing")):
                verdict="VALIDITY_REFUSE"; reason="Debt evidence failed proof-carrying checks."
            else:
                self.last_debt[key]=float(evidence.upper_bound)
                residual=float(rho0)-float(evidence.upper_bound)
                po["strict_reserve_gt_debt"]=float(rho0)>float(evidence.upper_bound)
                if po["strict_reserve_gt_debt"]:
                    verdict="ACT"; reason="Certified reserve remains: rho_0 > D_t."
                else:
                    verdict,reason=self._fallback(probe,repair,"Temporal debt consumed the reserve: certificate expired.")
        body={"runtime_version":VERSION,"contract_hash":self.contract_hash,"observer_hash":self.observer_hash,
              "base_verdict":base,"selected_action":action,"signature":list(signature),"signature_hash":h(list(signature)),
              "rho0":rho0,"debt_evidence":evidence.payload() if evidence else None,"residual_reserve":residual,
              "temporal_verdict":verdict,"reason":reason,"fracture":fracture,"proof_obligations":po,
              "kernel_reference":asdict(self.kernel),"now":now}
        body["certificate_hash"]=h(body)
        return body
    @staticmethod
    def verify(cert):
        rec=cert.get("certificate_hash"); body={k:v for k,v in cert.items() if k!="certificate_hash"}
        failures=[]
        if rec!=h(body): failures.append("HASH_MISMATCH")
        if cert.get("temporal_verdict")=="ACT":
            po=cert.get("proof_obligations",{})
            for k in ("contract_hash_match","observer_hash_match","certified_upper_bound","debt_nonnegative","evidence_not_expired","debt_nondecreasing","strict_reserve_gt_debt","observer_fracture_absent"):
                if po.get(k) is not True: failures.append("ACT_OBLIGATION:"+k)
        return {"valid":not failures,"failures":failures}

class FractureRegistry:
    def __init__(self): self.db={}
    def record(self,signature,required_action,provenance):
        key=h(list(signature)); per=self.db.setdefault(key,{})
        per.setdefault(str(required_action),provenance)
        acts=sorted(per)
        witness=None
        if len(acts)>1:
            witness={"signature":list(signature),"required_actions":acts,"provenance":[per[a] for a in acts]}
            witness["witness_hash"]=h(witness)
        return witness
