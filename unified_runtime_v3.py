"""INSACERMO V3: future-safe facade over unchanged certified historical runtime.
Finite rational linear contracts only. Not a machine-proof of this Python.
"""
from __future__ import annotations
from fractions import Fraction
from dataclasses import dataclass
from typing import Any
import hashlib, json
from proof_carrying_multi_probe_runtime_v1.multi_probe_runtime_v2 import (
    PlanCandidate, ProofCarryingMultiProbeRuntime, MultiProbeRuntimeError, h,
)

class UnifiedError(ValueError): pass

def natural(n):
    if type(n) is not int or n<0: raise UnifiedError("INVALID_NAT")
    return n

def ratio(v):
    if type(v) not in (str,int): raise UnifiedError("RATIONAL_STRING_REQUIRED")
    try: r=Fraction(v)
    except Exception as e: raise UnifiedError("INVALID_RATIONAL") from e
    if r<0: raise UnifiedError("NEGATIVE_RATIONAL")
    return r

def canonical(obj): return json.dumps(obj,sort_keys=True,separators=(",",":"),ensure_ascii=False)
def digest(obj): return hashlib.sha256(canonical(obj).encode()).hexdigest()

@dataclass(frozen=True)
class Contract:
    A: tuple[tuple[int,...], ...]       # rows: nutrients, columns: available actions
    b: tuple[int,...]
    future_worlds: tuple[tuple[bool,...], ...] # capabilities allowed in each future world
    annual_limit: int = 40
    annual_days: int = 365
    scale: int = 10
    def __post_init__(self):
        n=len(self.future_worlds[0]) if self.future_worlds else 0
        if not n or not self.A or len(self.b)!=len(self.A): raise UnifiedError("BAD_DIMENSIONS")
        if any(len(row)!=n for row in self.A) or any(len(row)!=n for row in self.future_worlds):
            raise UnifiedError("BAD_DIMENSIONS")
        if any(type(v) is not bool for row in self.future_worlds for v in row): raise UnifiedError("BAD_WORLD")
        for row in self.A:
            for v in row: natural(v)
        for v in self.b: natural(v)
        natural(self.annual_limit);natural(self.annual_days);natural(self.scale)
        if not self.scale: raise UnifiedError("ZERO_SCALE")
    def payload(self):
        return {"A":[list(r) for r in self.A],"b":list(self.b),
            "future_worlds":[list(r) for r in self.future_worlds],
            "annual_limit":self.annual_limit,"annual_days":self.annual_days,"scale":self.scale}
    @property
    def contract_hash(self):return digest(self.payload())

def check_recipe(c:Contract, x:tuple[Fraction,...]):
    if len(x)!=len(c.future_worlds[0]):raise UnifiedError("RECIPE_DIMENSION")
    if any(v<0 for v in x):raise UnifiedError("NEGATIVE_RECIPE")
    current=all(sum(c.A[i][j]*x[j] for j in range(len(x)))>=c.b[i]
                for i in range(len(c.b)))
    affordable=c.annual_days*sum(x)<=c.annual_limit
    world_checks=[all(x[j]==0 or permitted for j,permitted in enumerate(world))
                  for world in c.future_worlds]
    return {"current_valid":current,"annual_budget_valid":affordable,
            "future_worlds_valid":world_checks,"future_valid":all(world_checks)}

def decide(*,contract:Contract,base_certificate:dict[str,Any],
           proposals:list[dict[str,Any]],rho0:int,debt_before:int):
    natural(rho0);natural(debt_before)
    if base_certificate.get("contract_hash")!=contract.contract_hash:
        raise UnifiedError("CONTRACT_MISMATCH")
    if not proposals:raise UnifiedError("NO_PROPOSALS")
    evaluated=[];viable=[]
    ids=set()
    for p in proposals:
        pid=p.get("id")
        if type(pid) is not str or not pid or pid in ids:raise UnifiedError("INVALID_ID")
        ids.add(pid)
        x=tuple(ratio(v) for v in p["recipe"])
        prices=tuple(natural(v) for v in p["prices"])
        check=check_recipe(contract,x)
        item={"id":pid,"recipe":[str(v) for v in x],"prices":list(prices),
              "check":check}
        evaluated.append(item)
        if check["current_valid"] and check["annual_budget_valid"] and check["future_valid"]:
            viable.append(PlanCandidate(pid,prices,contract.contract_hash,digest(item)))
    if not viable:
        body={"contract_hash":contract.contract_hash,"verdict":"REFUSE_FUTURE_OR_PRESENT",
              "audited":evaluated,"scope":"NO_VIABLE_PROPOSAL_IN_SUPPLIED_FINITE_SET"}
        body["certificate_hash"]=digest(body)
        return body
    historical=ProofCarryingMultiProbeRuntime(contract_hash=contract.contract_hash)
    cert=historical.evaluate(base_integration_certificate=base_certificate,
          candidates=viable,rho0=rho0,debt_before=debt_before)
    if not historical.verify(cert)["valid"]:raise UnifiedError("HISTORICAL_CERTIFICATE_INVALID")
    body={"contract_hash":contract.contract_hash,"verdict":cert["verdict"],
         "audited":evaluated,"selected":cert["chosen_plan"]["plan_id"],
         "historical_certificate":cert,
         "scope":"FINITE_PROPOSALS; DECLARED_FUTURE_WORLDS; EXACT_RATIONAL_ARITHMETIC"}
    body["certificate_hash"]=digest(body)
    return body

def verify(*,contract:Contract,base_certificate:dict,proposals:list[dict],
           rho0:int,debt_before:int,certificate:dict)->bool:
    try:
        expected=decide(contract=contract,base_certificate=base_certificate,
            proposals=proposals,rho0=rho0,debt_before=debt_before)
        return expected==certificate
    except (UnifiedError,MultiProbeRuntimeError,TypeError,ValueError,KeyError,IndexError):
        return False
