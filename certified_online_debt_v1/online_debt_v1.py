from __future__ import annotations
from dataclasses import dataclass, asdict
from datetime import datetime
from typing import Any, Iterable
import hashlib, json, math

VERSION = "INSACERMO_CERTIFIED_ONLINE_DEBT_V1"

def h(obj: Any) -> str:
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()).hexdigest()

def _dt(s: str | None):
    return None if s is None else datetime.fromisoformat(str(s).replace("Z", "+00:00"))

class DebtVerificationError(ValueError):
    pass

@dataclass(frozen=True)
class AuthorityPolicy:
    authority_id: str
    recipe: str
    contract_hash: str
    observer_hash: str
    debt_scope: str = "TOTAL"
    component: str | None = None
    valid_from: str | None = None
    valid_until: str | None = None
    max_growth_per_step: float | None = None
    max_age_steps: int | None = None
    policy_version: str = "1"
    def payload(self):
        d=asdict(self); d["policy_hash"]=h(d); return d

@dataclass(frozen=True)
class DebtClaim:
    authority_id: str
    action: str
    contract_hash: str
    observer_hash: str
    debt_scope: str
    claimed_upper_bound: float
    issued_at: str
    epoch: str
    recipe: str
    witness: dict[str, Any]
    valid_until: str | None = None
    component: str | None = None
    def payload(self):
        d=asdict(self); d["claim_hash"]=h(d); return d

@dataclass(frozen=True)
class VerifiedDebtBound:
    authority_id: str
    action: str
    contract_hash: str
    observer_hash: str
    debt_scope: str
    upper_bound: float
    issued_at: str
    epoch: str
    valid_until: str | None
    component: str | None
    recipe: str
    authority_policy_hash: str
    source_claim_hash: str
    proof_rule: str
    verifier_version: str = VERSION
    def payload(self):
        d=asdict(self); d["verified_bound_hash"]=h(d); return d

class DebtVerifier:
    def __init__(self, policies: Iterable[AuthorityPolicy]):
        policies=list(policies)
        self.policies={p.authority_id:p for p in policies}
        if len(self.policies)!=len(policies): raise DebtVerificationError("DUPLICATE_AUTHORITY_ID")

    @staticmethod
    def _finite_nonnegative(x,label):
        try: y=float(x)
        except Exception as e: raise DebtVerificationError(label+"_NOT_NUMERIC") from e
        if not math.isfinite(y) or y<0: raise DebtVerificationError(label+"_INVALID")
        return y

    @staticmethod
    def _check_time_window(now,lo,hi,label):
        n=_dt(now)
        if lo is not None and n<_dt(lo): raise DebtVerificationError(label+"_NOT_YET_VALID")
        if hi is not None and n>_dt(hi): raise DebtVerificationError(label+"_EXPIRED")

    def verify(self,claim:DebtClaim,*,now:str)->VerifiedDebtBound:
        p=self.policies.get(claim.authority_id)
        if p is None: raise DebtVerificationError("UNKNOWN_AUTHORITY")
        if claim.recipe!=p.recipe: raise DebtVerificationError("RECIPE_MISMATCH")
        if claim.contract_hash!=p.contract_hash: raise DebtVerificationError("CONTRACT_SCOPE_MISMATCH")
        if claim.observer_hash!=p.observer_hash: raise DebtVerificationError("OBSERVER_SCOPE_MISMATCH")
        if claim.debt_scope!=p.debt_scope or claim.component!=p.component: raise DebtVerificationError("DEBT_SCOPE_MISMATCH")
        self._check_time_window(now,p.valid_from,p.valid_until,"POLICY")
        self._check_time_window(now,claim.issued_at,claim.valid_until,"CLAIM")
        w=claim.witness
        if p.recipe=="CURRENT_CERTIFIED_BOUND":
            computed=self._finite_nonnegative(w.get("current_upper_bound"),"CURRENT_BOUND")
            proof_rule="current_upper_bound_from_registered_authority"
        elif p.recipe=="DELAYED_EXACT_PLUS_GROWTH_CAP":
            if p.max_growth_per_step is None: raise DebtVerificationError("POLICY_MISSING_GROWTH_CAP")
            exact=self._finite_nonnegative(w.get("exact_debt_at_source"),"SOURCE_DEBT")
            try: source_step=int(w["source_step"]); target_step=int(w["target_step"])
            except Exception as e: raise DebtVerificationError("STEP_WITNESS_INVALID") from e
            if target_step<source_step: raise DebtVerificationError("NEGATIVE_ELAPSED_STEPS")
            age=target_step-source_step
            if p.max_age_steps is not None and age>p.max_age_steps: raise DebtVerificationError("SOURCE_TOO_OLD")
            growth=self._finite_nonnegative(p.max_growth_per_step,"GROWTH_CAP")
            computed=exact+growth*age
            proof_rule="delayed_exact_debt_plus_registered_per_step_growth_cap"
        elif p.recipe=="FRESH_PROBE_BOUND":
            computed=self._finite_nonnegative(w.get("probe_upper_bound"),"PROBE_BOUND")
            try: age=int(w.get("age_steps",0))
            except Exception as e: raise DebtVerificationError("PROBE_AGE_INVALID") from e
            if age<0: raise DebtVerificationError("PROBE_AGE_INVALID")
            if p.max_age_steps is not None and age>p.max_age_steps: raise DebtVerificationError("PROBE_TOO_OLD")
            proof_rule="fresh_probe_bound_from_registered_authority"
        else:
            raise DebtVerificationError("UNSUPPORTED_RECIPE")
        claimed=self._finite_nonnegative(claim.claimed_upper_bound,"CLAIMED_BOUND")
        if not math.isclose(claimed,computed,rel_tol=0.0,abs_tol=1e-12):
            raise DebtVerificationError("CLAIMED_BOUND_NOT_RECOMPUTABLE")
        return VerifiedDebtBound(claim.authority_id,claim.action,claim.contract_hash,claim.observer_hash,
            claim.debt_scope,computed,claim.issued_at,claim.epoch,claim.valid_until,claim.component,
            claim.recipe,p.payload()["policy_hash"],claim.payload()["claim_hash"],proof_rule)

def tighter_same_debt(bounds):
    bs=list(bounds)
    if not bs: raise DebtVerificationError("NO_BOUNDS")
    ctx={(b.action,b.contract_hash,b.observer_hash,b.epoch,b.debt_scope,b.component) for b in bs}
    if len(ctx)!=1: raise DebtVerificationError("MIN_REQUIRES_SAME_DEBT")
    return min(bs,key=lambda b:b.upper_bound)

def sum_components(bounds,total_scope="TOTAL"):
    bs=list(bounds)
    if not bs: raise DebtVerificationError("NO_BOUNDS")
    base={(b.action,b.contract_hash,b.observer_hash,b.epoch,b.debt_scope) for b in bs}
    comps=[b.component for b in bs]
    if len(base)!=1 or any(c is None for c in comps) or len(set(comps))!=len(comps):
        raise DebtVerificationError("INVALID_COMPONENT_SET")
    b=bs[0]
    return VerifiedDebtBound("COMPOSITE_SUM",b.action,b.contract_hash,b.observer_hash,total_scope,
        sum(x.upper_bound for x in bs),max(x.issued_at for x in bs),b.epoch,
        min((x.valid_until for x in bs if x.valid_until is not None),default=None),None,
        "SUM_COMPONENTS",h([x.authority_policy_hash for x in bs]),h([x.source_claim_hash for x in bs]),
        "sum_of_upper_bounds_for_declared_distinct_debt_components")

def no_free_debt_counterexample(*,reserve,observation,low_debt,high_debt,observation_only_bound):
    permit=observation_only_bound<reserve
    return {"same_observation":observation,"observation_only_bound":observation_only_bound,
      "reserve":reserve,"low_world_debt":low_debt,"high_world_debt":high_debt,
      "act_permitted_from_observation_only_bound":permit,
      "bound_sound_in_low_world":low_debt<=observation_only_bound,
      "bound_sound_in_high_world":high_debt<=observation_only_bound,
      "unsafe_hidden_world_exists":permit and reserve<=high_debt}
