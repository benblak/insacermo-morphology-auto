from __future__ import annotations

from dataclasses import dataclass, asdict
from typing import Any, Iterable
import hashlib
import json

from final_integration_v1.final_integration_v1 import CanonicalIntegration

VERSION = "INSACERMO_PROOF_CARRYING_MULTI_PROBE_RUNTIME_V2"


def h(obj: Any) -> str:
    return hashlib.sha256(
        json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
    ).hexdigest()


class MultiProbeRuntimeError(ValueError):
    pass


@dataclass(frozen=True)
class PlannerKernelRef:
    run_id: int = 37158868792
    commit: str = "3f676d4b8f8ea010067d353b647ae9223d1fc4b0"
    theorem_scope: str = "FINITE_AUDITED_CANDIDATES"
    lean_version: str = "4.33.1"


@dataclass(frozen=True)
class PlanCandidate:
    plan_id: str
    prices: tuple[int, ...]
    contract_hash: str
    contract_receipt_hash: str

    def __post_init__(self):
        if not self.plan_id:
            raise MultiProbeRuntimeError("EMPTY_PLAN_ID")
        if not self.contract_hash or not self.contract_receipt_hash:
            raise MultiProbeRuntimeError("MISSING_CONTRACT_BINDING")
        if any((not isinstance(x, int)) or isinstance(x, bool) or x < 0 for x in self.prices):
            raise MultiProbeRuntimeError("INVALID_NONNEGATIVE_INTEGER_PRICE")

    @property
    def total_price(self) -> int:
        return sum(self.prices)

    def payload(self) -> dict[str, Any]:
        d = asdict(self)
        d["prices"] = list(self.prices)
        d["total_price"] = self.total_price
        d["candidate_hash"] = h(d)
        return d


def _canonical_candidates(candidates: Iterable[PlanCandidate]) -> list[PlanCandidate]:
    xs = list(candidates)
    if not xs:
        raise MultiProbeRuntimeError("NO_AUDITED_CANDIDATES")
    ids = [x.plan_id for x in xs]
    if len(ids) != len(set(ids)):
        raise MultiProbeRuntimeError("DUPLICATE_PLAN_ID")
    return sorted(xs, key=lambda x: x.plan_id)


def select_minimum_price(candidates: Iterable[PlanCandidate]) -> PlanCandidate:
    xs = _canonical_candidates(candidates)
    return min(xs, key=lambda x: (x.total_price, len(x.prices), x.prices, x.plan_id))


def audited_set_hash(candidates: Iterable[PlanCandidate]) -> str:
    xs = _canonical_candidates(candidates)
    return h([x.payload() for x in xs])


class ProofCarryingMultiProbeRuntime:
    def __init__(self, *, contract_hash: str, kernel: PlannerKernelRef = PlannerKernelRef()):
        if not contract_hash:
            raise MultiProbeRuntimeError("EMPTY_CONTRACT_HASH")
        self.contract_hash = str(contract_hash)
        self.kernel = kernel

    def evaluate(
        self,
        *,
        base_integration_certificate: dict[str, Any],
        candidates: Iterable[PlanCandidate],
        rho0: int,
        debt_before: int,
    ) -> dict[str, Any]:
        if not isinstance(rho0, int) or isinstance(rho0, bool) or rho0 < 0:
            raise MultiProbeRuntimeError("INVALID_RESERVE")
        if not isinstance(debt_before, int) or isinstance(debt_before, bool) or debt_before < 0:
            raise MultiProbeRuntimeError("INVALID_DEBT_BEFORE")

        base_verification = CanonicalIntegration.verify_integration_certificate(
            base_integration_certificate
        )
        if not base_verification["valid"]:
            raise MultiProbeRuntimeError("INVALID_BASE_INTEGRATION_CERTIFICATE")
        if base_integration_certificate.get("contract_hash") != self.contract_hash:
            raise MultiProbeRuntimeError("BASE_CONTRACT_MISMATCH")

        xs = _canonical_candidates(candidates)
        for x in xs:
            if x.contract_hash != self.contract_hash:
                raise MultiProbeRuntimeError("CANDIDATE_CONTRACT_MISMATCH")

        chosen = select_minimum_price(xs)
        total_price = chosen.total_price
        debt_after = debt_before + total_price
        reserve_left = max(rho0 - debt_after, 0)
        affordable = debt_after < rho0
        verdict = "EXECUTE" if affordable else "REFUSE"

        obligations = {
            "base_integration_certificate_valid": True,
            "candidate_contracts_match": True,
            "chosen_is_member": chosen.plan_id in {x.plan_id for x in xs},
            "chosen_has_minimum_price": all(total_price <= x.total_price for x in xs),
            "price_recomputed": total_price == sum(chosen.prices),
            "debt_recomputed": debt_after == debt_before + total_price,
            "strict_reserve_rule": affordable,
            "refuse_excludes_all_audited_candidates": (
                False if affordable
                else all(debt_before + x.total_price >= rho0 for x in xs)
            ),
        }

        body = {
            "runtime_version": VERSION,
            "contract_hash": self.contract_hash,
            "base_integration_hash": base_integration_certificate.get("integration_hash"),
            "base_temporal_verdict": base_integration_certificate.get("temporal_verdict"),
            "rho0": rho0,
            "debt_before": debt_before,
            "audited_candidates": [x.payload() for x in xs],
            "audited_set_hash": audited_set_hash(xs),
            "chosen_plan": chosen.payload(),
            "total_price": total_price,
            "debt_after": debt_after,
            "reserve_left": reserve_left,
            "verdict": verdict,
            "proof_obligations": obligations,
            "kernel_reference": asdict(self.kernel),
            "scope": (
                "REFUSE excludes only the finite contract-bound candidate set embedded "
                "and hashed in this certificate."
            ),
        }
        body["certificate_hash"] = h(body)
        return body

    @staticmethod
    def verify(cert: dict[str, Any]) -> dict[str, Any]:
        failures: list[str] = []

        recorded = cert.get("certificate_hash")
        body = {k: v for k, v in cert.items() if k != "certificate_hash"}
        if recorded != h(body):
            failures.append("HASH_MISMATCH")

        candidates = cert.get("audited_candidates")
        if not isinstance(candidates, list) or not candidates:
            failures.append("NO_AUDITED_CANDIDATES")
            return {"valid": False, "failures": failures}

        try:
            normalized = []
            for raw in candidates:
                p = PlanCandidate(
                    plan_id=raw["plan_id"],
                    prices=tuple(raw["prices"]),
                    contract_hash=raw["contract_hash"],
                    contract_receipt_hash=raw["contract_receipt_hash"],
                )
                if raw.get("candidate_hash") != p.payload()["candidate_hash"]:
                    failures.append("CANDIDATE_HASH_MISMATCH:" + p.plan_id)
                if raw.get("total_price") != p.total_price:
                    failures.append("CANDIDATE_PRICE_MISMATCH:" + p.plan_id)
                normalized.append(p)
            xs = _canonical_candidates(normalized)
        except Exception as exc:
            failures.append("CANDIDATE_PARSE_ERROR:" + type(exc).__name__)
            return {"valid": False, "failures": failures}

        if cert.get("audited_set_hash") != audited_set_hash(xs):
            failures.append("AUDITED_SET_HASH_MISMATCH")

        contract_hash = cert.get("contract_hash")
        if any(x.contract_hash != contract_hash for x in xs):
            failures.append("CANDIDATE_CONTRACT_MISMATCH")

        chosen = select_minimum_price(xs)
        chosen_raw = cert.get("chosen_plan") or {}
        if chosen_raw.get("candidate_hash") != chosen.payload()["candidate_hash"]:
            failures.append("CHOSEN_NOT_CANONICAL_MINIMUM")

        total_price = chosen.total_price
        if cert.get("total_price") != total_price:
            failures.append("TOTAL_PRICE_MISMATCH")

        rho0 = cert.get("rho0")
        debt_before = cert.get("debt_before")
        if not isinstance(rho0, int) or not isinstance(debt_before, int):
            failures.append("INVALID_NUMERIC_FIELDS")
            return {"valid": False, "failures": failures}

        debt_after = debt_before + total_price
        if cert.get("debt_after") != debt_after:
            failures.append("DEBT_AFTER_MISMATCH")
        if cert.get("reserve_left") != max(rho0 - debt_after, 0):
            failures.append("RESERVE_LEFT_MISMATCH")

        affordable = debt_after < rho0
        expected_verdict = "EXECUTE" if affordable else "REFUSE"
        if cert.get("verdict") != expected_verdict:
            failures.append("VERDICT_MISMATCH")

        po = cert.get("proof_obligations") or {}
        required_true = [
            "base_integration_certificate_valid",
            "candidate_contracts_match",
            "chosen_is_member",
            "chosen_has_minimum_price",
            "price_recomputed",
            "debt_recomputed",
        ]
        for key in required_true:
            if po.get(key) is not True:
                failures.append("OBLIGATION:" + key)

        if expected_verdict == "EXECUTE":
            if po.get("strict_reserve_rule") is not True:
                failures.append("OBLIGATION:strict_reserve_rule")
        else:
            if po.get("strict_reserve_rule") is not False:
                failures.append("OBLIGATION:strict_reserve_rule_false")
            if po.get("refuse_excludes_all_audited_candidates") is not True:
                failures.append("OBLIGATION:refuse_excludes_all_audited_candidates")
            if not all(debt_before + x.total_price >= rho0 for x in xs):
                failures.append("REFUSE_SCOPE_NOT_RECOMPUTABLE")

        return {"valid": not failures, "failures": failures}
