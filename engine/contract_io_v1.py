"""INSACERMO Contract Engine I/O V1.

This module is a presentation/orchestration layer for the modern INSACERMO
engine.  It does NOT reimplement the Lean kernel or domain certificate
mathematics.  A backend supplies future assessments, certificates, probes and
repairs; this layer validates them and exposes a stable, JSON-serialisable
contract result for CLI/web front-ends.

Frozen semantic reference: INSACERMO engine freeze 2026-09-26.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from enum import Enum
import json
from typing import Iterable, Optional


class Decision(str, Enum):
    ACT = "ACT"
    PROBE = "PROBE"
    REPAIR = "REPAIR"
    REFUSE = "REFUSE"


class FutureStatus(str, Enum):
    IMMEDIATE = "immediate"
    RECOVERABLE = "recoverable"
    IRREVERSIBLE = "irreversible"
    UNKNOWN = "unknown"


class EvidenceLevel(str, Enum):
    FORMAL = "formal"
    EXACT = "exact"
    EXHAUSTIVE = "exhaustive"
    EMPIRICAL = "empirical"
    HEURISTIC = "heuristic"
    DECLARED = "declared"


@dataclass(frozen=True)
class FutureRequirement:
    future_id: str
    required: bool = True
    weight: float = 1.0
    deadline: Optional[int] = None
    description: str = ""


@dataclass(frozen=True)
class FutureAssessment:
    future_id: str
    status: FutureStatus
    depth: Optional[int] = None
    explanation: str = ""

    def validate(self) -> None:
        if self.depth is not None and self.depth < 0:
            raise ValueError(f"negative depth for {self.future_id}")
        if self.status is FutureStatus.IMMEDIATE and self.depth not in (None, 0):
            raise ValueError(
                f"immediate future {self.future_id} must have depth 0 or None"
            )
        if self.status is FutureStatus.RECOVERABLE and self.depth is None:
            raise ValueError(
                f"recoverable future {self.future_id} requires a finite depth"
            )
        if self.status in (FutureStatus.IRREVERSIBLE, FutureStatus.UNKNOWN) and self.depth is not None:
            raise ValueError(
                f"{self.status.value} future {self.future_id} cannot carry finite depth"
            )


@dataclass(frozen=True)
class JointObstruction:
    bundle: tuple[str, ...]
    explanation: str
    certificate_id: Optional[str] = None


@dataclass(frozen=True)
class CertificateReceipt:
    certificate_id: str
    backend: str
    evidence_level: EvidenceLevel
    statement: str
    verified: bool = False
    reference: str = ""


@dataclass(frozen=True)
class ProbeOption:
    probe_id: str
    resolves: tuple[str, ...]
    explanation: str


@dataclass(frozen=True)
class RepairOption:
    repair_id: str
    repairs: tuple[str, ...]
    explanation: str
    cost: Optional[float] = None


@dataclass
class ContractInput:
    requirements: list[FutureRequirement]
    horizon: Optional[int] = None
    contract_id: str = "default"

    def validate(self) -> None:
        ids = [r.future_id for r in self.requirements]
        if not ids:
            raise ValueError("contract must contain at least one future requirement")
        if len(ids) != len(set(ids)):
            raise ValueError("future requirement ids must be unique")
        if self.horizon is not None and self.horizon < 0:
            raise ValueError("horizon must be nonnegative")

    def effective_deadline(self, req: FutureRequirement) -> Optional[int]:
        return req.deadline if req.deadline is not None else self.horizon


@dataclass
class BackendAudit:
    assessments: list[FutureAssessment]
    joint_obstructions: list[JointObstruction] = field(default_factory=list)
    certificates: list[CertificateReceipt] = field(default_factory=list)
    probes: list[ProbeOption] = field(default_factory=list)
    repairs: list[RepairOption] = field(default_factory=list)
    backend_name: str = "unspecified"

    def validate(self, contract: ContractInput) -> None:
        known = {r.future_id for r in contract.requirements}
        seen: set[str] = set()
        for a in self.assessments:
            a.validate()
            if a.future_id not in known:
                raise ValueError(f"assessment for undeclared future {a.future_id}")
            if a.future_id in seen:
                raise ValueError(f"duplicate assessment for {a.future_id}")
            seen.add(a.future_id)

        missing = known - seen
        if missing:
            raise ValueError(f"missing assessments for: {sorted(missing)}")

        for obstruction in self.joint_obstructions:
            unknown = set(obstruction.bundle) - known
            if unknown:
                raise ValueError(
                    f"joint obstruction contains undeclared futures: {sorted(unknown)}"
                )


@dataclass
class ContractResult:
    contract_id: str
    decision: Decision
    backend_name: str
    immediate_futures: list[str]
    recoverable_futures: list[dict]
    irreversible_futures: list[str]
    unknown_futures: list[str]
    deadline_violations: list[str]
    joint_obstructions: list[JointObstruction]
    probes: list[ProbeOption]
    repairs: list[RepairOption]
    certificates: list[CertificateReceipt]
    reasons: list[str]

    def to_dict(self) -> dict:
        def normalise(value):
            if isinstance(value, Enum):
                return value.value
            if isinstance(value, tuple):
                return list(value)
            if isinstance(value, list):
                return [normalise(v) for v in value]
            if isinstance(value, dict):
                return {k: normalise(v) for k, v in value.items()}
            if hasattr(value, "__dataclass_fields__"):
                return normalise(asdict(value))
            return value

        return normalise(asdict(self))

    def to_json(self, *, indent: int = 2) -> str:
        return json.dumps(self.to_dict(), ensure_ascii=False, indent=indent)


def _covered(targets: Iterable[str], options: Iterable[tuple[str, ...]]) -> bool:
    covered: set[str] = set()
    for option in options:
        covered.update(option)
    return set(targets).issubset(covered)


def evaluate_contract(contract: ContractInput, audit: BackendAudit) -> ContractResult:
    """Build a front-end decision from backend-certified assessments.

    Decision policy:
    - unknown required futures -> PROBE when probes cover them, otherwise REFUSE;
    - required irreversible/deadline-violating futures or joint obstructions ->
      REPAIR when declared repairs cover the affected named futures, otherwise
      REFUSE;
    - otherwise -> ACT.

    This policy is intentionally conservative.  It is an orchestration rule,
    not a substitute for the backend theorem/certificate semantics.
    """

    contract.validate()
    audit.validate(contract)

    req_by_id = {r.future_id: r for r in contract.requirements}
    assessment_by_id = {a.future_id: a for a in audit.assessments}

    immediate: list[str] = []
    recoverable: list[dict] = []
    irreversible: list[str] = []
    unknown: list[str] = []
    deadline_violations: list[str] = []

    required_unknown: list[str] = []
    required_blocked: list[str] = []

    for req in contract.requirements:
        a = assessment_by_id[req.future_id]
        if a.status is FutureStatus.IMMEDIATE:
            immediate.append(req.future_id)
        elif a.status is FutureStatus.RECOVERABLE:
            recoverable.append({"future_id": req.future_id, "depth": a.depth})
            deadline = contract.effective_deadline(req)
            if deadline is not None and a.depth is not None and a.depth > deadline:
                deadline_violations.append(req.future_id)
                if req.required:
                    required_blocked.append(req.future_id)
        elif a.status is FutureStatus.IRREVERSIBLE:
            irreversible.append(req.future_id)
            if req.required:
                required_blocked.append(req.future_id)
        else:
            unknown.append(req.future_id)
            if req.required:
                required_unknown.append(req.future_id)

    required_joint_obstructions = [
        obstruction
        for obstruction in audit.joint_obstructions
        if all(req_by_id[f].required for f in obstruction.bundle)
    ]
    for obstruction in required_joint_obstructions:
        required_blocked.extend(obstruction.bundle)

    required_blocked = sorted(set(required_blocked))
    required_unknown = sorted(set(required_unknown))

    reasons: list[str] = []

    if required_unknown:
        if _covered(required_unknown, (p.resolves for p in audit.probes)):
            decision = Decision.PROBE
            reasons.append(
                "Required future status is not yet certified; declared probes cover "
                "the unresolved requirements."
            )
        else:
            decision = Decision.REFUSE
            reasons.append(
                "Required future status is not certified and no declared probe covers "
                "all unresolved requirements."
            )
    elif required_blocked or required_joint_obstructions:
        repair_targets = required_blocked
        if _covered(repair_targets, (r.repairs for r in audit.repairs)):
            decision = Decision.REPAIR
            reasons.append(
                "At least one required future is blocked or a required joint bundle "
                "is obstructed; declared repairs cover the affected requirements."
            )
        else:
            decision = Decision.REFUSE
            reasons.append(
                "The current backend audit cannot certify the declared hard contract: "
                "a required future/deadline or joint bundle is blocked."
            )
    else:
        decision = Decision.ACT
        reasons.append(
            "All declared required futures are certified immediate or recoverable "
            "within their applicable deadline, with no required joint obstruction."
        )

    if audit.certificates:
        verified_count = sum(1 for c in audit.certificates if c.verified)
        reasons.append(
            f"{verified_count}/{len(audit.certificates)} supplied certificate receipts "
            "are marked verified by their backend."
        )

    return ContractResult(
        contract_id=contract.contract_id,
        decision=decision,
        backend_name=audit.backend_name,
        immediate_futures=sorted(immediate),
        recoverable_futures=sorted(
            recoverable, key=lambda x: (x["depth"], x["future_id"])
        ),
        irreversible_futures=sorted(irreversible),
        unknown_futures=sorted(unknown),
        deadline_violations=sorted(deadline_violations),
        joint_obstructions=audit.joint_obstructions,
        probes=audit.probes,
        repairs=audit.repairs,
        certificates=audit.certificates,
        reasons=reasons,
    )
