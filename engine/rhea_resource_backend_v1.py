"""Frozen Rhea resource backend for INSACERMO Contract Engine V1.

This adapter encodes the exact finite-inventory resource semantics already
audited in the repository for the 2026-09-26 freeze:

- 10 explicit left-to-right Rhea reactions;
- each consumes exactly one unit of (2S)-naringenin;
- none regenerates that shared resource;
- post-destruction capacity = 9;
- the 10-goal bundle is therefore infeasible;
- every proper subbundle is feasible;
- adding one unit repairs the full bundle.

Scope is deliberately narrow: this is a frozen local Rhea module, not a
whole-cell metabolic impossibility claim.
"""

from __future__ import annotations

from dataclasses import dataclass

from engine.contract_io_v1 import (
    BackendAudit,
    CertificateReceipt,
    ContractInput,
    EvidenceLevel,
    FutureAssessment,
    FutureStatus,
    JointObstruction,
    RepairOption,
)

FROZEN_RHEA_IDS = (
    "RHEA:15434",
    "RHEA:31540",
    "RHEA:32756",
    "RHEA:35488",
    "RHEA:57589",
    "RHEA:61085",
    "RHEA:61097",
    "RHEA:61105",
    "RHEA:65153",
    "RHEA:73288",
)

RESOURCE = "(2S)-naringenin"
BASELINE_RESOURCE_UNITS = 10
DESTRUCTION_UNITS = 1
POST_DESTRUCTION_CAPACITY = BASELINE_RESOURCE_UNITS - DESTRUCTION_UNITS
UNIT_BURDEN = 1
PREAUDIT_R = 1 + POST_DESTRUCTION_CAPACITY // UNIT_BURDEN


@dataclass(frozen=True)
class FrozenRheaResourceModel:
    """Parameters of the frozen exact resource-capacity witness."""

    model_id: str = "rhea-frozen-naringenin-resource-v1"
    repair_cost: float = 1.0


def _minimal_over_capacity(
    ids: list[str],
    capacity: int,
    burden: int,
) -> list[tuple[str, ...]]:
    """Exact minimal over-capacity bundles for uniform positive burden."""
    if burden <= 0:
        raise ValueError("burden must be positive")
    threshold = capacity // burden + 1
    if threshold > len(ids):
        return []
    if threshold == len(ids):
        return [tuple(sorted(ids))]

    # General exact finite catalogue case; small by design for this adapter.
    from itertools import combinations
    return [tuple(c) for c in combinations(sorted(ids), threshold)]


def audit_frozen_rhea_resource(
    contract: ContractInput,
    model: FrozenRheaResourceModel | None = None,
) -> BackendAudit:
    model = model or FrozenRheaResourceModel()
    contract.validate()

    declared = [r.future_id for r in contract.requirements]
    unknown = set(declared) - set(FROZEN_RHEA_IDS)
    if unknown:
        raise ValueError(
            "Rhea frozen backend only accepts the audited reaction ids; "
            f"unknown ids: {sorted(unknown)}"
        )

    # Every individual selected reaction fits in post-destruction capacity.
    assessments = [
        FutureAssessment(
            future_id=fid,
            status=FutureStatus.IMMEDIATE,
            depth=0,
            explanation=(
                f"Single reaction requires {UNIT_BURDEN} unit of {RESOURCE}; "
                f"post-destruction capacity is {POST_DESTRUCTION_CAPACITY}."
            ),
        )
        for fid in declared
    ]

    minimal = _minimal_over_capacity(
        declared,
        POST_DESTRUCTION_CAPACITY,
        UNIT_BURDEN,
    )

    obstructions: list[JointObstruction] = []
    certificates: list[CertificateReceipt] = []
    for i, bundle in enumerate(minimal, start=1):
        total = len(bundle) * UNIT_BURDEN
        cert_id = f"{model.model_id}:capacity:{i}"
        obstructions.append(
            JointObstruction(
                bundle=bundle,
                explanation=(
                    f"Bundle requires {total} units of {RESOURCE}, exceeding "
                    f"post-destruction capacity {POST_DESTRUCTION_CAPACITY}; "
                    "every proper subbundle fits."
                ),
                certificate_id=cert_id,
            )
        )
        certificates.append(
            CertificateReceipt(
                certificate_id=cert_id,
                backend=model.model_id,
                evidence_level=EvidenceLevel.EXACT,
                statement=(
                    f"Uniform burden certificate: (m-1)*{UNIT_BURDEN} <= "
                    f"{POST_DESTRUCTION_CAPACITY} but "
                    f"m*{UNIT_BURDEN} > {POST_DESTRUCTION_CAPACITY}."
                ),
                verified=True,
                reference=(
                    "experiments/rhea_exact_resource_preaudit_depth_v3.py; "
                    "experiments/rhea_high_order_resource_obstruction_v1.py"
                ),
            )
        )

    repairs = []
    if obstructions:
        blocked = tuple(sorted({x for o in obstructions for x in o.bundle}))
        repairs.append(
            RepairOption(
                repair_id="add-one-naringenin-unit",
                repairs=blocked,
                explanation=(
                    f"Restore one unit of {RESOURCE}; capacity returns from "
                    f"{POST_DESTRUCTION_CAPACITY} to {BASELINE_RESOURCE_UNITS}."
                ),
                cost=model.repair_cost,
            )
        )

    return BackendAudit(
        assessments=assessments,
        joint_obstructions=obstructions,
        certificates=certificates,
        repairs=repairs,
        backend_name=model.model_id,
    )
