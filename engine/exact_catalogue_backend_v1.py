"""Exact finite-catalogue backend for the INSACERMO contract engine.

The backend is exact **relative to the supplied finite model**.  It does not
claim that the supplied model is a faithful representation of an external
physical/biological/economic system.

It converts:
- immediate futures,
- finite recovery depths,
- irreversible futures,
- explicit forbidden future bundles,
- optional probes / repairs

into the stable BackendAudit consumed by contract_io_v1.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable

from engine.contract_io_v1 import (
    BackendAudit,
    CertificateReceipt,
    EvidenceLevel,
    FutureAssessment,
    FutureStatus,
    JointObstruction,
    ProbeOption,
    RepairOption,
    ContractInput,
)


@dataclass
class ExactCatalogueModel:
    available_now: set[str] = field(default_factory=set)
    recovery_depths: dict[str, int] = field(default_factory=dict)
    irreversible: set[str] = field(default_factory=set)
    forbidden_bundles: list[tuple[str, ...]] = field(default_factory=list)
    probes: list[ProbeOption] = field(default_factory=list)
    repairs: list[RepairOption] = field(default_factory=list)
    model_id: str = "exact-catalogue-v1"

    def validate(self, contract: ContractInput) -> None:
        declared = {r.future_id for r in contract.requirements}

        sources = {
            "available_now": set(self.available_now),
            "recovery_depths": set(self.recovery_depths),
            "irreversible": set(self.irreversible),
        }
        for name, ids in sources.items():
            unknown = ids - declared
            if unknown:
                raise ValueError(
                    f"{name} contains undeclared futures: {sorted(unknown)}"
                )

        overlaps = (
            (sources["available_now"] & sources["recovery_depths"])
            | (sources["available_now"] & sources["irreversible"])
            | (sources["recovery_depths"] & sources["irreversible"])
        )
        if overlaps:
            raise ValueError(
                "future status sources must be disjoint; overlap: "
                f"{sorted(overlaps)}"
            )

        for future_id, depth in self.recovery_depths.items():
            if not isinstance(depth, int) or depth < 1:
                raise ValueError(
                    f"recovery depth for {future_id} must be an integer >= 1"
                )

        for bundle in self.forbidden_bundles:
            if not bundle:
                raise ValueError("forbidden bundles must be nonempty")
            unknown = set(bundle) - declared
            if unknown:
                raise ValueError(
                    "forbidden bundle contains undeclared futures: "
                    f"{sorted(unknown)}"
                )


def _canonical_bundle(bundle: Iterable[str]) -> tuple[str, ...]:
    return tuple(sorted(set(bundle)))


def _minimal_forbidden(
    bundles: Iterable[tuple[str, ...]],
) -> list[tuple[str, ...]]:
    """Return inclusion-minimal forbidden bundles exactly."""
    unique = sorted(
        {_canonical_bundle(bundle) for bundle in bundles},
        key=lambda b: (len(b), b),
    )
    minimal: list[tuple[str, ...]] = []
    for bundle in unique:
        s = set(bundle)
        if any(set(existing).issubset(s) for existing in minimal):
            continue
        minimal.append(bundle)
    return minimal


def audit_exact_catalogue(
    contract: ContractInput,
    model: ExactCatalogueModel,
) -> BackendAudit:
    contract.validate()
    model.validate(contract)

    assessments: list[FutureAssessment] = []
    for req in contract.requirements:
        fid = req.future_id
        if fid in model.available_now:
            assessments.append(
                FutureAssessment(
                    future_id=fid,
                    status=FutureStatus.IMMEDIATE,
                    depth=0,
                    explanation="Available in the supplied finite model.",
                )
            )
        elif fid in model.recovery_depths:
            d = model.recovery_depths[fid]
            assessments.append(
                FutureAssessment(
                    future_id=fid,
                    status=FutureStatus.RECOVERABLE,
                    depth=d,
                    explanation=(
                        f"First declared recovery depth in the finite model: {d}."
                    ),
                )
            )
        elif fid in model.irreversible:
            assessments.append(
                FutureAssessment(
                    future_id=fid,
                    status=FutureStatus.IRREVERSIBLE,
                    explanation=(
                        "Declared irrecoverable in the supplied finite model."
                    ),
                )
            )
        else:
            assessments.append(
                FutureAssessment(
                    future_id=fid,
                    status=FutureStatus.UNKNOWN,
                    explanation=(
                        "No immediate, finite-depth, or irreversible status was "
                        "supplied for this future."
                    ),
                )
            )

    minimal = _minimal_forbidden(model.forbidden_bundles)
    obstructions: list[JointObstruction] = []
    certificates: list[CertificateReceipt] = []

    for i, bundle in enumerate(minimal, start=1):
        cert_id = f"{model.model_id}:forbidden:{i}"
        obstructions.append(
            JointObstruction(
                bundle=bundle,
                explanation=(
                    "Inclusion-minimal forbidden future bundle in the supplied "
                    "finite catalogue."
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
                    "This bundle is explicitly forbidden and no supplied proper "
                    "forbidden subbundle exists."
                ),
                verified=True,
                reference="exact finite-catalogue set computation",
            )
        )

    return BackendAudit(
        assessments=assessments,
        joint_obstructions=obstructions,
        certificates=certificates,
        probes=model.probes,
        repairs=model.repairs,
        backend_name=model.model_id,
    )


def model_from_dict(data: dict) -> ExactCatalogueModel:
    return ExactCatalogueModel(
        available_now=set(data.get("available_now", [])),
        recovery_depths={
            str(k): int(v) for k, v in data.get("recovery_depths", {}).items()
        },
        irreversible=set(data.get("irreversible", [])),
        forbidden_bundles=[
            tuple(str(x) for x in bundle)
            for bundle in data.get("forbidden_bundles", [])
        ],
        probes=[
            ProbeOption(
                probe_id=p["probe_id"],
                resolves=tuple(p.get("resolves", [])),
                explanation=p.get("explanation", ""),
            )
            for p in data.get("probes", [])
        ],
        repairs=[
            RepairOption(
                repair_id=r["repair_id"],
                repairs=tuple(r.get("repairs", [])),
                explanation=r.get("explanation", ""),
                cost=r.get("cost"),
            )
            for r in data.get("repairs", [])
        ],
        model_id=data.get("model_id", "exact-catalogue-v1"),
    )
