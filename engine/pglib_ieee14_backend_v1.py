"""Frozen exact PGLib IEEE-14 DC backend for INSACERMO Contract Engine V1.

This adapter exposes the exact certificate-only witness already audited in the
repository. It does NOT rerun the full PGLib extreme-ray enumeration at request
time; it packages the frozen, reproducible result into the common contract API.

Frozen exact result:
- goal catalogue: buses 3,9,4,2,14,13,6,10
- outage index 0, branch 1-2
- cross-certified minimal failed bundle:
  buses 3,4,2,14,13,6,10
- all 127 proper subbundles of that 7-bus witness accepted by all post-outage
  exact rays
- exact pre-audit / certificate-only depth = 7
- 80,276 exact outage extreme rays enumerated in V3
- no order-8 compatible minimal ray
- baseline accepts the 7-bus witness

Scope: exact for the encoded DC LP and fixed catalogue, not full AC security.
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

CATALOGUE_BUSES = ("3", "9", "4", "2", "14", "13", "6", "10")
WITNESS_BUSES = ("3", "4", "2", "14", "13", "6", "10")
WITNESS_SET = frozenset(WITNESS_BUSES)
OUTAGE_INDEX = 0
OUTAGE_BRANCH = (1, 2)
EXACT_PREAUDIT_DEPTH = 7
TOTAL_EXACT_EXTREME_RAYS = 80276
PROPER_SUBBUNDLES_CHECKED = 127


@dataclass(frozen=True)
class FrozenPglibIEEE14Model:
    model_id: str = "pglib-ieee14-dc-exact-witness-v1"
    repair_cost: float | None = None


def _normalise_future_id(fid: str) -> str:
    value = str(fid)
    if value.startswith("BUS:"):
        value = value.split(":", 1)[1]
    return value


def audit_frozen_pglib_ieee14(
    contract: ContractInput,
    model: FrozenPglibIEEE14Model | None = None,
) -> BackendAudit:
    model = model or FrozenPglibIEEE14Model()
    contract.validate()

    declared_raw = [r.future_id for r in contract.requirements]
    normalised = [_normalise_future_id(x) for x in declared_raw]
    mapping = dict(zip(declared_raw, normalised))

    unknown = set(normalised) - set(CATALOGUE_BUSES)
    if unknown:
        raise ValueError(
            "PGLib frozen backend only accepts the audited IEEE-14 goal buses; "
            f"unknown buses: {sorted(unknown)}"
        )

    # The V4 certificate-only closure proves every proper subbundle of the
    # 7-bus witness feasible after outage. The witness itself is infeasible.
    # We therefore only make an exact ACT/REPAIR claim for contracts contained
    # in the witness or containing the full witness. Contracts involving bus 9
    # without the full witness are outside this frozen certificate slice.
    declared_set = set(normalised)
    in_certified_slice = declared_set.issubset(WITNESS_SET) or WITNESS_SET.issubset(
        declared_set
    )

    assessments = []
    if in_certified_slice:
        assessments = [
            FutureAssessment(
                future_id=raw,
                status=FutureStatus.IMMEDIATE,
                depth=0,
                explanation=(
                    "Singleton requirement lies in the frozen IEEE-14 exact DC "
                    "certificate slice for outage branch 1-2."
                ),
            )
            for raw in declared_raw
        ]
    else:
        assessments = [
            FutureAssessment(
                future_id=raw,
                status=FutureStatus.UNKNOWN,
                explanation=(
                    "This bus combination was not closed by the frozen V4 "
                    "cross-certificate witness; no stronger claim is made."
                ),
            )
            for raw in declared_raw
        ]

    obstructions: list[JointObstruction] = []
    certificates: list[CertificateReceipt] = []
    repairs: list[RepairOption] = []

    if WITNESS_SET.issubset(declared_set):
        raw_by_norm = {norm: raw for raw, norm in mapping.items()}
        bundle = tuple(raw_by_norm[b] for b in WITNESS_BUSES)
        cert_id = f"{model.model_id}:outage0:witness7"

        obstructions.append(
            JointObstruction(
                bundle=bundle,
                explanation=(
                    "Exact dual-only cross-certified minimal DC infeasibility "
                    "under outage of branch 1-2."
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
                    "7-bus witness is rejected by an exact post-outage Farkas "
                    "ray; all 127 proper subbundles are accepted by every "
                    "post-outage exact ray; baseline accepts the full witness. "
                    "Exact certificate-only depth = 7."
                ),
                verified=True,
                reference=(
                    "experiments/pglib_ieee14_dc_exact_preaudit_depth_v3.py; "
                    "experiments/pglib_ieee14_dc_exact_certificate_only_depth_v4.py"
                ),
            )
        )
        repairs.append(
            RepairOption(
                repair_id="restore-outaged-branch-1-2",
                repairs=bundle,
                explanation=(
                    "Restore the audited outaged branch 1-2, returning to the "
                    "baseline DC model in which the full witness is accepted by "
                    "all exact baseline rays."
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
