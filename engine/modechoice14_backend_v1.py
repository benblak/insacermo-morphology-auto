"""Frozen real-data ModeChoice 14-world structural backend for INSACERMO.

Source semantics:
- 210-individual real statsmodels ModeChoice data;
- 14-world structural test sample = first two representatives of each of the
  seven observed actionability patterns;
- four raw travel modes, dominance-compressed to two canonical facets;
- exact obstruction order 2 with 12 minimal obstructions;
- independent brute-force audit matches the compiler;
- exhaustive one-new-action support sweep: universal support 14/14 is the
  unique one-action support that makes all 14 worlds jointly actionable and
  leaves zero residual obstructions.

Important: this is a structural/actionability backend, not a recommendation
about which transport mode a person should choose.
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

WORLD_IDS = (
    "individual_5",
    "individual_15",
    "individual_19",
    "individual_57",
    "individual_16",
    "individual_17",
    "individual_66",
    "individual_106",
    "individual_24",
    "individual_46",
    "individual_1",
    "individual_2",
    "individual_175",
    "individual_191",
)

LEFT_EXCLUSIVE = (
    "individual_5",
    "individual_15",
    "individual_19",
    "individual_57",
    "individual_66",
    "individual_106",
)

RIGHT_EXCLUSIVE = (
    "individual_175",
    "individual_191",
)

CORE = (
    "individual_16",
    "individual_17",
    "individual_24",
    "individual_46",
    "individual_1",
    "individual_2",
)

FACET_A = frozenset((*LEFT_EXCLUSIVE, *CORE))
FACET_B = frozenset((*CORE, *RIGHT_EXCLUSIVE))
MINIMAL_OBSTRUCTIONS = tuple(
    (a, b) for a in LEFT_EXCLUSIVE for b in RIGHT_EXCLUSIVE
)

EXACT_SUPPORTS_TESTED = 16384
UNIVERSAL_REPAIR_SUPPORT = 14
UNIVERSAL_REPAIR_RESIDUAL_OBSTRUCTIONS = 0


@dataclass(frozen=True)
class FrozenModeChoice14Model:
    model_id: str = "modechoice-real-14world-structural-v1"
    repair_cost: float | None = None


def _contained_minimal_obstructions(ids: set[str]) -> list[tuple[str, str]]:
    return [pair for pair in MINIMAL_OBSTRUCTIONS if set(pair).issubset(ids)]


def audit_frozen_modechoice14(
    contract: ContractInput,
    model: FrozenModeChoice14Model | None = None,
) -> BackendAudit:
    model = model or FrozenModeChoice14Model()
    contract.validate()

    declared = [r.future_id for r in contract.requirements]
    declared_set = set(declared)
    unknown = declared_set - set(WORLD_IDS)
    if unknown:
        raise ValueError(
            "ModeChoice frozen backend only accepts the audited 14 representative "
            f"world ids; unknown ids: {sorted(unknown)}"
        )

    assessments = [
        FutureAssessment(
            future_id=fid,
            status=FutureStatus.IMMEDIATE,
            depth=0,
            explanation=(
                "World is present in the frozen real-data-derived actionability "
                "complex; singleton feasibility is exact in this finite sample."
            ),
        )
        for fid in declared
    ]

    contained = _contained_minimal_obstructions(declared_set)
    obstructions: list[JointObstruction] = []
    certificates: list[CertificateReceipt] = []

    for i, pair in enumerate(contained, start=1):
        cert_id = f"{model.model_id}:pair:{i}"
        obstructions.append(
            JointObstruction(
                bundle=pair,
                explanation=(
                    "Exact minimal nonface in the frozen ModeChoice structural "
                    "complex: the two worlds do not share a common admissible "
                    "canonical action."
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
                    "Order-2 obstruction from the exact structural compiler; "
                    "independent brute-force minimal-nonface audit matched exactly."
                ),
                verified=True,
                reference=(
                    "INSACERMO_STRUCTURAL_COMPILER_REAL_MODECHOICE_TEST_V1_REPORT.md"
                ),
            )
        )

    repairs: list[RepairOption] = []
    if contained:
        blocked = tuple(sorted({x for pair in contained for x in pair}))
        repairs.append(
            RepairOption(
                repair_id="add-universal-structural-action",
                repairs=blocked,
                explanation=(
                    "Add the unique one-action universal support over all 14 frozen "
                    "worlds. Exhaustive support sweep tested 16,384/16,384 supports; "
                    "support 14/14 yields zero residual obstructions. This is an "
                    "abstract structural repair, not a transport recommendation."
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
