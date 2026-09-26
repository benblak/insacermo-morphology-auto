from engine.contract_io_v1 import (
    BackendAudit,
    ContractInput,
    FutureAssessment,
    FutureRequirement,
    FutureStatus,
    JointObstruction,
    ProbeOption,
    RepairOption,
    Decision,
    evaluate_contract,
)


def contract(*ids: str, horizon: int | None = 2) -> ContractInput:
    return ContractInput(
        requirements=[FutureRequirement(x) for x in ids],
        horizon=horizon,
        contract_id="test",
    )


def test_act():
    result = evaluate_contract(
        contract("a", "b", horizon=2),
        BackendAudit(
            assessments=[
                FutureAssessment("a", FutureStatus.IMMEDIATE, depth=0),
                FutureAssessment("b", FutureStatus.RECOVERABLE, depth=2),
            ],
            backend_name="test",
        ),
    )
    assert result.decision is Decision.ACT


def test_probe():
    result = evaluate_contract(
        contract("a"),
        BackendAudit(
            assessments=[FutureAssessment("a", FutureStatus.UNKNOWN)],
            probes=[ProbeOption("sense-a", ("a",), "observe a")],
        ),
    )
    assert result.decision is Decision.PROBE


def test_repair_irreversible():
    result = evaluate_contract(
        contract("a"),
        BackendAudit(
            assessments=[FutureAssessment("a", FutureStatus.IRREVERSIBLE)],
            repairs=[RepairOption("restore-a", ("a",), "restore capability a")],
        ),
    )
    assert result.decision is Decision.REPAIR


def test_refuse_without_probe_or_repair():
    result = evaluate_contract(
        contract("a"),
        BackendAudit(
            assessments=[FutureAssessment("a", FutureStatus.UNKNOWN)],
        ),
    )
    assert result.decision is Decision.REFUSE


def test_deadline_violation_requires_repair():
    result = evaluate_contract(
        contract("a", horizon=1),
        BackendAudit(
            assessments=[FutureAssessment("a", FutureStatus.RECOVERABLE, depth=3)],
            repairs=[RepairOption("accelerate-a", ("a",), "recover a before deadline")],
        ),
    )
    assert result.decision is Decision.REPAIR
    assert result.deadline_violations == ["a"]


def test_joint_obstruction_is_not_hidden_by_singletons():
    result = evaluate_contract(
        contract("a", "b"),
        BackendAudit(
            assessments=[
                FutureAssessment("a", FutureStatus.IMMEDIATE, depth=0),
                FutureAssessment("b", FutureStatus.IMMEDIATE, depth=0),
            ],
            joint_obstructions=[
                JointObstruction(("a", "b"), "a and b cannot be guaranteed jointly")
            ],
        ),
    )
    assert result.decision is Decision.REFUSE
    assert len(result.joint_obstructions) == 1


def test_joint_obstruction_can_route_to_repair():
    result = evaluate_contract(
        contract("a", "b"),
        BackendAudit(
            assessments=[
                FutureAssessment("a", FutureStatus.IMMEDIATE, depth=0),
                FutureAssessment("b", FutureStatus.IMMEDIATE, depth=0),
            ],
            joint_obstructions=[
                JointObstruction(("a", "b"), "joint obstruction")
            ],
            repairs=[
                RepairOption("joint-fix", ("a", "b"), "restore joint feasibility")
            ],
        ),
    )
    assert result.decision is Decision.REPAIR


if __name__ == "__main__":
    tests = [
        test_act,
        test_probe,
        test_repair_irreversible,
        test_refuse_without_probe_or_repair,
        test_deadline_violation_requires_repair,
        test_joint_obstruction_is_not_hidden_by_singletons,
        test_joint_obstruction_can_route_to_repair,
    ]
    for test in tests:
        test()
    print(f"CONTRACT_IO_V1_TESTS: PASS ({len(tests)} tests)")
