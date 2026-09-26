from engine.contract_cli_v1 import run_payload
from engine.pglib_ieee14_backend_v1 import (
    EXACT_PREAUDIT_DEPTH,
    WITNESS_BUSES,
)


def payload(ids):
    return {
        "contract": {
            "contract_id": "pglib-ieee14-test",
            "requirements": [
                {"future_id": f"BUS:{bus}", "required": True} for bus in ids
            ],
        },
        "backend": {"type": "pglib_ieee14_dc_frozen"},
    }


def test_witness_requires_repair():
    result = run_payload(payload(WITNESS_BUSES))
    assert result["decision"] == "REPAIR"
    assert len(result["joint_obstructions"]) == 1
    assert len(result["joint_obstructions"][0]["bundle"]) == 7
    assert result["certificates"][0]["evidence_level"] == "exact"
    assert result["certificates"][0]["verified"] is True
    assert result["repairs"][0]["repair_id"] == "restore-outaged-branch-1-2"
    assert EXACT_PREAUDIT_DEPTH == 7


def test_every_single_deletion_is_act():
    for omitted in WITNESS_BUSES:
        ids = [b for b in WITNESS_BUSES if b != omitted]
        result = run_payload(payload(ids))
        assert result["decision"] == "ACT", (omitted, result)


def test_bus9_mixed_slice_is_unknown_not_overclaimed():
    ids = ["9", "3", "4"]
    result = run_payload(payload(ids))
    assert result["decision"] == "REFUSE"
    assert set(result["unknown_futures"]) == {"BUS:9", "BUS:3", "BUS:4"}


if __name__ == "__main__":
    test_witness_requires_repair()
    test_every_single_deletion_is_act()
    test_bus9_mixed_slice_is_unknown_not_overclaimed()
    print("PGLIB_IEEE14_BACKEND_V1_TESTS: PASS (3 groups)")
