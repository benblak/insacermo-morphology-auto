from engine.contract_cli_v1 import run_payload
from engine.rhea_resource_backend_v1 import FROZEN_RHEA_IDS, PREAUDIT_R


def payload(ids):
    return {
        "contract": {
            "contract_id": "rhea-frozen-test",
            "requirements": [
                {"future_id": rid, "required": True} for rid in ids
            ],
        },
        "backend": {
            "type": "rhea_resource_frozen",
        },
    }


def test_all_ten_require_repair():
    result = run_payload(payload(FROZEN_RHEA_IDS))
    assert result["decision"] == "REPAIR"
    assert len(result["immediate_futures"]) == 10
    assert len(result["joint_obstructions"]) == 1
    assert len(result["joint_obstructions"][0]["bundle"]) == 10
    assert result["certificates"][0]["evidence_level"] == "exact"
    assert result["certificates"][0]["verified"] is True
    assert result["repairs"][0]["repair_id"] == "add-one-naringenin-unit"
    assert PREAUDIT_R == 10


def test_nine_are_actionable():
    result = run_payload(payload(FROZEN_RHEA_IDS[:9]))
    assert result["decision"] == "ACT"
    assert len(result["joint_obstructions"]) == 0


if __name__ == "__main__":
    test_all_ten_require_repair()
    test_nine_are_actionable()
    print("RHEA_RESOURCE_BACKEND_V1_TESTS: PASS (2 tests)")
