from engine.contract_cli_v1 import run_payload
from engine.modechoice14_backend_v1 import (
    LEFT_EXCLUSIVE,
    RIGHT_EXCLUSIVE,
    CORE,
    MINIMAL_OBSTRUCTIONS,
    WORLD_IDS,
)


def payload(ids):
    return {
        "contract": {
            "contract_id": "modechoice14-test",
            "requirements": [
                {"future_id": x, "required": True} for x in ids
            ],
        },
        "backend": {"type": "modechoice14_frozen"},
    }


def test_full_sample_requires_repair():
    result = run_payload(payload(WORLD_IDS))
    assert result["decision"] == "REPAIR"
    assert len(result["joint_obstructions"]) == 12
    assert len(MINIMAL_OBSTRUCTIONS) == 12
    assert all(c["evidence_level"] == "exact" for c in result["certificates"])
    assert all(c["verified"] is True for c in result["certificates"])
    assert result["repairs"][0]["repair_id"] == "add-universal-structural-action"


def test_each_canonical_facet_is_act():
    result_a = run_payload(payload((*LEFT_EXCLUSIVE, *CORE)))
    result_b = run_payload(payload((*CORE, *RIGHT_EXCLUSIVE)))
    assert result_a["decision"] == "ACT"
    assert result_b["decision"] == "ACT"


def test_each_minimal_pair_requires_repair():
    for pair in MINIMAL_OBSTRUCTIONS:
        result = run_payload(payload(pair))
        assert result["decision"] == "REPAIR", (pair, result)
        assert len(result["joint_obstructions"]) == 1


if __name__ == "__main__":
    test_full_sample_requires_repair()
    test_each_canonical_facet_is_act()
    test_each_minimal_pair_requires_repair()
    print("MODECHOICE14_BACKEND_V1_TESTS: PASS (3 groups)")
