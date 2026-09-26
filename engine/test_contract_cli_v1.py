import json
import subprocess
import sys
import tempfile
from pathlib import Path

from engine.contract_cli_v1 import run_payload


PAYLOAD = {
    "contract": {
        "contract_id": "exact-demo",
        "horizon": 2,
        "requirements": [
            {"future_id": "A"},
            {"future_id": "B"},
            {"future_id": "C"},
        ],
    },
    "backend": {
        "type": "exact_catalogue",
        "model_id": "exact-test-v1",
        "available_now": ["A"],
        "recovery_depths": {"B": 2},
        "irreversible": ["C"],
        "forbidden_bundles": [["B", "C"], ["A", "B", "C"]],
        "repairs": [
            {
                "repair_id": "restore-Y",
                "repairs": ["B", "C"],
                "explanation": "restore Y",
            }
        ],
    },
}


def test_direct():
    result = run_payload(PAYLOAD)
    assert result["decision"] == "REPAIR"
    assert result["immediate_futures"] == ["A"]
    assert result["recoverable_futures"] == [{"future_id": "B", "depth": 2}]
    assert result["irreversible_futures"] == ["C"]
    assert len(result["joint_obstructions"]) == 1
    assert result["joint_obstructions"][0]["bundle"] == ["B", "C"]
    assert result["certificates"][0]["evidence_level"] == "exact"
    assert result["certificates"][0]["verified"] is True


def test_cli():
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "input.json"
        path.write_text(json.dumps(PAYLOAD), encoding="utf-8")
        proc = subprocess.run(
            [sys.executable, "-m", "engine.contract_cli_v1", str(path)],
            capture_output=True,
            text=True,
        )
        assert proc.returncode == 0, proc.stderr
        result = json.loads(proc.stdout)
        assert result["decision"] == "REPAIR"
        assert result["backend_name"] == "exact-test-v1"


if __name__ == "__main__":
    test_direct()
    test_cli()
    print("CONTRACT_CLI_V1_TESTS: PASS (2 tests)")
