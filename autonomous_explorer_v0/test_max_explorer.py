from pathlib import Path
import json

from max_explorer import FreeExplorer, valid_removed, verify_run

HERE = Path(__file__).resolve().parent
fx = json.loads((HERE / "fixtures" / "erdos302_frontier_734.json").read_text())


def test_real_two_steps():
    ex = FreeExplorer(fx["exact_n"], fx["exact_k"], set(fx["witness"]))
    out = ex.run(max_frontier_steps=2)
    assert verify_run(out)
    assert out["final_exact_n"] == 736
    assert out["final_exact_k"] in (609, 610)

    acts = [e for e in out["trace"] if e["phase"] == "ACT"]
    assert acts[0]["n"] == 735
    assert acts[0]["operator"] == "SAFE_ADD"
    assert acts[-1]["n"] == 736
    assert acts[-1]["details"]["global_replay"] == "PASS"

    # If SAT escalation was used, it must be cross-checked and explicitly
    # labelled computational rather than Lean-verified.
    if acts[-1]["operator"] == "EXACT_HITTING_SET":
        assert acts[-1]["details"]["primary_solver"] != acts[-1]["details"]["check_solver"]
        assert acts[-1]["details"]["new_exact_k"] == acts[-1]["details"]["crosscheck_value"]
        assert acts[-1]["details"]["proof_status"] == "EXACT_COMPUTATIONAL_CROSSCHECK_NOT_LEAN"


def test_generic_validity_primitive():
    edges = [(1, 2, 5), (2, 3, 6)]
    assert valid_removed({2}, edges)
    assert not valid_removed({4}, edges)


if __name__ == "__main__":
    test_real_two_steps()
    test_generic_validity_primitive()
    print("AUTONOMOUS_MAX_TESTS_OK")
