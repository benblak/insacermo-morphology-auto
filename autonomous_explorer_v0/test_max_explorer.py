from pathlib import Path
import json

from max_explorer import FreeExplorer, valid_witness, verify_run

HERE = Path(__file__).resolve().parent
fx = json.loads((HERE / "fixtures" / "erdos302_frontier_734.json").read_text())


def test_frontier_through_736():
    ex = FreeExplorer(fx["exact_n"], fx["exact_k"], set(fx["witness"]))
    out = ex.run(max_frontier_steps=2)
    assert verify_run(out)
    assert out["final_exact_n"] == 736
    assert out["final_exact_k"] in (609, 610)

    acts = [e for e in out["trace"] if e["phase"] == "ACT"]
    assert acts[0]["n"] == 735
    assert acts[0]["operator"] == "SAFE_ADD"

    last = acts[-1]
    assert last["n"] == 736
    if last["operator"] == "MIP_TARGET_FEASIBILITY":
        assert last["details"]["proof_status"] == "EXACT_COMPUTATIONAL_MIP_CROSSCHECK_NOT_LEAN"


def test_generic_witness_replay():
    edges = [(1, 2, 5), (2, 3, 6)]
    assert valid_witness({1, 3, 4}, edges)
    assert not valid_witness({1, 2, 5}, edges)


if __name__ == "__main__":
    test_frontier_through_736()
    test_generic_witness_replay()
    print("AUTONOMOUS_MIP_TESTS_OK")
