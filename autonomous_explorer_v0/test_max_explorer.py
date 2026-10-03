from pathlib import Path
import json
from max_explorer import FreeExplorer, triples_upto, valid_removed, verify_run

HERE=Path(__file__).resolve().parent
fx=json.loads((HERE/"fixtures"/"erdos302_frontier_734.json").read_text())

def test_real():
    ex=FreeExplorer(fx["exact_n"],fx["exact_k"],set(fx["witness"]),max_swap_depth=4)
    out=ex.run(max_frontier_steps=3)
    assert verify_run(out)
    assert out["final_exact_n"] >= 735
    assert out["final_exact_k"] >= 609
    # Every ACT carries a global replay certificate.
    for e in out["trace"]:
        if e["phase"]=="ACT":
            assert e["details"]["global_replay"]=="PASS"
            assert e["details"]["witness_size"]==e["details"]["new_exact_k"]

def test_not_hardcoded():
    # Generic validity primitive on a toy hypergraph.
    edges=[(1,2,5),(2,3,6)]
    assert valid_removed({2},edges)
    assert not valid_removed({4},edges)

if __name__=="__main__":
    test_real(); test_not_hardcoded()
    print("AUTONOMOUS_MAX_TESTS_OK")
