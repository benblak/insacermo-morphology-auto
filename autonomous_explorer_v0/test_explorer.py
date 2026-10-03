import json
from pathlib import Path

from explorer import (
    FrontierState,
    AutonomousFrontierExplorer,
    reciprocal_endpoint_edges,
    verify_trace,
)


HERE = Path(__file__).resolve().parent


def load_fixture():
    return json.loads((HERE / "fixtures" / "erdos302_frontier_734.json").read_text())


def test_autonomous_frontier_discovers_735_then_refuses_736():
    fx = load_fixture()
    state = FrontierState(
        exact_n=fx["exact_n"],
        exact_k=fx["exact_k"],
        witness=set(fx["witness"]),
    )
    ex = AutonomousFrontierExplorer(state, reciprocal_endpoint_edges)
    out = ex.run_until_refuse(max_steps=4)

    assert verify_trace(out)["valid"]
    assert out["final_exact_n"] == 735
    assert out["final_exact_k"] == 609

    phases = [(e["phase"], e["n"], e["status"]) for e in out["trace"]]
    assert phases == [
        ("PROBE", 735, "OBSERVED"),
        ("ACT", 735, "EXACT_FRONTIER_EXTENDED"),
        ("PROBE", 736, "OBSERVED"),
        ("REFUSE", 736, "EXACTNESS_NOT_CERTIFIED"),
    ]

    p735 = out["trace"][0]["details"]
    assert p735["endpoint_edges"] == [[210, 294, 735], [294, 490, 735]]
    assert p735["active_obstructions"] == []
    assert p735["common_missing_blockers"] == [294]

    p736 = out["trace"][2]["details"]
    assert [224, 322, 736] in p736["active_obstructions"]


def test_scheduler_is_not_hardcoded_to_735():
    # Tiny synthetic endpoint generator: no obstruction at 5, one at 6.
    def toy(c):
        if c == 5:
            return [(1, 4, 5)]
        if c == 6:
            return [(2, 3, 6)]
        return []

    state = FrontierState(exact_n=4, exact_k=2, witness={2, 3})
    ex = AutonomousFrontierExplorer(state, toy)
    out = ex.run_until_refuse(max_steps=3)

    assert out["final_exact_n"] == 5
    assert out["final_exact_k"] == 3
    assert out["trace"][-1]["phase"] == "REFUSE"
    assert out["trace"][-1]["n"] == 6


if __name__ == "__main__":
    test_autonomous_frontier_discovers_735_then_refuses_736()
    test_scheduler_is_not_hardcoded_to_735()
    print("AUTONOMOUS_EXPLORER_TESTS_OK")
