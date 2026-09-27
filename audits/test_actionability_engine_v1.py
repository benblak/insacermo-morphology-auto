#!/usr/bin/env python3

from insacermo_actionability_engine_v1 import (
    FiniteContract,
    ContextContract,
    audit_observation,
    minimum_action_cover,
    minimum_safe_partition,
    minimum_certified_messages,
    verify_certified_messages,
    pareto_frontier,
)


def main():
    c = FiniteContract(
        worlds=("L", "M", "R"),
        actions=("alpha", "beta"),
        available=frozenset({"alpha", "beta"}),
        admissible_pairs=frozenset({
            ("L", "alpha"),
            ("M", "alpha"),
            ("M", "beta"),
            ("R", "beta"),
        }),
    )

    assert minimum_action_cover(c).value == 2
    assert minimum_safe_partition(c).value == 2
    mp = minimum_certified_messages(c)
    assert mp.value == 2
    assert verify_certified_messages(c, mp.witness)

    # Signature-like 3-symbol observation is safe but not minimum.
    obs3 = {"L": 0, "M": 1, "R": 2}
    assert audit_observation(c, obs3).status == "ACT"

    # One-symbol observation is unsafe.
    obs1 = {"L": 0, "M": 0, "R": 0}
    assert audit_observation(c, obs1).status == "REFUSE"

    # Both optimal two-way merges are safe.
    obs_a = {"L": 0, "M": 0, "R": 1}
    obs_b = {"L": 0, "M": 1, "R": 1}
    assert audit_observation(c, obs_a).status == "ACT"
    assert audit_observation(c, obs_b).status == "ACT"

    cc = ContextContract(
        contexts=("a0", "a1", "b0", "b1"),
        local_worlds=(None,),
        actions=("alpha", "beta"),
        available=frozenset({"alpha", "beta"}),
        admissible_triples=frozenset({
            ("a0", None, "alpha"),
            ("a1", None, "alpha"),
            ("b0", None, "beta"),
            ("b1", None, "beta"),
        }),
    )

    front = pareto_frontier(cc, max_q=4, max_m=2)
    assert front == ((1, 2), (2, 1)), front

    print("SUCCESS")
    print("minimum_action_cover=2")
    print("minimum_safe_partition=2")
    print("minimum_certified_messages=2")
    print("context_message_pareto=((1, 2), (2, 1))")


if __name__ == "__main__":
    main()
