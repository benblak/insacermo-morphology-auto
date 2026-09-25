# INSACERMO — PGLib IEEE-14 DC heredity audit V1
#
# Checks the exact assumption needed before identifying the bundle-feasibility
# family with a ContractComplex/simplicial complex:
#
#   feasible(F) and G subset F  => feasible(G).
#
# We test baseline and every single in-service branch outage on the same
# 8-goal catalogue used by the DC benchmark. This is an exhaustive finite
# audit of heredity for that catalogue, not a theorem for arbitrary DC grids.

from __future__ import annotations

import pglib_ieee14_dc_hidden_bundle_audit_v1 as base

TOP_LOAD_GOALS = 8


def main():
    raw = base.download(base.URL)
    text = raw.decode("utf-8", errors="replace")
    grid = base.Grid(
        base.parse_scalar(text, "baseMVA"),
        base.parse_matrix(text, "bus"),
        base.parse_matrix(text, "gen"),
        base.parse_matrix(text, "branch"),
    )

    goal_buses = [
        b for b, pd in sorted(grid.load.items(), key=lambda kv: (-kv[1], kv[0]))
    ][:TOP_LOAD_GOALS]
    masks = list(range(1, 1 << len(goal_buses)))

    def mask_to_set(mask):
        return frozenset(
            goal_buses[i]
            for i in range(len(goal_buses))
            if mask & (1 << i)
        )

    scenarios = [("BASELINE", None)]
    for oi, br in enumerate(grid.branch):
        if int(br[10]) == 1:
            scenarios.append((f"OUTAGE_{oi}", oi))

    total_violations = 0
    violating_scenarios = 0
    max_examples = 20
    examples = []

    print("INSACERMO_PGLIB_DC_HEREDITY_AUDIT_V1")
    print("STATUS EXHAUSTIVE_FINITE_CATALOGUE_HEREDITY_CHECK")
    print("GOAL_LOAD_BUSES", " ".join(map(str, goal_buses)))
    print("CATALOGUE_NONEMPTY_BUNDLES", len(masks))
    print("SCENARIOS", len(scenarios))

    for label, outage in scenarios:
        feasible = {
            mask: base.dc_feasible(grid, mask_to_set(mask), outage)
            for mask in masks
        }

        violations = 0
        for F in masks:
            if not feasible[F]:
                continue
            sub = (F - 1) & F
            while sub:
                if not feasible[sub]:
                    violations += 1
                    total_violations += 1
                    if len(examples) < max_examples:
                        examples.append((label, F, sub))
                sub = (sub - 1) & F

        if violations:
            violating_scenarios += 1
        print(
            "SCENARIO", label,
            "FEASIBLE_BUNDLES", sum(feasible.values()),
            "HEREDITY_VIOLATIONS", violations,
        )

    print("VIOLATING_SCENARIOS", violating_scenarios)
    print("TOTAL_HEREDITY_VIOLATIONS", total_violations)

    for label, F, G in examples:
        print(
            "HEREDITY_COUNTEREXAMPLE",
            label,
            "SUPERSET_BUSES", " ".join(map(str, sorted(mask_to_set(F)))),
            "SUBSET_BUSES", " ".join(map(str, sorted(mask_to_set(G)))),
        )

    print("HEREDITARY_ON_TESTED_CATALOGUE", int(total_violations == 0))
    print("INTERPRETATION",
          "if_zero_then_ContractComplex_embedding_is_empirically_valid_on_this_finite_catalogue")
    print("LIMITATION finite_catalogue_check_not_general_DC_theorem")
    print("RESULT COMPLETE")


if __name__ == "__main__":
    main()
