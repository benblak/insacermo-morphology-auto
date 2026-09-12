# INSACERMO V5 — Infinite-Horizon Fixed-Point Existence Target

Date frozen: 2026-09-12

## Question

The discounted infinite-horizon Bellman operator has already been formally shown to satisfy the finite sup-distance contraction bound and to have at most one fixed point for `0 <= gamma < 1`.

This target asks the missing question:

> Does a Bellman fixed point actually exist under the same finite-state discounted hypotheses?

## Frozen setting

- finite nonempty decision-state type `X`;
- finite nonempty action type `A`;
- normalized exact finite transition law `P : X -> A -> FiniteLaw X`;
- stage cost `stageCost : X -> A -> Real`;
- discount `gamma : Real` with `0 <= gamma` and `gamma < 1`;
- Bellman self-map on the function space `X -> Real`.

The function space uses mathlib's finite-product sup metric. Since `Real` is complete, the finite function space is complete.

## Frozen theorem targets

1. Re-express the already-proved pointwise contraction as a genuine `LipschitzWith gamma` theorem for the Bellman self-map on `X -> Real`.
2. Package `0 <= gamma < 1` and that Lipschitz result as `ContractingWith`.
3. Apply mathlib's Banach fixed-point theorem on the complete nonempty metric space `X -> Real`.
4. Prove existence:

   `∃ Vstar, InfiniteBellmanFixedPoint P stageCost gamma Vstar`.

5. Combine with the existing uniqueness theorem to obtain existence-and-uniqueness.
6. Define or expose the canonical Banach fixed point and prove it satisfies the Bellman equation.
7. Reuse the existing `InfiniteBellmanGood`, `SafeRep`, and planner connection with the now-proved fixed point rather than a merely supplied candidate value function.

## Guardrails

This target remains finite-state and discounted. It does NOT prove:

- continuous POMDP belief-space existence;
- average-cost or undiscounted gamma = 1 control;
- unknown-model learning;
- approximation guarantees for finite belief abstractions;
- measurable-state dynamic programming;
- historical novelty.

## Falsification discipline

Do not weaken the Bellman contract or alter the already-verified contraction theorem to force Banach to apply. If the function-space metric does not line up with the proved finite sup bound, formalize that mismatch explicitly rather than hiding it.
