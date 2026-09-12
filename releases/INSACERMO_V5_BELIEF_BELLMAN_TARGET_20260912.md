# INSACERMO V5 — Finite-Horizon Belief Bellman Target

Date frozen: 2026-09-12

## Question

Does the INSACERMO actionability kernel remain coherent when finite-horizon control is computed recursively on Bayesian belief states rather than supplied as a precompiled policy predicate?

This target is the first explicit Bellman recursion on top of the verified finite Bayes filter.

## Frozen setting

- hidden state type `S`, finite;
- action type `A`, finite and nonempty;
- observation type `O`, finite;
- exact rational beliefs `FiniteLaw S`;
- transition kernel `T : A -> S -> FiniteLaw S`;
- observation kernel `Z : A -> S -> FiniteLaw O`;
- rational one-step cost `stageCost : FiniteLaw S -> A -> Q`;
- rational terminal cost `terminalCost : FiniteLaw S -> Q`.

The verified Bayes filter supplies prediction, observation evidence, and positive-evidence posterior update.

## Zero-evidence convention

Bellman expectation ranges over all finite observations. The posterior after an impossible observation is mathematically irrelevant because its probability weight is zero.

We therefore define a total belief update:

- if evidence(o) > 0, use the exact Bayesian posterior;
- otherwise use a fixed fallback belief.

A theorem target must prove that every zero-evidence branch contributes exactly zero to the continuation expectation. The fallback must therefore have no effect on the Bellman value.

This is a semantic device for total recursion, not a claim that conditioning on a zero-probability event has a unique Bayesian meaning.

## Bellman recursion

For continuation value `V`, define

`Q_V(b,a) = stageCost(b,a) + sum_o P(o | b,a) * V(update(b,a,o))`.

For finite nonempty action sets,

`B(V)(b) = min_a Q_V(b,a)`.

Finite-horizon value:

- `V_0(b) = terminalCost(b)`;
- `V_{n+1}(b) = B(V_n)(b)`.

## Formal targets

1. totalized Bayesian update equals exact `bayesUpdate` whenever evidence is positive;
2. nonpositive evidence is exactly zero, using already verified evidence nonnegativity;
3. zero-evidence continuation terms are exactly zero;
4. finite action minimum exists for every belief;
5. Bellman recursion satisfies its successor equation exactly;
6. at least one Bellman-optimal action exists at every belief and finite horizon;
7. define `BellmanGood(n,b,a)` as exact Bellman optimality;
8. instantiate `SafeRep` with `BellmanGood` and prove standard capability and information monotonicity;
9. prove full-belief identity representation is actionable when all actions are available.

## Interpretation target

If this passes, INSACERMO will have an explicit finite-horizon partially observed control recursion whose actionability predicate is generated endogenously by Bellman optimality on Bayesian beliefs.

The central object is then no longer merely a supplied policy contract:

`belief -> Bellman Q-values -> optimal-action contract -> SafeRep -> planner`.

## Guardrails

This target does NOT yet prove:

- equivalence with all history-dependent POMDP policies;
- infinite-horizon Bellman fixed points;
- discounted contraction theorems;
- continuous/measurable belief spaces;
- model learning or unknown transition/observation kernels;
- path-dependent budgets or risk unless they are included in the state;
- that the zero-evidence fallback is a posterior semantics.

## Falsification boundary

If a Bellman-optimal action cannot be represented by the current information fibers, `SafeRep` must fail. The response is to refine information, expand capabilities, augment state, or refuse; not to alter the frozen optimality contract after seeing the result.
