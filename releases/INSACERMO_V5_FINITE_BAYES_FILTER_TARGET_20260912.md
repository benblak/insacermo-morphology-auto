# INSACERMO V5 — Finite Bayes Filter + Belief Actionability Target

Date frozen: 2026-09-12

## Question

Can the abstract belief-state sufficiency theorem be connected to an explicit finite partially observed stochastic system, rather than assuming an opaque history-to-belief map?

This target introduces the first explicit Bayesian filtering layer used by INSACERMO.

## Frozen model

All spaces are finite and probabilities are exact rationals.

- hidden state type `S`;
- control/action type `A`;
- observation type `O`;
- belief `b : FiniteLaw S`;
- transition kernel `T : A -> S -> FiniteLaw S`;
- observation kernel `Z : A -> S -> FiniteLaw O`.

For action `a`, the predicted next-state mass is

`pred(s') = sum_s b(s) * T(a,s)(s')`.

For observation `o`, the unnormalized posterior weight is

`w(s') = pred(s') * Z(a,s')(o)`

with evidence

`eta = sum_s' w(s')`.

When `eta > 0`, the posterior is

`post(s') = w(s') / eta`.

## Formal targets

1. prediction is nonnegative;
2. prediction normalizes to one, hence defines a finite belief;
3. evidence is nonnegative;
4. positive-evidence Bayesian update is nonnegative and normalizes to one;
5. the next-belief map is extensional in the current belief: equal beliefs give equal posteriors for the same action and observation;
6. the predictive observation law is a normalized finite law;
7. a history contract defined only through the recursively generated Bayesian belief is `BeliefSufficient`;
8. therefore the already verified history/belief SafeRep equivalence applies to the explicit finite Bayes filter.

## Why this test matters

The previous theorem said that *if* a belief map is contract-sufficient, history may be forgotten without losing actionability. This target builds the core belief update itself and verifies that it remains a valid probability state under finite exact stochastic dynamics.

It does not claim that every decision contract factors through the standard hidden-state posterior. A budget, accumulated risk, unknown parameter, path constraint, or other history-dependent quantity may require an augmented belief/state.

## Guardrails

This target is deliberately finite and rational. It does NOT yet prove:

- measure-theoretic/continuous Bayesian filtering;
- zero-evidence conditioning semantics;
- optimal POMDP Bellman equations;
- infinite-horizon control;
- unknown-model learning;
- parameter uncertainty unless included in the hidden state;
- that a state-only posterior is sufficient for arbitrary path-dependent contracts.

## Falsification boundary

If a contract does not factor through the computed belief, the existing belief-sufficiency theorem explicitly refuses the compression. The correct response is to augment the state/belief or retain more history, not to tune away the disagreement.
