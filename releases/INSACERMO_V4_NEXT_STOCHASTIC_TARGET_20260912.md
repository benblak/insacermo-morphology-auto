# INSACERMO V5 Target Freeze — Finite Stochastic Actionability

Date frozen: 2026-09-12

This note freezes the first post-V4 mathematical extension before implementation.

## Goal

Test whether the frozen three-layer skeleton

`Contract -> Actionability / Obstructions -> Planner`

survives replacement of deterministic Boolean `Good(s,a)` by admissibility induced from a finite outcome law and a fixed risk criterion.

## First stochastic semantics

Let `O` be a finite outcome type. For each world/action pair `(s,a)`, let `P(s,a)` be a finite probability law on `O`.

Let `loss : O -> ℚ` and threshold `theta : ℚ`.

Define expected loss

`EL(s,a) = sum_o P(s,a)(o) * loss(o)`

and risk admissibility

`RiskGood(s,a) :<=> EL(s,a) <= theta`.

The first stochastic SafeRep is not a new runtime layer. It is the existing finite SafeRep instantiated with `RiskGood`.

## Frozen claims to test/formalize

1. **Capability monotonicity survives** under fixed stochastic law, loss and threshold:
   if `C subset C'` and `RiskSafeRep(B,C,h)`, then `RiskSafeRep(B,C',h)`.

2. **Information refinement monotonicity survives** under the same fixed contract.

3. **Finite hypergraph characterization survives exactly** because stochastic admissibility induces a capability-relative Boolean contract predicate:

   `RiskSafeRep iff RiskHypergraphSafe`.

4. **The source of possible failure is not stochasticity by itself.** Failure of these monotonicity statements can only enter when changing capability also changes the contract predicate itself, for example through endogenous shared budgets, interaction costs, policy coupling, learning effects or path-dependent risk.

## Deliberate boundary

This first V5 target does NOT yet claim closure for:

- continuous outcome spaces;
- CVaR/chance constraints beyond what can be encoded as a fixed local admissibility predicate;
- POMDP belief evolution;
- stochastic transitions across time;
- endogenous information acquisition;
- unknown models / posterior uncertainty;
- multi-agent coupling;
- capability-dependent contracts.

Those are subsequent attempts to break the skeleton.

## Falsification discipline

If finite stochastic local-risk actionability does not reduce cleanly to the frozen SafeRep kernel, the V4 architecture must be revised. If it does reduce cleanly, that is evidence that the first stochastic extension is an instantiation of the kernel rather than a new theory layer.
