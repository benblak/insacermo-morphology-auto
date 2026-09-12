# INSACERMO Wine Repair-Only Blind Test V1 — FROZEN PREREGISTRATION

Date frozen: 2026-09-12

## Dataset
Use `sklearn.datasets.load_wine()` exactly as distributed with the installed scikit-learn package.

## Contract
- World = wine sample.
- Actions = the three class labels exposed by the dataset target names.
- `Good(s,a)` is deterministic and true exactly for the observed class label of sample `s`.

## Frozen representations
Feature order is the dataset's published `feature_names` order. No supervised feature selection.

- `h0`: constant.
- `h13_q2`: all 13 features, empirical median bins via `pandas.qcut(..., q=2, duplicates="drop", labels=False)` per feature.
- `h13_q4`: all 13 features, empirical quartile bins via the same rule.
- `h13_q8`: all 13 features, empirical octile bins via the same rule.
- `hexact`: exact raw 13-feature tuple.

## Capabilities
Let dataset target names in published order be `a0,a1,a2`.

- Base capability set `C0 = {a0,a1}`.
- Repair adds exactly `a2`, so `C1 = {a0,a1,a2}`.

No alternative repair bundle is allowed after outcomes are opened.

## Primary repair-only endpoint
At each frozen representation h, classify the 2x2 local route status:
- base safe? `SafeRep(h,C0)`
- repaired safe? `SafeRep(h,C1)`

A clean REPAIR-only witness exists iff there is a frozen h such that:
`SafeRep(h,C0)=False` and `SafeRep(h,C1)=True`.

If no frozen h has this pattern, the repair-only endpoint FAILS. This is accepted; no post-outcome retuning.

## Additional endpoints
1. Exact agreement between direct `SafeRep` and deterministic obstruction criterion for every frozen h × {C0,C1}.
2. Capability monotonicity from C0 to C1 at every h.
3. Information monotonicity along the frozen refinement chain.
4. First representation safe under C1.
5. First representation, if any, witnessing REPAIR-only.
6. Obstruction decomposition:
   - under C0, missing-a2 worlds are rank-1 capability-hole obstructions;
   - under C1, any remaining representational unsafety is rank-2 cross-label aliasing.

## Guardrails
- Structural in-sample test only; not wine-quality prediction or recommendation.
- Deterministic-label capability-completion repair is intentionally a simple REPAIR mechanism; success would establish existence of a real-data REPAIR-only regime, not a deep complementarity result.
- No causal or out-of-sample interpretation.
- Any outcome is accepted and no representation, feature order, quantizer, target mapping, or capability set may be changed after this commit.
