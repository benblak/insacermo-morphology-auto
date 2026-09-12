# INSACERMO Breast Cancer Blind Hypergraph Test V1 — FROZEN PREREGISTRATION

Date frozen: 2026-09-12

## Dataset

Use `sklearn.datasets.load_breast_cancer()` exactly as distributed with the installed scikit-learn package.

Expected semantic interpretation from the dataset object only:
- one world = one patient/sample,
- two actions = the two diagnosis labels exposed by `target_names`,
- `Good(s,a)` is deterministic and true exactly for the observed target label of sample `s`.

No feature/label outcome is to be inspected before this file is committed.

## Capabilities

Let `Cmax` contain both diagnosis actions. Also test both singleton capability sets and `Cmax`.

With deterministic `Good`, singleton capability holes are permitted to generate rank-1 obstructions. Under `Cmax`, any representational unsafety must have a rank-2 cross-label witness; rank > 2 is not expected and is not a success criterion.

## Frozen observation chain

Feature order is the dataset's published `feature_names` order. No supervised feature selection is allowed.

Define nested representations:

- `h0`: constant representation.
- `h1`: first feature, empirical median bin (q=2).
- `h2`: first 2 features, each empirical median bin (q=2).
- `h4`: first 4 features, each empirical median bin (q=2).
- `h8`: first 8 features, each empirical median bin (q=2).
- `h16`: first 16 features, each empirical median bin (q=2).
- `h30`: all 30 features, each empirical median bin (q=2).
- `h30_q4`: all 30 features, empirical quartile bins (q=4).
- `h30_q8`: all 30 features, empirical octile bins (q=8).
- `hexact`: all 30 raw feature values as an exact tuple.

Quantile discretization must use `pandas.qcut(..., duplicates="drop", labels=False)` independently per feature over the full dataset. This is a structural in-sample fiber test, not predictive validation.

## Primary endpoints

1. Exact agreement between direct `SafeRep` and an independently computed obstruction criterion over every frozen representation × capability state.
2. Capability monotonicity: if `C ⊆ C'` and `SafeRep(h,C)`, then `SafeRep(h,C')`.
3. Information monotonicity along the frozen refinement chain: if finer representation refines coarser and coarser is safe under fixed `C`, finer must be safe.
4. Router verdict from `(h0,Cmax)`:
   - ACT if `h0` is safe;
   - PROBE if `h0` unsafe but at least one finer frozen representation is safe;
   - REFUSE if even `hexact` is unsafe.
5. First safe representation in the frozen chain under `Cmax`.

## Secondary endpoints

- Number of realized fibers and unsafe fibers by representation.
- Number of minimal obstruction witnesses by rank under each capability state.
- For `Cmax`, lexicographically first cross-label rank-2 witness at the coarsest unsafe representation, if one exists.
- Nominal observation price within the frozen chain: cost = number of binary feature bins used for q=2 representations, `30*2=60` nominal bit-units for q4, `30*3=90` for q8, exact representation cost left undefined. This is not Shannon entropy or physical bandwidth.

## Outcome acceptance

Any of ACT / PROBE / REFUSE is accepted. No representation, feature order, quantile rule, target mapping, or capability set may be changed after outcomes are opened.

## Guardrails

- Structural medical-dataset test only; no clinical recommendation or diagnostic claim.
- In-sample zero-error actionability, not generalization accuracy.
- Deterministic-label setting means higher-order rank >2 obstructions under complete capabilities are not expected; absence of rank-3 is not a failure.
- Historical novelty is not tested here.
