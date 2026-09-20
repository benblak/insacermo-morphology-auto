# INSACERMO OpenFlights Nontrivial Repair Bound — Selected-Candidate Audit

**Date:** 20 September 2026

## Status

This is **post-selection validation on the same frozen OpenFlights snapshot**, not an independent confirmatory experiment.

The candidate pair was selected by the preceding exploratory scan over the 40 airline classes with the largest sole-carrier edge counts. The deterministic ranking criterion was:

1. at least one newly created higher-order obstruction exclusively repaired by each of the two airline restorations;
2. maximize the total number of exclusive obstructions;
3. lexicographic tie-break.

The selected pair was:

- Turkish Airlines: `TK`
- Qatar Airways: `QR`

No claim of preregistration or independent holdout is made.

## Frozen source and inherited contract

- OpenFlights source commit: `5d623a6969a1adee7961cf1c9a8a212c4a784713`
- SHA256: `bd373706238134f619c624c606dccc74c05c2582a977c489c81de501735f2390`
- start: `KEF`
- 25 inherited target airports
- horizon: `H=3`
- bundle sizes: 1, 2, 3
- directed route graph
- one airline restoration class has unit cost 1

## Decision / repair model

The degraded state removes both airline classes `TK` and `QR`.

Concrete repair actions are:

- NONE, cost 0
- RESTORE_TK, cost 1
- RESTORE_QR, cost 1
- RESTORE_BOTH, cost 2

For every minimal obstruction newly created by the combined deletion, repair capability is **derived by actually restoring one airline class and recomputing finite-horizon feasibility**. It is not assigned by hand.

## Endpoints

Compute exactly:

- baseline and degraded minimal obstructions;
- newly created minimal obstructions;
- number exclusively repaired by TK;
- number exclusively repaired by QR;
- number repaired by either;
- number requiring both / neither single restoration;
- trivial one-atom lower bound;
- weighted transversal price \(\tau\);
- exact concrete repair price \(C^*\) over the four repair actions.

The key nontrivial endpoint is:

\[
1=c_{\rm trivial}<\tau\le C^*.
\]

Because this is post-selection on the same data, even a successful result is evidence of mechanism, not independent external validation.
