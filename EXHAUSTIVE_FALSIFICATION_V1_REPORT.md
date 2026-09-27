# INSACERMO — Exhaustive Finite Falsification Audit V1
## 27 September 2026

Reference workflow:
- branch: `insacermo-exhaustive-falsification-v1`
- script: `audits/exhaustive_finite_kernel_audit.py`
- GitHub Actions run: `36339803373`
- result: **SUCCESS**

This audit is deliberately independent of Lean: it reimplements the finite semantics by brute force and attempts to find counterexamples.

## A. Core equivalence audit

Enumerated **38,860** finite systems with:
- worlds: 1..4
- actions: 1..3
- every action-availability mask
- every admissibility relation

Results:
- pointwise feasible: **8,666**
- pointwise infeasible: **30,194**
- no counterexample

For every feasible system, four quantities were computed independently and agreed exactly:
1. minimum safe partition / safe information symbols;
2. minimum available action cover;
3. minimum certified messages;
4. minimum coloring of the minimal-obstruction hypergraph.

Minimum histogram among feasible systems:
- minimum 1: **4,024**
- minimum 2: **4,504**
- minimum 3: **138**

Every pointwise-infeasible system was rejected by all four formulations.

Interpretation:
The equality of the finite information / cover / certified-message / obstruction formulations survived exhaustive brute-force testing over the entire audited universe.

This is **computational evidence**, not an additional mathematical proof.

## B. Context-message frontier audit

Enumerated **364** context/action systems with:
- contexts: 1..3
- actions: 1..2
- local world: Unit
- every availability mask
- every admissibility relation
- every summary alphabet size q=1..|K|
- every message alphabet size m=1..|A|

Results:
- pointwise feasible systems: **70**
- all tested feasibility regions were upward closed
- all computed Pareto minima were pairwise incomparable
- maximum frontier size observed: **2**
- total Pareto-minimal points across the audited systems: **84**
- multiple systems exhibited the strict frontier:
  [
  {(1,2),(2,1)}
  ]
  with ((1,1)) infeasible.

Additional audit:
For every pointwise-feasible system, the minimum combined alphabet product (q m) equaled the independently computed minimum global certified-message count over the audited rectangle.

Also verified:
If a global (m)-message protocol exists, then a one-summary-symbol ((1,m)) representation exists. This confirms computationally why minimizing context cardinality alone is degenerate when the message channel is unrestricted.

## C. Tree congruence brute-force audit

Audited:
- world alphabet size: 2
- message alphabet size: 2
- **1,024** complete local encoders
- all **10** trees of depth <= 1
- every same-message pair
- every one-step parent context using every audited sibling and both left/right placements

Counts:
- same-message subtree pairs encountered: **36,352**
- parent-context replacement checks: **1,454,080**
- counterexamples: **0**

Interpretation:
For every enumerated encoder, equal child messages remained equal after embedding under every tested parent environment. This independently stress-tests the operational congruence mechanism used by the recursive Lean kernel.

## D. What this audit does NOT prove

It does not replace the Lean theorems.

It does not establish:
- infinite-state closure;
- stochastic closure;
- cyclic-graph closure;
- continuous dynamics;
- empirical validity on physical data;
- asymptotic complexity;
- worldwide novelty.

Its role is falsification:
the implementation recomputes the finite objects independently and would stop at the first discovered counterexample.

## E. Current combined evidence stack

### Formal
Lean kernel:
- Total Closure commit: `8917974781182fed71c7d2e4fac538622c63d2d2`
- run: `36339127455` SUCCESS

### Independent exhaustive computation
- run: `36339803373` SUCCESS
- 38,860 core systems
- 364 context-message systems
- 1,454,080 tree parent-context checks

### Empirical
Existing real-data studies remain a separate evidence layer, including the prospective MetroAT official TRAIN/TEST holdout described in the current synthesis.

## F. Scientific conclusion from V1

The strongest justified statement is now:

> The finite deterministic INSACERMO theorem chain is both machine-checked in Lean and independently consistent with an exhaustive brute-force audit over tens of thousands of small finite systems, including exact information/cover/message/obstruction equivalence, context-message Pareto behavior, and more than 1.45 million local tree-congruence replacement checks.

This materially strengthens confidence in the implementation and theorem interpretation while remaining strictly below a claim of universal validity.
