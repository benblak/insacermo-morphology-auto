# INSACERMO Post-Freeze OpenFlights Private-Witness V1 — Frozen Protocol

**Freeze date:** 19 September 2026  
**Purpose:** real-data confirmatory test of finite-horizon minimal-obstruction private witnesses after the V1 freeze.

## Inherited choices (not tuned for this endpoint)

The protocol inherits unchanged from OpenFlights joint PR #53:

- source data: OpenFlights `routes.dat` from the same public upstream URL;
- start airport: `KEF`;
- required future airports: the same fixed list of 25 targets;
- deadline: `H = 3`;
- scenarios: `BASELINE`, `NO_FI`, `NO_LHR`, `NO_FI_NO_LHR`, `KEF_SHUTDOWN`;
- directed route graph and the same scenario-removal rules.

## New confirmatory endpoint

For bundle sizes 2 and 3 only:

1. A bundle F is a **finite-horizon obstruction at H=3** when no directed path of length <= 3 from KEF visits every airport in F.
2. F is **minimal** when every proper nonempty subbundle is feasible by H=3.
3. For every q in a minimal obstruction F, require a concrete path p_q of length <= 3 that visits every airport in F \\ {q}.
4. Verify mechanically that p_q does **not** visit q. If it did, F itself would be feasible and the candidate would not be an obstruction.
5. Record counts by scenario and obstruction order, and print the first ten obstructions in deterministic lexicographic order with all private witness paths.

## Strong higher-order endpoint

A rank-3 finite-horizon obstruction is counted only when:

- the triple is infeasible by H=3;
- all three constituent pairs are feasible by H=3.

Thus pairwise compatibility is explicitly required before calling a triple a higher-order obstruction.

## Exact path semantics

Feasibility and witness extraction use BFS on augmented states `(airport, visited-target-mask)` up to H=3. This directly represents one common directed route from KEF and returns an explicit route witness.

## Guardrails

- No horizon change after observing results.
- No target-list change after observing results.
- No scenario change after observing results.
- No search for a different start airport if the result is null.
- A null result is retained as a valid negative control.
- This test concerns **finite-horizon obstruction at H=3**, not eventual irreversibility.
- It does not establish historical novelty or external validity.

The protocol is frozen before the new endpoint is executed in CI.
