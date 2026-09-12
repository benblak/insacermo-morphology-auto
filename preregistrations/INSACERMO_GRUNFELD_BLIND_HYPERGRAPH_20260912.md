# INSACERMO Grunfeld Blind Hypergraph Test — Frozen Protocol

Date frozen: 2026-09-12
Status: FROZEN BEFORE OUTCOME ANALYSIS

## Purpose

Independent-domain structural replication of the finite INSACERMO hypergraph-actionability mechanism after the exploratory ModeChoice result. This test is not intended as a finance recommendation, causal investment study, or historical novelty claim.

## Dataset

Public Grunfeld investment panel as shipped in `statsmodels.datasets.grunfeld`.

Expected structure (dataset metadata only, inspected before freeze):
- 220 firm-year rows
- columns: `invest`, `value`, `capital`, `firm`, `year`

No hypergraph, SafeRep, obstruction-rank, or route outcome from this dataset has been computed before this freeze.

## Decision contract

Worlds: calendar years in the panel.

Actions: firms present in every year of the balanced panel.

For a fixed year y and firm a, define three objectives from the observed row:
- maximize `invest`
- maximize `value`
- minimize `capital`

`Good(y,a)` holds iff firm a is Pareto-undominated in that year under those three objectives.

This is a structural multi-objective allocation contract only. It is not a claim that historical investors should have selected these firms.

## Capability sets

Primary capability set Cmax: all firms in the balanced panel.

For monotonicity audit, test all nonempty capability subsets only if |A| <= 10. If |A| > 10, use the deterministic frozen subset family:
- all singletons
- all pairs
- all complements of singletons
- Cmax
No outcome-dependent subset selection is allowed.

## Observation representations

The representation library is frozen before outcome analysis.

Let year rank run from earliest to latest.

- h0: constant observation
- h1: decade bucket = floor((year - min_year)/10)
- h2: 5-year bucket = floor((year - min_year)/5)
- h3: 2-year bucket = floor((year - min_year)/2)
- h4: exact year

These form a deterministic refinement chain h4 -> h3 -> h2 -> h1 -> h0 on the realized panel.

No representation may use `invest`, `value`, or `capital`; those variables define the action contract and remain hidden from the observation map.

## Primary endpoints

1. Exact equivalence audit for every frozen representation x capability state:

   SafeRep(Good,B,C,h)
   iff
   no realized observation fiber contains a minimal common-action obstruction.

Primary success criterion: 0 mismatches.

2. Capability monotonicity:

   C subset C' and SafeRep(C) => SafeRep(C').

Primary success criterion: 0 violations.

3. Information/refinement monotonicity:

   if fine refines coarse and SafeRep(coarse,C), then SafeRep(fine,C).

Primary success criterion: 0 violations.

## Secondary endpoints

- Counts of minimal obstruction hyperedges by rank for each representation at Cmax.
- Maximum observed minimal obstruction rank.
- Whether any rank >= 3 obstruction occurs.
- Smallest representation in the frozen chain that is SafeRep at Cmax, if one exists.
- Router regime from h0 under Cmax along observation refinement only: ACT if h0 safe, PROBE if some finer h is safe, REFUSE if h4 remains unsafe.

## Higher-order witness rule

If a rank >= 3 minimal obstruction exists, report the lexicographically first witness under ordering:
1. coarsest representation first: h0,h1,h2,h3,h4
2. fiber key ascending
3. obstruction rank ascending
4. tuple of firm names lexicographically

No witness may be hand-selected for visual appeal.

## Guardrails

- Do not change the Pareto objectives after seeing results.
- Do not alter the representation library after seeing results.
- Do not add or remove firms based on obstruction outcomes; only balance/complete-case handling dictated by the raw panel is permitted.
- A null result, only rank-2 result, immediate ACT, PROBE, or REFUSE all count as valid scientific outcomes.
- This dataset is economic panel data and is domain-distinct from the earlier transport ModeChoice test.
- The test is preregistered/frozen on GitHub before any Grunfeld SafeRep or hypergraph outcome is computed.
