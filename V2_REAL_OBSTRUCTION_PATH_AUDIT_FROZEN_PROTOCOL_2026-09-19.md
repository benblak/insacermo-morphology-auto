# INSACERMO V2 — Real Obstruction-Path Audit — Frozen Protocol

**Freeze date:** 19 September 2026  
**Status:** exploratory V2 protocol frozen before result  
**Frozen V1 artifacts modified:** NO

## Question

The previous derived bridge showed that a chain of pairwise minimal obstructions has a uniform safe-bundle endpoint occupancy converging to

[
arphi^{-2}=(3-sqrt5)/2approx0.38196601125.
]

This audit asks whether the *real* pair-obstruction graphs already produced by the frozen OpenFlights protocol contain path-like components or exhibit uniform-safe-bundle occupancies near that value without fitting anything to the constant.

## Frozen data semantics

Reuse unchanged from PR #78:

- OpenFlights routes.dat;
- start airport KEF;
- same fixed 25 future targets;
- H=3;
- scenarios BASELINE, NO_FI, NO_LHR, NO_FI_NO_LHR, KEF_SHUTDOWN;
- exact augmented-state BFS;
- order-2 minimal obstructions are graph edges.

No target, scenario, start airport, horizon, or feasibility rule may change after result inspection.

## Part A — Exact connected path components

For each scenario, build the undirected graph G whose vertices are the 25 declared futures and whose edges are exactly order-2 minimal obstructions at H=3.

Report every connected component with at least two vertices.

A component is an **exact path component** iff it is connected, has |E|=|V|-1, and maximum degree <=2.

For every exact path component of size n:

- compute its two endpoint marginal inclusion probabilities under the uniform distribution on graph-independent subsets;
- compare against the exact path value F_n/F_{n+2};
- report distance to phi^-2;
- do not discard short paths.

Primary endpoint: existence and lengths of exact path components in the real obstruction graph.

## Part B — Full pair-obstruction graph safe-bundle measure

For each scenario, compute exactly (by memoized branching, not Monte Carlo):

- total number of independent sets Z(G);
- for each vertex v, number of independent sets containing v;
- marginal inclusion p_v;
- mean, min, max and standard deviation of p_v;
- count of vertices within absolute distance 0.005 and 0.01 of phi^-2;
- closest vertex and its distance.

These are descriptive diagnostics only. No p-value and no post-hoc tolerance adjustment.

## Part C — Structural controls

Report:

- number of vertices and edges;
- connected-component sizes;
- degree distribution;
- whether each component is a path, cycle, tree but not path, or contains cycles/branching;
- graph density.

Interpretation is frozen:

1. If long exact path components exist, phi^-2 is structurally relevant there by the already-derived path theorem.
2. If no long path components exist, the path mechanism is not a global explanation of this adapter.
3. A vertex marginal numerically close to phi^-2 in a non-path graph is not evidence of universality.
4. Pair-obstruction results remain finite-horizon H=3 results and do not imply infinite-horizon irreversibility.
5. The historical constant is not fitted to the graph.

## Guardrails

- No retuning.
- Negative results retained.
- No claim that Fibonacci/independent-set combinatorics is new.
- No claim that phi^-2 is a universal INSACERMO constant.
- No mutation of the frozen Core V1 artifacts.
