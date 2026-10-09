# INSACERMO — Adaptive Sensing and Conditional Repair Audit (V7–V8)

Date: 2026-10-09. Dataset: historical OpenFlights pinned commit `7d1a611e070295dba776d6afb86e57d0d1aa1cef`, SHA256 `bd373706238134f619c624c606dccc74c05c2582a977c489c81de501735f2390`, 37,594 distinct directed edges.

## Results

V7, ACT iff the target remains reachable, else REFUSE. Up to two failures, perfect edge-status observations. Generic Bellman minimax decision-tree optimization over graph-derived minimal cut basis `P2`. Two deterministic cohorts previously frozen in V3, 240 each.

| Cohort | Fixed probe sum | Adaptive worst-case depth sum | Improved contracts |
|---|---:|---:|---:|
| 240 random reachable source–target pairs | 497 | 469 | 16 |
| 240 random existing directed routes | 41 | 41 | 0 |

Run: https://github.com/benblak/insacermo-morphology-auto/actions/runs/37915042383.

Notable witness: `NDY -> LMT`, 5 mandatory fixed probes vs optimal adaptive worst-case 3 under the given allowed probe library. This policy is computed by Bellman; exhaustive label validation over all modeled cut-basis failure signatures and additional comparisons to the original graph were performed. Small random independent depth-feasibility oracle: 140 cases.

V8, ACT if connected; otherwise REPAIR a minimum-cardinality subset of the actually failed edges, with lexicographic tie-break, then ACT. Same cohorts and failure bound. Again, the identical aggregated probe depths: 497→469 (16 improved) and 41→41 (none improved). The maximum individual saving was 3 probes. Minimal actual repair is verified by direct reachability enumeration for 0–2 failures, and original-graph comparisons across modeled worlds plus sampled full-network worlds. Independent depth-feasibility oracle: 140 cases. Run: https://github.com/benblak/insacermo-morphology-auto/actions/runs/37915305586.

These sums are sums of independent per-contract WORST-CASE quantities; they are not measured operational savings, cannot be treated as representative of all source-target pairs, and do not establish average number of inspections on a probabilistic distribution.

## Lean kernel

A new independent Lean 4 proof file, `lean/OneHotObservationKernelV1.lean`, formalizes:

1. Two worlds with no matching individual one-hot probes have identical observation signatures.
2. A fixed individual one-hot probe set makes all decisions identifiable if and only if all unprobed worlds have the same required action.
3. Two worlds requiring different actions cannot both be unprobed by a globally sound fixed observation set.

Build and forbidden-placeholder audit SUCCESS: https://github.com/benblak/insacermo-morphology-auto/actions/runs/37915561318. No sorry/admit/custom axioms in this file. An initial CI failure was due to a non-portable `by_contra` tactic; the replacement `Classical.byContradiction` preserved the theorem.

This kernel **does not yet prove**:
- the historical OpenFlights interpreter or pinned data hash;
- enumeration of minimal s–t cuts and the cut basis `P2`;
- Bellman recurrence optimality and runtime implementation;
- the V7/V8 individual certificates;
- the end-to-end INSACERMO MAX TOTAL planner.

## Scope and next science

The P2 graph-cut adapter was specialized and run before the generic Bellman tree generator. The exact minimax optimum is relative to the derived P2 individual perfect-probe library, rather than a proof over every conceivable sensor, nonlocal group test, or correlated reading.

Related areas already studied in the literature include sequential fault diagnosis, minimal cutsets, decision-tree construction, graph connectivity sensitivity, repair-cost optimization, and active sensing. Scientific novelty cannot be established solely by V7/V8; stronger comparative work is needed against existing methods and under realistic costs.

Next decisive experiments: full general engine as one execution path; explicit observer pricing, repair time and partial effectiveness, noisy/failing sensors, future-contract changes, and independent proof-carrying runtime checks of emitted decision trees.
