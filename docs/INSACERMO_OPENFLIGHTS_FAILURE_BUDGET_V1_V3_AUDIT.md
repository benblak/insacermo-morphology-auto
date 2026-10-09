# INSACERMO — Contract-relative failure-budget information (OpenFlights V1–V3)

Date: 2026-10-09. Status: Python CI SUCCESS for V1, V2, V3; **not Lean-kernel-verified**.

## What was actually tested

Historical OpenFlights `routes.dat`, pinned upstream commit `7d1a611e070295dba776d6afb86e57d0d1aa1cef`, SHA256 `bd373706238134f619c624c606dccc74c05c2582a977c489c81de501735f2390`. Graph simplification: directed unweighted edges (source and destination airport code), duplicate edges merged; 67,662 accepted raw rows, 37,594 unique directed edges. The routes data is historical (not live flight operations). It ignores capacity, schedules, transfers, and airlines.

V1 selected its source/target after looking for a *forced chain*, so this is a data-dependent witness and not independent task selection. The source-target pair was STZ->BSB. Under **exactly one failed directed edge** there are four critical edges STZ->SXO, SXO->GRP, GRP->MQH, MQH->BSB. Fixed perfect individual edge probes: 4 necessary/sufficient to choose ACT if the broken edge is irrelevant, otherwise REPAIR its identity, then ACT. Five possible decision classes (four repairs and ACT), which is a distinct claim from the number of edge probes. The V1 Python script specialized to this graph problem; it does not show that the general INSACERMO runtime or Lean checker executed these exact computations.

V2 fixed RNG seed 20261009 and tested two cohorts: 240 random reachable source-target pairs (conditioning only on original reachability), and 240 random directly linked pairs. Selection did not test failure sensitivity in advance. The code enumerated inclusion-minimal single-edge and two-edge cuts by path-intersection enumeration, matching an independent exhaustive oracle for 900 small-graph source-target instances. Outcomes:

| Metric | 240 random reachable pairs | 240 random directed edges |
|---|---:|---:|
| At least one single-edge cut | 128 | 9 |
| At least one inclusion-minimal two-edge cut | 105 | 12 |
| Zero single-edge cuts, nonzero two-edge cuts | 60 | 12 |

The cohort samples can overlap; 60+12 is a count of occurrences across cohorts, not necessarily unique source-target pairs.

V3 computed the exact minimum **fixed individual binary edge-status probes** under an **at-most-one** versus an **at-most-two** failed-edge budget. The contract was deliberately narrowed to the binary assertion `Reachable(s,t)`, not minimal-cost repair or exact repair identity:

| Metric | 240 random reachable pairs | 240 random directed edges |
|---|---:|---:|
| Mean probes, up to 1 failure | 0.7667 | 0.0375 |
| Mean probes, up to 2 failures | 2.0708 | 0.1708 |
| Median probes, up to 2 failures | 2 | 0 |
| Maximum probes, up to 2 failures | 8 | 6 |
| Oracle path checks V3 | 6404 | 5147 |

An illustrative witness is YZY->YKA: 0 individual status probes are needed to ascertain reachability under at most one failed edge, but 2 are necessary and sufficient under at most two, because {YZY->LHW, YZY->XIY} is a minimal pair cut. Another witness YIK->SYX requires 0 under one failure and 6 under two.

## Theorem: minimum fixed perfect per-edge probe basis

Let `G=(V,E)` be a finite directed graph with fixed source `s` and target `t`, and suppose `t` is initially reachable from `s`. Let a hidden failure set `F subset E` obey `|F|<=k`, with no other graph changes. A probe reveals the exact yes/no status of **one selected edge**, perfectly and without ambiguity; the set of probed edges must be fixed independent of the hidden failure set. The contract is to answer correctly for every allowable `F` whether `t` remains reachable from `s` in `G - F`.

Define `C_k` to be all inclusion-minimal s-t edge cut sets `C` with `|C|<=k`; define `P_k = union_{C in C_k} C`.

**Claim:** `P_k` is the unique inclusion-minimal and minimum-cardinality set of fixed individual edge-status probes sufficient to decide reachability for all `F` with `|F|<=k`.

Proof (mathematical, NOT a Lean proof):

1. Every disconnected `G-F` has an inclusion-minimal cut `C subseteq F` (finite), hence `C in C_k`. All members of `C` belong to `P_k`. Thus observing `F intersect P_k` reveals at least one full failed minimal cut, and proves disconnection. Conversely no disconnected signature can be falsely observed when `G-F` remains reachable. Thus `P_k` suffices.
2. For any `e in P_k`, take a minimal cut `C in C_k` with `e in C`. The worlds `F=C` and `F'=C\{e}` are both admissible. By minimality of `C`, the first is disconnected and the second connected. Their edge statuses differ only at `e`. Every sufficient fixed individual probe set therefore must contain `e`. Applying this to every `e in P_k` proves necessity and uniqueness.

The theorem is a graph-cut consequence and must **not** be presented as a previously unknown result in graph theory. INSACERMO's candidate contribution to examine is how this basis is plugged into a general contract/actionability/planner/proof-carrying runtime across heterogeneous domains.

## Crucial distinctions and next steps

- V1 exact-one-failure **repair identity** and V3 at-most-two-failures **binary reachability** are different contracts. Do not equate their probe counts.
- Failure budget can make an observation relevant that was irrelevant under a smaller failure budget: `P_1 subseteq P_2 subseteq ...`.
- For **adaptive probes**, group tests, noisy observations, sensor costs, distributed sensing, or unknown dynamic edges, the theorem requires a new model and does not claim optimality.
- For **minimal-cost REPAIR**, observed cut statuses alone need not be the optimal policy. Extend formal action semantics and possible futures before making claims.
- Next proof target: formalize finite `Finset` graph reachability, minimal cuts and `P_k` theorem in Lean with 0 sorry/admit and no new axioms; verify independent instance certificates tied to SHA256, contract, and kernel.
- Next runtime target: call the current general INSACERMO pipeline on the exact same locked inputs and compare decisions/probes against the specialized scripts. Passing CI for stand-alone scripts is not equivalent to proving the full engine.
- Next empirical target: precommit independently chosen destinations/contract, test 3+ failures on tractable cases, physical repair costs, noisy sensor policies and transfer constraints, compare against baseline graph-cut algorithms and adaptive plans.

## Reproducibility

- V1 run: https://github.com/benblak/insacermo-morphology-auto/actions/runs/37899605489
- V2 run: https://github.com/benblak/insacermo-morphology-auto/actions/runs/37901042989
- V3 run: https://github.com/benblak/insacermo-morphology-auto/actions/runs/37901323320
- Source scripts: `experiments/openflights_minimal_sufficient_information_v1.py`, `experiments/openflights_blind_dual_failure_v2.py`, `experiments/openflights_failure_budget_min_probes_v3.py`.
