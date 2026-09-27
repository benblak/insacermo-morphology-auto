# INSACERMO — MetroAT Interface/Pareto V1 — Frozen Protocol
## Freeze date: 2026-09-27

## Evidence class

This is a **pre-specified secondary holdout reanalysis** of MetroAT.

The official MetroAT TEST archive was already opened in the earlier INSACERMO information-refinement experiment. Therefore this new endpoint must **not** be described as a pristine prospective holdout. The new interface/Pareto endpoint is frozen here before it is computed, and no TEST-derived threshold, feature order, component topology, resource grid, or endpoint rule may be changed afterward.

The earlier prospective experiment remains the primary untouched TRAIN/TEST holdout.

## Frozen source mechanics

Dataset:
- MetroAT v1 — TU Wien / Wiener Linien
- DOI: 10.48436/9ja0q-bq581
- official TRAIN archive MD5: 6ba8fd0cd9c65b02ca5319e99a6fa002
- official TEST archive MD5: e5638ac4ced34231223015f1bfcb29d2

Reuse without modification:
- 60-second minute-state construction from the earlier frozen MetroAT implementation;
- four-bit future-event signature;
- strict continuity rule;
- only 1 h and 6 h horizons as supported primary horizons;
- TRAIN-derived q2/q4 thresholds from prior run 36322103082;
- TRAIN-derived SHA256 feature order from prior run 36322103082.

Frozen prior hashes:
- TRAIN thresholds SHA256: 980c95f2cdbdea6ac8c7840d25b9a8e020ffbf18df80a9c4dc00c5a7888fea09
- TRAIN feature order SHA256: 1c7f643034d3fd6d76154bd49d5a874ae08c0141f12620a81edb5f9ad5557d5d

No threshold fitting is permitted in the new TEST runner.

## Frozen interface topology

The interface topology is defined **only from column names**, before computing the new endpoint.

Local pneumatic components:
- CW1 = all derived features whose raw variable begins `CW1_`
- CW2 = all derived features whose raw variable begins `CW2_`
- MW1 = all derived features whose raw variable begins `MW1_`
- MW2 = all derived features whose raw variable begins `MW2_`
- MW3 = all derived features whose raw variable begins `MW3_`
- MW4 = all derived features whose raw variable begins `MW4_`

Shared global context:
- all derived features whose raw variable begins `TRAIN_`
- `AMBIENT_TEMPERATURE`
- `TRAIN_SPEED_ACTUAL`

A derived feature inherits the raw-variable group from the substring before `__`.

No component regrouping is permitted after endpoint computation.

## Contract

For each eligible minute state and horizon H in {1 h, 6 h}, the required future answer is the same four-bit event signature used by MetroAT V1:
- future failure flag,
- future non-normal failure-type flag,
- future maintenance flag,
- future non-normal maintenance-type flag.

A context/message cell is certified exactly when every eligible minute mapped to that cell has the same future-event signature.

Thus this experiment uses zero-error future-certification, not average prediction accuracy.

## Candidate summary/message family

For each component independently:

Context summary:
- quantization: q2 or q4 using frozen TRAIN thresholds;
- prefix depths: 1, 2, 4, 8, 16, ALL, truncated to the actual number of global-context features.

Local component message:
- quantization: q2 or q4 using frozen TRAIN thresholds;
- prefix depths: 1, 2, 4, 8, 16, 32, ALL, truncated to the actual number of component features.

Feature order within each group is the subsequence induced by the already-frozen global SHA256 feature order.

No new feature ranking is fitted.

## Constructed interface resources

For each candidate pair of context setting and local-message setting, report:

- context_setting
- message_setting
- q_eff = number of distinct observed context-summary symbols among eligible states
- m_eff = number of distinct observed local-message symbols among eligible states
- joint_cells = number of observed (context,message) cells
- certified_count
- certified_rate
- globally_safe = certified_count == eligible

The pair (q_eff,m_eff) is a **constructed feasible resource point only when globally_safe is true**.

When globally_safe is false, the setting still contributes to per-state actionability and destruction diagnostics but is not called a feasible point of the exact theoretical region.

## Primary endpoints

For each component and H in {1 h, 6 h}:

1. finite_interface_D:
   number and rate of eligible states certified by at least one candidate context/message setting.

2. REFUSE_interface:
   eligible states not certified by any candidate pair.

3. monotonicity:
   zero expected violations when either context or local representation is refined while the other is held fixed.

4. per-state minimal frontier:
   count how many states first become certifiable at nondominated context/message settings under the frozen representation-order lattice.

5. constructed globally-safe Pareto points:
   among globally-safe candidate settings, retain nondominated resource pairs (q_eff,m_eff).

6. centralized reference:
   recompute the earlier full-system q4,ALL certification on the same minute states and horizon.

## Secondary endpoints

- context-only certification;
- component-only certification;
- comparison of effective alphabet sizes;
- TRAIN-to-TEST stability of component ordering by finite_interface_D rate;
- whether multiple incomparable constructed Pareto points occur.

## Falsification criteria

The interface hypothesis is weakened if any of the following occurs:

- component grouping cannot be reproduced from the frozen schema;
- TEST feature set differs from frozen TRAIN;
- any threshold or feature ordering is re-fitted on TEST;
- refinement monotonicity is violated;
- all components have near-zero finite_interface_D despite centralized certification;
- apparent Pareto effects disappear on TEST;
- results depend on changing topology, grids, or thresholds after seeing TEST.

## Interpretation boundary

A positive result would show that the new interface/actionability geometry appears in a real industrial dataset under a pre-specified component decomposition.

It would **not** establish:
- causal failure prevention;
- optimal physical controller synthesis;
- exact minimality over all possible encoders;
- a deployed industrial safety guarantee;
- universal validity of INSACERMO.

The exact theoretical Pareto frontier minimizes over all encoders. This empirical V1 searches only a frozen finite family of quantized feature-prefix encoders and therefore produces **constructed upper-bound resource points**, not a proof of globally minimal interface complexity.
