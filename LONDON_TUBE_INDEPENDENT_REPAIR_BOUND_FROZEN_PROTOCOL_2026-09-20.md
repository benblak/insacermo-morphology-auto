# INSACERMO London Tube Independent Repair-Bound Test — Frozen Protocol

**Freeze date:** 20 September 2026  
**Status:** preregistered before computing the endpoint on this dataset.

## Purpose

Independent transport-network test of the nontrivial repair-bound endpoint discovered on OpenFlights.

The target inequality is:

\[
1=c_{\rm trivial}<\tau_w\le C^*_{\rm repair}.
\]

A null result is retained if \(\tau_w=1\), if no suitable newly created obstruction exists, or if the atomic repair model is not adequate.

## Independent dataset

Repository: `nicola/tubemaps`  
Frozen commit: `f20f2ad9397e4a1756770d1111b7f5d2413244bc`

Files:

- `datasets/london.connections.csv` — Git blob `e82645fc4fb49a671730fa57b6afe19244d25732`
- `datasets/london.stations.csv` — Git blob `cdaa3638d69cd534675201c60904955c4acab29f`
- `datasets/london.lines.csv` — Git blob `355aec097b1f26c3f40784dcb577c9cce423fe4c`

The network is treated as undirected. If several Tube lines share the same station pair, the edge survives deletion of a line whenever at least one undeleted line still serves that pair.

## Frozen contract construction

- start station: **Baker Street**
- route horizon: **H = 8 edges**
- maximum future-bundle size: **3**
- target count: **25**

Targets are selected mechanically, without endpoint inspection:

1. compute baseline unweighted shortest-path distance from Baker Street;
2. retain stations with distance in \([3,8]\);
3. order retained stations by `SHA256(station_name)`, with station name as tie-break;
4. take the first 25.

This deterministic target rule is frozen before running the repair-bound endpoint.

## Frozen degradation / repair classes

The two degraded Tube lines are selected mechanically from the raw connection data, without looking at future feasibility:

1. count connection rows for each line id;
2. rank by descending count, with line id as ascending tie-break;
3. select the top two line ids.

The degraded state removes both selected line classes.

Concrete repair actions:

- `NONE`, cost 0
- `RESTORE_A`, cost 1
- `RESTORE_B`, cost 1
- `RESTORE_BOTH`, cost 2

No line pair will be changed after observing the result.

## Future complex

For each scenario, for every target bundle \(F\) of size 1, 2, or 3, compute the exact minimum number of edges in a route starting at Baker Street that visits every station in \(F\).

A bundle is feasible at horizon \(H=8\) iff that minimum is at most 8.

A minimal obstruction is an infeasible bundle whose every proper nonempty subbundle is feasible.

The endpoint uses **new minimal obstructions**:

\[
\mathcal O_{new}
=
\mathcal O_{degraded}\setminus\mathcal O_{baseline}.
\]

## Repair capability and soundness

For each new obstruction \(O\), singleton repair capability is derived by direct recomputation:

- A can resolve \(O\) iff `RESTORE_A` makes \(O\) feasible;
- B can resolve \(O\) iff `RESTORE_B` makes \(O\) feasible.

No repair capability is assigned by hand.

Let \(\mathcal O_{atomic}\subseteq\mathcal O_{new}\) be the obstructions resolved by at least one singleton repair class.

The transversal price \(\tau_w\) is the minimum unit-cost subset of \(\{A,B\}\) hitting every capability set of \(\mathcal O_{atomic}\).

The exact repair price \(C^*\) is computed over the four concrete repair actions as the least cost restoring every obstruction in \(\mathcal O_{atomic}\).

Obstructions requiring both classes jointly but neither singleton are reported separately and are not silently assigned to either atom.

## Frozen endpoints

Report:

- selected line A and line B;
- 25 selected target stations;
- baseline and degraded feasible-bundle counts;
- baseline and degraded minimal-obstruction counts;
- number of newly created minimal obstructions;
- number in \(\mathcal O_{atomic}\);
- counts resolved only by A, only by B, by either, and by neither singleton;
- trivial lower bound \(c_{trivial}\);
- transversal price \(\tau_w\);
- exact repair price \(C^*\);
- ratio \(\tau_w/C^*\).

### Primary endpoint

Success only if:

\[
\boxed{1=c_{trivial}<\tau_w\le C^*}
\]

with at least one order-\(\ge2\) obstruction exclusively requiring A and at least one order-\(\ge2\) obstruction exclusively requiring B.

Otherwise the primary endpoint is **NULL**.

## Guardrails

- no change to start station, horizon, target count, target-selection rule, line-pair rule, bundle size, repair costs, or endpoint after observing the result;
- no search for a better London line pair after a null result;
- this is an independent dataset from OpenFlights, but it is one finite historical transport network, not evidence of universality;
- Lean certification of the abstract lower-bound theorem does not validate the empirical model assumptions.
