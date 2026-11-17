# INSACERMO — unknown target, unknown exponents, physical invariant hunt
Protocol frozen 2026-11-17 **before downloading/viewing any dataset results** on this branch. Independent external Python lab. Original MAX TOTAL/C3/Lean and prior labs are frozen.

## New physical domain
NASA Exoplanet Archive `pscomppars` public catalogue, TAP endpoint `https://exoplanetarchive.ipac.caltech.edu/TAP/sync` ; query fixed and ordered by `pl_name`:
`SELECT pl_name,hostname,discoverymethod,pl_orbper,pl_orbsmax,st_mass,st_teff,st_rad,sy_dist FROM pscomppars ORDER BY pl_name`
All six physical channels have positive finite values, otherwise drop the row. Select **one planet per hostname** (alphabetically first `pl_name`) to avoid multiple planet leakage. Exclude all discovery methods except exactly `Transit` or `Radial Velocity`.
The oracle does not give the learner the physics channel names, discovery method, target column, exponent, constant, or law.
Record downloaded source SHA256 and publish source bytes in isolated lab for reproducibility. Dataset snapshot may change from NASA and will not be tuned after seeing results.

## Strict provenance caution
Semi-major axes may be *computed* from orbital period and stellar mass by catalog contributors; the table may encode Kepler-law assumptions. Finding that relation would be **catalogue consistency rediscovery**, not new independent evidence that Kepler's law is true. Prior public scientific knowledge is not erased.

## Frozen information partition
- Method `Transit`: stable deterministic hash SHA256(hostname+":insacermo:20261117") order, first 60% complete hosts form discovery, next 20% challenge, last 20% independent in-method holdout.
- Entire `Radial Velocity` method excluded from ALL selection, training and challenge; method-shift physical holdout.
- Require at least 250 discovery, 35 challenge, 50 Radial Velocity; otherwise report INFEASIBLE, never change partitions.
- Fixed **24** requested challenge target values; only 24 are revealed by oracle, not any holdout values.
- The learner sees 6 unnamed numeric columns on discovery, and challenge columns except target after selecting target.

## No given equation, no given target
From six anonymous positive measured channels, the system invents candidate multiplicative laws of the form
`X_j ≈ c × X_k^a` or `X_j ≈ c × X_k^a × X_l^b`
for every target j and 1 or 2 other feature columns. Intercept and **real-valued exponents are fitted freely from measured log-values**, not supplied as a fixed list of exponents. This is a programmer-defined multiplicative representation class, **not free invention of all possible mathematical syntax**.
For each candidate, evaluate 3 stable, host-hash based cross-validation folds on discovery only using median absolute log residual / SD(log target) + 0.2*90th-percentile abs log residual / SD(log target) + 0.005 per input feature. Require target SD(log target)>0.2. Tie-break (score, target index, predictor indexes).
Select best relation on discovery, with no target predesignation. Fix target after discovery; never select the target using holdout or challenge answers.

## Experimental self-direction
Keep five top-scored alternative laws for the selected target; at each step select a challenge row using disagreement of their predicted log-targets (std) multiplied by (1+0.2*min(3, nearest Euclidean distance of logarithmic normalized predictors to already queried rows)); deterministic lowest row ID on ties. Query the hidden target; after each query refit and re-score all candidate source pairs, permitting changes in predictor count and exponents, and save hypothesis and query history. Exactly 24 challenges.
Compare against **8** independent fixed seeded random-order query sequences (17,31,43,59,71,89,101,127), same 24-observation budget, same model fitting/reranking and same initially selected target; seal all 9 policies before accessing holdout targets.

## Acceptance gate — precommitted
Evaluate the selected model and the *best one-input formula refitted on same 24+discovery observed rows* against ALL strictly held-out Radial Velocity hosts. Report in-domain independent Transit holdout too.
`ACCEPT_CATALOGUE_INVARIANT_TRANSFER` only when:
1. external RV holdout median absolute relative error ≤5%;
2. at least 90% RV holdout predicted within ±15% of measured value;
3. RV median relative error at least 25% below one-input baseline; AND
4. in-method independent Transit holdout median relative error ≤5%.
Otherwise `REFUSE_CATALOGUE_INVARIANT`.
No thresholds or input columns changed based on unseen labels. Archive success AND refusals.

## Negative and failure controls
After sealing and scoring: 100 fixed-seed shuffles of holdout target assignments, compare original median accuracy. Report ALL 8 random same-budget controls, never select the best seed after holdout. Independently rerun algebra and rows to verify metrics; compare read-only hashes of sealed models. Report discovered column names **only after target selection** as an interpretation layer.
Explicitly report how many features were excluded for missingness, median/max error and possible catalog-derived circularity. Do not call any such physical relation a historical new discovery. No Lean theorem about orbital physics.
