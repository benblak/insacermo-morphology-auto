# INSACERMO MAX — Pre-registered autonomous search on TWO untouched physical time series
Date: 2026-11-17. This pre-registration is committed **before measuring holdout errors**.
Historical INSACERMO/C3/Lean and earlier airfoil results remain FROZEN.

## Scientific question
Without a supplied period, fixed target law, or human intermediate choice, can the same finite, transparent external program build a useful empirical representation of both (a) annual sunspot counts, and (b) monthly El Niño-region sea surface temperature observations, select 16 extra experimental observations, correct its hypotheses when challenged, and reject unsupported extrapolation?

## Frozen public physical data
Local `statsmodels` 0.14.6 bundled historic public datasets:
- sunspots 309 observations, 1700–2008, columns YEAR,SUNACTIVITY; canonical `DataFrame.to_csv(index=False)` SHA256 `4425242e45763740928ab4e1f7357fee786cd0780f0f3bf2673c0fe4211d6957`
- elnino 61 years × 12 monthly means, 1950–2010, flatten by year then month -> 732 readings; canonical `DataFrame.to_csv(index=False)` SHA256 `943c737c7430447b21cc819212e97c7e4aa895042043c129f8d4f04d465bff36`
Use sample index, NOT year/month name, as the independent variable. In particular do NOT tell the discovery engine that one series is annual or that the other is monthly.
These two physical series are already historically studied; no novelty claim for a cycle found in them.

## Strict chronological split
For N records: discovery indices [0,floor(.60N)), challenge [floor(.60N),floor(.80N)), untouched holdout [floor(.80N),N).
Only discovery labels may be read at initialization. The oracle reveals exactly **16** challenge labels on request; all other challenge labels remain hidden for model fitting and may be used only for independent posthoc audit. No holdout labels can be accessed until all active/random models and queried indices are written to disk.
Preliminary discovery includes at least 185 sunspot observations or 439 sea-temperature observations.

## Program-generated expression language
Allowed primitive syntax: constant; normalized time t; t²; optional positive time hinge at a fraction of discovery length; sin(2πt/P) and cos(2πt/P), plus their second harmonics; period P is NOT given.
Enumerate trend degree 0,1,2; harmonic count 0,1,2; period grid 6.0 through 24.0 *sample intervals*, increment 0.5. Optional hinge selection from 40%,60%,80% of observed time (no advanced regressors).
For fixed basis choose coefficients using ridge least squares (penalty 0.1 times discovery variance scaling for non-intercept terms); choose representation by two growing-time-origin validation folds (0–40% -> 40–60%; 0–60% -> 60–80% of currently acquired time-ordered labelled observations), score mean fold RMSE + 0.015*discovery target SD per non-intercept term; use deterministic tie-breaking. At least 3 candidate representations kept as a committee.
The generator may change trend degree, harmonic order, period and optional hinge after acquiring more observations; no target formula provided.
All fitting and expression search is supervised *parametric* learning from observations; it is not a proof of a physical mechanism and not unrestricted mathematical invention.

## Autonomous challenge protocol
At steps 1..16 choose unobserved challenge index maximizing disagreement of predictions from the 5 best cross-validated candidate expressions (standard deviation), tie lowest row ID; impose distance penalty `1+min(3, nearest selected challenge distance)/3` so not all queries cluster. At steps 0,8,16 rebuild the complete ranking of representations using all acquired labels, but leave precomputed feature normalizers frozen at discovery. Refit selected representation after each oracle call. Emit query trace and provisional hypotheses before holdout scoring.
Compare with **six** deterministic random challenge-query policies, seeds 17,31,43,59,71,89, under same search schedule and same 16-label budget. Evaluate ALL random policies; do not choose the most favorable one.

## Holdout and verdict rule
After sealing all models and query indices, evaluate strictly heldout chronological labels. Reference on the identical acquired 16+discovery observations: ridge linear trend in time (intercept + normalized t) and constant mean. Report final expression, period, all probe choices, holdout RMSE, linear RMSE, discovery y-SD, all 6 random controls and scores.
An **EMPIRICAL_TRANSFER_PASS** for each physical series requires BOTH:
(a) RMSE of selected formula <=0.75*discovery-label SD
(b) RMSE at least 15% below linear-trend comparator on holdout.
Otherwise **REFUSE_EMPIRICAL_LAW** with observed reasons.
No universal law is certified by prediction. No infinite-future claims or Lean theorem about the physical dynamics. Any formal certification would be independent finite-arithmetic verification of the numerical verdict only.

## Integrity
Do not change any threshold, split, grammar, query budget, random seeds or penalty after seeing holdout scores. Public historical data can never guarantee truly novel physical discovery. The automatic policy does NOT correspond to remote operation of a telescope or oceanographic sensor.
