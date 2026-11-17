# INSACERMO inverse — certifiable wave change across a missing measurement, not invented midpoints
**Preregistered 2026-11-17, before looking at the raw WVHT magnitudes adjacent to missing reports.** New isolated lab; prior MAX TOTAL/C3 kernel unchanged. Do not choose a different data source or outcome after inspecting results.

## Question
Given the previously independently discovered 30-minute observation clock, can INSACERMO tell (1) that a scheduled report is missing, (2) whether real measured wave levels changed across the gap, and (3) when the unobserved wave at the center remains underdetermined? Distinguish an exact *observed endpoint change certificate* from a physical causal law or prediction of missing values.

## Fixed real primary sources
Five SHA256-pinned NOAA NDBC .gz files previously audited: 41002/2023, 42002/2023, 46002/2023, 41002/2024, 42002/2024. Same SHA values as previous independent wave dropout audit, no replacements, no 2025. Contrast training/source series = 41002 2023; four other station-years are independent transfer/falsification domains for an empirical association. Previous work has inspected the dropout counts, NOT the adjacent physical wave-height differences used here. Archive source is NOAA historical stdmet records with UTC time and WVHT.

## Exact eligibility and no fabricated data
A triplet of actual raw NOAA records at t-30m, t, t+30m, with t at the observed 30-min wave clock phase minute=10 or 40, and **both endpoint WVHT values truly valid** in [0,40] m. Compare middle WVHT: missing => 'gap'; valid => 'control'. Convert recorded WVHT to 0.1-m resolution (integer decimeters) before comparing. Never impute WVHT for the midpoint. Exclude absent whole NOAA meteorological rows and triplets with missing endpoints; record exclusion counts. Overlap of triplets means independence cannot be assumed.

### Predeclared primary observed physical target
Observable 60-minute net wave-height difference `abs(WVHT(t+30)-WVHT(t-30)) >= 0.5 m` (5 decimeters). Secondary >=1.0m (10 decimeters), descriptive. Both are properties of genuinely observed ENDPOINT values and are decidable without a value for the absent midpoint, conditional on accuracy of the reported instrument values. Neither identifies wave amplitude nor path at missing t. For a missing middle, **all** outputs must explicitly mark its value `UNKNOWN`. The test does not infer that an absence is caused by wave motion.

## Null, comparison and fixed acceptance gate
Calculate for each archive:
- gap triples, control triples;
- event counts / rates in each; net-change rate ratio and difference;
- 0.5m and 1.0m counts for gaps;
- counts of gaps with observed nonzero endpoint change (>=0.1m);
- example first five certifiable gap intervals (UTC, both observed endpoints, no missing imputation).
The prior 41002/2023 series is **exploratory**; do not interpret selected signs as prospectively prespecified. Fixed hypothesis to challenge across other sources: 'strong net change more frequent in gap triples than in controls'. Pass only if >=3/4 holdout series have a positive gap-vs-control primary rate difference, each holdout has >=20 eligible gap triples, AND 1000-replicate day-level block bootstrap 95% CI lower limit of pooled 4-source gap-vs-control rate difference >0. Otherwise **REFUSE_PHYSICAL_ASSOCIATION**. Any observed changes across gaps remain valid observed endpoint facts whether or not association passes. Show sample sizes and zero cells.

Use fixed RNG seed 20261117 for day block bootstrap, per-source daily clustering; resample days within each holdout station-year, combine 4 series, and compute pooled gap rate minus pooled control rate. Strict no hidden-new-law claim.

## Formal boundary and independent audit
Independent second Python script must reparse raw bytes, recompute EVERY exact gap/complete interval table and example, verify SHA256s and never fabricate midpoint wave heights. Lean proof must establish (a) observed endpoints can certify at least a measured net difference without knowing midpoint and (b) the same observed endpoints are consistent with multiple distinct middle values, so no inference of the precise missing value without structural assumptions. These are formal logic statements, NOT Lean certifying NOAA physics. Archive exact source, sealed protocol and full negative outcomes.

No new physical law/novelty claim. No modification to the historical MAX TOTAL kernel or C3 Lean.
