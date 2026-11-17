# INSACERMO — Reverse discovery from the *absence* of observations, with real primary NOAA evidence

**Date:** 2026-11-17. Core priority, no modification whatsoever to frozen INSACERMO MAX TOTAL or C3/Lean historic kernel.

## Inverse reasoning / exactly what was discovered
The preceding genuinely novel wave-physics experiment honestly stopped as `INFEASIBLE` because wave channels had "missing" values. Instead of changing stations and rerunning a known-law detector, this lab asked whether absence itself is structured. Its unknown period was searched from 20 to 180 minutes, in 10-minute increments, using Bernoulli phase likelihood BIC, plus a constant-rate null model, without giving the learner the wave-data reporting cadence. All hypotheses and validation rules precommitted before parsing phase timing as commit `5f9e4e1daf21d801d08538b459608140ac06e1ad`.

**Discovery source (only):** NOAA NDBC 41002, 2023, 52,526 raw ten-minute meteorological records; height-of-waves `WVHT` present in 17,438 (33.20%). The learner found a period of exactly **30 min**, phase frequencies relative to 10-min bins `[0/17506, 17438/17512, 0/17508]` (phase indexes 0,1,2). A separate wave-related APD column independently yielded the same phase clock; wind `WSPD` did **not** find a periodic reporting schedule (null wins). This is *a data acquisition protocol*, not a novel natural law. It should not be called a newly discovered physical law; NOAA instrument schedules may document it.

The 2023 trained model was cryptographically sealed **before retrieving four falsification sources**, via SHA256 `cd5a8d8f3a343ccc8606a0677208ddb831da9b74e437ea03572b864638f5fd95`. The complete 3-bin probabilities were `[0.00005711674663, 0.99571771154505, 0.00005711022273]`, no refitting to 2023 or 2024 new sites.

## Truly cross-station/year validation (model fixed; no retuning)
| NOAA station | Year | raw rows | predicted reporting-event F1 | Brier gain vs null |
| --- | --- | ---: | ---: | ---: |
| 42002 | 2023 | 52,464 | 99.8282% | 99.486% |
| 46002 | 2023 | 38,338 | 99.8119% | 99.438% |
| 41002 | 2024 | 52,534 | 99.8570% | 99.572% |
| 42002 | 2024 | 40,453 | 99.8180% | 99.456% |

All six preregistered success criteria passed. **The forecast is for WHETHER a wave-height measurement is reported, not for the physical magnitude of wave height.** Reporting can fail at expected slots: real dropouts remain.

**Data provenance:** Five NOAA original compressed files, SHA256s and upstream NDBC URLs in `labs/inverse_clock_results_20261117/audit.json`. Original raw .gz stored in the GitHub Actions artifact `INSACERMO_REAL_NOAA_INVERSE_CLOCK_RAW_AND_AUDIT` with 90-day retention.

## Reproducible independent controls
- Completely separate source module `labs/inverse_noaa_clock_independent_audit.py` parses raw compressed text and row timestamps independently, independently recalculates all 15 channel×archive event phase tables, confusion matrices, Brier and F1, and checks compressed/decompressed file hashes. Receipt `labs/inverse_clock_results_20261117/independent_receipt.json`: **INDEPENDENT_NOAA_CLOCK_PASS**, five raw sources, 15 checks.
- Lean 4.33.1 compiled `labs/InverseNoaaClock.lean` successfully, source SHA256 `16760e950d905c088f1b8379c6e740c1bc0a8240bfeaa08d079395044f9d0e51`. It proves exact three-slot cycle, that a shorter 1-slot or 2-slot period cannot describe the idealized pattern, and that an unqueried exception cannot be excluded by finite observations. This checks mathematical properties **of a modeled clock**, NOT independent instrument truth.
- Status `labs/inverse_clock_results_20261117/status.txt`: `program_exit=0`, `independent_result=PASS`, `lean_result=PASS`. Frozen historic kernel blob `bd5310b3692bcbad4e874005b7dd8eda90616f74` unchanged.

## Concrete consequence for physical discovery
The 10-min meteorological source has systematically scheduled wave observability at only one of each three time slots. Blindly replacing the other 2/3 missing/sentinel wave heights with zero would bias the empirical reported-wave mean downward by a factor `17,438/52,526 = 0.33198797` (a **66.80%** underestimation) *in this 2023 archive*, conditional on using the whole 10-minute row count as denominator. This is an exactly reproducible count-based artifact, not a physical statement about the ocean.

## Boundaries
- Not a new physics equation or historical discovery, no new empirical dependence law between wind and wave height; likely documented NOAA sensor schedule.
- The phase grammar (periods 20..180min) and penalized binomial hypothesis selection are provided; the actual 30-min period and phase were discovered from 2023 observations.
- The model need not predict all real dropouts; all validation datasets were previously examined only for broad raw channel availability, never for specific phase before preregistration. This is an exploratory but cross-validated observation mechanism discovery.
- This supports a *different* crucial layer of INSACERMO thinking: before discovering laws, first find whether the **observation process** is censoring the world, and refuse interpretations that do not distinguish systematic sampling from natural absence. Historic original engine frozen.
