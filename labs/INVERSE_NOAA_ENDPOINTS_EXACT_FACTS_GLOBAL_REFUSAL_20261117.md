# INSACERMO inverse NOAA — EXACT observable changes across unobserved midpoint, rigorous REFUSE (2026-11-17)

The only priority is continuing the user’s INSACERMO reverse scientific search, based on the previously verified actual NOAA 30-minute wave reporting clock and clustered outages. Historical MAX TOTAL, C3, Lean kernel unchanged.

## FROZEN preregistration before examining adjacent physical wave heights
Commit `f52ddf5e5947aaaf3c407962d86671f2354236f3` defines exactly 5 same SHA256-pinned real NOAA NDBC raw archives: training/exploration 41002 2023, independent series 42002 2023, 46002 2023, 41002 2024, 42002 2024. Evaluate only timestamps with BOTH actual wave-height readings at t-30m and t+30m and a raw record at central t; mark center missing vs present. Never impute center. Strong physical association preregistered only if at least 3/4 holdout gap-vs-control differences are positive, >=20 gap intervals each, and a 1,000-replicate day-level cluster bootstrap pooled 95% lower bound >0.

## Actual NOAA observational results (GitHub Actions)
Real complete 60-minute endpoint intervals: **78,199**.
Of those, middle wave height unavailable at **195** expected reporting times.
Of 195, observed ENDPOINT values differ by >=0.5m at **8** intervals, each independently certified as a raw measurement comparison, and not evidence of the exact missing middle reading.

| Station/year | Genuine gap intervals with both endpoints | Endpoint change >=0.5m | Complete center control intervals | >=0.5m events in controls |
|--|--:|--:|--:|--:|
| 41002 2023 | 50 | 2 | 17,309 | 386 |
| 42002 2023 | 32 | 1 | 17,337 | 99 |
| 46002 2023 | 32 | 2 | 12,648 | 748 |
| 41002 2024 | 40 | 1 | 17,367 | 378 |
| 42002 2024 | 41 | 2 | 13,343 | 120 |

A concrete example from true NOAA source 46002 2023: UTC `2023-02-23T10:10:00+00:00`, observed heights 7.4m at t-30m and 8.0m at t+30m, **0.6m net observed change**, missing physical height at center **UNKNOWN**. There is NO justified claim of a 0.6m monotone rise during the gap; the path and any extrema are unknown.

### Strict hypothesis result: REFUSE, NOT PASS
The hypothesis 'large end-to-end wave changes are more frequent in gaps than controls' has 4/4 positive observed holdout rate differences and >=20 gaps each, but the day-cluster bootstrap 95% CI of the pooled rate difference is **[-0.0087273, +0.0508606]**, including zero. **`REFUSE_PHYSICAL_ASSOCIATION`**. The original contract's third gate fails; do not re-label this a discovery of the cause of missingness or of sea-wave dynamics. No new physical law discovered.

## Independent verification and Lean
- Completely different raw NOAA text reader `labs/independent_wave_endpoint_audit.py` validated all five original gzipped file SHA256s, all five 2×2 interval tables, threshold counts, and example timestamps/endpoint values. GitHub receipt `labs/wave_endpoint_results_20261117/independent_receipt.json`: **INDEPENDENT_WAVE_ENDPOINTS_PASS**, 195 gaps, 8 endpoint changes >=0.5m, 0 imputed midpoints. Status `independent_exit=0`.
- Lean 4.33.1 `labs/WaveEndpointObservability.lean`: certified finite observability statements that end-to-end measured change does not require a missing intermediate wave height; same endpoints are compatible with distinct hypothetical physical center values; exact height cannot be deduced from an absent observation. GitHub workflow `labs/wave_endpoint_results_20261117/status.txt`: **lean_exit=0**; source SHA256 `d29786ff50cff1b6c8992b60f95f53fc2c31eca66057affbeb37db0b7da8da95`. Lean does NOT certify NOAA data or prove a physical theory.
- GitHub workflow artifact `INSACERMO_NOAA_WAVE_ENDPOINTS_RAW_CERTIFICATES` preserves five actual gzipped source bytes, and original full audit receipt for 90 days. The audit output `labs/wave_endpoint_results_20261117/audit.json` includes five original historical source SHA256s, first five true gap examples per source, full bootstrap interval.

## Central INSACERMO reverse lesson
One can determine some truth about the world even when part of its observations are missing (e.g., exact *net difference of two observed wave measurements*) without pretending to know the missing observation. Conditional exact ACT for observed endpoint change (given instrument accuracy), unconditional REFUSE on the unknown midpoint and on a statistically unsupported cross-domain association. The source instrument process and genuine wave motion must remain separate. All original kernel code frozen; these are laboratory Python and Lean checks, not a proof that a C3 engine processed every raw line.

Further tests should only deepen causal discriminations with independent measurements and robust identification; never rerun old synthetic laws, Kepler, Wine, or replace refused hypotheses with post-hoc hits.
