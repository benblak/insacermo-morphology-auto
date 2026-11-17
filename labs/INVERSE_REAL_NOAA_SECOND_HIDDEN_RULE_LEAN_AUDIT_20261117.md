# INSACERMO — THE REVERSE PATH: a second verified mechanism in real NOAA acquisition observations (2026-11-17)

The preceding test learned, *without being told the reporting period*, that wave-height presence is scheduled at 30-minute intervals in real NDBC 10-minute meteorological archives, and it validated that on four independently selected station-year series. This new isolated test retains that discovered clock, asks whether remaining **true missing measurements AT expected reporting times** themselves obey a further structure, and keeps MAX TOTAL/C3 original engine unchanged.

## Precommit BEFORE looking at temporal dropout structure
Fixed original protocol `labs/INVERSE_WAVE_DROPOUT_MECHANISM_PREREG_20261117.md` committed `da4e043587e01f642125034d057a543cc5b2ac01`. Five competing mechanisms: preceding wave sample was missing, high wind, low atmospheric pressure, UTC night, high gust. Train only 41002 year 2023, compare two-state empirical conditional Bernoulli with baseline using BIC; require ≥10 BIC gain before considering a mechanism; completely freeze fitted thresholds and probabilities before accessing the four other original raw sources. All raw gzip bytes checked against SHA256 of previous study. Exclude unscheduled 10-min lines and missing complete meteorological rows.

## Actual blind training and transfer: independently verified
- Automatically SELECTED: `previous_dropout`. 2023 41002 train counts 17,490 eligible consecutive scheduled 30-minute transitions and 63 current failures.
- Original exact 2×2 transition table: `[[17367,53],[60,10]]`, rows previous present / previous missing, columns current present / current missing.
- If previous wave height was received: **53/17420=0.3042%** chance next wave height is missing. If previous was missing: **10/70=14.2857%** chance next is missing. Empirical risk ratio approx **46.96×** (observational, no causal attribution).
- Model probabilities Laplace-smoothed `[0.0030995293307312594,0.1527777777777778]`, sealed original model SHA256 `6a43db4c88213cba6d71ca1d7aeb52f5704a1084804e2a10a19b1c0c2dbc8455`.
- Four held-out station-year series tested with **NO re-fitting**:

| Validation | eligible 30m transitions | current wave dropouts | risk after prior received | risk after prior missing | held-out logloss gain vs frozen constant risk |
|--|--:|--:|--:|--:|--:|
| NOAA 42002 2023 | 17,480 | 55 | 42/17,425=0.241% | 13/55=23.636% | **11.9457%** |
| NOAA 46002 2023 | 12,764 | 39 | 32/12,719=0.2516% | 7/45=15.556% | **8.2022%** |
| NOAA 41002 2024 | 17,496 | 38 | 33/17,446=0.1892% | 5/50=10.000% | **5.6498%** |
| NOAA 42002 2024 | 13,481 | 49 | 45/13,432=0.3350% | 4/49=8.163% | **2.3690%** |

**All four holdouts improved** both logarithmic loss and Brier score, and all four had the same positive dropout-clustering direction. Aggregate validation **log loss improvement 7.230574%**, passes preregistered >=5% threshold. Verdict `MECHANISM_ASSOCIATION_TRANSFER_PASS`. This is a statistical *predictive association* about SENSOR REPORTING FAILURES, NOT an unrecognized ocean physics law, and does not determine the underlying wave height in missing rows.

## Independent evidence
**Independent raw-audit PASS**, `labs/wave_dropout_results_20261117/independent_receipt.json`: entirely separate parser reads all 5 original NOAA.gz archives and recomputes the exact 5 contingency tables, logloss and Brier values on **78,711** real, eligible consecutive expected-reporting transitions; actual source integrity SHA256 all passed.

**Lean 4.33.1 PASS**, `labs/DropoutLogicalBoundary.lean` source SHA256 `cdb15dd62e09c170a4d1943225e2c843d56a779a6f6191ec82e09ab8c7846d56`, original CI result in `labs/wave_dropout_results_20261117/status.txt`. Lean proves exact comparison of conditional dropout rates for all five independently observed contingency tables; and a generic theorem showing that no decoder can recover a physical height uniquely from an absent measurement (two different heights yield the same missing observation). It does NOT prove the external measurement values or a physical causal theory. Original historical engine git blob `bd5310b3692bcbad4e874005b7dd8eda90616f74` unchanged.

## Understanding the three layers
1. Real dynamics: ocean wave height, not established by these results.
2. Sensor/protocol clock: discovered 30-minute reporting schedule.
3. Residual *dropouts of expected reports*: discovered event persistence, learned as a two-state predictive rule with positive cross-source external performance.

**Interpretation:** Not every missing wave entry means calm seas; many scheduled missing entries are linked to missingness in the preceding scheduled interval. No identification of the *cause* of those outages (radio connection, processing, instrument, weather) has been established. The dropout effect has differing magnitudes across station-years; tiny dropouts count means considerable uncertainty about the precise risk on a particular platform. Do not describe as globally universal; the physical waves remain unidentified where their readings are absent.

Source code: `labs/inverse_wave_dropout_mechanism.py`, independent audit `labs/inverse_wave_dropout_independent_audit.py`, Lean `labs/DropoutLogicalBoundary.lean`. Full original data files in GitHub Actions artifact `INSACERMO_WAVE_DROPOUT_RAW_AND_SCORES` for 90 days, result JSON and original sealed training model committed on this lab branch. No new version of historical engine, no site changes.
