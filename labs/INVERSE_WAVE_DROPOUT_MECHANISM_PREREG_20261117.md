# INSACERMO — Reverse the hidden observation clock, identify the missingness mechanism
2026-11-17. Research question selected **before examining time-local dropouts or weather associations**. This is a follow-up to the audited NOAA 30-minute wave sampling clock, not a new task/domain. The previously observed phase counts are known; time series of individual failures and associated weather have not been analyzed.

**Training (and sole mechanism selection):** NOAA buoy 41002, 2023. **Independent transfer/falsification:** buoy 42002 (2023), buoy 46002 (2023), buoy 41002 (2024), buoy 42002 (2024). No substitutions. Upstream original gz archives and SHA256 must match files in previous inverse-clock audit. NOAA 46002 (2024) is not in scope because that archive was previously unavailable.

**Eligibility for a true wave-sensor dropout:** raw standard met row with valid wind WSPD and valid pressure PRES, timestamp in the previously verified 30-minute schedule phase (UTC minute mod30=10), but invalid WVHT (sentinel or outside [0,40]). Exclude unscheduled 10-min records: their lack of wave data is a known acquisition protocol, NOT a wave-sensor failure. A complete 30-min predecessor must exist in the original file for temporal association test. Do not impute absent whole meteorological rows as wave-sensor dropouts.

**Precommitted finite mechanism grammar:** constant Bernoulli baseline; five binary covariates, defined before target labels are inspected:
(A) immediately preceding scheduled measurement missing, only if exactly 30m before in raw archive;
(B) current WSPD at/above 90th percentile of valid WSPD on TRAIN scheduled rows (all other stations use this frozen physical threshold);
(C) current pressure PRES at/below TRAIN 10th percentile;
(D) 00:00–05:59 UTC;
(E) current wind gust GST at/above train 90th percentile.
For each candidate learn dropout frequency for feature 0/1 with additive-one count smoothing, compare likelihood against baseline with BIC (one extra free parameter penalty log N). Select a candidate ONLY if BIC improves > 10, otherwise select NULL. No composite feature search, no retuning cutoffs on 2024 or holdouts.

**Validation:** Transfer the exact two dropout probabilities and frozen thresholds to each of four validation series (no retraining). Report sample size, missing-wave count, event rates by binary feature and log-loss and Brier vs frozen null, plus F1/precision/recall if meaningful. Strong mechanism claim only if selected nonnull and >=3/4 validation files improve log loss and Brier over frozen null, >=3/4 show same sign of event association, combined log-loss gain >= 5%, and min 20 dropout events in each. Otherwise REFUSE_MECHANISM; still report raw counts and all negatives. Do not treat observational association as causation.

**Independent control:** Separate code parses all five original NOAA archives, recomputes 2x2 feature/event contingency tables and model scores. File SHA and source tags pinned; check training model hash sealed BEFORE accessing validation files. Do not claim Lean proved the empirical mechanism. Lean should prove that observation masks never determine missing wave values and exact local-action criterion from all completions, as a mathematical boundary.

**Interpretation:** Even if the clock and a dropout mechanism are identified, high-frequency physical wave amplitudes remain unknown outside reported slots. It is mathematically invalid to infer a universal wave law from the reporting schedule alone. Archived MAX TOTAL / C3 Lean kernel stays unchanged.