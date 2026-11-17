# INSACERMO INVERSE — Discover an observation mechanism from its missing values
Frozen at 2026-11-17, BEFORE parsing minute-of-hour sampling phases in any real NOAA archive.

## Scientific question (inverse direction)
The previous physical-law experiment failed because missing observations were treated as if data did not exist. Can the **pattern of absence** itself reveal a hidden acquisition schedule, without knowing the wave sensor reporting period? This is discovery of an instrument/data-protocol regularity, NOT discovery of novel physical dynamics.

### No arbitrary target search
Primary observed bit is WVHT valid (1) vs missing/sentinel (0). APD valid (independent same-family cross-check) and WSPD valid (negative control). A raw NOAA archive includes 10-minute samples and associated UTC timestamps. The learner knows only these binary event flags and timestamps; no supplied period, wave schedule, or phase. It has a GENERIC periodic clock grammar P = 20, 30, ..., 180 minutes (2–18 ten-minute slots), plus a phase-independent null model. Period chosen by penalized binomial likelihood (BIC) using **only NOAA 41002 2023**. Default model is phase-independent. Laplace smoothing 1 count per class for out-of-sample predictions. No retuning of period or phase after choosing.

### Data sources and order
Training NOAA 41002 in 2023, 
https://www.ndbc.noaa.gov/data/historical/stdmet/41002h2023.txt.gz
Four validation files, NEVER used to select a period or a phase:
- NOAA 42002 in 2023
- NOAA 46002 in 2023
- NOAA 41002 in 2024
- NOAA 42002 in 2024

Exact URL form https://www.ndbc.noaa.gov/data/historical/stdmet/<station>h<year>.txt.gz. These files were already confirmed accessible in previous attempt, but *minute-phase wave-presence breakdowns had not been analyzed* for this new inquiry. Their overall sensor-valid counts were previously inspected, so do NOT imply that all aspects of holdout files were unseen.

### Evaluation and falsification
For WVHT, select clock family only if it beats null under training BIC, with minimum 10 BIC-point difference. Record period, phase response probabilities, empirical individual phase rates, and cross-validated Brier score, Bernoulli log loss, F1 for present-wave class, true-positive recall and precision, for every station-year. The exact phase probability model is transported without change to all four validations. Strong pass means four validation F1 >= 0.90 and Brier score improves > 40% over null for all four (null probability obtained from training only). Negative control WSPD should prefer null or have no >10 BIC-point periodic advantage. APD check must have same inferred period and agree on >=99% of raw wave-present indicators in the training series.

An independent second script parses raw NOAA bytes separately, validates row-level timestamps, period and expected exact phase event counts, and recomputes all scores. All source gzip SHA256 values are retained, raw blobs uploaded to GitHub artifact. No substitutions, no selective periods after a failed evaluation, no exceptions. Infeasible files => explicitly INFEASIBLE. Main mechanism cannot claim a physically novel law nor prove universal scheduling rules from finite observations. Historical MAX TOTAL/C3/Lean kernel remains exactly frozen.
