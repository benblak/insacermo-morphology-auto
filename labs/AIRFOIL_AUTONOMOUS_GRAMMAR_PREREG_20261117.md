# INSACERMO – Airfoil acoustics, pre-registration (2026-11-17)
Created **before** scoring the held-out acoustic outputs. Existing historical INSACERMO/C3 and Lean files remain FROZEN.

## Physical source
NASA Airfoil Self-Noise data (UCI ID 291): 1,503 wind-tunnel observations, inputs frequency (Hz), angle (degrees), chord (m), airflow speed (m/s), boundary-layer displacement thickness (m), target scaled sound-pressure level (dB).
Pinned GitHub source `rupakc/UCI-Data-Analysis` commit `b2937bc0f36f570b5a6bb4049656f5239a1f334c`, file `Airfoil Dataset/airfoil_self_noise.dat`, blob `9f6fdafab6a323514c2a0407dea680fcb23d6795`. Public archive previously known to the scientist; *the scores must not be looked at before this protocol is fixed*.

## Strict testing division
- The **entire 31.7 m/s wind-speed condition** is held out as a distinct, lower-speed physical setting (no response labels for constructing a model or queries).
- For all other speeds (39.6, 55.5, 71.3 m/s), allocate 60% to initial discovery and 40% to a challenge pool, by deterministic row ID salted hash `20261117:airfoil:<index>`, sorting hashes and taking first floor(0.6*n). Source order, not target, determines partition.
- No response from the 31.7 m/s holdout can be inspected until coefficients, final query indices, hypotheses and acceptance rules are frozen.

## Autonomous model grammar and protocol
- Candidate forms composed automatically from the five measured inputs: centered/scaled raw x_i, log1p-positive (log of strictly positive inputs; log1p on angle), squared centered x_i, pairwise raw products x_i*x_j, and three hinge bases max(0, standardized x_i - {-0.5,0,+0.5}). Normalizers fixed by discovery X only.
- Ridge least squares with L2 penalty 1.0 on non-intercept coefficients; intercept unpenalized.
- Greedy forward subset search among every generated basis expression, at most 7 terms, and accept any next term only if RMSE improves by >=0.05 dB in cross-validation that leaves each of the **three known wind speeds** out in turn. Inference uses acoustic labels from initial discovery only.
- Reserve 40 adaptive queries from challenge pool; at each step choose the unqueried case where committee predictions disagree most (fitted selected model, raw linear model, log-linear model). Record the pre-observation prediction and hidden answer. Refit each model after observing the answer; repeat full grammar search at rounds 10,20,30,40. No holdout labels are consulted.
- Refit final selected representation on discovery+40 adaptive query labels.
- Baselines: intercept-only and all five raw-input linear ridge, refit on **the same labeled rows**. Record active versus random query order comparisons separately if feasible, never pick best seed after viewing holdout.

## Precommitted validation
- On strictly held-out 31.7 m/s measurements, report RMSE, MAE, raw-linear comparator RMSE and learned formula, coefficients, query indices, every tentative contradiction. Report baseline even if hypotheses fail.
- **ACCEPT EMPIRICAL TRANSFER** iff final model RMSE <=5.0 dB AND at least 10% lower RMSE than the raw-linear model fit on equal labeled measurements. Otherwise **REFUSE_UNSEEN_CONDITION**.
- Separately report whether an active 40-query policy is more efficient than random at equal label cost; no efficiency claim without the comparison.
- No physical law is mathematically certified by good predictive error; this is an observational **empirical relation**, not a universal aeroacoustic theorem.
- Any model family remains constrained by the grammar; the program is not a physically embodied autonomous experimenter. The 31.7 m/s data is public historical information; independence is procedural rather than sealed from every possible auditor.

## Change control
No tuning of thresholds, partitions, feature candidates, regularization, complexity cap, or query budget after scoring. Report failures as failures. **Never change the historical kernel or proclaim Lean-certified model discovery.**
