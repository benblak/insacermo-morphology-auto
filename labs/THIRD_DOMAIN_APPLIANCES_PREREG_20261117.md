# INSACERMO — Pre-registered third-domain transfer, 2026-11-17

Parent: verified two-domain run 44046321838, SHA cc11849e102526f5a03efdf24e38a2a36a04a93d.
Historical C3 kernel, Lean files, and two-domain script MUST NOT be edited.
This is one external laboratory evaluation. No tuning after viewing holdout labels.

DATA
- UCI Appliances Energy Prediction, 19,735 10-minute real readings, 2016.
- Publisher source: LuisM78/Appliances-energy-prediction-data at commit e3e4c27a4ae2b41b21f84b4c9ac2d822d3d0ace1, file energydata_complete.csv.
- Target: Appliances in Wh. FIXED THRESHOLD: 100 Wh (>=100 = positive).
- Do not use date, Appliances, lights, rv1, rv2 as proxy features. Use all other
  numeric sensor/weather columns in source order. No feature engineering.

PARTITION
- Calibration: 256 earliest chronological target labels (fully charged).
- Evaluation: all later rows, SHA256 sorted using namespace
  "appliances-third-20261117", seed 20261117, deterministic 8-row groups.
  Exclude at most 7 unmatched rows. No holdout target used for ordering.

UNCHANGED QUERY POLICY
- Same Python calibration_policy from labs/calibrated_probe_order_two_power_domains.py.
- Select ONE feature by largest abs standardized positive-negative mean gap
  on calibration only, tie by input index.
- Query likely negatives first, sorted by calibrated sign * selected feature.
- Contract: certify >=6 positives among 8, or <6; stop only at 6 observed
  positives or 3 observed negatives; every unknown outcome remains arbitrary.
- No trained neural network, no new engine logic.

SCORING
- Exact random-permutation expectation, per group, by hypergeometric sum.
- Net benefit = exact random total - actual selected-order queries - 256.
- Report calibration classes, selected feature, direction, all groups,
  errors, means, gross and net benefits, independent all-completions audit.
- Transfer success iff net benefit > 0 and zero contradicted decisions.
- No alternative cutoffs, variables, calibration budgets or domains chosen
  after result. Failed transfer must be reported.

INTERPRETATION
- Archived public measurements, not a real-time physical campaign.
- Selection uses supervised calibration external to frozen C3; guarantees
  come from exact stopping logic, not from predictive accuracy.
- Original Lean C3 certificates certify their declared local contracts,
  not the entire data-processing script.
