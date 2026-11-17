# INSACERMO MAX — real CO2 physical-series discovery and falsification, 2026-11-17

**Status: LOCAL PYTHON EXPLORATION, independently audited. NOT GitHub Actions SUCCESS; NO NEW LEAN proof. Frozen historical INSACERMO/C3 unchanged.**

The experiment was preregistered on this branch at commit b6315c65f996ab03538daa027212467c90b64ef0 before holdout evaluation.

- Real historic weekly Mauna Loa CO2 observations from `statsmodels.datasets.co2`, 1958–2001.
- Discovery observations through 1985: **1390**. Challenge observations in 1986–1990: **261**, of which the adaptive learner queried **32**; untouched scoring interval from 1991: **574** records.
- Supplied restricted candidate grammar: polynomial trend degree 0, 1, 2, plus 0, 1, 2 Fourier harmonics; chronological cross-validation on discovery observations chooses family. The seasonal period is inferred by scanning 8–156 weeks without supplying the expected 52-week period.
- Inferred period: **52.0 weeks**; selected model quadratic trend and two harmonics.
- The learner chooses challenge measurements using disagreement of top-three candidate predictions; the final model and query sequence are sealed before holdout scoring.
- Holdout RMSE **4.4221243 ppm**, MAE and full coefficients in artifact. Linear baseline RMSE **6.4483425 ppm**, or **31.42% relative RMSE improvement**.
- **Verdict: REFUSE_OUT_OF_SAMPLE_LAW.** Prespecified rule required RMSE <2.5 ppm and at least 20% gain over linear. The first condition failed.
- Same-budget comparison: active sequence beat 9/10 fixed random sequences on this particular holdout, not a significant universal discovery claim.
- Independent auditor verified all reported metrics from sealed coefficients, 32 unique challenge query rows, their recorded oracle answers, and refusal threshold: `INDEPENDENT_AUDIT_PASS`.

Scientific interpretation: a restricted external Python experiment discovered a periodic structure in already well-known real measurements, but could not confirm the candidate law to the preset precision. No new CO2 physical law, no autonomous invention of representational primitives, and no generalization proof. Input archive is public, and the oracle is code-enforced rather than cryptographically isolated; genuine blinded prospective work is a separate unmet milestone. No new kernel change.

Reproducible user-facing artifact from this conversation:
`INSACERMO_REAL_CO2_AUTONOMOUS_FALSIFICATION_20261117.zip`
includes preregistration, runnable `real_co2_discovery.py`, `independent_audit.py`, sealed model, query trace, full `audit.json`, documentation and SHA256SUMS.
