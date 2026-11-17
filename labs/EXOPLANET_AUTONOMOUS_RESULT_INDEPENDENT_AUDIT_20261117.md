# INSACERMO — NASA exoplanet target-free law redetection, verified 2026-11-17

**Result: ACCEPT_CATALOGUE_INVARIANT_TRANSFER. Independent source and query-trace audit PASS.** Historical INSACERMO MAX TOTAL and C3/Lean code remain frozen, completely unchanged.

Preregistered BEFORE observing outcomes: `labs/EXOPLANET_UNKNOWN_LAW_PREREG_20261117.md`, Git commit `af1c43d3a5e47e830bb2bfeccba2a26da58b964b`.

Original data: NASA Exoplanet Archive `pscomppars`, 6 measured or adopted positive numeric channels plus planet name, hostname and discovery method; one planet per host. Query source SHA256 `2d35f6c7b82e55957f33e64adf010e26f5131996460634774aeb82d0ab0f3252`. Counts: 6470 catalogue rows, 5506 eligible rows with all six positive measurements, 4071 unique-star records, 1981 Transit discovery, 661 Transit challenge, 661 withheld Transit holdout, 768 wholly withheld Radial Velocity holdout.

Discovery program was not given a target variable, power-law relation, exponents, or Kepler's Law. Its **programmer-specified** grammar generated one-/two-input multiplicative expressions; log-space exponents were fitted from the initial data. Automatically selected target `pl_orbsmax` (orbital semi-major axis, astronomical units) and predictor channels `pl_orbper` (days) and `st_mass` (stellar solar masses).

Discovered relation:

```
a (AU) ≈ 0.01947349060727095 * P(days)^0.6681187903564834 * Mstar(Msun)^0.32624595590461786
```

For comparison, the low-planet-mass approximation to Kepler's third law is `a(AU) ≈ (P(days)/365.25)^(2/3) * Mstar(Msun)^(1/3)`; expected P exponent 0.66667 and stellar mass exponent 0.33333. The found scaling is numerically similar.

Precommitted gate and withheld Radial Velocity results (768 different host systems):
- Median relative error selected: **0.47147766957524856 %**
- 90th percentile relative error selected: 5.865837646981345 %
- Fraction within 15% relative error: **0.9661458333333334**.
- One-input baseline median relative error: **6.7739883766169875 %**.
- Withheld Transit test (661 hosts), median relative error: **0.8504805793138756 %**.
- All four preregistered gates passed.
- Precommitted 24 challenge-target oracle responses.
- 8 random-query controls with same budget: active beats **4 of 8** by RV holdout median error. **No general query-efficiency superiority demonstrated**.
- Auxiliary 100 posthoc shuffled-target controls: 0 as accurate as original. Not a prespecified acceptance criterion.

Independent replay: `labs/exoplanet_independent_audit.py` validates source SHA256, all four host partitions, independently selected target/initial representation, per-step oracle choices and prior forecasts, final regression parameters, one-input reference and all held-out metric/verdicts across **9 policies × 24 challenge steps = 216 verified steps**.
Receipt `labs/exoplanet_results_20261117/independent_receipt.json` says:
`INDEPENDENT_SOURCE_AND_216_PROBES_AUDIT_PASS`.

**Critical limitation — do NOT claim historical discovery or independent validation of gravity:**
The NASA PSCompPars catalog is a compilation of published and some calculated parameters. Some semi-major axes can be determined from orbital period and stellar mass using Kepler's already-known law. Agreement here may therefore be internally constructed **catalogue consistency**, not an independent physical test. The archive notes the use of calculated parameter fields, and many exoplanet catalogues derive semi-major axis with Kepler. The algorithm's syntactic grammar (power laws with ≤2 inputs), cross-validation, 24-query budget and acceptance gates were all programmed; no mathematics invented without any assumptions. No new astronomical observations were made or requested from a telescope; no novel mathematical law or Lean proof of the orbital formula exists.

Scientific next test must use independently measured raw quantities, such as raw light-curve timing and radial-velocity measurements, or separate direct orbital distances with verified provenance, and independently test not-yet-used observations; do not relabel this catalogue rediscovery as new fundamental physics.

Files: `labs/exoplanet_target_free_discovery.py`, `labs/exoplanet_independent_audit.py`, `labs/exoplanet_results_20261117/audit.json`, `labs/exoplanet_results_20261117/sealed_before_holdout.json`, `labs/exoplanet_results_20261117/provenance.json`, `labs/exoplanet_results_20261117/independent_receipt.json`.
