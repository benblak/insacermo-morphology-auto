# INSACERMO — two real physical-series empirical results, 2026-11-17

**Status: isolated LOCAL PYTHON lab, NOT a historical INSACERMO engine change, NOT a Lean proof of physical laws.**

Pre-registered study (before running the final holdout): commit `433ea279169237103a4afdd092b173da436b36ed`, `labs/TWO_PHYSICAL_SERIES_AUTONOMY_PREREG_20261117.md`.

## Frozen source and partitions

- `statsmodels` 0.14.6 sunspots, 309 annual samples (1700–2008), 185 discovery, 62 challenge, 62 final chronological holdout. Canonical dataset SHA256 `4425242e45763740928ab4e1f7357fee786cd0780f0f3bf2673c0fe4211d6957`.
- `statsmodels` 0.14.6 elnino, 732 monthly sea-surface-temperature samples (1950–2010), 439 discovery, 146 challenge, 147 final chronological holdout. Canonical dataset SHA256 `943c737c7430447b21cc819212e97c7e4aa895042043c129f8d4f04d465bff36`.
- Same external program and 675 candidate **generated expressions** in both domains. The *grammar* (trend, hinges, harmonic sin/cos) was supplied; the target formulas and periodicities were not. Period search from 6 to 24 sample intervals.
- Autonomous learner chooses 16 challenge queries; six seeded random policies (17,31,43,59,71,89) make 16 queries each. All seven models, coefficients, traces, and queries were written to sealed JSON files **before** computing final holdout metrics.

## Results on strictly reserved data

| Domain | Selected period | Selected holdout RMSE | Linear RMSE | Gain | Verdict |
| --- | --- | ---: | ---: | ---: | --- |
| Monthly eastern Pacific SST | 12 samples (12 months) | 0.8266963 °C | 2.2031690 °C | 62.47695% | EMPIRICAL_TRANSFER_PASS |
| Annual sunspots | 10 samples (10 years) | 54.162703 index units | 57.071647 | 5.0970% | REFUSE_EMPIRICAL_LAW |

Predeclared gate required RMSE <=0.75 × discovery standard deviation AND at least 15% lower RMSE than the same-budget linear benchmark. Pacific met both; Sunspots met neither.

- Pacific: active query RMSE 0.826696, six random policies mean 0.827570; active better than **3/6**, so no strong advantage from adaptive ordering is established here.
- Sunspots: active query RMSE 54.162703, six random policies mean 54.613697; active better than **6/6**, **but all these results are inadequate to certify a reliable prediction**.
- **Independent Python auditor passed** on all 14 runs (7 per domain). Recomputed source checksums, chronological partitions, sealed JSON hashes, individual query predictions and answer traces, adaptive choices from the sealed committee, randomized choices, coefficients via an independent least-squares routine, and holdout errors. Thus the reported experiment is reproducible, not externally peer reviewed.

## Explicit deviations — do not conceal or retune

Although the main splits, period range, query budget, seeds, and acceptance thresholds match the pre-registration, **two implementation parameters differ from the written protocol**:

1. The document called for hinges at 40/60/80% of the discovery time interval; the actual generator places them at z=0.4/0.6/0.8 on *centered normalized time*, not the same times. Neither final model uses a hinge, but candidate ranking could be affected.
2. The document described ridge regularization as 0.1 scaled relative to discovery target dispersion; implementation uses a fixed coefficient penalty 0.1.

These deviations were discovered **after scoring**, so NO after-the-fact correction on this exposed holdout will be called pre-registered success. This is an **exploratory empirical test with recorded pre-registration deviations**, and should be rerun on fresh unseen cases for a strictly clean prospective claim.

No novel physical law was found: annual and seasonal oscillations are known, and the search representation is constrained. This is *not* proof that the program invents mathematics from scratch and *not* proof that adaptive experimental selection is universally optimal.

## Full reproducibility

Conversation artifact `INSACERMO_MAX_TWO_PHYSICAL_SERIES_AUTONOMY_20261117.zip`
SHA256 `9383710bc01f5a22b55d9a3bf8591164bd41f74bd4f9a513730814605ca111ee`
includes `discovery.py`, `independent_audit.py`, `audit.json`, `independent_receipt.json`, full sealed models and 224 queried observations with candidate predictions, README and SHA256SUMS.

The historical INSACERMO kernel, its frozen Lean proofs, site, and earlier laboratory results are unchanged.
