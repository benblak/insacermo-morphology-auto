# INSACERMO target-free invariant search — independent lab result (2026-11-17)

## Registered *before* final scoring
See `labs/TARGET_FREE_INVARIANT_PREREG_20261117.md`, commit `d07e88c176b445ec94c065f5b5aebd3a1c7a62ea`. Historical INSACERMO/MAX TOTAL, C3, Lean, web site are UNMODIFIED.

## A genuinely different question, not a target-supplied regression
From an array of unnamed real-valued feature channels, the searcher decides **which channel to explain**, **which other channel**, **which exponent**, **which coefficient**, and adaptively requests 20 further target readings. This is an autonomous target selection **within a fixed, programmed power-law grammar**, not unconstrained mathematics invention.

| Source/train->excluded regime | Chosen target | Candidate relation | Excluded samples | Median relative error | Fraction under 10% | Verdict |
|--|--|--|--:|--:|--:|--|
| Real WDBC morphology, 1→0 | mean radius | radius ≈ 0.57053012 × sqrt(mean area) | 212 | 0.608702 % | 100 % | ACCEPT |
| Same real WDBC morphology, 0→1 | mean radius | radius ≈ 0.56766792 × sqrt(mean area) | 357 | 0.504535 % | 100 % | ACCEPT |
| Real Wine chemistry, classes 0,1→2 | alcohol | alcohol ≈ 1.31011840 × sqrt(magnesium) | 48 | 5.407547 % | 87.5 % | REFUSE |

Precommitted acceptance gate: median relative error <=4%, >=90% of held-out predictions within 10%, >=50% reduction vs constant-median predictor.

## Independent reproducibility
An independent, separately implemented Python auditor **PASS** replays **27 different policies × 20 probes = 540 individual probe decisions**, independently reconstructs target choices, discovers candidate ordering and coefficients, verifies every policy's entire query history, fixed random-seed controls, heldout metrics, source hashes and acceptance/refusal. All heldout labels read for scoring only after sealed query traces are written. No Lean certificate produced for these relationships.

- Adaptive selection beats random controls only **1/8, 0/8 and 2/8**, respectively; NO superiority of query efficiency is established.
- Posthoc 1000-permutation tests destroy WDBC row-wise correspondence in both directions (0/1000 permutations as good as original), but not for Wine (836/1000 as good or better). They are auxiliary falsification tests, **not** a precommitted new acceptance gate.

## Strong scientific limitations
- The WDBC radius-area relation is a familiar, unsurprising morphological/geometrical dependency; **no discovery of a new biological law** and not diagnostic medical research.
- The experimental designer had explored radius/area ratios prior to preregistration, so the scientist was **not human-blind**; only the software searcher was not given a target. The instrument's numeric feature search is restricted to hand-defined exponents -2,-1,-.5,.5,1,2.
- WDBC and Wine are domains used previously in INSACERMO research. The new ability demonstrated is target-free synthesis, not a novel data source.
- An external retrospective lab, no novel physical law, no claim of energy savings or medical validity, historical engine remains frozen.

## Deliverables
Reproducible complete user-conversation ZIP: `INSACERMO_TARGET_FREE_INVARIANTS_20261117.zip`
ZIP SHA256: `3125ada5efe6c26dc3e6efca060e8c1f310bdd9eab01bf16ed9dbbda0b6c0ee4`.
Includes full `run.py`, independent `independent_audit.py`, `negative_controls.py`, all **three sealed policy traces**, reports, README and source SHA256SUMS. Runs locally with scikit-learn and NumPy.

**Next consequential requirement:** discover nontrivial relations on genuinely new physical data from a representation language that can itself adapt, and prove out-of-sample causal/predictive claims where possible; do not spend further cycles restaging WDBC/Wine.
