# INSACERMO — MetroAT V1 — Final Prospective Holdout Record

Date: 2026-09-27  
Repository: benblak/insacermo-morphology-auto  
Branch: insacermo-metroat-prospective-v1

## Status

**OFFICIAL TEST HOLDOUT: SUCCESS**

MetroAT V1 was evaluated as a real temporal industrial system using the official TU Wien MetroAT v1 TRAIN/TEST split. The final TEST run used thresholds and feature order frozen from TRAIN only. No TEST retuning was performed.

This record does **not** claim a universal theorem or causal maintenance result. It documents an out-of-sample structural result under the declared INSACERMO contract and finite representation family.

## Dataset

MetroAT v1, TU Wien Research Data / Wiener Linien  
DOI: 10.48436/9ja0q-bq581

Official archives:
- train.zip — 1,578,314,818 bytes — MD5 6ba8fd0cd9c65b02ca5319e99a6fa002
- test.zip — 842,648,328 bytes — MD5 e5638ac4ced34231223015f1bfcb29d2

Observed schema:
- 101 observable variables
- 4 future-label fields
- 276 derived present-state features in the final 60-second representation

## Frozen question

How much present information may be destroyed while preserving the declared ability to distinguish future failure / maintenance event signatures?

Architecture:

RAW SENSOR DATA -> 60 s STATE -> CONTRACT -> INFORMATION REFINEMENT -> ACT / PROBE / REFUSE

Current operating point: q2, k=16.

Legal probes are frozen refinements toward larger prefixes and/or q4. No primary REPAIR is allowed in this experiment.

## Important pre-TEST corrections

Two implementation issues were found using TRAIN only and documented before TEST was opened.

1. Label sentinel semantics:
   - "No Failure" is normal, not a failure type.
   - "No Revision" is normal, not a maintenance type.

2. 60-second implementation:
   - the preregistration specified a 60-second past window;
   - an early TRAIN implementation accidentally used 60 minute-level rows;
   - the final implementation computes current / mean / change from raw samples inside each calendar minute.

No scientific endpoint, official split, horizons, q2/q4 rule, SHA feature order, current q2,k16 point, ACT/PROBE/REFUSE semantics, or no-retuning rule was changed after opening TEST.

## Final TRAIN reference

Run: 36322103082  
Implementation commit: 88903abf6d9607dcb1c513b1ac27124c7bb974e3  
Freeze receipt commit: 73188d4875de8c59cf7edb6b5a8e960d013f54d0

TRAIN:
- 249,990 minute states
- 276 features

### Horizon 1 h

Eligible: 222,746

- ACT: 10,148 (4.56%)
- PROBE: 212,598 (95.44%)
- REFUSE: 0
- finite D_info: 222,746 / 222,746
- infinite D_info: 0
- monotonicity violations: 0

Destruction relative to q4,ALL:
- k=4: 222,498
- k=8: 207,136
- k=16: 123,554
- k=32: 18,632
- k=64: 22
- k=128: 0

### Horizon 6 h

Eligible: 134,554

- ACT: 10,071 (7.48%)
- PROBE: 124,483 (92.52%)
- REFUSE: 0
- finite D_info: 134,554 / 134,554
- infinite D_info: 0
- monotonicity violations: 0

Destruction relative to q4,ALL:
- k=4: 134,018
- k=8: 115,880
- k=16: 56,097
- k=32: 6,007
- k=64: 10
- k=128: 0

24 h, 72 h and 168 h were **UNSUPPORTED_BY_CONTINUITY**, not failed endpoints. The maximum continuous TRAIN segment was 1,379 minutes, below 24 hours.

## Official TEST holdout

Run: 36324520031  
Final freeze commit: 05c5523b5ffb701579dfc9bea6d6d41a0a1fe92e

Provenance checks:
- retuned_on_test = false
- TRAIN thresholds SHA-256: 980c95f2cdbdea6ac8c7840d25b9a8e020ffbf18df80a9c4dc00c5a7888fea09
- TRAIN feature order SHA-256: 1c7f643034d3fd6d76154bd49d5a874ae08c0141f12620a81edb5f9ad5557d5d
- TEST feature schema matches TRAIN: true

TEST:
- 136,900 minute states
- 276 features

### Horizon 1 h

Eligible: 88,872

- ACT: 12,263 (13.80%)
- PROBE: 76,609 (86.20%)
- REFUSE: 0
- finite D_info: 88,872 / 88,872
- infinite D_info: 0
- monotonicity violations: 0

Destruction relative to q4,ALL:
- k=4: 88,171
- k=8: 67,258
- k=16: 28,445
- k=32: 4,587
- k=64: 23
- k=128: 0

### Horizon 6 h

Eligible: 41,953

- ACT: 5,635 (13.43%)
- PROBE: 36,318 (86.57%)
- REFUSE: 0
- finite D_info: 41,953 / 41,953
- infinite D_info: 0
- monotonicity violations: 0

Destruction relative to q4,ALL:
- k=4: 40,972
- k=8: 29,900
- k=16: 10,433
- k=32: 1,532
- k=64: 8
- k=128: 0

24 h, 72 h and 168 h are again UNSUPPORTED_BY_CONTINUITY.

## What the experiment establishes

Within the frozen MetroAT contract and tested finite representation family:

1. Coarser representations merge present states that require different future answers.
2. Refining information restores contract-relative actionability for those states.
3. The loss of future certification is strongly graded with representation depth rather than behaving as an all-or-nothing artifact.
4. The refinement relation is empirically monotone across every checked edge: zero monotonicity violations on both TRAIN and official TEST.
5. Every eligible state had finite D_info within the tested family.
6. The same structural phenomenon survived the official TEST holdout with TRAIN-derived thresholds and feature order, without TEST retuning.

A compact statement is:

> In MetroAT V1, under the declared future-event contract, present-information compression causes a measurable loss of future certifiability, while frozen information refinement restores actionability monotonically on an unseen official holdout.

## What it does not establish

- It does not prove INSACERMO universally correct for arbitrary systems.
- It does not prove that the selected sensors causally prevent failures.
- PROBE means refinement in the declared information family, not necessarily a physical intervention.
- The 24 h+ horizons cannot be judged from this dataset under the strict continuity rule.
- The result is contract-relative and representation-relative.

## Audit trail

Key files in this pack include:
- PREREG_FROZEN.md / .json
- SCHEMA_MAPPING_FROZEN.json
- TRAIN_SEMANTIC_CORRECTION_BEFORE_TEST.json
- TRAIN_60S_IMPLEMENTATION_CORRECTION_BEFORE_TEST.json
- TRAIN_FINAL_FROZEN_BEFORE_TEST.json
- TEST_OPENING_FROZEN.json
- OFFICIAL_TEST_HOLDOUT_SUCCESS_FROZEN.json
- run_train_mechanics.py
- run_train_diagnostics.py
- run_test_holdout.py
- MetroAT GitHub workflows
- frozen TRAIN artifact and official TEST holdout artifact
- SHA256SUMS.txt
