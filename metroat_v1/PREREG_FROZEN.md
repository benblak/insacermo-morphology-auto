# INSACERMO — MetroAT Prospective Information-Destruction Test V1
**Status:** FROZEN BEFORE DATA VALUES / HOLDOUT UNOPENED
**Date:** 2026-09-27
**Framework baseline:** INSACERMO V1.3 Freeze (2026-09-27)

Official dataset: MetroAT v1 (TU Wien / Wiener Linien), DOI 10.48436/9ja0q-bq581.
Official archive hashes frozen before values:
- train.zip MD5 6ba8fd0cd9c65b02ca5319e99a6fa002
- test.zip MD5 e5638ac4ced34231223015f1bfcb29d2

Primary protocol frozen before numerical values:
- official TRAIN/TEST split unchanged
- failure/maintenance variables prohibited as current features
- decision states at one-minute boundaries
- trailing 60 s features only
- deterministic SHA256(feature_name) order
- k in {4,8,16,32,64,128,ALL}
- q2 TRAIN medians, q4 TRAIN quartiles
- horizons 1h,6h,24h,72h,7d
- current setting (q2,k=16)
- verdicts ACT/PROBE/REFUSE
- D_info frontier and q4 information-destruction audit
- no TEST retuning; negatives retained

Full preregistration SHA-256 (local frozen artifact):
adfaab8650554c2c901794a755508b02314c36e97d7ae9124052b9ae048ac0e2
