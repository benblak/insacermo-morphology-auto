# INSACERMO — autonomous representation repair, blind synthetic finite tests (2026-11-17)

Status: LOCAL PYTHON LAB ONLY. No new GitHub Actions successful run, no new Lean proof. Historic INSACERMO and C3 frozen, unchanged.

Following the original autonomous Boolean-law lab and the separately documented **third real-domain efficiency failure** (net −287.88 queries after calibration on appliance consumption), this additional isolated laboratory asks: when the initial Boolean expression language is falsified, can a searcher automatically move to a minimally repaired representation and still refuse unsupported claims?

A generator creates 21,075 distinct Boolean behavior classes from constants/five inputs/AND/OR/XOR with syntactic cost ≤9; it is not handed the target formula or a candidate formula list. An independent subprocess answers queried bits. The search process chooses measurements by candidate disagreement or attempts to falsify apparent agreement. When no pure expression fits observed answers, the preprogrammed representation-repair operation XORs up to two isolated observed exceptions. If every base model requires >=3 exceptions, it refuses that **specific** model class. It does not claim no possible mathematical law exists.

Five randomized blind batches, six declared synthetic case types each: **30 cases**, **20 exact 32/32 finite-domain reconstructions**, **10 relative-model-class refusals**, five independent trace audit passes. For all accepted cases the complete 32-input truth table was queried, so no arbitrary unseen-function generalization is claimed. Preview accuracy at 16 observations, measured only after secret reveal on unqueried points, averaged 100% (simple xor), 91.2% (xor with one exception), 82.5% (composite with two exceptions) across five runs. This is prediction, not certification, and other case types performed worse.

Provenance: complete standalone Python scripts, audit.json records, independent verifier, README and SHA256SUMS are in conversation artifact:
`INSACERMO_MAX_AUTONOMOUS_MODEL_REPAIR_5x6_2026_11_17.zip`
SHA256: `e2335e4fcb57b0bc0cebaa75ca6cb4ed878a926368b6839bb7a7647a654008e8`.

Limits: handcrafted grammar and repair rule, known finite domain, synthetic oracles, no novel physical discovery; local independent code audit is not independent external peer validation; no Lean verification of synthesis. The historic C3 kernel and prior results are frozen. Next goal is **autonomous representation selection and real unseen measurements with out-of-sample falsification**, not adding another motor version or posthoc changing thresholds.
