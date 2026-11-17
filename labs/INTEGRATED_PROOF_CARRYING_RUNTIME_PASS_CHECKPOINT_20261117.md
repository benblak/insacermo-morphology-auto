# INSACERMO — Single orchestrated proof-carrying discovery laboratory (2026-11-17)

**VALIDATED PASS, not an aspiration.** Historical MAX TOTAL and C3 are NOT changed. This is an isolated external orchestrator connecting real observation, constrained law discovery and falsification, local representation repair, active query and real historical C3 Lean-gated decision authorization.

## The complete actually executed one-run protocol

Protocol preregistered BEFORE integrated run in commit `705c722dc3ae6093500892909047d78b2e2da01e`, file `labs/INTEGRATED_PROOF_CARRYING_RUNTIME_PROTOCOL_20261117.md`.

One process, `labs/integrated_proof_carrying_runtime.py`, ran **14 successive stages**:

1. `OBSERVE_REAL_NOAA`: read three original checksum-pinned raw NOAA NDBC .gz archives, 41002/2023, 42002/2023, 46002/2023.
2. `DISCOVER_UNKNOWN_CLOCK`: from 52,526 genuinely recorded 10-min observations, choose **30-min** wave-reporting clock from an unknown period via penalized Bernoulli likelihood.
3. `FALSIFY_ON_OTHER_REAL_STATION`: untouched 42002/2023, 52,464 observations; F1 **0.998282278843401**, no fitted phase or period retuning.
4. `REAL_ACT_NET_ENDPOINT_CHANGE`: actual NOAA 46002 on 2023-02-23T10:10 UTC: measured 7.4m to 8.0m over 60 minutes with unmeasured middle. Construct 2-world C3 contract guaranteeing observed 0.6m net endpoint change, obtain **ACT + same-input Lean certificate**.
5. `REAL_REFUSE_UNOBSERVED_CENTER`: the same input with two physically possible unknown middle heights, no exact-height action safe in both, obtain **REFUSE_ROBUST + Lean certificate**.
6. `DISCOVER_SYNTHETIC_LAW_CONDITIONALLY`: an unknown 24-bit monotone Boolean oracle, 212 queries, four minimal positive terms, full quotient coverage **ONLY conditional on monotonicity**.
7. `FALSIFY_MONOTONICITY_ON_ALTERNATE_DEVICE`: independent query-only adversarial VARIANT deliberately differs; observed positive subset and negative superset contradict inherited monotonicity on variant.
8. `LOCAL_REPAIR_OF_REPRESENTATION`: patch **one witnessed exception**, independently labeled local and with global validity REFUSED.
9. `CERTIFIED_ACTIVE_PROBE`: original C3 engine issues **PROBE** for a genuinely unqueried input on the alternate device; generated proof compiled and replayed.
10. `ACQUIRE_PROBE_RESPONSE`: actual second oracle process response received.
11. `CERTIFIED_ACT_AFTER_OBSERVED_PROBE`: conditional local two-world label contract updated from actual response; **ACT + verified C3 Lean proof**, ONLY on this input.
12. `CERTIFIED_STATE_REPAIR`: a genuine C3 **REPAIR** with a declared effective two-world state transition to an action-safe state; it is explicitly **SIMULATED**, not a command to the NOAA instrument.
13. `LEAN_CERTIFY_DYNAMIC_REAL_DATA_FACTS`: generate `NoaaEvidence.lean` from parsed original observed decimeters (74,80), compile with Lean 4.33.1, proving exact difference 6 decimeters, >=5 dm, and indistinguishable missing midpoints.
14. `CERTIFICATE_TAMPERING_AND_MISSING_LEAN_REJECTED`: altered authorized receipt rejected, missing Lean binary rejected, restored genuine receipt reverified.

## Machine-verified evidence

GitHub Actions `.github/workflows/insacermo-single-integrated-runtime.yml`:
- `labs/integrated_runtime_results_20261117/status.txt` has **runtime_exit=0** and **independent_exit=0**.
- `labs/integrated_runtime_results_20261117/audit.json`: **INTEGRATED_C3_LEAN_CHAIN_PASS**, 14 stages, five C3 receipts, and all scoped proof statements.
- **Five actual Lean-compiled and independently replayed C3 certificates**: `REAL_ACT_NET_ENDPOINT_CHANGE (ACT)`, `REAL_REFUSE_UNOBSERVED_CENTER (REFUSE_ROBUST)`, `SYNTHETIC_PROBE (PROBE)`, `SYNTHETIC_ACT_AFTER_PROBE (ACT)`, `SYNTHETIC_STATE_REPAIR (REPAIR)`. Original `insacermo_one_engine.py` Git blob SHA1 **bd5310b3692bcbad4e874005b7dd8eda90616f74** untouched.
- **Actual same-output Lean evidence dynamically generated** and compiled: `labs/integrated_runtime_results_20261117/NoaaEvidence.lean`, SHA256 `cdbb101a09f410ea57b0358d33d474a1fbac6be1066b0aa98d87caebccecdff4`.
- Distinct module `labs/independent_integrated_proof_audit.py` reparsed **three original NOAA gzip bytes**, checked their original SHA256s, the entire training reporting-phase contingency counts, independent station Brier and confusion matrix, actual endpoint recorded heights and absent midpoint, five model hash/receipt/source triples, checked 14 stages, and absence of universal discovery claim. Receipt `labs/integrated_runtime_results_20261117/independent_receipt.json`: **INDEPENDENT_INTEGRATED_BRIDGE_PASS**.
- Source of orchestrator SHA256 `00aa759c56c1f1f145075cf32d60f99e3d680a737e27cc84ede11a6285d2f7a4`, archived in `status.txt`.
- Reproducible raw .gz files, all C3/Lean proof sources and receipts and full stage log included in GitHub Actions artifact **INSACERMO_SINGLE_INTEGRATED_RUNTIME_NOAA_C3_LEAN** (90-day retention); JSON summaries/checkpoints in git. The earlier attempt failed because C3 requires ≥1 declared sensor even when depth 0; adapter only was fixed to supply a disabled placeholder sensor. That failure is preserved in prior git commit history, not represented as current result.

## Avoid overstating

**This is a real integration milestone, not full formal verification of all discovered sciences.**
- The programmed orchestration and period-search/symbolic-search Python algorithms are NOT formally verified in Lean for arbitrary input; their concrete raw-data outputs were checked by a separately coded empirical auditor.
- Only small local C3 finite contracts (max 8 declared worlds) and directly generated exact NOAA value equalities are kernel-certified. C3 was not extended to all 2^24 possible worlds.
- Boolean monotonicity is a conditional search premise (a predeclared counterexample on the changed device refutes it); the exception repair is an observed local patch, not proven globally.
- The binary oracle variants and repair transition are synthetic; NOAA sources are real, but no new physical law was discovered.
- Other earlier experimental representation learners (latent XOR, multi-domain scientific discovery), energy optimization and MAX TOTAL-specific semantics are not yet all imported into this one executable, nor end-to-end Lean verified. No retroactive claim that original engine alone magically performs all external lab research.
- **Fail closed:** any missing Lean compiler, bad proof or receipt must prevent positive authorization. Historical MAX TOTAL/C3 code and site frozen as instructed.

Run on a Linux system with Lean 4.33.1, Python 3 and NOAA network access:
```bash
export LEAN_PATH=.:lean PYTHONPATH=.:labs
lean -o C3/PortableFiniteVerifierV1.olean C3/PortableFiniteVerifierV1.lean
lean -o C3/PortableVerifierSoundnessV1.olean C3/PortableVerifierSoundnessV1.lean
lean -o C3/PortableExactSearchV1.olean C3/PortableExactSearchV1.lean
python labs/integrated_proof_carrying_runtime.py /tmp/insacermo_unified
python labs/independent_integrated_proof_audit.py /tmp/insacermo_unified
```

**Scientific inference:** this establishes a proof-carrying pipeline integrating observation, conditional discovery, falsification, local repair, local active questioning, C3 verdicts and exact Lean evidence on real data, with explicit source-provenance and independent Python audit. It does NOT establish an unrestricted autonomous universal scientist.
