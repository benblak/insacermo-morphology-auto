# INSACERMO — Exact Pre-Audit Depth r = 7 (PGLib IEEE-14 DC)

**Status:** exact rational pre-audit closure  
**Date:** 2026-09-25  
**Branch:** `insacermo-structural-audit-kernel-v1-20260920`  
**Scope:** encoded DC linear feasibility model, PGLib IEEE-14 active-power-increase case, catalogue of 8 load goals.

## Executive result

The structural pre-audit depth is now certified exactly, in rational arithmetic, for the encoded DC LP and the fixed 8-goal catalogue:

[
r_{\mathrm{pre}} = 7.
]

The exact run reports:

- `STATUS EXACT_RATIONAL_PREAUDIT_DEPTH`
- `TOTAL_EXACT_EXTREME_RAYS 80276`
- `EXACT_ORDER8_COMPATIBLE_RAYS 0`
- `EXACT_ORDER7_WITNESS_FOUND 1`
- `EXACT_PREAUDIT_UPPER_BOUND 7`
- `EXACT_PREAUDIT_LOWER_WITNESS 7`
- `EXACT_PREAUDIT_DEPTH 7`
- `GLOBAL_TIGHT_PREAUDIT_R 7`
- `BUNDLE_FEASIBILITY_CALLS_TO_DERIVE_R 0`
- `BUNDLE_ENUMERATION_USED_TO_DERIVE_R 0`
- `RESULT COMPLETE`

Thus the pre-audit derives the same depth previously observed by exhaustive bundle auditing without using bundle feasibility to derive the number.

## What changed from the numerical V2

The earlier V2 result was already structurally independent of bundle enumeration, but it still used floating-point linear algebra and SVD to discover and measure extreme Farkas rays.

RUN 283, after the SVD tolerance correction, produced:

[
\texttt{GLOBAL\_TIGHT\_PREAUDIT\_R}=7,
]

with zero feasibility calls and zero bundle enumeration used to derive the bound. The correction fixed a real numerical defect: a structurally zero projected singleton column could appear numerically around (10^{-14}), and a purely relative SVD threshold could incorrectly classify it as full rank. Adding an absolute tolerance floor restored the missing singleton rays; for outage 1 the ray count became 362 in the numerical pipeline and the depth became 7.

This correction did not inject the desired answer. It repaired the nullspace detection mechanism.

## Exact V3 closure

The exact checker replaces floating/SVD reasoning by exact rational arithmetic over the finite-decimal PGLib data.

For the equality system and inequality system

[
A x=b_F, qquad Gx\le h,
]

Farkas stationarity is

[
A^T y + G^T z = 0,qquad z\ge0.
]

After projection through an exact basis of (ker(A)), the checker enumerates the positive circuits/extreme rays of the projected cone exactly.

For the regular outages, the projected cone has rank 2 and all extreme rays are exhaustively captured by singleton, pair and triple supports. Branch angle-difference rows are removed only after an exact dominance check showing that the thermal flow bounds imply the ±30° angle bounds for this benchmark, so the reduced LP is feasibility-equivalent for the tested model.

### Special case: outage 13 (branch 7–8)

The first exact run failed here with:

[
dimker(A)=3
]

instead of the expected 2.

This was not a counterexample to the depth result. The outage isolates bus 8, which has no active catalogue load and no active generator in the encoded model. Its nodal balance becomes the trivial equation (0=0), and its angle variable appears only in its own independent finite bounds.

The exact checker was therefore corrected by factoring out only this independent feasible product component:

- 1 zero equality row removed,
- 1 isolated angle variable removed,
- 2 independent bound rows removed.

After this exact factorization, outage 13 again has projected nullity 2, with 4,302 exact extreme rays and zero order-8-compatible rays.

## Exact upper bound: no order 8

Across all 20 single-branch outages, the exact checker enumerated:

[
80{,}276
]

extreme Farkas rays.

Among all of them:

[
oxed{\texttt{EXACT\_ORDER8\_COMPATIBLE\_RAYS}=0}.
]

Therefore, under the pre-audit criterion based on extreme Farkas rays and one-deletion minimality,

[
r_{\mathrm{pre}}\le 7.
]

This is exact over the rationalized encoded LP; no numerical tolerance is involved in the final comparison.

## Exact lower witness: order 7

The checker also finds an exact order-7 witness:

- outage: 0,
- branch: 1–2,
- exact ray support indices: `0,68`,
- goal buses: ({3,4,2,14,13,6,10}).

The exact quantities are:

[
\beta = 358,
]

[
S=\frac{37117}{100}=371.17,
]

[
p_{\min}=\frac{1769}{100}=17.69.
]

Hence:

[
S-\beta=\frac{1317}{100}=13.17>0,
]

and

[
\beta-(S-p_{\min})=\frac{113}{25}=4.52>0.
]

So the ray satisfies exactly the order-7 one-deletion minimality compatibility inequalities:

[
S>\beta,qquad S-p_{\min}\le\beta.
]

Therefore:

[
r_{\mathrm{pre}}\ge7.
]

Combining both directions:

[
oxed{r_{\mathrm{pre}}=7}.
]

## Independent agreement with the exhaustive audit

The earlier exhaustive bundle audit found maximum observed minimal-loss order:

[
\kappa_{\mathrm{observed}}=7.
]

The exact pre-audit now independently gives:

[
r_{\mathrm{pre}}^{\mathrm{exact}}=7.
]

Thus, for this benchmark:

[
oxed{r_{\mathrm{pre}}^{\mathrm{exact}}=\kappa_{\mathrm{observed}}=7}.
]

The important methodological point is that the left-hand value is not obtained by querying bundle feasibility. The exhaustive audit remains an independent validation layer.

## Scientific interpretation

The result supports the INSACERMO idea that an audit horizon can sometimes be derived from the structure of the admissibility problem itself rather than learned only after exhaustive search.

For this benchmark the chain is:

[
\text{encoded DC LP}
\rightarrow
\text{Farkas dual geometry}
\rightarrow
\text{exact extreme rays}
\rightarrow
\text{one-deletion minimality criterion}
\rightarrow
r_{\mathrm{pre}}=7
\rightarrow
\text{independent exhaustive audit}=7.
]

In plain language:

> the engine can determine how deep it may need to look before enumerating the future bundles themselves.

This is a benchmark-specific exact result, not yet a universal theorem for arbitrary systems.

## Important limits

The exact statement is deliberately narrow:

1. It applies to the encoded **DC linearized** power-flow feasibility model, not full AC security.
2. It applies to the fixed catalogue of the eight largest positive-Pd load buses used by the benchmark.
3. The exact value (r_{\mathrm{pre}}=7) is the depth of the defined **pre-audit structural criterion** based on extreme Farkas rays plus one-deletion minimality compatibility.
4. Actual primal minimality of the observed failed bundles was checked separately by the exhaustive audit. The two layers should remain distinct in any paper.
5. The benchmark result motivates, but does not by itself prove, a general theorem that exact pre-audit depth always equals actual obstruction depth.

## Reproducibility / traceability

Key commits:

- `ac0fa15435cc4b3544b4d0c325e255e4c06dfd85` — fix absolute SVD tolerance for singleton Farkas rays.
- `54c30b5058fa58e1e48f5a864d9952998187fb37` — corrected numerical tight pre-audit result / RUN 283.
- `4c3bfc59321ea677ae79c0d87a80e76ea65cfda5` — add exact rational DC pre-audit depth V3.
- `15aa3aaf27b93641e7a9258300fbdf1d00b3698f` — exact handling of the trivial island factor.
- `62d2ab37630ccc42a62561aff3179297bff60b90` — dedicated exact pre-audit workflow.

Key runs:

- RUN 283 — numerical tight pre-audit after SVD correction: SUCCESS.
- Exact DC Preaudit Depth V3, RUN 1 — failed at outage 13, revealing the isolated trivial factor.
- Exact DC Preaudit Depth V3, RUN 3 — SUCCESS; exact rational closure.

Exact successful run:
https://github.com/benblak/insacermo-morphology-auto/actions/runs/36179362122

Primary exact checker:
`experiments/pglib_ieee14_dc_exact_preaudit_depth_v3.py`

Dedicated workflow:
`.github/workflows/pglib_exact_preaudit_depth_v3.yml`

## Recommended paper wording

A conservative, defensible formulation is:

> For the encoded PGLib IEEE-14 DC feasibility model with an eight-goal load catalogue, the extreme-ray pre-audit criterion has exact rational depth (r_{\mathrm{pre}}=7). This value is derived without bundle-feasibility calls or bundle enumeration and independently matches the maximum minimal-loss order (7) observed by exhaustive audit.

Avoid stating that this is already a general theorem about all power systems or all INSACERMO contracts.


---

## Strengthened closure — certificate-only actual depth V4

A stronger test was added after the exact pre-audit V3.

The question was no longer only:

> can the dual geometry prove the upper bound (r_{\mathrm{pre}}=7)?

but:

> can the same exact certificate family prove that an order-7 witness is genuinely minimal, without any primal feasibility call?

The answer is yes for this benchmark.

### Exact certificate-only result

Dedicated exact workflow result:

- `STATUS EXACT_DUAL_ONLY_MINIMAL_LOSS_CLOSURE`
- `PRIMAL_FEASIBILITY_CALLS 0`
- `FULL_CATALOGUE_BUNDLE_ENUMERATION_USED 0`
- `TOTAL_EXACT_OUTAGE_RAYS 80276`
- `EXACT_ORDER8_COMPATIBLE_RAYS 0`
- `EXACT_CERTIFICATE_ONLY_DEPTH 7`
- `RESULT COMPLETE`

The witness is again:

- outage 0,
- branch 1–2,
- buses ({3,4,2,14,13,6,10}).

For the post-outage system:

[
\texttt{POST\_OUTAGE\_EXACT\_RAYS}=4722.
]

Exactly one ray rejects the full seven-goal bundle:

[
\texttt{FULL\_BUNDLE\_NEGATIVE\_RAYS}=1,
]

with exact value

[
-\frac{1317}{100}=-13.17.
]

### Strong minimality without a primal solver

The V4 checker does not assume downward closure.

Instead, it enumerates all proper subbundles of the one seven-goal witness:

[
\sum_{k=0}^{6} \binom{7}{k}=127.
]

Every one of those 127 proper subbundles is evaluated against every one of the 4,722 exact post-outage rays.

The result is:

- `WITNESS_PROPER_SUBBUNDLES_CHECKED 127`
- `WITNESS_PROPER_SUBBUNDLES_WITH_NEGATIVE_RAY 0`
- `ALL_PROPER_SUBBUNDLES_ACCEPTED_BY_ALL_POST_OUTAGE_RAYS 1`
- `CROSS_CERTIFIED_MINIMAL 1`

For each one-goal deletion specifically, the exact minimum certificate value is (0), never negative.

Thus the full order-7 witness is rejected, while every proper subbundle is accepted by the complete exact post-outage certificate family.

### Baseline feasibility from certificates alone

The witness is also checked against the exact baseline certificate family:

[
\texttt{BASELINE\_EXACT\_RAYS}=4943.
]

No baseline ray rejects it:

[
\texttt{BASELINE\_NEGATIVE\_RAYS\_FOR\_WITNESS}=0.
]

Therefore the same dual framework establishes:

1. feasible before outage,
2. infeasible after outage,
3. every proper subbundle feasible after outage,

without calling the primal feasibility solver.

For this witness, actual minimality is therefore dual-certified exactly.

### Formal theorem layer

A new Lean module was added:

`InsacermoActionabilityInformation/CertificatePreAuditDepth.lean`

It formalizes the abstract bridge between certificate pre-audit depth and actual obstruction depth.

Key theorem:

[
\boxed{\kappa\le r_{\mathrm{pre}}}
]

whenever the certificate family exactly characterizes feasibility.

The module also defines a stronger condition, `CrossCertifiedMinimal`, and proves that if an exact pre-audit upper bound (r) is attained by a cross-certified witness of cardinality (r), then the actual obstruction depth is exactly (r).

The dedicated Lean workflow passed:

- bootstrap: SUCCESS,
- placeholder rejection: SUCCESS,
- mathlib/Lean action: SUCCESS,
- direct theorem-file check: SUCCESS.

Hence, for this benchmark, the computational V4 witness discharges the exact structural condition required by the formally verified theorem scheme.

### Updated conclusion

The strongest current statement for this benchmark is now:

[
oxed{
r_{\mathrm{pre}}^{\mathrm{exact}}
=
\kappa_{\mathrm{certificate\text{-}closed}}^{\mathrm{exact}}
=
7.
}
]

More concretely:

> For the encoded PGLib IEEE-14 DC model and the fixed eight-goal catalogue, exact extreme-ray certificates both derive the audit upper bound 7 before full catalogue enumeration and certify an actual minimal order-7 loss without any primal feasibility call.

This remains benchmark-specific and does not establish a universal equality for arbitrary INSACERMO systems.

### Additional traceability

- Lean theorem commit: `a80d22bdd81998f2ae7d951bbeb204e9b525669b`
- Lean import commit: `121fc4152c51029d2794a451720ae1a8a4052634`
- Dedicated Lean workflow commit: `ddbd3af74d0b27763212ae9c4857a035d7e42faf`
- Certificate-only V4 experiment commit: `e9db3af3401795dce1819d79543873c107a42454`
- Strong all-proper-subbundle V4 commit: `822d62d59e5a23fee8ab6d5fbf4eb24edf71eff7`
- Workflow integration commit: `363bd209b262a69593e66371cb91fcb2db4d0dae`
- Exact V4 successful workflow: run 10 of `INSACERMO Exact DC Preaudit Depth V3`.
