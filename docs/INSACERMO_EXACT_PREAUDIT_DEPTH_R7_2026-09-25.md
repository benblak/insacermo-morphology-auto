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
