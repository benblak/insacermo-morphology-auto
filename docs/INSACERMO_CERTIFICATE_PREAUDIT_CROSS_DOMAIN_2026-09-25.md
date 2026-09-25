# INSACERMO — Certificate Pre-Audit Depth: Cross-Domain Closure

**Date:** 2026-09-25  
**Status:** abstract Lean theorem verified + two exact computational domains

## Core abstract result

INSACERMO now contains a formal distinction between:

- actual minimal-obstruction depth (kappa),
- certificate-derived pre-audit depth (r_{\mathrm{pre}}).

The Lean module:

`InsacermoActionabilityInformation/CertificatePreAuditDepth.lean`

defines an exact certificate characterization of feasibility and proves:

[
\boxed{\kappa \le r_{\mathrm{pre}}}
]

whenever the certificate family exactly characterizes feasibility.

It also introduces a stronger condition, `CrossCertifiedMinimal`, and proves that an attained witness of cardinality (r), rejected by the full bundle certificate family while every proper subbundle is accepted by all certificates, closes the equality:

[
\boxed{\kappa = r_{\mathrm{pre}} = r}.
]

Dedicated Lean workflow:
`INSACERMO Certificate Preaudit Lean`

Result: SUCCESS for bootstrap, placeholder rejection, mathlib/Lean action, and direct theorem-file check.

## Domain A — PGLib IEEE-14 DC / Farkas geometry

Certificate class: exact extreme Farkas rays.

Exact pre-audit:

- 80,276 exact outage rays,
- 0 order-8-compatible rays,
- an exact order-7 witness,
- no bundle feasibility calls,
- no full catalogue bundle enumeration.

Therefore:

[
r_{\mathrm{pre}}=7.
]

Stronger V4 closure checks the order-7 witness using certificates only:

- post-outage exact rays: 4,722,
- full bundle negative rays: 1,
- exact negative value: (-1317/100),
- proper subbundles checked: 127,
- proper subbundles with any negative ray: 0,
- baseline exact rays: 4,943,
- baseline negative rays for witness: 0,
- primal feasibility calls: 0.

Thus, for this encoded DC LP and fixed 8-goal catalogue:

[
\boxed{\kappa = r_{\mathrm{pre}} = 7}
]

is closed by the exact certificate family itself.

## Domain B — Rhea finite-inventory Petri/resource module

Certificate class: exact integer resource-capacity certificate.

Frozen real-data module:

- 10 explicit left-to-right Rhea reactions,
- common limiting resource: ((2S))-naringenin,
- ChEBI:17846,
- each frozen reaction consumes exactly one resource unit,
- none regenerates the resource.

After destruction:

[
C=9,qquad \delta=1.
]

For an inclusion-minimal resource obstruction of size (m), every proper ((m-1))-goal deletion must fit:

[
(m-1)\delta\le C.
]

Therefore:

[
m\le 1+\left\lfloor\frac{C}{\delta}\right\rfloor
=1+9=10.
]

The exact pre-audit workflow reports:

- `STATUS EXACT_INTEGER_RESOURCE_PREAUDIT_BOUND`,
- `BUNDLE_FEASIBILITY_CALLS_TO_DERIVE_R 0`,
- `BUNDLE_ENUMERATION_USED_TO_DERIVE_R 0`,
- `EXECUTION_SIMULATION_USED_TO_DERIVE_R 0`,
- `EXACT_RESOURCE_PREAUDIT_R 10`.

An earlier independent Petri audit on the same frozen real module found:

- witness order 10,
- full bundle feasible before destruction,
- infeasible after destruction,
- all 1,022 non-empty proper subbundles feasible after destruction,
- adding one unit of naringenin repairs the full bundle.

Hence the resource pre-audit independently predicts the same observed depth:

[
\boxed{r_{\mathrm{pre}}=10=\kappa_{\mathrm{observed}}}.
]

The Rhea pre-audit derives 10 without bundle enumeration or execution simulation.

## Cross-domain interpretation

The two exact cases use different mathematics:

[
\text{DC power flow}
\quad\Rightarrow\quad
\text{Farkas/extreme-ray geometry}
\quad\Rightarrow\quad
r_{\mathrm{pre}}=7,
]

while

[
\text{Rhea/Petri resource competition}
\quad\Rightarrow\quad
\text{integer capacity certificate}
\quad\Rightarrow\quad
r_{\mathrm{pre}}=10.
]

The shared INSACERMO layer is not the domain-specific certificate itself. It is the architecture:

[
\boxed{
\text{CONTRACT}
\rightarrow
\text{CERTIFICATE FAMILY}
\rightarrow
\text{PRE-AUDIT DEPTH}
\rightarrow
\text{CROSS-CERTIFIED WITNESS}
\rightarrow
\text{ACTUAL OBSTRUCTION DEPTH}
}
]

This supports the interpretation of certificate pre-audit depth as a reusable INSACERMO operator rather than a Farkas-specific construction.

## Limits

This is not yet a universal theorem that every domain has a tight certificate family or that (r_{\mathrm{pre}}=\kappa) automatically.

What is currently established is:

1. the abstract upper-bound theorem is formally verified;
2. equality follows formally from the stronger cross-certified witness condition;
3. two structurally different real-data domains instantiate the pattern with exact arithmetic / exact integer reasoning;
4. in both domains, the pre-audit depth matches the independently observed obstruction depth.

## Traceability

Key files:

- `formal/actionability_information/InsacermoActionabilityInformation/CertificatePreAuditDepth.lean`
- `experiments/pglib_ieee14_dc_exact_preaudit_depth_v3.py`
- `experiments/pglib_ieee14_dc_exact_certificate_only_depth_v4.py`
- `experiments/rhea_exact_resource_preaudit_depth_v3.py`

Key commits:

- `a80d22bdd81998f2ae7d951bbeb204e9b525669b` — abstract Lean theorem.
- `822d62d59e5a23fee8ab6d5fbf4eb24edf71eff7` — strong all-proper-subbundle DC V4.
- `47dbb7f97e918f96c2f08345fb4b70824b020009` — Rhea exact resource pre-audit.
- `33cadc22852153ff8857a1fceb672b6bbe744981` — dedicated Rhea pre-audit workflow.
