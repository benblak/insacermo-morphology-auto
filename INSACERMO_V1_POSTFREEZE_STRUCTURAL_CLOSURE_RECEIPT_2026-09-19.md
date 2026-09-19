# INSACERMO V1 — Post-Freeze Structural Closure Receipt

**Date:** 19 September 2026  
**Author:** Benjamin Lenoir  
**Status:** additive post-freeze verification receipt  
**Frozen papers modified:** NO

## 1. Canonical frozen artifacts remain unchanged

This receipt does not replace, rewrite, or supersede the 18 September 2026 V1 freeze papers.

Frozen SHA256 anchors:

- `INSACERMO_CORE_V1_4_FINAL_FREEZE_2026-09-18.pdf`  
  `b2c199b06d582c4c0046d5ebf2d3854e8dc9727f4892d9dab35079c7ff945430`
- `INSACERMO_VERIFICATION_REPRODUCIBILITY_LEDGER_V1_2_FINAL_FREEZE_2026-09-18.pdf`  
  `7593e3e19e60334ab6b98319552a20a74a11da2585211359b27240f19255373a`

The frozen Core V1.4 and Ledger V1.2 remain the canonical 18 September 2026 records.

## 2. Additive post-freeze formal closure

GitHub PR #77: **Repair-nerve / Future-Helly bridge V1**

Current head:

`46dbf3a9c185a3319189cb0930f20336b7af1918`

PR state at receipt creation: **OPEN**.

No frozen Core definition was changed to obtain the results below.

### A. Repair-plan duality

File:

`formal/actionability_information/InsacermoActionabilityInformation/RepairPlanDuality.lean`

Kernel-checked statements include:

- bundle feasibility iff one plan signature contains the bundle;
- infeasibility iff every complete plan fails at least one future in the bundle;
- every future in a minimal bundle obstruction has a private witness plan satisfying all the other futures while failing that future;
- budget feasibility is monotone;
- exact bridge from finite-horizon joint recoverability to a certified common-plan formulation;
- chain-collapse for nested mandatory repair signatures.

First fully green repair-plan duality head:

`dcd4ff6569ed79adc480d68b9f84ef6493e4c3cd`

Verification:

- INSACERMO Repair Nerve Future Helly V1 — run #5 / ID `35400430352` — **SUCCESS**
- INSACERMO Actionability Information Lean — run #148 / ID `35400430411` — **SUCCESS**

### B. Budget / temporal / chain-collapse closure

Head:

`811091962885384d994d8664ca11ec62b233c588`

Verification:

- INSACERMO Repair Nerve Future Helly V1 — run #6 / ID `35401150360` — **SUCCESS**
- INSACERMO Actionability Information Lean — run #149 / ID `35401150414` — **SUCCESS**

This head verifies the additive bridge among:

`BudgetBundleFeasible -> CertifiedJointPlan -> JointRecoverable -> RequiredRepairs chain-collapse`.

### C. Master closure

File:

`formal/actionability_information/InsacermoActionabilityInformation/MasterClosureV1.lean`

Final head:

`46dbf3a9c185a3319189cb0930f20336b7af1918`

Kernel-checked master equivalences include:

1. finite-horizon depth threshold  
   `<->` temporal feasibility  
   `<->` certified common-plan feasibility;

2. unknown-future safety for a declared family Gamma  
   `<->` every bundle in Gamma has a certified common plan by the horizon;

3. eventual family safety  
   `<->` every declared bundle has some finite-horizon joint certificate;

4. deadline repair within budget  
   `<->` a repair of admissible cost moves the state to one with a certified common plan;

5. under a pre-transformation family guarantee, robust admissibility  
   `<->` no declared possible future is destroyed  
   `<->` every declared bundle still has an eventual common-plan certificate after transformation.

Final verification:

- INSACERMO Repair Nerve Future Helly V1 — run #7 / ID `35401702171` — **SUCCESS**
- INSACERMO Actionability Information Lean — run #150 / ID `35401702011` — **SUCCESS**

At the same final head, the following regression/integration workflows also completed **SUCCESS**:

- Post-Freeze Cosmology Null Dynamics V1 — run #13
- Post-Freeze Email-Eu-core Blind V1 — run #14
- Post-Freeze Intel Sensor Coverage V1 — run #15
- Final E2E OpenFlights Decision V1 — run #19
- Post-Freeze Debian Installability V1 — run #18


## 2D. Confirmatory real-data private-witness audit

PR #78: **Post-freeze OpenFlights private-witness real-data audit V1**

Frozen-before-result protocol commit:

`70912a6f41a48b8312fc7674c87314b22018214a`

Audit head:

`90b1738248a02ceed3467fecfa3b1bcc8a764a64`

Merged into PR #77 as:

`a6362390b2c74f08c21d576e260e6ad22ac739d3`

Workflow:

- INSACERMO Post-Freeze OpenFlights Private Witness V1 — run #1 / ID `35403202183` — **SUCCESS**

The protocol inherited the previously fixed OpenFlights joint settings: 67,663 routes, start `KEF`, the same 25 future targets, deadline `H=3`, and the same five scenarios. No target, horizon, start airport, or scenario was changed after observing the endpoint.

Baseline result:

- singleton feasibility: 25/25;
- pair feasibility: 213/300;
- triple feasibility: 754/2300;
- minimal obstructions of order 2: 87;
- minimal obstructions of order 3: 215;
- rank-3 pairwise-compatibility check: **YES**.

Across all five scenarios:

- minimal obstructions: 1,859;
- order 2: 390;
- order 3: 1,469;
- private-witness audit: **PASS**.

Interpretation guardrail: these are finite-horizon `H=3` obstructions. They do not by themselves establish infinite-horizon irreversibility. The empirical audit confirms the minimal-obstruction/private-witness structure on the inherited OpenFlights adapter; it is not presented as a new discovery of joint interaction itself, which had already been observed in the earlier OpenFlights joint study.

## 3. Interpretation

The post-freeze work does **not** replace the Core V1.4 paper.

It adds a structural closure layer showing that previously separate V1 objects are exact views of the same contract-relative future-feasibility structure:

`CONTRACT -> ACTIONABILITY -> COMMON PLAN -> JOINT COMPLEX -> DEPTH / REPAIR -> UNKNOWN-FUTURE ROBUSTNESS`

The phrase **"Core V1 structurally closed"** is therefore used here in this limited sense: the deterministic V1 formal spine now has explicit kernel-checked bridges among its main representations.

## 4. Guardrail

As in the frozen verification ledger, green CI establishes only that the encoded definitions and theorem statements passed the declared checks. It does not establish historical novelty, external validity, adequacy of any domain adapter, or universal applicability.

---

**Receipt rule:** keep the 18 September 2026 freeze artifacts immutable. Record post-freeze closure through additive receipts and repository history.
