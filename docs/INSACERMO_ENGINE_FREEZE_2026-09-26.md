# INSACERMO — Engine Freeze Manifest
## Frozen reference: 2026-09-26

### 1. Frozen code reference

- Repository: `benblak/insacermo-morphology-auto`
- Frozen branch: `insacermo-engine-freeze-2026-09-26`
- Frozen commit: `3b712a0afdbe5f8893a43cbbe94868f2b8627e06`
- Source branch at freeze: `insacermo-structural-audit-kernel-v1-20260920`
- Root validation: **INSACERMO Actionability Information Lean — RUN 336**
- Root run ID: `36244409179`
- Root result: **SUCCESS**

This branch is the reference snapshot for the current formally integrated INSACERMO engine. Later development may continue elsewhere; claims about this freeze should be tied to this commit.

---

## 2. What INSACERMO is at this freeze

INSACERMO is a contract-driven engine for preserving, auditing, recovering and planning future capability.

Its current conceptual pipeline is:

```text
FUTURE FAMILY / REQUIREMENTS
          ↓
       CONTRACT
          ↓
PRESERVATION / RECOVERABILITY
          ↓
     ACTIONABILITY
          ↓
CERTIFICATES / OBSTRUCTIONS
          ↓
      PRE-AUDIT
          ↓
 ACT / PROBE / REFUSE
          ↓
        REPAIR
          ↓
 DEPTH / DEBT / RISK
          ↓
       PLANNER
```

The central question is:

> What may be transformed, forgotten, consumed or destroyed now while still preserving the future capabilities required by the declared contract?

The engine is not defined by one dataset, one score, one certificate family, or one domain. Those are instantiations or adapters around a shared future-capability semantics.

---

## 3. Evidence classes kept separate

The freeze deliberately separates the following evidence levels:

1. **Conceptual definition**
2. **Mathematical theorem**
3. **Lean formalization**
4. **Lean kernel / checker validation**
5. **Exact or exhaustive computation**
6. **Real-data / real-domain audit**
7. **Literature positioning**
8. **External independent replication**

A Lean proof certifies the formal statement encoded in Lean. It does not by itself certify the fidelity of a real-world model, dataset, or scientific interpretation.

---

## 4. Core mathematical objects

### 4.1 Contract and future capability

A contract identifies future requirements that must remain satisfiable.

The engine distinguishes:
- immediate availability,
- finite-horizon recoverability,
- irreversible loss,
- individual future feasibility,
- joint future feasibility.

### 4.2 Future-depth spectrum

For state `x` and finite future bundle `F`:

```text
Spectrum(x,F) = finite d
```

when the bundle is jointly recoverable for the first time at depth `d`, and:

```text
Spectrum(x,F) = infinite
```

when no finite common recovery plan exists.

This spectrum is a master representation for the temporal filtration of joint future feasibility.

### 4.3 Debt

Future debt represents required futures not presently guaranteed.

Zero debt corresponds to full guarantee of the declared contract.

### 4.4 Risk

The engine supports:
- deadline risk mass,
- irreversible risk mass,
- eventual survival mass,
- weighted future catalogues,
- budget-constrained risk optimization.

Weights may represent probabilities when normalized, but probability normalization is not required by the structural kernel.

---

## 5. Verified formal bridges to classical theories

These bridges identify where established theories occur inside the INSACERMO architecture. They are not novelty claims about the classical theories.

### 5.1 Helly / IIS bridge

File:
`InsacermoActionabilityInformation/HellyIISBridge.lean`

Verified result in the relevant finite intersection semantics:

```text
FiniteHellyAtMost(K,r)
    ↔
ActualDepthAtMost(IntersectionFeasible K,r)
```

and corresponding conflict-hypergraph rank equivalence.

Interpretation:
- classical Helly/IIS structure explains obstruction depth in the appropriate intersection setting;
- INSACERMO does not claim to invent Helly number, IIS, MUS, or conflict hypergraph rank.

Status: **LEAN KERNEL VERIFIED**

### 5.2 Viability bridge

File:
`InsacermoActionabilityInformation/ViabilityBridge.lean`

Key bridge:
- strict one-future preservation reduces to classical one-step safety / controlled invariance in the formal encoding.

Separation witness:

```text
¬ PRESERVE ∧ PRESERVE_WITHIN(1)
```

Interpretation:
- current safety and deadline recoverability are distinct;
- a currently unavailable capability can remain recoverable.

Status: **LEAN KERNEL VERIFIED**

### 5.3 Future-task bridge

File:
`InsacermoActionabilityInformation/FutureTaskBridge.lean`

Pointwise future-task preservation is identified with the corresponding PRESERVE form.

Separation witness:

```text
each singleton future feasible
does not imply
their joint bundle feasible
```

Interpretation:
- pointwise future-task preservation does not encode all collective incompatibility information.

Status: **LEAN KERNEL VERIFIED**

### 5.4 Blackwell / PROBE bridge

File:
`InsacermoActionabilityInformation/BlackwellProbeBridge.lean`

In the deterministic signal setting:

```text
Refines(fine,coarse)
    ↔
SafeDominatesFor(fine,coarse)
```

under the theorem's stated type assumptions.

A second witness constructs two globally incomparable observations, each useful for a different declared contract.

Interpretation:
- deterministic refinement gives universal information dominance;
- contract-relative probe usefulness can still matter when experiments are incomparable under the universal order.

This does not claim that contract-relative preference among incomparable experiments is new to decision theory.

Status: **LEAN KERNEL VERIFIED**

Dedicated run:
- run ID `36241345057`
- conclusion: **SUCCESS**

### 5.5 Anticipatory Planning bridge

File:
`InsacermoActionabilityInformation/AnticipatoryPlanningBridge.lean`

The bridge defines:

```text
AnticipatoryObjective
    = immediate cost + future cost
```

and proves that a binary deadline-miss expected future cost is exactly representable as weighted deadline-risk mass over the future-depth spectrum.

Separation witness:

```text
equal expected future scalar cost
does not imply
equal hard-contract preservation
```

Two plans can tie under a symmetric aggregate expected-future-cost objective while one destroys a required future bundle and the other preserves it.

Interpretation:
- scalar anticipatory cost is a valid projection;
- INSACERMO can retain the identity and joint structure of future obligations before optional aggregation.

Status: **LEAN KERNEL VERIFIED**

Dedicated run:
- run ID `36244409130`
- conclusion: **SUCCESS**

---

## 6. Certificate-domain architecture

Generic formal layer:

`InsacermoActionabilityInformation/CertificateDomain.lean`

A domain supplies:
- a feasibility predicate,
- a certificate family,
- an exact certificate characterization.

The generic layer then derives pre-audit results independently of the certificate mathematics.

Conceptual adapter:

```text
DOMAIN
  ↓
CERTIFICATE ADAPTER
  ↓
PRE-AUDIT RESULT
  ↓
GENERIC INSACERMO THEOREMS
```

The generic pre-audit formalization distinguishes:
- same-certificate local deletion minimality,
- actual obstruction depth,
- cross-certified minimality.

Core form:

```text
κ ≤ r_pre
```

under exact certificate characterization.

With an attained cross-certified witness:

```text
κ = r_pre = r
```

This separation is important: local deletion minimality of one certificate alone is not enough to prove exact global obstruction depth.

Status: **LEAN KERNEL VERIFIED**

---

## 7. Exact / real-domain audit coverage in ROOT RUN 336

The root workflow passed all integrated steps through completion.

Included successful stages include:

- Lean bootstrap and manifest
- proof-placeholder rejection
- Lean build
- OpenFlights structural audit
- Email-Eu-core structural audit
- Wiki-Vote structural audit
- Wiki-Vote pair-obstruction witness
- France rail structural audit
- passenger-weighted France rail audit
- France sovereign-finance capability audit
- finance return-threshold analysis
- finance marginal-return analysis
- rail capability-finance bridge
- rail investment-envelope frontier
- fiscal-trajectory rail frontier
- human-capability baseline
- work-time transformation
- SIGNOR causal-signaling structural stress test
- Rhea stoichiometric resource competition
- Rhea high-order obstruction search
- PGLib IEEE14 DC hidden-bundle audit
- PGLib IEEE14 AC cross-check
- Rhea equation-level Petri test
- Rhea exact resource pre-audit depth
- PGLib DC cut certificate
- PGLib DC Farkas certificate
- PGLib exact rational Farkas
- automatic DC certificate router
- PGLib heredity audit
- PGLib extreme-ray pre-audit depth V1
- PGLib tight extreme-ray pre-audit depth V2
- PGLib exact rational pre-audit depth V3

Root result:

```text
RUN 336 — SUCCESS
```

This is an integration result for the frozen repository state, not a universal validation of every future domain or scientific model.

---

## 8. Important exact audit anchors

### PGLib IEEE-14 DC exact pre-audit

Known exact audit result in the fixed DC formulation/catalogue:

```text
TOTAL_EXACT_EXTREME_RAYS 80276
EXACT_ORDER8_COMPATIBLE_RAYS 0
EXACT_PREAUDIT_DEPTH 7
GLOBAL_TIGHT_PREAUDIT_R 7
```

A cross-certified order-7 witness was identified.

Scope:
- fixed DC LP semantics and audited catalogue;
- not a universal AC or physical-grid theorem.

### Rhea resource obstruction

For the frozen selected reaction module:
- 10 selected reactions,
- limiting resource: (2S)-naringenin,
- post-destruction resource capacity 9,
- full order-10 set fails,
- every nonempty proper subset succeeds,
- one unit of resource repairs the obstruction.

Scope:
- selected local reaction module;
- not a whole-cell biological theorem.

### Signed topology

For the canonical signed XOR setting:
- satisfiability corresponds to balanced closed walks;
- minimal unsatisfiable structures correspond to unbalanced simple cycles;
- pre-audit depth equals unbalanced girth in the formal bridge.

Status: **LEAN KERNEL VERIFIED**

---

## 9. ACT / PROBE / REFUSE / REPAIR remains part of the engine

The later theory does not replace the operational decision layer.

Its meaning is now clearer:

- **ACT**: the declared contract is sufficiently guaranteed for the proposed action.
- **PROBE**: additional information can resolve the decision safely or improve contract-specific actionability.
- **REFUSE**: the declared requirements cannot be certified under the current state/contract.
- **REPAIR**: add or restore capability/resources/structure so the blocked contract becomes actionable.

The planner then reasons over sequences, residual obligations, future debt and depth.

---

## 10. Relationship to the original website engine

The original website engine remains useful but represents only part of the current architecture.

### Original visible layer

Typical functionality:
- upload / select data,
- extract actionability structure,
- inspect facets / cores / obstructions,
- DSCI / HOAFT and related diagnostics,
- ACT / PROBE / REFUSE style decisions,
- visual exploration.

### Current underlying architecture

The modern engine adds explicit:
- future contracts,
- strict preservation vs deadline recoverability,
- unknown future families,
- joint contract bundles,
- temporal depth spectrum,
- future debt,
- structural and weighted risk,
- certificate plugins,
- pre-audit depth,
- repair,
- Bellman-style planning,
- formal bridges to adjacent literatures.

Therefore the website should be treated as a front-end / laboratory over the broader engine, not as the complete definition of INSACERMO.

---

## 11. What is NOT claimed by this freeze

This freeze does **not** claim:

- that every mathematical component is novel;
- that Helly/IIS, viability, Blackwell comparison, Bellman recursion, expected future cost, MUS/IIS, Farkas certificates or related classical concepts were invented by INSACERMO;
- that no prior work combines any subset of these ideas;
- that the current literature review proves nonexistence of a prior end-to-end equivalent framework;
- that formal verification proves real-world model fidelity;
- that successful tests on current domains establish universal correctness;
- that the current engine is already production-ready.

The strongest defensible current positioning is:

> INSACERMO integrates a contract-centric future-capability semantics across preservation, information acquisition, collective feasibility, certificates, repair and planning; several classical theories are now formally identified as special cases or projections of specific layers. No exact end-to-end equivalent of the entire typed stack has yet been identified in the current review, but this is not a proof of absence.

---

## 12. What is genuinely frozen here

At this point, the following are no longer open conceptual questions for this snapshot:

- INSACERMO has an explicit contract layer.
- Future capability can be represented structurally rather than only by a scalar.
- Immediate preservation and finite-horizon recoverability are distinct.
- Joint future feasibility is distinct from singleton feasibility.
- Future depth admits a Bellman-style recursion.
- Irreversible and deadline risk can be computed over declared future laws.
- Domain certificates can feed a generic pre-audit abstraction.
- ACT / PROBE / REFUSE / REPAIR remain compatible with the expanded theory.
- The five literature bridges listed above compile and are kernel-checked in their dedicated runs.
- The integrated root workflow for this snapshot passed.

---

## 13. Next engineering phase

The next phase should be product consolidation rather than unrestricted theoretical expansion.

Priority order:

1. Keep this freeze untouched as a scientific reference.
2. Create a clean public architecture document derived from this manifest.
3. Refactor the website around the current pipeline.
4. Define stable input/output schemas for domain adapters.
5. Expose certificate backends as plugins.
6. Expose temporal depth / debt / risk in the UI.
7. Add contract construction and future-family controls.
8. Add ACT / PROBE / REFUSE / REPAIR explanations in human-readable form.
9. Build reproducible examples from PGLib, Rhea, ModeChoice and a small generic toy model.
10. Prepare publication packages separating:
   - core theory,
   - certificate/pre-audit layer,
   - temporal future geometry/planner,
   - literature bridges,
   - empirical demonstrations.

---

## 14. One-sentence frozen definition

> **INSACERMO is a contract-driven engine for deciding what can be done now while preserving, recovering, certifying, repairing and planning the future capabilities that may still be required.**

---

## 15. Freeze rule

For reproducibility, any result described as belonging to the **INSACERMO Engine Freeze 2026-09-26** should be traceable to:

```text
branch: insacermo-engine-freeze-2026-09-26
commit: 3b712a0afdbe5f8893a43cbbe94868f2b8627e06
root run: 36244409179
root conclusion: SUCCESS
```
