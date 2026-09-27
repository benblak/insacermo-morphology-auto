# INSACERMO × Bennu Curation V1 — Frozen protocol

Date frozen: 2026-09-27
Branch: insacermo-bennu-curation-v1

## Status

This is a **real-domain external-policy replay / engine stress test**, not a prospective scientific prediction and not a claim about NASA allocation decisions beyond the public facts encoded below.

The INSACERMO V1 kernel, equations, Lean files, and actionability engine are frozen before this test. This experiment may add only:
- a Bennu domain adapter,
- a frozen case table,
- a runner/report,
- workflow plumbing.

No generic INSACERMO theorem, actionability rule, or engine criterion may be altered to improve the outcome.

## Domain

NASA OSIRIS-REx curation of irreplaceable Bennu material.

The test asks whether the frozen finite deterministic engine can reproduce the four INSACERMO operational semantics in a domain where obtaining information can itself consume future scientific capability.

## Public source facts frozen before calculation

1. NASA reports 121.6 g returned from Bennu and states that at least 70% is to be preserved for future research.
   Source: NASA Science, "NASA Announces OSIRIS-REx Bulk Sample Mass" (2024-02-15).

2. NASA/JSC curation describes XCT as valuable for characterizing particles while keeping them **curation pristine**.
   Source: ARES Astromaterials Newsletter, OSIRIS-REx News, Vol. 8 No. 1 (May 2026).

3. The same May 2026 newsletter publicly lists catalog entries that were XCT scanned since the previous newsletter and separately lists particles newly designated **"not to be XCT scanned" per the collection conservation plan**.

4. NASA's 2026 sample-request guidance says PIs should state whether XCT could negatively affect their proposed science; when they do, JSC curation will ensure those samples are not XCT scanned before allocation.
   Source: NTRS 20250011677, "Requesting Asteroid Bennu Samples From the NASA OSIRIS-REx Curation Laboratory."

5. The May 2026 newsletter says returned investigator samples are available to the community and encourages their use because doing so does **not require making new Bennu samples non-pristine**. It specifically describes OREX-800023-120 as a chip of mottled parent OREX-800023 on carbon tape on an SEM stub.

These are the only external facts used in the V1 endpoint logic.

## Frozen cases

### Direct XCT replay

The frozen table contains:
- 17 catalog entries publicly listed as XCT scanned since the previous newsletter;
- 8 catalog entries publicly designated "not to be XCT scanned."

For this replay only:
- a listed XCT-scanned entry is encoded as an admissible XCT action;
- a listed no-XCT entry is encoded as an inadmissible XCT action.

The expected engine verdict is therefore ACT for the former and REFUSE for the latter. This is a domain-adapter conformance test, not an independent prediction of NASA choices.

### PROBE witness

A generic pre-allocation XCT request has one missing contract-relevant fact:
- XCT-sensitive = false -> XCT admissible;
- XCT-sensitive = true -> XCT inadmissible.

The frozen decision rule is:
- if every completion is ACT -> ACT;
- if every completion is REFUSE -> REFUSE;
- if completions disagree -> PROBE.

The single probe is the real request-form question: can XCT negatively affect the proposed science?

### REPAIR witness

Scientific request: SEM-compatible characterization of mottled Bennu material.

Base capability set:
- prepare a newly non-pristine mottled chip.

Frozen conservation obligation:
- do not make a new pristine Bennu sample non-pristine when a suitable already non-pristine returned sample is available for the declared request.

Base action is therefore inadmissible.

Repair capability:
- use returned OREX-800023-120, described publicly as a chip of mottled OREX-800023 already mounted on carbon tape on an SEM stub and available for community request.

If capability expansion changes the one-state audit from REFUSE to ACT, the operational verdict is REPAIR.

This is a test of INSACERMO's capability-expansion semantics, not a claim that OREX-800023-120 is suitable for every microscopy proposal.

## Frozen operational compiler

For every case the unmodified `insacermo_actionability_engine_v1.py` supplies the finite `FiniteContract` and `audit_observation` semantics.

The Bennu adapter may only compile:
- complete single-action cases -> ACT / REFUSE from the engine;
- partial relation completions -> PROBE iff ACT/REFUSE truth differs across completions;
- capability expansion -> REPAIR iff base is REFUSE and expanded contract is ACT;
- otherwise -> REFUSE.

Priority for a declared request:
ACT -> PROBE -> REPAIR -> REFUSE,
with PROBE considered only when a named missing fact exists and REPAIR only when a named capability expansion exists.

## Endpoints

Primary:
1. direct XCT replay agreement count over 25 catalog entries;
2. exact PROBE verdict on the XCT-sensitivity case;
3. exact REPAIR verdict on the returned-sample substitution case;
4. zero internal certificate inconsistencies.

Secondary:
- status histogram ACT / PROBE / REPAIR / REFUSE;
- explicit witnesses used for each non-ACT verdict.

## Falsification criteria

The test fails if any of the following occurs:
- an XCT-scanned replay entry is not ACT;
- a no-XCT replay entry is not REFUSE;
- the incomplete XCT-sensitivity case is not PROBE;
- the returned-sample substitution case is not REPAIR;
- any reported ACT lacks an engine-level admissible common action;
- the generic engine or kernel has to be edited after seeing the endpoint.

## Non-claims

This test does not:
- validate NASA policy;
- reproduce NASA's full allocation process;
- assert that public XCT/no-XCT labels exhaust all curation constraints;
- establish global optimality of sample allocation;
- constitute a new pristine holdout;
- change INSACERMO V1 theory.

Its purpose is narrower and harder to fake: run the already-frozen engine in a real irreversible-curation domain where information acquisition, material preservation, missing information, and capability substitution all coexist.
