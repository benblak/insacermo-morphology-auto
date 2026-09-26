# INSACERMO — Website / Engine Migration Roadmap
## From the original public tool to the 2026-09-26 frozen architecture

### Goal

Update the public INSACERMO tool so that it reflects the current engine without exposing unnecessary formal complexity.

The website should remain usable by a non-specialist while mapping faithfully to the current core.

---

## 1. Keep

Keep the useful parts of the current public engine:
- CSV/data ingestion
- structural summaries
- facets / cores / obstructions
- DSCI / HOAFT where relevant
- ACT / PROBE / REFUSE outputs
- interactive exploration / heatmaps / diagnostics

These remain domain-level analysis tools.

---

## 2. Reframe

The site should no longer present those analyses as the whole of INSACERMO.

Top-level engine framing:

```text
1. What future must remain possible?
2. What is available now?
3. What can be lost temporarily?
4. What becomes impossible?
5. Why?
6. What information would help?
7. Can the obstruction be repaired?
8. How many steps are needed to recover?
9. What future risk does each action create?
10. Which plan preserves the declared contract?
```

---

## 3. New public workflow

### Step A — Define the contract

User selects:
- required futures,
- optional future family,
- deadline/horizon,
- hard requirements vs weighted possibilities.

UI label:
**Future Contract**

### Step B — Load current system

User supplies:
- current state/data,
- possible actions,
- constraints,
- available capabilities,
- optional domain certificate adapter.

UI label:
**Current Capabilities**

### Step C — Structural audit

Engine computes:
- individual feasibility,
- joint bundle feasibility,
- facets,
- minimal obstructions,
- certificate evidence when available.

UI label:
**What blocks the future?**

### Step D — Decision layer

Return:
- ACT
- PROBE
- REPAIR
- REFUSE

Each output should include a plain-language explanation.

### Step E — Temporal layer

Expose:
- immediately available,
- recoverable within H,
- minimum recovery depth,
- irreversible.

UI label:
**How far away is each future?**

### Step F — Risk layer

Optional:
- deadline-risk mass,
- irreversible-risk mass,
- future survival mass,
- weighted scenario comparison.

UI label:
**What future risk does this choice create?**

### Step G — Planner

Show:
- candidate plan,
- residual obligations,
- sequence of repairs/probes/actions,
- final contract status.

UI label:
**How do I recover the future I need?**

---

## 4. Human-readable result card

A final decision should look like:

```text
DECISION: PROBE

Why:
The current information is insufficient to guarantee the declared contract.

Current status:
- 8 required futures immediately available
- 3 recoverable within 2 steps
- 1 jointly blocked bundle
- 0 proven irreversible losses

Needed next:
Observe variable X.

After this probe:
- ACT if branch A
- REPAIR with resource Y if branch B
```

The user should not need to understand Lean, Helly numbers, Farkas rays or Bellman equations to use the engine.

---

## 5. Expert audit drawer

Advanced users may open a technical panel exposing:
- contract complex
- future-depth spectrum
- obstruction rank / pre-audit depth
- certificate backend
- exact witness
- proof status
- computation type: exact / exhaustive / heuristic / empirical
- Lean theorem reference when applicable

This preserves scientific transparency without overwhelming normal users.

---

## 6. Stable output schema

Recommended common result object:

```text
contract
current_state
decision
immediate_futures
recoverable_futures
irreversible_futures
joint_obstructions
certificates
required_probe
repair_options
depth_spectrum
deadline_risk
irreversible_risk
plan
evidence_level
```

Domain-specific plugins may add fields but should not change the shared semantics.

---

## 7. Domain plugin interface

A domain adapter should ideally provide:

```text
parse_input
define_capabilities
define_requirements
feasible(bundle)
certificate(bundle)
apply(action,state)
available_futures(state)
cost(action)
```

Examples:
- PGLib → Farkas / grid feasibility backend
- Rhea → stoichiometric/resource backend
- graph topology → signed-cycle certificate backend
- ModeChoice → admissible-mode / Pareto backend

---

## 8. Site language

Avoid presenting INSACERMO as:
- a universal predictor,
- a generic AI model,
- a single score,
- a replacement for domain simulation.

Preferred wording:

> INSACERMO audits how present decisions affect future capabilities.

Secondary wording:

> It identifies what remains possible, what becomes blocked, what can be recovered, what additional information is useful, and what repair or plan can preserve the declared future contract.

---

## 9. Versioning

Public site should display:

```text
INSACERMO Engine
Core reference: 2026-09-26 freeze
Formal status: selected core bridges kernel-verified
Domain status: per-adapter audit shown separately
```

Never collapse formal proof status and empirical/domain validation into one badge.

---

## 10. Recommended implementation order

Phase 1:
- update language / architecture
- retain existing uploads and plots
- add Future Contract panel
- map old ACT/PROBE/REFUSE outputs to new semantics

Phase 2:
- add joint bundles / obstructions
- add certificates and evidence panel
- add REPAIR

Phase 3:
- add temporal depth spectrum
- add deadline / irreversibility view
- add risk comparison

Phase 4:
- add planner / Bellman-backed trajectories
- plugin registry
- reproducible example catalogue

---

## 11. Migration principle

Do not rewrite the working public tool from scratch.

Treat it as the existing front-end shell and progressively replace the semantic core behind it.

```text
OLD SITE
  ↓
KEEP DATA + VISUALS
  ↓
REPLACE SEMANTIC CORE
  ↓
ADD CONTRACT
  ↓
ADD TEMPORAL / CERTIFICATE / REPAIR / PLANNER LAYERS
```

This minimizes regression risk and keeps the historical tool recognizable while exposing the modern engine.
