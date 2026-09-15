# INSACERMO Core V1 — Release Manifest

Release date: 2026-09-15
Author: Benjamin Lenoir
Repository: benblak/insacermo-morphology-auto
Stable branch: `insacermo-core-v1-20260915`

## Certified kernel anchor

The exact Lean source state certified by CI is anchored at:

`dc8878f8cee3f8d8bfd4769523077d829b246a62`

Pull request merge ref checked by CI:

`397ab61326202877ce5c750991d28d086d2989cc`

GitHub Actions run:

- Workflow: `INSACERMO Actionability Information Lean`
- Run number: `#113`
- Run id: `34984977418`
- Job id: `104434638249`
- Result: `success`

Verification conditions observed in the CI logs:

1. proof-placeholder rejection succeeded (`sorry` / `admit` rejected),
2. full `lake build` succeeded,
3. build completed successfully with 8684 jobs,
4. targeted `leanchecker` succeeded on:
   `InsacermoActionabilityInformation.DecisionSemantics`.

Companion benchmark workflow:

- `INSACERMO Obstruction Depth Benchmark`
- Run number: `#26`
- Result: `success`

## Core formal spine

INSACERMO Core V1 is organized around the following verified chain:

`SafeRep`
→ `FutureEnvelope`
→ `FutureDebt`
→ `FutureConservationPlanner`
→ `TemporalRecoverabilityEnvelope`
→ `RecoveryDepthIrreversibility`
→ `DecisionSemantics`

Mathematically:

- current guarantee envelope: `E(x)`,
- temporal recoverability envelope: `R_H(x)`,
- eventual finite-horizon recoverability: `R_∞(x) = ⋃_H R_H(x)`,
- immediate debt: `Req \ E(x)`,
- temporal debt: `Req \ R_H(x)`,
- irreversible debt: `Req \ R_∞(x)`,
- minimum recovery depth: `D_q(x) = min {H | q ∈ R_H(x)}` when finite,
- public decision semantics: `ACT / PROBE / REPAIR / RECOVER / REFUSE / PRESERVE / DESTROY`.

## Public semantics

The seven public words are intentionally not seven mutually-exclusive output classes.

### Future status

- `ACT`: the future is safely actionable now.
- `RECOVER(H)`: it is not actionable now but is recoverable within horizon `H`.
- `REFUSE`: no finite admissible plan can recover it.

### Recovery mechanisms

- `PROBE`: an information-gathering/refinement transition restores actionability.
- `REPAIR`: a capability-expansion transition restores actionability.

### Transition permissions

- `PRESERVE`: required futures remain safe after the transition.
- `DESTROY(H)`: a declared destructive transition is permitted only if every required future remains recoverable within horizon `H`.

## Core principle

> A loss of information is not yet destruction of a required future. Destruction occurs only when the future leaves the admissible recoverability envelope defined by the contract and the allowed planner dynamics.

## Scope discipline

Core V1 does **not** claim that every component concept is historically new. Reachability, viability, decision sufficiency, abstraction, synthesis, value of information, unlearning, minimal obstructions and contract-based design all have substantial prior literatures.

The candidate INSACERMO contribution is the unified, contract-relative architecture in which information, capabilities, obstructions, planning, recoverability and safe destruction are all evaluated through the same object: the family of future contracts that remain guaranteeable or recoverable.

## Next phase after V1 freeze

1. central paper,
2. 2–3 externally legible real-data demonstrations,
3. public engine exposing the seven semantics with witnesses/certificates,
4. only then extension to explicit recovery price `P` and the triple `(rho, D, P)`.
