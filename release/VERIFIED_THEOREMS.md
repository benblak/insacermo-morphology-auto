# INSACERMO Core V1 — Verified Theorem Map

Kernel anchor: `dc8878f8cee3f8d8bfd4769523077d829b246a62`
CI: Actionability Information Lean #113 — success

## 1. Representation safety

Module: `BiMonotone.lean`

Core object:

`SafeRep Good B C h`

Interpretation: every realized representation fiber admits at least one capability in `C` that is good for every possible world in that fiber.

Key monotonicity principle: finer information and/or a larger capability set cannot destroy an already-safe representation.

## 2. Future envelope

Module: `FutureEnvelope.lean`

`Envelope Good B C h`

Interpretation: set of declared future contracts that are safely actionable now.

Verified principles include:

- membership iff `SafeRep` for the corresponding future contract,
- monotonicity under information refinement,
- monotonicity under capability expansion,
- no lost futures under combined refinement + capability expansion,
- finite audit equivalence under uniform obstruction-rank bounds,
- large-obstruction witness for false-safe destruction under insufficient audit depth.

## 3. Future debt

Module: `FutureDebt.lean`

`Debt Req Good B C h = Req \ Envelope ...`

Verified principles include:

- zero debt iff all required futures are guaranteed,
- debt is antitone under information refinement and capability expansion,
- probe/repair monotonicity,
- preservation of required futures under admissible monotone moves.

## 4. Future-conservation planner

Module: `FutureConservationPlanner.lean`

Core objects:

- `DebtState`,
- `DebtNonIncreasing`,
- `Reach`,
- `Goal`,
- `Solves`.

Verified principles include:

- debt monotonicity lifts across finite planner reach,
- zero debt is absorbing under debt-nonincreasing continuation,
- solved plans remain solved under safe continuation,
- planner goal instantiated on contract states iff the future-envelope guarantee holds.

## 5. Temporal recoverability envelope

Module: `TemporalRecoverabilityEnvelope.lean`

`RecoverableEnvelope Avail Step H x`

Interpretation: futures available now or recoverable through admissible transitions within horizon `H`.

Verified principles include:

- `R_0(x) = E(x)`,
- current availability is included in every finite-horizon recoverability envelope,
- one admissible step transports successor recoverability to predecessor recoverability,
- horizon monotonicity `R_H ⊆ R_(H+1)`,
- temporal debt `Req \ R_H`,
- horizon-antitone temporal debt,
- temporal debt is contained in immediate debt,
- exact decomposition of immediate debt into temporal debt plus deferred-but-recoverable debt,
- zero temporal debt iff all required futures are in `R_H`,
- a future may be unavailable now yet recoverable in one step.

## 6. Recovery depth and irreversibility

Module: `RecoveryDepthIrreversibility.lean`

Core objects:

- `EventuallyRecoverableEnvelope`,
- `IrreversibleDebt`,
- `LateDebt`,
- `RecoveryDepthAtMost`,
- `FirstRecoveryAt`,
- `RecoveryDepth`.

Verified principles include:

- arbitrary finite-horizon monotonicity,
- every finite-horizon recoverable future is eventually recoverable,
- admissible predecessors inherit eventual recoverability,
- irreversible debt is contained in every finite-horizon temporal debt,
- temporal debt decomposes exactly into irreversible debt plus late debt,
- eventual safety iff irreversible debt is empty,
- every eventually recoverable future has a minimum finite recovery depth,
- the minimum depth actually recovers the future,
- it is no larger than any successful recovery horizon,
- it is an exact first-entry horizon,
- safety within horizon `H` iff every required future is recoverable within `H`,
- under eventual recoverability, safety within `H` iff every minimum recovery depth is ≤ `H`.

## 7. Public decision semantics

Module: `DecisionSemantics.lean`

### Status

- `ACT`: future is actionable now.
- `RECOVER(H)`: unavailable now but recoverable within `H`.
- `REFUSE`: not eventually recoverable by any finite admissible plan.

Verified separation:

- `ACT -> not RECOVER`,
- `ACT -> not REFUSE`,
- `RECOVER -> not REFUSE`,
- for required futures, `REFUSE` iff membership in `IrreversibleDebt`.

### Mechanisms

- `PROBE`: an information-gathering transition restores immediate actionability.
- `REPAIR`: a capability-changing transition restores immediate actionability.

Verified soundness:

- admissible `PROBE -> RECOVER(1)`,
- admissible `REPAIR -> RECOVER(1)`.

### Transition permissions

- `PRESERVE`: all required futures remain immediately actionable after transition.
- `PRESERVE_WITHIN(H)`: all required futures remain recoverable within horizon `H`.
- `DESTROY(H)`: a declared destructive transition is permitted only if `PRESERVE_WITHIN(H)` holds afterward.

Verified consequences:

- immediate preservation implies preservation within every finite horizon,
- `DESTROY(H)` implies zero temporal debt at horizon `H`,
- `DESTROY(H)` excludes irreversible debt for every required future.

## Core theorem-level reading

The verified kernel supports the following interpretation:

`current guarantee` → `deadline recoverability` → `minimum recovery depth` → `irreversible loss` → `public decision semantics`.

This is a formal correctness result for the stated definitions and theorems. It is not, by itself, a claim of historical novelty or empirical usefulness; those require literature comparison and external validation.
