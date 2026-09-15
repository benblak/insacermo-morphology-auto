# INSACERMO Core V1

## Contract-Relative Conservation, Recovery, and Destruction of Exigible Futures

**Benjamin Lenoir**

### Abstract

INSACERMO studies a contract-relative question: after transforming information, capabilities, or internal state, which future obligations remain safely actionable, recoverable before a deadline, or irreversibly lost? The framework centers on a future envelope `E`, the set of future contracts currently guaranteed by the available representation and capabilities, and on a temporal recoverability envelope `R_H`, the set of futures that are either actionable now or can be restored by an admissible plan within horizon `H`. This yields immediate debt `Req \ E`, temporal debt `Req \ R_H`, eventual finite-horizon recoverability `R_∞`, irreversible debt `Req \ R_∞`, and a minimum recovery depth `D_q` for each eventually recoverable future. The public semantics ACT, PROBE, REPAIR, RECOVER, REFUSE, PRESERVE and DESTROY are then defined from these objects. The Lean 4 formalization establishes monotonicity, exact debt decompositions, recovery-depth minimality, irreversibility criteria, and safety conditions for destructive transitions. The resulting perspective separates loss of information from destruction of future actionability: information may be discarded while a required future remains recoverable by admissible sensing, repair, or planning. INSACERMO is not proposed as a replacement for state abstraction, viability, control synthesis, decision sufficiency, value of information, or machine unlearning, but as a unifying contract-relative architecture connecting these concerns through the conservation of exigible futures.

## 1. Problem statement

Many systems transform, compress, forget, aggregate, or delete information. The usual question is whether a chosen statistic, representation, controller state, or learned model remains sufficient for a current task. INSACERMO instead takes the set of future obligations as primitive.

Given:

- possible worlds `S`,
- capabilities/actions `A`,
- a family of future contracts/questions `Q`,
- a predicate `Good(q,s,a)` expressing that action `a` safely satisfies future contract `q` in world `s`,
- an ambiguity set `B ⊆ S`,
- an available capability set `C ⊆ A`,
- a representation `h : S → Y`,
- a required future family `Req ⊆ Q`,

we ask:

> What may the system lose, change, or destroy now while preserving the futures the contract still requires?

## 2. Safe representation and current future envelope

A representation is safe for a future contract when every realized representation fiber admits at least one available action that is good for every possible world in that fiber.

Define the current future envelope:

`E(Good,B,C,h) = {q | SafeRep (Good q) B C h}`.

`E` is the set of future contracts safely actionable now.

The required-future debt is:

`Debt = Req \ E`.

Thus:

`Debt = ∅  <->  Req ⊆ E`.

The verified monotonicity law is joint in information and capability: information refinement and capability expansion cannot remove a future already in the envelope.

## 3. Obstructions and certification depth

Safe actionability may fail because a fiber contains a subset of possible worlds with no common admissible action. Minimal such subsets form common-action obstructions.

A finite obstruction-rank bound yields a finite audit depth: when every minimal obstruction has size at most `k`, checking all subsets through size `k` is complete for the relevant safety predicate. Conversely, larger minimal obstructions produce false-safe local audits at insufficient depth.

This gives the first complexity coordinate:

`rho = certification depth`.

It answers:

> How deeply must the system inspect local combinations before it may certify a transformation as safe?

## 4. Temporal recoverability envelope

Current failure is not equivalent to destruction.

Let `X` be a planner state space, `Avail(x) ⊆ Q` the futures actionable at state `x`, and `Step(x,y)` an admissible transition relation.

Define recursively:

`R_0(x) = Avail(x)`

and

`R_(H+1)(x) = Avail(x) ∪ {q | exists y, Step(x,y) and q ∈ R_H(y)}`.

`R_H(x)` is the set of futures recoverable within horizon `H`.

The verified laws include:

- `R_H(x) ⊆ R_(H+1)(x)`,
- current availability is contained in every `R_H`,
- one admissible predecessor step transports successor recoverability to the predecessor.

Define temporal debt:

`TDebt_H(x) = Req \ R_H(x)`.

Then temporal debt is antitone in the horizon:

`TDebt_(H+1)(x) ⊆ TDebt_H(x)`.

Immediate debt decomposes into deadline debt plus futures currently unavailable but recoverable before the deadline.

## 5. Eventual recoverability and irreversible debt

Define:

`R_∞(x) = {q | exists H, q ∈ R_H(x)}`.

This is eventual finite-horizon recoverability.

Irreversible debt is:

`IDebt(x) = Req \ R_∞(x)`.

A required future is therefore irreversibly lost in the model exactly when no finite admissible plan can recover it.

Temporal debt at horizon `H` decomposes exactly into:

`TDebt_H = IDebt ∪ LateDebt_H`,

where `LateDebt_H` contains futures that miss the declared deadline but remain recoverable at some later finite horizon.

This separates three cases:

1. actionable now,
2. not actionable now but recoverable,
3. not recoverable by any finite admissible plan.

## 6. Minimum recovery depth

For any eventually recoverable future `q`, define:

`D_q(x) = min {H | q ∈ R_H(x)}`.

The Lean development proves:

- `q ∈ R_(D_q)(x)`,
- if `q ∈ R_H(x)` then `D_q(x) ≤ H`,
- `D_q` is an exact first-entry horizon.

Under eventual recoverability of all required futures:

`SafeWithin_H(x)  <->  forall q in Req, D_q(x) ≤ H`.

This gives the second complexity coordinate:

`D = recovery/planning depth`.

It answers:

> How many admissible transitions are minimally required before a future becomes safely actionable again?

## 7. Public decision semantics

The public INSACERMO vocabulary is separated into three layers.

### 7.1 Future status

`ACT(q)`:

`q ∈ E`.

The future is actionable now.

`RECOVER_H(q)`:

`q ∉ E` and `q ∈ R_H`.

The future is unavailable now but recoverable before the declared deadline.

`REFUSE(q)`:

`q ∉ R_∞`.

No finite admissible plan can recover the future.

The formalization proves:

- `ACT -> not RECOVER`,
- `ACT -> not REFUSE`,
- `RECOVER -> not REFUSE`.

For required futures, `REFUSE` coincides with membership in irreversible debt.

### 7.2 Recovery mechanisms

`PROBE` denotes an information-acquisition/refinement transition that restores immediate actionability.

`REPAIR` denotes a capability-changing transition that restores immediate actionability.

When these transitions are included in the admissible planner relation:

- `PROBE -> RECOVER(1)`,
- `REPAIR -> RECOVER(1)`.

Thus PROBE and REPAIR are not alternative status classes; they are mechanisms that can witness recovery.

### 7.3 Transition permissions

`PRESERVE` requires all required futures to remain immediately actionable after a transition.

`PRESERVE_WITHIN(H)` requires all required futures to remain recoverable within horizon `H`.

`DESTROY(H)` permits a declared destructive transition only when `PRESERVE_WITHIN(H)` holds after the transition.

The formalization proves:

`DESTROY(H) -> TDebt_H = ∅`

and therefore:

`DESTROY(H) -> no required future belongs to irreversible debt`.

This yields the central operational principle:

> Information loss is not itself destruction of a required future. A destructive transformation is permitted when the required future family remains inside the admissible recoverability envelope imposed by the contract.

## 8. Relationship between information and capability

Information and capability enter symmetrically at the level of actionability but through different mechanisms.

A finer representation may separate previously ambiguous worlds. A larger capability set may provide an action that works uniformly across an ambiguous fiber. Therefore capability can compensate for information loss.

This motivates the phrase:

> Capability can buy the right to forget.

The verified envelope monotonicity makes this precise: a refinement of information and/or expansion of capability cannot remove an already guaranteed future.

## 9. Planner semantics

The future-conservation planner operates on states carrying a debt set. A debt-nonincreasing transition relation ensures that finite reach cannot increase debt, and zero debt is absorbing under safe continuation.

The planner goal is therefore not an arbitrary target state but:

`Debt = ∅`.

The temporal extension refines this into deadline safety:

`TDebt_H = ∅`.

The minimum recovery depth then supplies a quantitative planner interpretation for individual futures.

## 10. What is and is not claimed as novel

INSACERMO does not claim priority for the individual ideas of:

- reachability or backward reachability,
- viability,
- state abstraction,
- sufficient statistics,
- belief states,
- control synthesis,
- temporal-logic realizability,
- minimal unsatisfiable cores,
- Helly-type local-to-global bounds,
- value of information,
- data minimization,
- machine unlearning,
- decision-sufficient representation learning.

The candidate contribution is instead the contract-relative unification:

`representation`
→ `current future envelope`
→ `debt`
→ `temporal recoverability`
→ `minimum recovery depth`
→ `irreversibility`
→ `public action semantics`
→ `safe destruction`.

The core invariant is not retained information itself, but the family of exigible futures that remain guaranteeable or recoverable.

## 11. Formal verification

The Core V1 Lean 4 development is anchored at commit:

`dc8878f8cee3f8d8bfd4769523077d829b246a62`.

GitHub Actions run #113 completed successfully with:

- rejection of `sorry` / `admit`,
- full `lake build`,
- 8684 jobs completed successfully,
- targeted `leanchecker` success on `DecisionSemantics`.

This verifies the stated formal results relative to the Lean kernel and imported foundations. It does not establish historical novelty, empirical superiority, or real-world safety outside the modeled assumptions.

## 12. Empirical program

Core V1 should be evaluated using externally legible demonstrations in which the contract, information state, available capabilities and admissible recovery transitions are all explicit.

Three recommended classes are:

1. representation preservation in AI,
2. real-world multi-action decision data such as travel-mode choice,
3. a biological or medical actionability setting with carefully stated non-clinical interpretation.

The engine should return not only a label but a witness or certificate:

- ACT witness,
- PROBE route,
- REPAIR route,
- RECOVER depth,
- REFUSE irreversibility witness relative to the finite model,
- PRESERVE certificate,
- DESTROY permission with deadline.

## 13. Future extension: recovery price

Core V1 intentionally stops before adding another major axis.

The next quantitative coordinate is a recovery price `P`, giving the minimum admissible cost required to eliminate debt or recover a future. Together with obstruction/certification depth `rho` and recovery/planner depth `D`, this would yield the future complexity signature:

`(rho, D, P)`.

This extension is not part of the frozen Core V1 claim.

## Conclusion

INSACERMO Core V1 reframes information preservation as conservation of future actionability. The central distinction is between information that has been lost, futures that are temporarily unavailable, futures that miss a deadline, and futures that no finite admissible plan can recover. By indexing safety to explicit future contracts, capabilities and planner dynamics, the framework supports a precise notion of permission to preserve, probe, repair, recover, refuse, or destroy.

The resulting principle is:

> Preserve not the past for its own sake, but exactly what the declared future still requires—or enough structure and capability to recover it before it is due.
