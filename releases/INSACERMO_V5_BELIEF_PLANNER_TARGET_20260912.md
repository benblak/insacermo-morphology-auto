# INSACERMO V5 — Belief-Space Planner Target

Date frozen: 2026-09-12

## Question

Can the already verified finite-horizon Bellman actionability contract be connected to the existing INSACERMO sequential router so that a belief-space decision state is classified as ACT, REFUSE, or a minimum-cost PROBE / REPAIR / PROBE+REPAIR frontier?

This target does not alter the Bellman contract. It treats Bellman-optimal actionability as the fixed safety predicate that the planner must reach.

## Frozen ingredients

The current verified stack provides:

- exact finite rational belief laws;
- finite Bayes prediction and posterior update;
- finite-horizon Bellman recursion;
- existence of Bellman-optimal actions;
- `BellmanGood(n,b,a)`;
- `BellmanSafeRep` on belief representations and capability sets.

The earlier sequential planner provides:

- move kinds `probe`, `repair`, `probeRepair`;
- natural-valued move costs;
- legality constraints;
- PRESERVE guards on information-losing moves;
- finite-plan reachability;
- global minimum-cost plan existence whenever a safe finite plan exists;
- top-level router completeness: ACT / REFUSE / nonempty optimal frontier.

## Candidate-state abstraction

Let `I` index admissible planner states. For each `i : I` provide:

- a capability set `caps i : Set A`;
- a belief representation `obs i : FiniteLaw S -> Y`.

For fixed Bayes/Bellman contract parameters and a fixed admissible belief set `B`, define

`BellmanCandidateSafe(i)`

iff

`BellmanSafeRep ... B (caps i) (obs i)`.

Planner moves operate on candidate indices `I`, not on hidden extra information. Their declared `MoveKind` records whether the transition is interpreted as PROBE, REPAIR, or PROBE+REPAIR.

## Formal targets

1. import the already verified sequential PRESERVE and planner modules into the current V5 branch without changing their semantics;
2. define `BellmanCandidateSafe`;
3. define belief-planner reachability and optimality by instantiating the generic sequential planner with `BellmanCandidateSafe`;
4. prove ACT is exactly current Bellman actionability;
5. prove REFUSE means no legal finite candidate trajectory reaches Bellman actionability;
6. prove that any unsafe but reachable candidate has a nonempty globally minimum-cost route frontier whose first move is PROBE, REPAIR, or PROBE+REPAIR;
7. prove the full router trichotomy for every candidate state;
8. preserve the existing rule that information-losing transitions require an explicit PRESERVE certificate.

## Interpretation target

If this passes, the stack becomes

`belief -> Bayes update -> Bellman optimal-action contract -> SafeRep -> sequential planner`.

The planner will not merely answer which action is Bellman-optimal. It will classify whether the current information/capability state already justifies such an action, whether more information or capability can reach such a state at minimum declared cost, or whether the declared search space must REFUSE.

## Guardrails

This target does NOT yet prove:

- that any particular domain's candidate graph contains every physically possible probe or repair;
- that declared Nat move costs equal money, time, energy, entropy, or bandwidth unless modeled as such;
- infinite-horizon Bellman fixed points;
- unknown-model learning;
- continuous belief spaces;
- completeness relative to all possible POMDP policies outside the declared candidate graph.

## Falsification boundary

If the Bellman actionability predicate cannot serve as the sequential planner's safety target without modifying either Bellman optimality or `SafeRep`, the integration fails. The frozen contract must not be weakened after seeing the result.
