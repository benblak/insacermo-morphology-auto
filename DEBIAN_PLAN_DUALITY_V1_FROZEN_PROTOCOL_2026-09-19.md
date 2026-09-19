# INSACERMO Post-Closure Debian Plan-Duality Audit V1 — Frozen Protocol

**Freeze date:** 19 September 2026  
**Status:** external post-closure validation; does not reopen Core V1.

## Inherited Debian choices

This audit inherits unchanged from `postfreeze_debian_installability_v1.py`:

- Debian release: version 13.7, codename `trixie`;
- architecture: `amd64`;
- exact solver: `dose-debcheck`;
- fixed target packages:
  `curl git nginx postgresql imagemagick ffmpeg rsync sqlite3`;
- future catalogue: all singleton, pair, and triple target bundles that are installable in intact Debian;
- the same deterministic structural selection of three perturbation package classes;
- repair cost: number of selected perturbation classes restored.

No target, release, architecture, structural-selection rule, or installability semantics may be changed after observing the new endpoint.

## New endpoint: repair-plan duality at budget B=1

Let P_B be the set of restoration plans whose cost is at most 1:
- restore nothing;
- restore exactly one of the three structurally selected perturbation classes.

For each future contract q in the intact baseline-feasible catalogue Gamma, define its plan support:
`Sigma(q) = { p in P_B : q is installable after plan p }`.

For a finite family F of future contracts:

- `F` is budget-1 jointly feasible iff the intersection of all `Sigma(q)`, q in F, is nonempty;
- `F` is a minimal budget-1 obstruction iff that intersection is empty and every proper nonempty subfamily has nonempty intersection.

Search all minimal obstructions of orders 2, 3, and 4.

## Private-witness requirement

For every minimal obstruction F and every q in F, require one explicit repair plan p_q such that:

- p_q supports every future in F \ {q};
- p_q does not support q.

Print the first ten minimal obstructions in deterministic catalogue order with all private witness plans.

## Strong higher-order checks

- Order 3 counts only families whose three pairs are all jointly feasible.
- Order 4 counts only families whose four triples are all jointly feasible.

## Guardrails

- No post-result change of budget B=1.
- No post-result change of target catalogue or perturbation selection.
- No replacement of Debian installability by a graph approximation.
- A null result is retained.
- This audit validates the plan-duality structure on the Debian adapter; it does not establish historical novelty or universal external validity.
