# INSACERMO V4 — Finite Actionability Theory Freeze

Date frozen: 2026-09-12

Reference manuscript:

- **INSACERMO — Obstruction Geometry of Actionability**
- Subtitle: *From capability-relative information to a finite hypergraph theory of justified action*
- PDF SHA256: `cee2e94d1cba2a7fbd221753b847cc15ae009d759191e92ac386ce20e6b55b7e`
- DOCX SHA256: `c7e0a98ea3cdf748240fe10a37825b7f5ea74904006d6e3c308ae0c39835df20`

## Frozen architectural skeleton

INSACERMO is treated as three operational layers only:

1. `Contract`
2. `Actionability / Obstructions`
3. `Planner`

`PRESERVE` is a legality constraint on planner transitions, not a fourth runtime layer.

## Frozen finite actionability kernel

For world set `B`, capability set `C`, contract predicate `Good`, and representation `h`, actionability is defined fiber-wise:

> `SafeRep(Good,B,C,h)` iff every realized observation fiber has at least one common action in `C` that is Good for every world in that fiber.

Define capability-relative common-action obstructions and their minimal members. The finite hypergraph of minimal obstructions is:

`H_C = { F : F is a minimal common-action obstruction under C }`.

The finite characterization is frozen as:

> `SafeRep(Good,B,C,h)` iff no realized observation fiber contains a hyperedge of `H_C`.

Equivalently: `SafeRep iff HypergraphSafe` on finite world spaces.

## Frozen interpretation

- PROBE refines/splits observation fibers.
- REPAIR enlarges capability and therefore changes the capability-relative obstruction hypergraph.
- ACT holds when every realized fiber is hit by a common available admissible action.
- REFUSE holds when no allowed observation/capability path reaches safety under the declared contract.
- PRESERVE forbids information coarsenings that recreate an obstruction required by an allowed future contract.

Canonical condensation:

`capabilities -> H_C -> safe fibers -> information price R_A -> minimal legal plan`

## Formally verified theorem/certificate families

The V4 theory relies on the following Lean-verified families developed before this freeze:

- capability-information monotonicity and strict witnesses;
- bi-monotone SafeRep under information refinement and capability expansion;
- sequential PRESERVE/resource/governance constraints;
- finite planner/router completeness;
- Bellman-style optimal-substructure with PRESERVE compliance;
- obstruction certificates and unsafe-fine-blocks-coarsening results;
- deterministic fiber criterion;
- maximal-feasibility gate;
- weighted hitting-set characterization of deterministic actionability;
- capability-information price antitonicity;
- capability complementarity and binary coarse-safety diminishing-returns violation;
- exact common-action fiber criterion;
- higher-order common-action obstructions and rank-3 pairwise-incompleteness witness;
- finite hypergraph characterization `SafeRep iff HypergraphSafe`.

## Empirical route map available at freeze

Observed structural regimes include:

- **ACT** — Grunfeld frozen real-data structural test;
- **PROBE -> ACT** — Breast Cancer Wisconsin Diagnostic frozen structural test;
- **REPAIR -> ACT** — Wine frozen repair-only structural test;
- **PROBE + REPAIR -> ACT** — ModeChoice exploratory real-data structural test;
- **REFUSE** — frozen ASlib scenarios and NASA C-MAPSS FD001 under their declared contracts.

These are not all equal in evidential status. Exploratory, frozen/preregistered, simulated, and benchmark evidence must remain explicitly distinguished.

## Scope boundary

This freeze establishes a **finite, exact, contract-relative theory of actionability under the declared SafeRep semantics**. It does not claim a universal stochastic, continuous, partially observed, learning-theoretic, or multi-agent closure.

The next extensions must test whether the same three-layer skeleton survives removal of finite/static/exact assumptions, rather than modifying the finite kernel to force agreement.

## Novelty boundary

Hypergraphs, hitting sets, set cover, Blackwell ordering, viability, sensor/actuator co-design, action-sufficient representations, zero-error ideas, rough-set reducts, and related combinatorial objects have substantial prior literature. Historical novelty is not asserted by formal verification. Candidate novelty must be argued at the level of the combined contract-relative architecture, exact obstruction semantics, capability-relative information price, planner routing, and preservation/debt structure after dedicated literature audit.

## Design rule after freeze

> No new runtime layer without a new irreducible operational function.

Any subsequent theorem, certificate, optimizer, or empirical study should attach to the frozen `Contract -> Actionability -> Planner` skeleton unless a mathematically unavoidable counterexample forces revision.
