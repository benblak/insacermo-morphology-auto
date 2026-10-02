# INSACERMO Adaptive Proof Acquisition V2

V1 chose minimum-cost evidence with deterministic advertised tightening. V2 handles **outcome-dependent
probes** and finite correlated worlds.

A probe is accepted only when every outcome certificate is a sound upper bound for all currently modeled
worlds compatible with that outcome. The planner then searches a finite contingent tree.

At an ACT leaf the obligation is still exactly:

`true_debt <= certified_upper_bound < reserve`.

A REFUSE leaf is always safe. Lean proves that a tree satisfying this leaf invariant cannot execute an unsafe
ACT on any branch.

## Why finite worlds?

Outcomes of successive probes are not independent. A single hidden world determines all probe outcomes.
Representing a finite version space prevents the planner from inventing impossible combinations of outcomes.

## Objective

V2 minimizes **worst-case additional acquisition cost** among trees that guarantee eventual ACT for every
currently possible world. It may stop early on branches whose certificate already satisfies the gate.

If no such tree exists, V2 returns REFUSE.

## Scope / non-claim

Adaptive test selection and decision trees are established research topics (active sensing, adaptive
submodularity, ECD/DRD). This implementation does not claim those generic ideas as novel.

The INSACERMO-specific object being tested is a fail-closed contingent tree whose ACT leaves must carry
sound proof-carrying debt bounds satisfying the pre-existing temporal gate.
