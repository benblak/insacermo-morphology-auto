# INSACERMO Repair-Nerve / Future-Helly Bridge V1

Status: exploratory bridge layered on top of Core V1. No Core definition is changed.

## Why this bridge exists

The blind Mathlib repair-geometry experiment produced nontrivial repair depths but no joint escalation. Its selected repair signatures were nested. Existing verified INSACERMO modules already contain the complementary phenomenon:

- `HigherOrderObstructions.lean` proves a rank-3 common-action obstruction with pairwise compatibility.
- `TemporalJointContractComplex.lean` distinguishes joint recovery along one common trajectory from separate singleton recovery.
- `FutureRepairPrice.lean` defines minimum repair budgets.

The present bridge does not introduce the rank-3 phenomenon as new. It links these existing ideas to the repair-depth experiment.

## Abstract plan formulation

Let `Plan` be a set of complete admissible plans, not merely first actions. For a budget/horizon H and future q, let

A_H(q) = { p : Plan | p is admissible at H and p satisfies q }.

A finite bundle F is jointly feasible iff

intersection_{q in F} A_H(q) is nonempty.

Therefore the joint-feasibility complex is exactly the nerve of the family {A_H(q)}.

This distinction matters: if a "plan" were only the first repair action, singleton feasibility could use incompatible later trajectories. The plan object must encode enough continuation information to witness true joint feasibility.

## Chain-collapse special case

If every future has one mandatory atomic repair signature R(q), unit repair costs give

D(F) = | union_{q in F} R(q) |.

For two futures q,r,

D({q,r}) - max(D(q),D(r))
= min(|R(q) \\ R(r)|, |R(r) \\ R(q)|).

Hence zero pair escalation is equivalent to comparability by inclusion. Zero pair escalation for every pair means the repair signatures form a chain; then every bundle satisfies

D(F) = max_{q in F} D(q).

The Mathlib blind witness is of this nested type.

## Arbitrary-order obstruction

With k actions and k futures, let future i accept every singleton action except action i. Every nonempty proper bundle has a common cost-1 plan, but the full k-bundle has no common cost-1 plan and needs cost 2. Thus the budget-1 complex is the boundary of a (k-1)-simplex and the unique minimal obstruction has order k.

This is already conceptually consistent with the verified generic higher-order obstruction machinery; the accompanying Python audit checks the construction for k=3,...,12.

## Helly interpretation

The maximum size of an inclusion-minimal bundle with empty common-plan intersection is the Helly number of the corresponding finite plan-feasible set family. Consequently:

- in unrestricted discrete plan systems, obstruction order is unbounded;
- under additional geometric assumptions, classical Helly-type bounds can limit how many futures need to be checked jointly;
- observing a high-order obstruction rules out low-dimensional convex representations of the plan-feasible sets.

These are interpretation bridges to classical Helly/nerve theory, not claims that those mathematical results are new.
