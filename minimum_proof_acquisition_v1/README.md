# INSACERMO Minimum Proof Acquisition V1

## Purpose

This layer sits before Certified Online Debt. It does **not** change ACT / PROBE / REPAIR /
REFUSE. It plans which already-declared evidence source(s) would be sufficient to satisfy the
existing proof obligation.

For integer reserve `rho` and certified debt upper bound `U`, define

`Delta(rho,U) = 0` if `U < rho`, otherwise `U-rho+1`.

Lean proves that for `rho > 0`:

`U - G < rho  <->  Delta(rho,U) <= G`.

Thus `Delta` is the exact guaranteed tightening required to restore ACT.

## Two composition regimes

1. **Same debt / min composition.** If several certificates all upper-bound the same debt and
   compose by minimum, any successful bundle contains a successful singleton. With nonnegative
   acquisition costs, the planner therefore selects the cheapest individually sufficient source.

2. **Declared additive components.** When the debt is soundly decomposed into distinct additive
   components, different evidence sources may tighten different components. V1 exhaustively
   enumerates finite source subsets, permits at most one selected offer per component, and returns
   the minimum-cost bundle whose post-acquisition certified total satisfies `U_post < rho`.

The planner never mints a certificate. Its output is a **plan**. The chosen producer(s) must still
run, Certified Online Debt must verify their receipts, and only then may the Temporal Runtime
renew ACT.

## Relation to prior work

Minimum-cost information gathering is not new. Value of Information, active sensing, adaptive
submodularity, and Decision Region Determination already study how to acquire information or tests
economically for decision making. V1 does not claim novelty for that generic optimization problem.

The specific bridge tested here is narrower: transform INSACERMO's proof-carrying temporal
obligation `U < rho` into an exact proof deficit, then optimize only over evidence sources whose
outputs are independently verifiable upper-bound certificates. Failure to close the obligation
remains fail-closed.
