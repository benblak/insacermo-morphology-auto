# INSACERMO Autonomous Explorer — MAX MIP experiment

The SAT feasibility experiment still timed out at the first hard UNSAT frontier.
That is a computational failure, not a mathematical conclusion.

This revision preserves the same information-minimal question:

> from exact f(n)=k, does an admissible witness of size k+1 exist at n+1?

It changes only the external exact-search operator.

The query is now solved in two equivalent binary MILP formulations:

- KEEP form: every forbidden triple has at most two kept vertices and at least
  k+1 vertices are kept;
- REMOVED form: every forbidden triple has at least one removed vertex and at
  most n-(k+1) vertices are removed.

Both are solved by HiGHS through scipy.optimize.milp, and any feasible witnesses
are replayed against every forbidden triple before ACT.

This is a cross-check of two formulations using the same MIP backend, so it is
explicitly labelled:

`EXACT_COMPUTATIONAL_MIP_CROSSCHECK_NOT_LEAN`

It is not a Lean theorem and not an independently checkable proof certificate.

The INSACERMO point of the experiment is unchanged: the controller is allowed
to abandon an unproductive proof/search operator while preserving the contract,
the exact question, and the refusal discipline.
