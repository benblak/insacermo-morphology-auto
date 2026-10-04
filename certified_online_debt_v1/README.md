# INSACERMO Certified Online Debt V1

This layer sits **before** the Proof-Carrying Temporal Runtime.

It does not change the canonical decision semantics. Its job is narrower: a temporal debt
value may reach the ACT gate only after a registered authority recipe has been checked and
the claimed upper bound has been recomputed from its witness.

Core rules:

- same observation is not enough to certify hidden current debt (No-Free-Debt);
- delayed exact debt is reusable only through an explicit certified growth cap;
- fresh probes can certify a bound only inside their declared freshness horizon;
- two valid bounds on the same debt may be tightened;
- bounds on declared distinct debt components may be added;
- absent a legitimate current bound, downstream ACT must not be renewed.

The Lean kernel proves the abstract statements. Python checks the concrete receipt mechanics.
Neither layer magically proves external physical facts: those remain explicit roots of trust.
