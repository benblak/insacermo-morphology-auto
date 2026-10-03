# INSACERMO Autonomous Explorer — MAX experiment

This branch does **not** replace or rewrite the frozen INSACERMO core.

The first MAX attempt deliberately tried explicit 1/2/3/4-swap enumeration.
That experiment hit the expected combinatorial explosion and timed out. The
lesson is now part of the policy: when local symbolic repair ceases to be an
efficient certificate route, the explorer may autonomously escalate to an
external **exact combinatorial solver**.

Current operator policy:

1. choose the next unresolved frontier point;
2. enumerate its new constraints exactly;
3. try a structural SAFE_ADD;
4. if blocked, escalate to a minimum hitting-set computation;
5. cross-check the optimum with a second SAT backend;
6. replay the returned witness against every forbidden triple;
7. resolve either GROWTH (k+1) or PLATEAU (k);
8. REFUSE on solver disagreement, replay failure, or a value outside the
   inherited band f(n-1) <= f(n) <= f(n-1)+1.

The exact SAT backend is **not machine learning** and is not described as an
INSACERMO/Lean proof. It is an external exact search operator selected by the
autonomous loop. Results from this layer are labelled
`EXACT_COMPUTATIONAL_CROSSCHECK_NOT_LEAN` until separately formalized.

"MAX freedom" here means freedom to choose among auditable strategies while
preserving the rule: no ACT without a replayable witness/certificate path.
