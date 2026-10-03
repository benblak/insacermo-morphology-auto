# INSACERMO Autonomous Explorer — MAX feasibility experiment

The previous MAX attempts exposed the wrong question.

At an exact frontier `f(n)=k`, the next value automatically lies in

`k <= f(n+1) <= k+1`.

So the explorer must **not** solve a new global optimization problem. It only
needs one bit:

> Does an admissible witness of size `k+1` exist?

This branch implements that information-minimal policy.

For the reciprocal-triple problem the query is encoded as a cardinality SAT
instance: choose at most `(n+1)-(k+1)` removed vertices that hit every forbidden
triple. Two different SAT backends answer the same feasibility question.

- both SAT + both witnesses replay globally -> **GROWTH**;
- both UNSAT -> **PLATEAU**;
- disagreement or failed replay -> **REFUSE**.

A direct structural SAFE_ADD is still tried first because it is cheaper and
more transparent than SAT.

This is intentionally not labelled Lean verification. SAT results are recorded
as `EXACT_COMPUTATIONAL_CROSSCHECK_NOT_LEAN` until a separate formal
certificate layer is added.

The experiment tests a core INSACERMO principle:

> compute only the information needed to decide the next certified action.
