# INSACERMO Autonomous Explorer V0

This is an **external exploration harness**, not a rewrite of the frozen INSACERMO core.

The experiment asks a deliberately narrow question:

> If the system is given a certified finite frontier and a problem relation, can it choose the next structural question itself, extend the frontier when it has a certificate, and refuse when it cannot certify the next step?

## Policy

The loop chooses the first unresolved endpoint after the current exact frontier.

- **PROBE** — enumerate the new endpoint constraints exactly.
- **ACT** — extend the witness only when no new constraint is active; combine the witness lower bound with the generic upper rule `f(n) <= f(n-1)+1`.
- **REFUSE** — if the current witness is broken by the endpoint, do not invent a repair or an exact maximum. Emit the obstruction and the next question that would be required.

There is no machine learning, no opaque scoring model, and no hard-coded target 735.

## Erdős 302 fixture

Input frontier: `f(734)=608` with the public 608-element witness as an explicit premise.

Expected autonomous trace:

1. PROBE 735.
2. Discover exactly the endpoint triples `(210,294,735)` and `(294,490,735)`.
3. Observe that the witness omits 294, so neither new triple is active.
4. ACT: extend to a 609-element witness and certify the transfer to 735.
5. PROBE 736.
6. Detect an active obstruction `(224,322,736)`.
7. REFUSE exactness at 736 under the current certificate grammar.

This is a first test of **autonomous question selection with certified stopping**, not a claim of general autonomous scientific discovery.
