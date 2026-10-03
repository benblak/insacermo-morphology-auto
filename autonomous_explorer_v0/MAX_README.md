# INSACERMO Autonomous Explorer — MAX experiment

This branch does **not** replace or rewrite the frozen INSACERMO core.

It tests a stronger external autonomy loop: the system receives a certified
frontier, a relation, and an operator grammar. It is not given the next target
or a hand-written plan.

At each unresolved frontier point it autonomously chooses among:

1. exact endpoint probing;
2. safe extension;
3. certified 1-swap repair;
4. certified 2-swap repair;
5. certified 3-swap repair;
6. certified 4-swap repair;
7. REFUSE if none survives a full global replay.

Every ACT candidate is replayed against **all** forbidden triples before it is
accepted. A failed search is not treated as a proof of impossibility.

"MAX freedom" here therefore means maximum freedom inside the current explicit,
auditable symbolic operator grammar. It does not mean unbounded or magical
scientific autonomy.
