# INSACERMO V2 — Duality / Golden-Point No-Go and Symmetry Audit — Frozen Protocol

**Freeze date:** 19 September 2026  
**Status:** exploratory V2 protocol frozen before result  
**Frozen V1 artifacts modified:** NO

## Question

Can the old fixed point

[
Phi_*=(3-sqrt5)/2approx0.38196601125
]

be recovered from the V1 common-plan / obstruction duality alone, without inserting
(Phi=(1-Phi)^2), the golden ratio, or an equivalent identity as an axiom?

## Part A — Pure finite combinatorial no-go

Use only the V1 pair-obstruction semantics.

For a minimal pair obstruction F={a,b}:

- no plan signature contains {a,b};
- there exists a private witness plan for dropping a;
- there exists a private witness plan for dropping b.

Enumerate all distinct simple failure-set families on {a,b} satisfying these conditions.

Check:

1. the exact plan/failure hitting duality;
2. whether the duality determines any unique scalar weight x in (0,1);
3. whether swap symmetry a<->b selects x=1/2 under ordinary normalized linear weights.

Primary pure-math endpoint:

> Repair-plan duality plus pair symmetry does **not** by itself force 0.381966... .

## Part B — Extra-axiom localization

Study the weighted maximin family

[
B_c(x)=min(c x,(1-x)^2),qquad c>0.
]

Compute its unique maximizer x_c analytically and numerically.

Primary endpoint:

- x_c varies with c;
- x_1=(3-sqrt5)/2;
- therefore the golden point requires the additional equal-scale nonlinear balance c=1, not duality alone.

No value of c will be fitted to empirical data.

## Part C — Frozen OpenFlights private-witness symmetry audit

Reuse unchanged the PR #78 OpenFlights setup:

- public OpenFlights routes.dat;
- start KEF;
- same 25 targets;
- H=3;
- same five scenarios;
- exact augmented-state BFS;
- minimal obstructions of order 2 and 3.

For every minimal obstruction, compute shortest private-witness path lengths.

Predeclared summaries:

### Pair obstructions
- count;
- fraction with equal private-witness lengths;
- mean absolute witness-length difference;
- exact distribution of unordered witness-length pairs.

### Triple obstructions
- count;
- fraction with all three witness lengths equal;
- mean witness-length range max-min;
- exact distribution of sorted witness-length triples.

Interpretation rule frozen before result:

- equality of witness lengths is at most a concrete symmetry proxy;
- it cannot prove equal probabilistic weighting;
- unequal witness lengths directly refute any claim that equal witness cost is structurally forced in this adapter.

## Guardrails

- Do not change the V1 Core or its frozen PDFs.
- Do not reinterpret H=3 obstructions as infinite-horizon irreversibility.
- Do not fit the old constant to the OpenFlights outputs.
- Do not call 0.381966 a universal INSACERMO constant.
- A negative result is retained.
- Historical novelty is outside this audit.

## Expected scientific decision

PASS means the audit cleanly identifies whether the golden point is:
(a) forced by duality,
(b) forced only after an extra nonlinear/equal-scale axiom,
or (c) empirically suggested by witness-cost symmetry.

The protocol is frozen before execution.
