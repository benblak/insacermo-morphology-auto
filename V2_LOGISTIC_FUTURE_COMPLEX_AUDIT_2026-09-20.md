# INSACERMO V2 — Logistic-Map Future-Complex Audit

**Date:** 20 September 2026  
**Status:** exploratory construction followed by deterministic mechanical audit  
**Preregistration status:** NOT preregistered. The future-predicate encoding and 12-step complex were explored before this file was frozen. The audit is therefore confirmatory/reproducibility evidence, not a blind discovery claim.  
**Frozen Core V1 artifacts modified:** NO

## 1. Dynamical system

The world generator is the classical logistic map

[
x_{t+1}=r x_t(1-x_t),qquad x_tin[0,1].
]

The engine is not given any known bifurcation locations.

Parameter sweep:

[
rin[2.8,4.0]
]

on the fixed grid step (0.002).

For every (r):

- 1024 deterministic initial seeds ((i+1/2)/1024);
- 1500 burn-in iterations;
- then a 12-step future window.

## 2. Contract-relative future predicates

For offsets (j=1,ldots,12), define the future predicate

[
q_j: x_{t+j}ge 1/2.
]

Each post-burn orbit segment therefore induces a 12-bit future signature

[
S(x,r)={j:q_j	ext{ holds}}.
]

A finite bundle (Fsubseteq{q_1,ldots,q_{12}}) is declared feasible at parameter (r) iff at least one sampled orbit signature contains (F).

Thus the family of feasible bundles is a finite simplicial complex (the downward closure of the observed maximal signatures). Minimal non-faces are the exact sampled future obstructions for this declared contract/ensemble.

This is a deterministic finite adapter. It does not claim exhaustive continuum coverage of all initial conditions.

## 3. Frozen outputs per r

The audit records:

- number of distinct 12-bit signatures;
- number of maximal signatures/facets;
- number of feasible bundles out of (2^{12}=4096);
- exact count of minimal obstructions by rank 1..12;
- minimum obstruction rank when one exists;
- maximum obstruction rank;
- Shannon entropy of the empirical signature distribution.

## 4. Deterministic image

The renderer produces an SVG directly from the computed outputs.

No image-generation model is involved.

Image semantics:

- horizontal coordinate = parameter (r);
- vertical coordinate = obstruction rank (k=1,ldots,12);
- each cell intensity = (log(1+N_k(r))), where (N_k(r)) is the exact sampled number of minimal obstructions of rank (k);
- a lower trace gives the number of maximal future signatures;
- known classical bifurcation values are added **only after computation as reference lines**, never used to choose or alter the engine outputs.

Reference values shown:

- first period doubling: (r=3);
- second period doubling: (r=1+sqrt6approx3.449489743);
- later period doublings: (rapprox3.544090359), (3.564407266);
- Feigenbaum accumulation point: (rapprox3.569945672);
- onset of the classical period-3 window: (r=1+sqrt8approx3.828427125).

## 5. Claim boundary

A structural change in this image means the declared 12-step future-compatibility complex changed under this finite sampled contract.

It is not automatically a theorem about chaos, Lyapunov exponents, or the continuum logistic map.

The scientific test is narrower:

> Does a contract-relative obstruction geometry, computed without being told the classical transition locations, reorganize near known dynamical regime changes?

Negative or mismatching results are retained.
