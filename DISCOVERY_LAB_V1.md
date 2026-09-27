# INSACERMO Discovery Lab V1 — blind finite search

The lab does **not** assume submodularity, matroidality, treewidth, or a target equation.
It generates exact finite actionability systems from primitive capabilities, action requirements,
and admissibility-cover regions, then computes the exact minimum action-cover number m(C).

## Exact exhaustive phase
- worlds: 3
- primitive capabilities: 3
- distinct actions per model: 4
- models enumerated: **367,290**
- distinct exact m-profiles: **228**
- finite local capability squares: **339,036**
- distinct square patterns (a,b,c,d): **13**
- all observed squares obey monotonicity a≥b,c and b,c≥d
- interaction balance eta=b+c-a-d:
  - -1: 306
  - 0: 331,482
  - +1: 7,197
  - +2: 51

So there is **no one-sided universal curvature** even in this small exact universe:
both complementarity and redundancy occur.

## Equation miner
Among primitive integer four-corner linear forms with coefficients of magnitude at most 2,
subject only to:
1. symmetry under swapping u and v,
2. vanishing on a constant square,
3. using all four corners,

there is exactly one candidate up to sign:

    [1, -1, -1, 1]

i.e.

    delta = a - b - c + d

equivalently eta=-delta=b+c-a-d.

This is the classical mixed second difference, not claimed as a new mathematical object.
Its role here is as the simplest local coordinate exposed by the INSACERMO search.

## Deterministic larger stress
Seed: **20260928**
- worlds: 4
- primitive capabilities: 4
- distinct actions per model: 6
- random distinct-action models: **100,000**
- finite local squares: **282,609**
- distinct square patterns: **27**
- eta spectrum: -2 (9), -1 (910), 0 (273,442), +1 (8,091), +2 (157)

Strict synergy (b=a, c=a, d<a) appeared through **two different mechanisms**:
- joint-action activation: **8,124**
- cover-level complementarity with no joint-only action: **5**

The second mechanism matters conceptually: synergy need not be encoded in one explicitly conjunctive
action. It can emerge from the geometry of several separately activated action regions.

## Status
This file reports exact computation plus deterministic stress testing.
The algebraic interaction-band theorem is separately formalized in Lean.
No claim of literature novelty is made here.
