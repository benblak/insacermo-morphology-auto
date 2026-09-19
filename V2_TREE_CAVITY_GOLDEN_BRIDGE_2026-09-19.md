# INSACERMO V2 — Tree-Cavity Interpretation of the Historical Closure Family

**Date:** 19 September 2026  
**Status:** mathematical derivation followed by mechanical confirmation  
**Frozen V1 artifacts modified:** NO

## 1. Motivation

Earlier INSACERMO work studied the scalar closure family

[
Phi_m=(1-Phi_m)^m.
]

The V2 obstruction program now supplies a natural combinatorial interpretation for this entire family.

## 2. Rooted obstruction tree

Consider a rooted full d-ary tree. Each vertex is a future obligation. Each parent-child edge is a pairwise minimal obstruction, so a safe future bundle is exactly an independent set of the tree.

Give each included future activity (lambda>0). Under the hard-core / weighted independent-set measure, let

[
R_h=rac{Z_h^{mathrm{in}}}{Z_h^{mathrm{out}}}
]

be the root inclusion/exclusion partition-function ratio for a depth-h rooted d-ary tree.

For a leaf:

[
R_0=lambda.
]

The exact recursion is

[
oxed{R_{h+1}=rac{lambda}{(1+R_h)^d}}.
]

The root inclusion probability is

[
p_h=rac{R_h}{1+R_h}.
]

A translation-invariant fixed point therefore satisfies

[
R=rac{lambda}{(1+R)^d}.
]

Writing (p=R/(1+R)), this becomes

[
oxed{p=lambda(1-p)^{d+1}}.
]

Thus at unit activity (lambda=1),

[
oxed{p=(1-p)^{d+1}}.
]

Therefore the historical family (Phi_m=(1-Phi_m)^m) is exactly the unit-activity rooted-tree fixed-point family under the identification

[
oxed{m=d+1}.
]

The old golden case (m=2) is the one-child tree, i.e. a ray/path endpoint:

[
Phi_2=(1-Phi_2)^2=arphi^{-2}.
]

The (m=3) member is the binary-tree fixed point, (m=4) the ternary-tree fixed point, and so on.

## 3. Stability / phase boundary

For the cavity recursion

[
f(R)=lambda(1+R)^{-d},
]

the derivative magnitude at a fixed point is

[
|f'(R_*)|=d,p_*.
]

Hence the translation-invariant fixed point is locally stable under the free-boundary recursion iff

[
oxed{d,p_*<1}.
]

At the stability boundary (p_*=1/d). Substitution into

[
p_*=lambda(1-p_*)^{d+1}
]

gives

[
oxed{lambda_c(d)=rac{d^d}{(d-1)^{d+1}}}
]

for (dge2).

At unit activity:

- d=1,2,3,4 are on the stable side;
- d>=5 are on the unstable side.

Thus the same closure family naturally carries a genuine tree-recursion phase boundary. The equation alone does not determine dynamics; this statement is specific to the independent-set / cavity mechanism.

## 4. Interpretation boundary

This bridge is classical independent-set / hard-core tree mathematics applied to the INSACERMO obstruction semantics. It is **not** a claim that the hard-core model, Fibonacci recurrences, tree recursions, or their phase transition are new.

The candidate INSACERMO significance is narrower:

[
	ext{pairwise obstruction geometry}
	o
	ext{safe-bundle independent-set complex}
	o
	ext{tree cavity recursion}
	o
Phi_m=(1-Phi_m)^m.
]

This gives the old scalar family a precise structural interpretation:

[
oxed{	ext{the exponent }m	ext{ can encode local rooted branching }d=m-1.}
]

It does not make any (Phi_m) universal across arbitrary obstruction geometries.

## 5. Mechanical audit

The companion audit checks:

1. finite-depth d-ary-tree recursions;
2. the fixed-point identity (p=lambda(1-p)^{d+1});
3. the unit-activity values for d=0..9;
4. the exact stability indicator (d p_*);
5. the critical activity (lambda_c(d));
6. stable convergence for d<=4 at lambda=1;
7. parity-separated limiting behavior for d>=5 under free-boundary iteration;
8. path/cycle/star/clique controls to show geometry dependence.
