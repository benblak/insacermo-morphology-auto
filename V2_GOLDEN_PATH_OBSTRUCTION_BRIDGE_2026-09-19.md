# INSACERMO V2 — Golden Point from a Path of Pairwise Obstructions

**Date:** 19 September 2026  
**Status:** derived mathematical bridge + mechanical audit  
**Preregistration status:** NOT preregistered. The mechanism was derived analytically before this audit. The audit is confirmatory.

## 1. Core-derived setup

Take a finite family of future obligations indexed 1,...,n.

Assume the only minimal obstructions are adjacent pairs:

[
{1,2},{2,3},ldots,{n-1,n}.
]

Then feasible future bundles are exactly subsets containing no adjacent pair, i.e. independent sets of the path graph P_n.

This is a special case of the V1 obstruction-complex semantics: feasible bundles avoid every minimal obstruction hyperedge.

## 2. Uniform safe-bundle counting

Let A_n be the number of feasible bundles on P_n.

Then

[
A_0=1,quad A_1=2,quad A_n=A_{n-1}+A_{n-2}.
]

Therefore A_n=F_{n+2} for the Fibonacci convention F_0=0,F_1=1.

Among all feasible bundles chosen uniformly:

- bundles containing endpoint n are in bijection with feasible bundles on P_{n-2};
- hence endpoint-inclusion probability is

[
p_n=rac{A_{n-2}}{A_n}=rac{F_n}{F_{n+2}}.
]

Thus

[
lim_{n	oinfty}p_n=arphi^{-2}=rac{3-sqrt5}{2}.
]

The endpoint-omission probability is

[
q_n=rac{A_{n-1}}{A_n}	oarphi^{-1}.
]

Hence at the limit

[
p=q^2,qquad p+q=1,
]

so

[
oxed{p=(1-p)^2}.
]

The historical INSACERMO golden closure therefore reappears without being imposed as the starting equation.

## 3. Weighted generalization

Give each feasible bundle S weight lambda^{|S|}, lambda>0.

Let Z_n(lambda) be the weighted safe-bundle partition function. Then

[
Z_n=Z_{n-1}+lambda Z_{n-2}.
]

The asymptotic endpoint-inclusion probability p(lambda) satisfies

[
oxed{p=lambda(1-p)^2}.
]

Therefore the historical equation

[
p=(1-p)^2
]

is exactly the unit-activity case lambda=1, i.e. equal weight per included future in the safe-bundle ensemble.

This does NOT make 0.381966 universal. It identifies a precise natural model in which it is intrinsic.

## 4. Interpretation boundary

The bridge requires all of the following:

1. pairwise obstruction geometry forming a path;
2. safe bundles counted through the independent-set complex;
3. uniform bundle weighting for lambda=1;
4. asymptotic chain length.

Changing the graph, weighting law, or finite size generally changes the value.

Therefore:

[
oxed{	ext{Core obstruction geometry + path + uniform safe-bundle measure}
Rightarrow arphi^{-2}}
]

but

[
oxed{	ext{Core V1 alone}
otRightarrow arphi^{-2}.}
]

## 5. Mechanical audit

The companion script checks exact integer recurrences through n=1000, verifies the endpoint-count bijection numerically, verifies convergence, and checks the weighted recurrence for several rational activities.
