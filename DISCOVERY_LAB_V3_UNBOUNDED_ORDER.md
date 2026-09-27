# INSACERMO Discovery Lab V3 — unbounded emergent order

## Result

The V2 three-way witness is not an isolated accident. It extends to an explicit family for **every**
integer n >= 1.

For n primitive capabilities c_1,...,c_n, create 2n worlds

    e_1,o_1,...,e_n,o_n.

Use the following actions.

Unconditional:
- E_i covers only e_i, for every i;
- O covers every odd world o_1,...,o_n.

Locally unlocked:
- capability c_i unlocks P_i, which covers exactly {e_i,o_i}.

Every action therefore has activation requirement of cardinality at most **1**.

Let C be the currently available capability subset and let m_n(C) be the exact minimum number of
available actions required to cover all 2n worlds.

Then

    m_n(C) = n+1  if C is a proper subset of {c_1,...,c_n},
    m_n(C) = n    if C contains all n capabilities.

### Proof

There is always a cover of size n+1: use E_1,...,E_n and O.

If all capabilities are present, P_1,...,P_n cover all worlds with n actions.

For the lower bound, each even world e_i can only be covered by E_i or P_i. Therefore every cover
needs at least one i-indexed action for every i, hence at least n actions.

If C is proper, choose a missing capability c_j. Then P_j is unavailable. The odd world o_j can now
only be covered by O. Since O covers no even world, it is required in addition to the n actions
needed for the even worlds. Therefore every proper C needs at least n+1 actions.

Hence the formula is exact.

## Pure n-way interaction

The cost profile is constant on every proper subset and drops only at the full capability set:

    m_n(C)=n+1 for C != N,
    m_n(N)=n.

Consequently, under the ordinary Möbius transform of the capability-set function:
- every nonempty coefficient of order < n is exactly 0;
- the unique top-order coefficient is -1.

Thus the model contains a **pure n-way interaction** even though its local activation language has
order only 1.

This gives the structural separation

    local activation order = 1,
    emergent future-preservation interaction order = n.

Since n is arbitrary, the gap is unbounded.

## Exact computational cross-check

The repository script checks the actual minimum-set-cover problem, not merely the closed formula,
for every capability subset for n=1,...,7. All 254 nontrivial capability states across the family
match the theorem exactly. The Möbius spectrum is also checked directly.

## Literature boundary

The Möbius transform, Harsanyi dividends, unanimity games, and arbitrary-order interaction indices
are classical. In fact, the resulting capability-value profile is algebraically a constant plus a
signed unanimity game.

The point requiring novelty caution is therefore **not** "higher-order interactions exist".
The specific INSACERMO statement is the realization mechanism:

> a minimum future-preservation cover can exhibit a pure interaction of arbitrary order n even when
> every primitive action is activated by at most one capability.

This report does not claim that this exact realization theorem is absent from all prior literature.
It is the next target for formal literature comparison and kernel formalization.

## Status

- explicit construction: proved by elementary combinatorial argument;
- exact computation: checked for n=1,...,7;
- current general Lean operational proof: not yet completed;
- existing Discovery Dialect pairwise kernel remains green and axiom-audited.
