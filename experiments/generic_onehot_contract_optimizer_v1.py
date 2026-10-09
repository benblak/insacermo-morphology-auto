#!/usr/bin/env python3
"""Generic exact optimizer for ONE-HOT observations and deterministic actions.

Finite declared worlds W. Each world has a unique one-hot probe p_w which
returns true exactly in that world. A global FIXED set of probes P is sound
iff any two worlds that agree on P require the same action.

No graph concepts, connectivity routines, or domain-specific feature selection.
"""
from collections import defaultdict
from dataclasses import dataclass
from itertools import combinations
import random

@dataclass(frozen=True)
class Result:
    probes: tuple
    minimum_count: int
    omitted_action: object
    largest_action_class: int
    world_count: int
    distinct_actions: int

def solve(worlds, actions):
    """Return a cardinality-minimal fixed per-world one-hot probe set.

    worlds: finite sequence of unique/hashable world names. The perfect
    individual probe of a world is named by that same world.
    actions: sequence of hashable required decisions, same ordering.
    """
    worlds=tuple(worlds);actions=tuple(actions)
    if len(worlds)!=len(actions):
        raise ValueError("WORLD_ACTION_LENGTH_MISMATCH")
    if len(worlds)!=len(set(worlds)):
        raise ValueError("DUPLICATE_WORLD")
    if not worlds:
        return Result((),0,None,0,0,0)
    classes=defaultdict(list)
    for w,a in zip(worlds,actions):
        classes[a].append(w)
    omitted=max(classes,key=lambda a:len(classes[a]))
    probes=tuple(w for w,a in zip(worlds,actions) if a!=omitted)
    ans=Result(probes,len(probes),omitted,len(classes[omitted]),
               len(worlds),len(classes))
    assert ans.minimum_count==len(worlds)-ans.largest_action_class
    assert is_sufficient(worlds,actions,ans.probes)
    return ans

def is_sufficient(worlds,actions,probes):
    """Independent signature check, O(number of worlds).

    All probed worlds have distinct one-hot signatures. Unprobed worlds
    have exactly the all-zero signature and must have an identical action.
    """
    P=set(probes)
    if len(P)!=len(tuple(probes)) or not P.issubset(set(worlds)):
        return False
    unprobed_action=set(a for w,a in zip(worlds,actions) if w not in P)
    return len(unprobed_action)<=1

def verify_lower_bound(worlds, actions, answer):
    """Finite certificate of global fixed-probe optimality for one-hot probes.

    Every sound probe set leaves at most one required-action class unprobed.
    The largest class size is M. Thus at least |W|-M probes are forced.
    """
    assert is_sufficient(worlds,actions,answer.probes)
    cls=defaultdict(int)
    for a in actions:cls[a]+=1
    maximum=max(cls.values(),default=0)
    assert answer.minimum_count==len(worlds)-maximum
    assert answer.largest_action_class==maximum
    return True

def exhaustive_selftest():
    rng=random.Random(20261009);checks=0
    for n in range(1,10):
        for _ in range(80):
            worlds=tuple(range(n))
            actions=tuple(rng.randrange(5) for _ in worlds)
            ans=solve(worlds,actions)
            oracle=min((len(c) for k in range(n+1)
                        for c in combinations(worlds,k)
                        if is_sufficient(worlds,actions,c)),default=0)
            assert ans.minimum_count==oracle,(n,actions,ans,oracle)
            assert verify_lower_bound(worlds,actions,ans)
            checks+=1
    return checks

if __name__=="__main__":
    print({"exhaustive_onehot_cases":"PASS","tests":exhaustive_selftest()})
