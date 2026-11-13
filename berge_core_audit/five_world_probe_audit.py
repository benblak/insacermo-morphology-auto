"""Independent exhaustive model check. Five worlds, four fixed binary probes, no lies.
These are stylized worlds/actions, not empirical OpenFlights performance figures.
"""
from itertools import combinations

W = frozenset(range(5))
ACTIONS = tuple(frozenset((0, i)) for i in range(1, 5))
PROBES = tuple(range(1, 5))

def subsets():
    for k in range(6):
        for xs in combinations(W, k):
            yield frozenset(xs)

ALL = tuple(subsets())

def feasible(B):
    return any(B <= a for a in ACTIONS)

def minimal_obstruction(B):
    return not feasible(B) and all(feasible(S) for S in ALL if S < B)

def signature(w, qs):
    return tuple(w == i for i in qs)

def after_feasible(B, qs):
    return all(any(frozenset(w for w in B if signature(w, qs) == sig) <= a
                   for a in ACTIONS)
               for sig in (signature(w, qs) for w in B)) if B else True

def after_minimal(B, qs):
    return not after_feasible(B, qs) and all(after_feasible(S, qs)
                                            for S in ALL if S < B)

old = frozenset(B for B in ALL if minimal_obstruction(B))
assert old == frozenset(frozenset((i, j)) for i, j in combinations(range(1, 5), 2))

checks = 0
for qs_len in range(5):
    for qs in combinations(PROBES, qs_len):
        after = frozenset(B for B in ALL if after_minimal(B, qs))
        predicted = frozenset(B for B in old
                              if len({signature(w, qs) for w in B}) == 1)
        assert after == predicted, (qs, after, predicted)
        # full contract must be feasible exactly when all old critical
        # obstructions are split, as demonstrated by the Lean theorem.
        full_feasible = after_feasible(W, qs)
        assert full_feasible == (not predicted)
        checks += len(ALL)
        print(f"probes={qs}, surviving_minimal={len(after)}, "
              f"guaranteed_action={full_feasible}")
        assert len(after) == {0:6, 1:3, 2:1, 3:0, 4:0}[qs_len]

assert checks == 512  # 16 probe subsets x 32 world subsets
print(f"PASS: {checks} exact checks; min reliable probes = 3")
