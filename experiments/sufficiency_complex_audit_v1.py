#!/usr/bin/env python3
from itertools import combinations, product

def powerset(items):
    items=list(items)
    for r in range(len(items)+1):
        for c in combinations(items,r):
            yield frozenset(c)

def actionable(B, good, caps):
    return any(all(good[x][a] for x in B) for a in caps)

def obstructions(worlds, good, caps):
    obs=[]
    for B in powerset(worlds):
        if not B: 
            continue
        if actionable(B,good,caps):
            continue
        if all(actionable(G,good,caps) for G in powerset(B) if G and G!=B):
            obs.append(B)
    return set(obs)

def surviving_old_obstructions(worlds, good, caps, b):
    old=[B for B in powerset(worlds) if B and not actionable(B,good,caps)]
    gb={x for x in worlds if good[x][b]}
    surv=[B for B in old if not B.issubset(gb)]
    mins=[]
    for B in surv:
        if not any(G < B for G in surv):
            mins.append(B)
    return set(mins)

def exhaustive():
    checked=0
    # 3 worlds, 3 actions; first 2 baseline, third repair.
    worlds=tuple(range(3)); actions=tuple(range(3)); caps={0,1}; b=2
    for bits in product([0,1], repeat=len(worlds)*len(actions)):
        good={x:{} for x in worlds}
        it=iter(bits)
        for x in worlds:
            for a in actions:
                good[x][a]=bool(next(it))
        lhs=obstructions(worlds,good,caps|{b})
        rhs=surviving_old_obstructions(worlds,good,caps,b)
        assert lhs==rhs, (good,lhs,rhs)
        checked+=1
    return checked

def reveal_triple_example():
    # Baseline:
    # a covers 0,1 ; c covers 1,2 ; no action covers all three.
    # Pair {0,2} is the only pair obstruction.
    # Add b covering {0,2}; then every pair is actionable, but {0,1,2} is not.
    worlds=(0,1,2)
    good={
      0:{"a":True, "c":False, "b":True},
      1:{"a":True, "c":True,  "b":False},
      2:{"a":False,"c":True,  "b":True},
    }
    before=obstructions(worlds,good,{"a","c"})
    after=obstructions(worlds,good,{"a","c","b"})
    assert before=={frozenset({0,2})}
    assert after=={frozenset({0,1,2})}
    return before,after

def main():
    checked=exhaustive()
    before,after=reveal_triple_example()
    print("SUFFICIENCY_COMPLEX_AUDIT_V1: PASS")
    print("exhaustive_systems",checked)
    print("before_minimal_obstructions",[sorted(x) for x in sorted(before,key=lambda z:(len(z),sorted(z)))])
    print("after_minimal_obstructions",[sorted(x) for x in sorted(after,key=lambda z:(len(z),sorted(z)))])
    print("interpretation","pair obstruction removed; pre-existing triple impossibility becomes minimal")

if __name__=="__main__":
    main()
