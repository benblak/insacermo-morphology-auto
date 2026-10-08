#!/usr/bin/env python3
from itertools import combinations, product

def powerset(items):
    items=tuple(items)
    for r in range(1,len(items)+1):
        for c in combinations(items,r):
            yield frozenset(c)

def actionable(B, good, caps):
    return any(all(good[x][a] for x in B) for a in caps)

def minobs(worlds, good, caps):
    out=set()
    for B in powerset(worlds):
        if actionable(B,good,caps):
            continue
        if all(actionable(G,good,caps) for G in powerset(B) if G < B):
            out.add(B)
    return out

def exposure_ok(worlds,good,caps,b):
    old=minobs(worlds,good,caps)
    new=minobs(worlds,good,caps|{b})
    Gb=frozenset(x for x in worlds if good[x][b])
    for B in new:
        # Case 1: an old minimal obstruction simply survives.
        if B in old and not B.issubset(Gb):
            continue
        # Case 2: newly exposed = repaired old minimal obstruction + exactly one outsider.
        witnesses=[]
        for H in old:
            if H.issubset(Gb) and H < B:
                outside=B-Gb
                if len(outside)==1 and B == H | outside:
                    witnesses.append(H)
        if not witnesses:
            return False,(old,new,Gb,B)
    return True,None

def exhaustive(n,base_actions=2):
    worlds=tuple(range(n))
    actions=tuple(range(base_actions+1))
    caps=set(range(base_actions)); b=base_actions
    checked=0
    lifts={}
    for bits in product([0,1], repeat=n*len(actions)):
        good={x:{} for x in worlds}; it=iter(bits)
        for x in worlds:
            for a in actions:
                good[x][a]=bool(next(it))
        ok,bad=exposure_ok(worlds,good,caps,b)
        assert ok,bad
        old=minobs(worlds,good,caps); new=minobs(worlds,good,caps|{b})
        Gb=frozenset(x for x in worlds if good[x][b])
        for B in new:
            if B not in old:
                for H in old:
                    if H.issubset(Gb) and H < B and B==H|(B-Gb) and len(B-Gb)==1:
                        lifts[(len(H),len(B))]=lifts.get((len(H),len(B)),0)+1
                        break
        checked+=1
    return checked,lifts

def arbitrary_family(n):
    # Worlds 0..n-1. Let H = 0..n-2.
    # Baseline action a_i (i in H) works everywhere except i.
    # Therefore H itself is the unique minimum obstruction among subsets of H,
    # while every H-minus-one is feasible. New b covers all of H.
    worlds=tuple(range(n))
    H=frozenset(range(n-1))
    actions=[f"a{i}" for i in range(n-1)]+["b"]
    good={x:{} for x in worlds}
    for x in worlds:
        for i in range(n-1):
            good[x][f"a{i}"]=(x!=i)
        good[x]["b"]=(x in H)
    caps=set(actions[:-1])
    old=minobs(worlds,good,caps)
    new=minobs(worlds,good,set(actions))
    return H,old,new

def main():
    total=0
    all_lifts={}
    for n in [1,2,3,4]:
        checked,lifts=exhaustive(n,2)
        total+=checked
        for k,v in lifts.items(): all_lifts[k]=all_lifts.get(k,0)+v
        print("n",n,"systems",checked,"lifts",dict(sorted(lifts.items())))
    # Construction family demonstrates k -> k+1 at arbitrary finite order (sample n=2..8).
    for n in range(2,9):
        H,old,new=arbitrary_family(n)
        assert H in old
        assert frozenset(range(n)) in new
        print("family",n,"old_contains",len(H),"new_contains",n)
    print("ONE_STEP_EXPOSURE_AUDIT_V1: PASS")
    print("total_exhaustive_systems",total)
    print("observed_lifts",dict(sorted(all_lifts.items())))
    print("law","one added capability: each newly minimal obstruction is repaired old minimal H plus exactly one outsider")

if __name__=="__main__":
    main()
