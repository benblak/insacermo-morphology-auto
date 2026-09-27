#!/usr/bin/env python3
from itertools import combinations
from collections import Counter
import json, random

def min_cover(world_n, cap_mask, actions):
    full=(1<<world_n)-1
    avail=[cover for req,cover in actions if req & ~cap_mask == 0]
    if not avail:
        return None
    inf=10**9
    dp=[inf]*(1<<world_n); dp[0]=0
    for cover in avail:
        nxt=dp[:]
        for mask,val in enumerate(dp):
            if val<inf:
                m=mask|cover
                nxt[m]=min(nxt[m],val+1)
        dp=nxt
    return None if dp[full]==inf else dp[full]

def profile(world_n,cap_n,actions):
    return tuple(min_cover(world_n,c,actions) for c in range(1<<cap_n))

def mobius_full(prof,cap_n):
    S=(1<<cap_n)-1
    total=0
    T=S
    while True:
        v=prof[T]
        if v is None:
            return None
        sign=-1 if ((cap_n-T.bit_count())%2) else 1
        total += sign*v
        if T==0:
            break
        T=(T-1)&S
    return total

def exhaustive_singleton_requirements():
    W,K,A=3,3,5
    reqs=[m for m in range(1<<K) if m.bit_count()<=1]
    types=[(r,c) for r in reqs for c in range(1,1<<W)]
    coeff=Counter(); models=finite=0
    witness=None
    for ids in combinations(range(len(types)),A):
        actions=tuple(types[i] for i in ids)
        models+=1
        p=profile(W,K,actions)
        mu=mobius_full(p,K)
        if mu is None:
            continue
        finite+=1; coeff[mu]+=1
        if mu != 0 and witness is None:
            witness={"actions":[list(x) for x in actions],
                     "profile":list(p),"third_order":mu}
    return {"models":models,"finite_profiles":finite,
            "third_order_spectrum":dict(sorted(coeff.items())),
            "first_nonzero_witness":witness}

def pure_three_way_witness():
    # Six worlds split into three pairs.
    # Base actions: even singleton worlds + one action covering all odd worlds.
    # Each primitive capability unlocks exactly one pair-cover action.
    # No action requires two or three capabilities.
    W,K=6,3
    actions=(
        (0,16),  # world 4
        (0,4),   # world 2
        (0,1),   # world 0
        (0,42),  # worlds 1,3,5
        (1,3),   # capability u -> worlds 0,1
        (2,12),  # capability v -> worlds 2,3
        (4,48),  # capability w -> worlds 4,5
    )
    p=profile(W,K,actions)
    assert p==(4,4,4,4,4,4,4,3)
    assert all(req.bit_count()<=1 for req,_ in actions)
    return {"actions":[list(x) for x in actions],"profile":list(p),
            "third_order":mobius_full(p,K),
            "interpretation":"every proper capability subset needs 4 actions; all 3 capabilities need 3"}

def deterministic_stress(seed=20260928,n=100000):
    W,K,A=4,3,7
    rng=random.Random(seed)
    reqs=[m for m in range(1<<K) if m.bit_count()<=1]
    types=[(r,c) for r in reqs for c in range(1,1<<W)]
    coeff=Counter(); finite=0
    pos=neg=None
    for i in range(n):
        actions=tuple(rng.sample(types,A))
        p=profile(W,K,actions)
        mu=mobius_full(p,K)
        if mu is None:
            continue
        finite+=1; coeff[mu]+=1
        if mu>0 and pos is None:
            pos={"draw":i,"actions":[list(x) for x in actions],"profile":list(p),"third_order":mu}
        if mu<0 and neg is None:
            neg={"draw":i,"actions":[list(x) for x in actions],"profile":list(p),"third_order":mu}
    return {"seed":seed,"models":n,"finite_profiles":finite,
            "third_order_spectrum":dict(sorted(coeff.items())),
            "positive_witness":pos,"negative_witness":neg}

def main():
    exact=exhaustive_singleton_requirements()
    pure=pure_three_way_witness()
    stress=deterministic_stress()
    assert exact["models"]==98280
    assert exact["finite_profiles"]==29421
    assert exact["third_order_spectrum"]=={-1:6,0:29415}
    assert pure["profile"]==[4,4,4,4,4,4,4,3]
    assert pure["third_order"]==-1
    assert stress["finite_profiles"]==32138
    assert stress["third_order_spectrum"]=={-2:1,-1:72,0:32058,1:7}
    print(json.dumps({"exact":exact,"pure_three_way":pure,"stress":stress},
                     indent=2,sort_keys=True))

if __name__=="__main__":
    main()
