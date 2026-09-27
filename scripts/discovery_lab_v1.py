#!/usr/bin/env python3
from collections import Counter
from itertools import combinations
from math import gcd
import json
import random

def min_cover(world_n, cap_mask, actions):
    full=(1<<world_n)-1
    avail=[cover for req,cover in actions if req & ~cap_mask == 0]
    if not avail: return None
    big=10**9
    dp=[big]*(1<<world_n); dp[0]=0
    for cover in avail:
        nxt=dp[:]
        for mask,val in enumerate(dp):
            if val<big:
                m=mask|cover
                nxt[m]=min(nxt[m],val+1)
        dp=nxt
    return None if dp[full]==big else dp[full]

def profile(world_n,cap_n,actions):
    return tuple(min_cover(world_n,c,actions) for c in range(1<<cap_n))

def finite_squares(cap_n,prof):
    for base in range(1<<cap_n):
        absent=[i for i in range(cap_n) if not (base>>i)&1]
        for u,v in combinations(absent,2):
            bu=base|(1<<u); bv=base|(1<<v); buv=bu|(1<<v)
            vals=(prof[base],prof[bu],prof[bv],prof[buv])
            if all(x is not None for x in vals):
                yield base,u,v,*vals

def joint_activation(base,u,v,actions):
    bu=base|(1<<u); bv=base|(1<<v); buv=bu|(1<<v)
    return any(req & ~buv == 0 and req & ~bu != 0 and req & ~bv != 0
               for req,_ in actions)

def primitive_balanced_symmetric_forms(max_coeff=2):
    forms=set(); rng=range(-max_coeff,max_coeff+1)
    for a in rng:
      for b in rng:
       for c in rng:
        for d in rng:
         x=(a,b,c,d)
         if x==(0,0,0,0): continue
         g=0
         for z in x: g=gcd(g,abs(z))
         if g>1: x=tuple(z//g for z in x)
         first=next((z for z in x if z),0)
         if first<0: x=tuple(-z for z in x)
         if x[1]!=x[2] or sum(x)!=0 or 0 in x: continue
         forms.add(x)
    return sorted(forms)

def exhaustive_small():
    W,K,A=3,3,4
    types=[(r,c) for r in range(1<<K) for c in range(1,1<<W)]
    patterns=Counter(); eta=Counter(); profiles=set()
    models=squares=finite_models=0
    for ids in combinations(range(len(types)),A):
        actions=tuple(types[i] for i in ids); models+=1
        p=profile(W,K,actions); profiles.add(p); had=False
        for _base,_u,_v,a,b,c,d in finite_squares(K,p):
            had=True; squares+=1
            patterns[(a,b,c,d)]+=1
            eta[b+c-a-d]+=1
        finite_models+=int(had)
    return {
      "models":models,"finite_models":finite_models,
      "distinct_profiles":len(profiles),"finite_squares":squares,
      "distinct_patterns":len(patterns),
      "eta":dict(sorted(eta.items())),
      "antitone":all(a>=b and a>=c and b>=d and c>=d for a,b,c,d in patterns)
    }

def deterministic_stress(seed=20260928,n=100000):
    W,K,A=4,4,6
    types=[(r,c) for r in range(1<<K) for c in range(1,1<<W)]
    rng=random.Random(seed)
    patterns=Counter(); eta=Counter(); mechanisms=Counter(); squares=0
    witness_cover_only=None
    for _ in range(n):
        actions=tuple(rng.sample(types,A))
        p=profile(W,K,actions)
        for base,u,v,a,b,c,d in finite_squares(K,p):
            squares+=1; patterns[(a,b,c,d)]+=1
            q=b+c-a-d; eta[q]+=1
            if b==a and c==a and d<a:
                mech="activation" if joint_activation(base,u,v,actions) else "cover_only"
                mechanisms[mech]+=1
                if mech=="cover_only" and witness_cover_only is None:
                    witness_cover_only={"base":base,"u":u,"v":v,"square":[a,b,c,d],
                        "actions":[list(x) for x in actions]}
    return {"models":n,"finite_squares":squares,"distinct_patterns":len(patterns),
            "eta":dict(sorted(eta.items())),"strict_synergy_mechanisms":dict(sorted(mechanisms.items())),
            "cover_only_witness":witness_cover_only}

def main():
    exact=exhaustive_small()
    stress=deterministic_stress()
    forms=primitive_balanced_symmetric_forms()
    result={"equation_candidates":[list(x) for x in forms],"exact":exact,"stress":stress}

    # Reproducibility locks. A change means either code/model semantics changed or results changed.
    assert forms==[(1,-1,-1,1)]
    assert exact=={
      "models":367290,"finite_models":155124,"distinct_profiles":228,
      "finite_squares":339036,"distinct_patterns":13,
      "eta":{-1:306,0:331482,1:7197,2:51},"antitone":True}
    assert stress["models"]==100000
    assert stress["finite_squares"]==282609
    assert stress["distinct_patterns"]==27
    assert stress["eta"]=={-2:9,-1:910,0:273442,1:8091,2:157}
    assert stress["strict_synergy_mechanisms"]=={"activation":8124,"cover_only":5}
    assert stress["cover_only_witness"] is not None
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=="__main__":
    main()
