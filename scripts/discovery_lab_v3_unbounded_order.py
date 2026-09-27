#!/usr/bin/env python3
import json

def construction(n):
    """Order-1 local activation family with pure n-way global interaction."""
    odd_all = sum(1 << (2*i+1) for i in range(n))
    actions=[(0, odd_all, "odd_all")]
    actions += [(0, 1 << (2*i), f"single_{i}") for i in range(n)]
    actions += [((1 << i), (1 << (2*i)) | (1 << (2*i+1)), f"pair_{i}") for i in range(n)]
    return actions

def min_cover(world_n, cap_mask, actions):
    full=(1<<world_n)-1
    avail=[cover for req,cover,_ in actions if req & ~cap_mask == 0]
    inf=10**9
    dp=[inf]*(1<<world_n); dp[0]=0
    for cover in avail:
        nxt=dp[:]
        for mask,val in enumerate(dp):
            if val<inf:
                m=mask|cover
                if val+1<nxt[m]:
                    nxt[m]=val+1
        dp=nxt
    return None if dp[full]==inf else dp[full]

def profile(n):
    actions=construction(n)
    return [min_cover(2*n,c,actions) for c in range(1<<n)]

def mobius(prof,n):
    out=[]
    for S in range(1<<n):
        total=0
        T=S
        while True:
            total += (-1 if ((S.bit_count()-T.bit_count())&1) else 1)*prof[T]
            if T==0:
                break
            T=(T-1)&S
        out.append(total)
    return out

def exact_checks(max_n=7):
    rows=[]
    for n in range(1,max_n+1):
        p=profile(n)
        expected=[n+1]*((1<<n)-1)+[n]
        assert p==expected
        mu=mobius(p,n)
        assert mu[0]==n+1
        assert all(x==0 for x in mu[1:-1])
        assert mu[-1]==-1
        assert max(req.bit_count() for req,_,_ in construction(n))<=1
        rows.append({
            "n":n,
            "worlds":2*n,
            "actions":2*n+1,
            "capability_states":1<<n,
            "proper_subset_cost":n+1,
            "full_cost":n,
            "nonzero_mobius":{
                "empty":mu[0],
                "full":mu[-1]
            }
        })
    return rows

def symbolic_certificate():
    return {
      "family":"For every n>=1: worlds e_i,o_i; base actions E_i={e_i}, O={all o_i}; capability i unlocks P_i={e_i,o_i}.",
      "upper_proper":"E_1,...,E_n plus O give a cover of size n+1.",
      "upper_full":"P_1,...,P_n give a cover of size n.",
      "lower_all":"Every e_i is covered only by E_i or P_i, so any cover needs at least one i-indexed action for every i: at least n actions.",
      "lower_proper":"If capability j is missing, P_j is unavailable and o_j is then covered only by O. Thus O is required in addition to the n i-indexed actions: at least n+1.",
      "conclusion":"m_n(C)=n+1 for every proper C, and m_n(N)=n.",
      "mobius":"All nonempty proper Möbius coefficients vanish; the top-order coefficient is -1.",
      "local_activation_order":1,
      "emergent_interaction_order":"n (unbounded)"
    }

def main():
    result={
      "exact_computational_checks":exact_checks(),
      "symbolic_certificate":symbolic_certificate()
    }
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=="__main__":
    main()
