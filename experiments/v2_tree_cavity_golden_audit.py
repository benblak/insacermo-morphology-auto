import math
from functools import lru_cache

def fixed_point_p(d, lam=1.0):
    # unique positive solution of p = lam (1-p)^(d+1)
    lo, hi = 0.0, 1.0
    for _ in range(300):
        m = (lo+hi)/2
        f = m - lam*(1-m)**(d+1)
        if f > 0: hi = m
        else: lo = m
    return (lo+hi)/2

def iterate_R(d, lam=1.0, h=300):
    R = lam
    seq=[]
    for _ in range(h+1):
        p = R/(1+R)
        seq.append(p)
        R = lam/(1+R)**d
    return seq

def lambda_c(d):
    if d < 2:
        return math.inf
    return (d**d)/((d-1)**(d+1))

print("INSACERMO_V2_TREE_CAVITY_GOLDEN_AUDIT")
print("STATUS","DERIVED_THEN_CONFIRMED")

for d in range(0,10):
    p = fixed_point_p(d,1.0)
    residual = p - (1-p)**(d+1)
    stab = d*p
    print("UNIT_ACTIVITY","D",d,"M",d+1,"P",f"{p:.15f}",
          "RES",f"{residual:.3e}","D_TIMES_P",f"{stab:.15f}",
          "LOCAL_STABLE", "YES" if stab < 1 else "NO")

gold=(3-math.sqrt(5))/2
p1=fixed_point_p(1,1.0)
print("GOLD_CASE","P",f"{p1:.15f}","TARGET",f"{gold:.15f}","ERR",f"{p1-gold:.3e}")
assert abs(p1-gold)<1e-14

for d in range(2,10):
    lc=lambda_c(d)
    pcrit=1/d
    res = pcrit - lc*(1-pcrit)**(d+1)
    print("CRITICAL","D",d,"LAMBDA_C",f"{lc:.15f}","P_CRIT",f"{pcrit:.15f}","RES",f"{res:.3e}")

for d in range(1,9):
    seq=iterate_R(d,1.0,400)
    tail=seq[-6:]
    print("FREE_BOUNDARY","D",d,"TAIL",",".join(f"{x:.15f}" for x in tail),
          "RANGE",f"{max(tail)-min(tail):.15e}")

# Geometry controls: uniform independent-set marginal on finite graphs
def independent_set_counts(n, edges):
    adj=[0]*n
    for a,b in edges:
        adj[a] |= 1<<b
        adj[b] |= 1<<a
    full=(1<<n)-1
    @lru_cache(None)
    def Z(mask):
        if mask==0: return 1
        v=(mask & -mask).bit_length()-1
        without=mask & ~(1<<v)
        return Z(without) + Z(without & ~adj[v])
    total=Z(full)
    inc=[]
    for v in range(n):
        inc.append(Z(full & ~(1<<v) & ~adj[v])/total)
    return total,inc

for n in [4,8,12]:
    path=[(i,i+1) for i in range(n-1)]
    cyc=path+[(n-1,0)]
    star=[(0,i) for i in range(1,n)]
    clique=[(i,j) for i in range(n) for j in range(i+1,n)]
    for name,edges in [("PATH",path),("CYCLE",cyc),("STAR",star),("CLIQUE",clique)]:
        total,inc=independent_set_counts(n,edges)
        print("GEOM",name,"N",n,"Z",total,"MEAN",f"{sum(inc)/n:.15f}",
              "MIN",f"{min(inc):.15f}","MAX",f"{max(inc):.15f}")
print("RESULT","COMPLETE")
