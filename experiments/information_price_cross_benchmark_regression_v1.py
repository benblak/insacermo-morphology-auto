#!/usr/bin/env python3
import json
import numpy as np
from functools import lru_cache
from sklearn.datasets import load_wine, load_breast_cancer, load_digits

def quartile(X):
    qs=np.quantile(X,[.25,.5,.75],axis=0)
    return np.column_stack([np.digitize(X[:,j],qs[:,j],right=False) for j in range(X.shape[1])]).astype(np.uint8)

def exact_solve(Xq,y,names,max_depth):
    n=len(y); full=(1<<n)-1
    actions=sorted(set(map(int,y)))
    am=[]
    for a in actions:
        m=0
        for i,v in enumerate(y):
            if int(v)==a:m|=1<<i
        am.append(m)
    out=[]
    for j in range(Xq.shape[1]):
        mp={}
        for i,o in enumerate(Xq[:,j]):
            mp[int(o)]=mp.get(int(o),0)|(1<<i)
        out.append(tuple(mp.values()))
    @lru_cache(None)
    def terminal(mask):
        return any(mask & ~g == 0 for g in am)
    @lru_cache(None)
    def parts(mask,j):
        return tuple(q for om in out[j] if (q:=mask&om))
    @lru_cache(None)
    def ordered(mask):
        z=[]
        for j in range(len(names)):
            ps=parts(mask,j)
            if len(ps)<=1: continue
            z.append((max(p.bit_count() for p in ps),-len(ps),str(names[j]),j))
        z.sort()
        return tuple(j for *_,j in z)
    @lru_cache(None)
    def feasible(mask,d):
        if terminal(mask): return True
        if d<=0:return False
        for j in ordered(mask):
            if all(feasible(c,d-1) for c in sorted(parts(mask,j),key=int.bit_count,reverse=True)):
                return True
        return False
    @lru_cache(None)
    def solve(mask,d):
        if terminal(mask): return 0,None
        best=None
        for j in ordered(mask):
            ps=parts(mask,j)
            if any(not feasible(c,d-1) for c in ps): continue
            total=mask.bit_count()
            ok=True
            for c in ps:
                sc,_=solve(c,d-1)
                if sc is None: ok=False; break
                total+=sc
            if ok and (best is None or total<best[0] or (total==best[0] and str(names[j])<str(names[best[1]]))):
                best=(total,j)
        return best if best is not None else (None,None)
    for d in range(max_depth+1):
        if feasible(full,d):
            total,j=solve(full,d)
            return {"depth":d,"root":str(names[j]),"total":int(total)}
    return {"verdict":"REFUSE"}

def digit_root_admissible(X,y,root,depth):
    n=len(y); full=(1<<n)-1
    actions=sorted(set(map(int,y)))
    am=[]
    for a in actions:
        m=0
        for i,v in enumerate(y):
            if int(v)==a:m|=1<<i
        am.append(m)
    out=[]
    for j in range(X.shape[1]):
        mp={}
        for i,o in enumerate(X[:,j]):
            mp[int(o)]=mp.get(int(o),0)|(1<<i)
        out.append(tuple(mp.values()))
    @lru_cache(None)
    def terminal(mask): return any(mask & ~g == 0 for g in am)
    @lru_cache(None)
    def parts(mask,j): return tuple(q for om in out[j] if (q:=mask&om))
    @lru_cache(None)
    def feasible(mask,d):
        if terminal(mask):return True
        if d<=0:return False
        for j in range(X.shape[1]):
            ps=parts(mask,j)
            if len(ps)<=1:continue
            if all(feasible(c,d-1) for c in sorted(ps,key=int.bit_count,reverse=True)):return True
        return False
    return all(feasible(c,depth-1) for c in parts(full,root)), feasible(full,depth), feasible(full,depth-1)

def main():
    out={"status":"SUCCESS","benchmarks":{}}
    w=load_wine(); wr=exact_solve(quartile(w.data),w.target,list(w.feature_names),3)
    out["benchmarks"]["wine"]=wr
    assert wr=={"depth":3,"root":"flavanoids","total":412}

    b=load_breast_cancer(); br=exact_solve(quartile(b.data),b.target,list(b.feature_names),4)
    out["benchmarks"]["wdbc"]=br
    assert br=={"depth":4,"root":"worst perimeter","total":1310}

    d=load_digits(); X=d.data.astype(np.uint8)
    # Historical naming is zero-based: pixel_r1_c5 = flat index 13.
    root_index=13
    root_ok,d4,d3=digit_root_admissible(X,d.target,root_index,4)
    dr={"depth4_feasible":bool(d4),"depth3_feasible":bool(d3),"historical_root":"pixel_r1_c5","historical_root_index":root_index,"historical_root_admissible_at_depth4":bool(root_ok),"historical_total_cost_documented_not_recomputed":5384}
    out["benchmarks"]["digits"]=dr
    assert d4 and not d3 and root_ok

    with open("INFORMATION_PRICE_CROSS_BENCHMARK_REGRESSION_V1.json","w") as f: json.dump(out,f,indent=2,sort_keys=True)
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=="__main__": main()
