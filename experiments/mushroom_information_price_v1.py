#!/usr/bin/env python3
import csv, hashlib, json, urllib.request, os, time
from collections import Counter
from functools import lru_cache

URL="https://archive.ics.uci.edu/ml/machine-learning-databases/mushroom/agaricus-lepiota.data"
PATH="mushroom.data"
NAMES=[
"cap-shape","cap-surface","cap-color","bruises","odor","gill-attachment","gill-spacing","gill-size",
"gill-color","stalk-shape","stalk-root","stalk-surface-above-ring","stalk-surface-below-ring",
"stalk-color-above-ring","stalk-color-below-ring","veil-type","veil-color","ring-number","ring-type",
"spore-print-color","population","habitat"
]

def load():
    if not os.path.exists(PATH):
        urllib.request.urlretrieve(URL,PATH)
    raw=open(PATH,"rb").read()
    sha=hashlib.sha256(raw).hexdigest()
    rows=[]
    for row in csv.reader(raw.decode("ascii").splitlines()):
        if not row: continue
        assert len(row)==23
        rows.append(row)
    y=[r[0] for r in rows]
    X=[r[1:] for r in rows]
    assert len(X)==8124
    return X,y,sha

def build_masks(X,y):
    n=len(y); p=len(X[0]); allmask=(1<<n)-1
    classes=sorted(set(y))
    cm={}
    for c in classes:
        m=0
        for i,v in enumerate(y):
            if v==c:m|=1<<i
        cm[c]=m
    values=[]
    for j in range(p):
        mp={}
        for i,row in enumerate(X):
            v=row[j]
            mp[v]=mp.get(v,0)|(1<<i)
        values.append(mp)
    return allmask,cm,values

def full_signature_collisions(X,y):
    seen={}; mixed=[]
    for i,(r,a) in enumerate(zip(X,y)):
        k=tuple(r)
        if k in seen and seen[k][0]!=a:
            mixed.append((seen[k][1],i))
        else:
            seen[k]=(a,i)
    return mixed,len(seen)

def exact_tree(X,y,names,max_depth=8):
    n=len(y); p=len(names); full=(1<<n)-1
    allmask,cm,values=build_masks(X,y)
    class_masks=tuple(cm[c] for c in sorted(cm))
    out=[tuple(mp.values()) for mp in values]
    @lru_cache(None)
    def terminal(mask):
        return any(mask & ~m == 0 for m in class_masks)
    @lru_cache(None)
    def parts(mask,j):
        return tuple(q for om in out[j] if (q:=mask&om))
    @lru_cache(None)
    def ordered(mask):
        z=[]
        for j in range(p):
            ps=parts(mask,j)
            if len(ps)<=1:continue
            z.append((max(q.bit_count() for q in ps),-len(ps),names[j],j))
        z.sort()
        return tuple(j for *_,j in z)
    @lru_cache(None)
    def feasible(mask,d):
        if terminal(mask):return True
        if d<=0:return False
        for j in ordered(mask):
            if all(feasible(c,d-1) for c in sorted(parts(mask,j),key=int.bit_count,reverse=True)):
                return True
        return False
    depth=None
    for d in range(max_depth+1):
        if feasible(full,d):
            depth=d;break
    if depth is None:return None
    @lru_cache(None)
    def solve(mask,d):
        if terminal(mask): return (0,None)
        best=None
        for j in ordered(mask):
            ps=parts(mask,j)
            if any(not feasible(c,d-1) for c in ps):continue
            total=mask.bit_count()
            ok=True
            for c in ps:
                sc,_=solve(c,d-1)
                if sc is None:ok=False;break
                total+=sc
            if ok and (best is None or total<best[0] or (total==best[0] and names[j]<names[best[1]])):
                best=(total,j)
        return best if best else (None,None)
    total,root=solve(full,depth)
    return {"depth":depth,"root":names[root],"total_cost":int(total),"mean_cost":total/n}

def exact_instance_prices(X,y,names,max_k=6):
    n=len(y); p=len(names)
    allmask,cm,values=build_masks(X,y)
    hist=Counter(); unresolved=[]; nodes=0
    t0=time.time()

    # For each world, each probe keeps same-value worlds.
    same=[]
    for j,mp in enumerate(values):
        same.append(mp)

    for i,(row,a) in enumerate(zip(X,y)):
        rem0=allmask ^ cm[a]
        # Full library certifiability.
        rem=rem0
        for j in range(p):
            rem &= same[j][row[j]]
            if rem==0:break
        if rem:
            unresolved.append(i); continue

        # Upper bound greedy.
        rem=rem0; chosen=[]
        while rem:
            best=None; bestrem=None; bestcnt=rem.bit_count()
            for j in range(p):
                nr=rem & same[j][row[j]]
                c=nr.bit_count()
                if c<bestcnt:
                    best,bestrem,bestcnt=j,nr,c
                    if c==0:break
            chosen.append(best);rem=bestrem
        upper=len(chosen)

        # Exact iterative deepening with conflict-world branching.
        @lru_cache(None)
        def feasible(rem,d):
            nonlocal nodes
            nodes+=1
            if rem==0:return True
            if d==0:return False
            # pick one uncovered conflicting world with fewest distinguishing probes
            bits=rem; bestcand=None
            for _ in range(24):
                if not bits:break
                b=bits & -bits; k=b.bit_length()-1; bits^=b
                cand=[j for j in range(p) if X[k][j]!=row[j]]
                if not cand:return False
                if bestcand is None or len(cand)<len(bestcand):bestcand=cand
            opts=[]
            seen=set()
            for j in bestcand:
                nr=rem & same[j][row[j]]
                if nr not in seen:
                    seen.add(nr);opts.append((nr.bit_count(),j,nr))
            for _,j,nr in sorted(opts):
                if feasible(nr,d-1):return True
            return False
        found=None
        for k in range(1,min(upper,max_k)+1):
            if feasible(rem0,k):
                found=k;break
        if found is None:
            found=upper
        hist[found]+=1

        if (i+1)%1000==0:
            print("P",i+1,dict(sorted(hist.items())),"unresolved",len(unresolved),"nodes",nodes,flush=True)

    count=sum(hist.values())
    mean=sum(k*v for k,v in hist.items())/count if count else None
    return {
      "certifiable":count,"uncertifiable":len(unresolved),
      "histogram":{str(k):v for k,v in sorted(hist.items())},
      "mean_exact_or_upper_price":mean,
      "exact_search_cap":max_k,
      "note":"All prices <= search cap are exact. Rows whose optimum exceeds the cap fall back to a valid greedy upper bound; inspect histogram before claiming a global exact mean.",
      "nodes":nodes,"elapsed_seconds":time.time()-t0
    }

def main():
    X,y,sha=load()
    mixed,distinct=full_signature_collisions(X,y)
    out={
      "experiment":"INSACERMO_MUSHROOM_INFORMATION_PRICE_V1",
      "source_url":URL,
      "sha256":sha,
      "rows":len(X),"probes":len(NAMES),"actions":sorted(set(y)),
      "distinct_full_signatures":distinct,
      "mixed_full_signature_pairs":len(mixed),
      "scope":"finite dataset-relative guarantee only; not a food-safety system",
    }
    out["planner"]=exact_tree(X,y,NAMES,max_depth=8)
    out["instance_prices"]=exact_instance_prices(X,y,NAMES,max_k=6)
    out["status"]="SUCCESS"
    with open("MUSHROOM_INFORMATION_PRICE_V1.json","w") as f:json.dump(out,f,indent=2,sort_keys=True)
    print("RESULT",json.dumps(out,indent=2,sort_keys=True))
if __name__=="__main__":main()
