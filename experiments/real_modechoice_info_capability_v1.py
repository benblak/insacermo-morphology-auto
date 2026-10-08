#!/usr/bin/env python3
import json, math, statistics, functools
from collections import Counter, defaultdict

MODES=("air","train","bus","car")

def load_data():
    import statsmodels.api as sm
    d=sm.datasets.modechoice.load_pandas().data.copy()
    # normalize columns across statsmodels versions
    d["individual"]=d["individual"].astype(int)
    d["mode"]=d["mode"].astype(str)
    if "choice" in d:
        d["choice"]=d["choice"].astype(str)
    return d

def traveler_records(df, train_factor=1.0):
    recs=[]
    for pid,g in df.groupby("individual",sort=True):
        rows={str(r["mode"]):r for _,r in g.iterrows()}
        if set(rows)!=set(MODES):
            raise RuntimeError((pid,set(rows)))
        vals={}
        for m in MODES:
            r=rows[m]
            gc=float(r["gcost"])
            if m=="train":
                gc*=train_factor
            total=float(r["wait"])+float(r["travel"])
            vals[m]={"gcost":gc,"time":total}
        admiss=[]
        for m in MODES:
            dom=False
            for k in MODES:
                if k==m: continue
                le=(vals[k]["gcost"]<=vals[m]["gcost"] and
                    vals[k]["time"]<=vals[m]["time"])
                strict=(vals[k]["gcost"]<vals[m]["gcost"] or
                        vals[k]["time"]<vals[m]["time"])
                if le and strict:
                    dom=True; break
            if not dom:
                admiss.append(m)
        recs.append((pid,vals,tuple(admiss)))
    return recs

def probes_for(recs):
    # Semantics-derived library: six unordered mode pairs x two criteria.
    probes=[]
    for crit in ("gcost","time"):
        for i,a in enumerate(MODES):
            for b in MODES[i+1:]:
                name=f"{a}_{crit}<={b}_{crit}"
                yes=0
                for idx,(_,vals,_) in enumerate(recs):
                    if vals[a][crit] <= vals[b][crit]:
                        yes |= (1<<idx)
                probes.append((name,yes))
    return probes

def action_masks(recs):
    out={}
    for m in MODES:
        mask=0
        for i,(_,_,adm) in enumerate(recs):
            if m in adm: mask|=(1<<i)
        out[m]=mask
    return out

def common_actions(mask, amasks):
    return tuple(m for m,M in amasks.items() if mask & ~M == 0)

def minimum_cover_number(full, amasks):
    from itertools import combinations
    items=list(amasks.items())
    for k in range(1,len(items)+1):
        for combo in combinations(items,k):
            U=0
            for _,M in combo: U|=M
            if full & ~U == 0:
                return k, tuple(m for m,_ in combo)
    return None,()

def exact_minimax_tree(recs):
    n=len(recs); full=(1<<n)-1
    probes=probes_for(recs); amasks=action_masks(recs)

    @functools.lru_cache(None)
    def solve(mask, availbits):
        acts=common_actions(mask,amasks)
        if acts:
            return (0,None,acts[0])
        best=None
        for p,(name,ymask) in enumerate(probes):
            if not (availbits>>p)&1: continue
            y=mask & ymask
            no=mask & ~ymask
            if y==0 or no==0: continue
            nxt=availbits & ~(1<<p)
            dy=solve(y,nxt)[0]
            dn=solve(no,nxt)[0]
            if dy>=10**6 or dn>=10**6: continue
            key=(1+max(dy,dn), 1+dy+dn, p)
            if best is None or key<best[0]:
                best=(key,p,None)
        if best is None:
            return (10**6,None,None)
        p=best[1]
        return (best[0][0],p,None)

    allbits=(1<<len(probes))-1
    depth,root,_=solve(full,allbits)

    leaf_depths={}
    leaf_modes=Counter()
    used_probes=Counter()
    uncertified=[]
    def walk(mask,availbits,d):
        acts=common_actions(mask,amasks)
        if acts:
            ids=[recs[i][0] for i in range(n) if (mask>>i)&1]
            for pid in ids: leaf_depths[pid]=d
            leaf_modes[acts[0]]+=len(ids)
            return
        _,p,_=solve(mask,availbits)
        if p is None:
            uncertified.extend(recs[i][0] for i in range(n) if (mask>>i)&1)
            return
        used_probes[probes[p][0]]+=1
        y=mask & probes[p][1]; no=mask & ~probes[p][1]
        nxt=availbits & ~(1<<p)
        walk(y,nxt,d+1); walk(no,nxt,d+1)

    walk(full,allbits,0)
    tau,cover=minimum_cover_number(full,amasks)
    return {
      "n_travelers":n,
      "probe_library_size":len(probes),
      "action_region_sizes":{m:(amasks[m]&full).bit_count() for m in MODES},
      "minimum_action_cover_number_tau":tau,
      "one_minimum_action_cover":cover,
      "ideal_unrestricted_binary_lower_bound": None if tau is None else (0 if tau<=1 else math.ceil(math.log2(tau))),
      "exact_restricted_probe_worst_case_depth": None if depth>=10**6 else depth,
      "exact_restricted_probe_mean_depth": None if uncertified else statistics.mean(leaf_depths.values()),
      "exact_restricted_probe_median_depth": None if uncertified else statistics.median(leaf_depths.values()),
      "certified_travelers":len(leaf_depths),
      "uncertified_travelers":len(uncertified),
      "leaf_selected_mode_counts":dict(leaf_modes),
      "tree_probe_use_counts":dict(used_probes),
      "root_probe": None if root is None else probes[root][0],
      "all_leaves_certified":len(uncertified)==0
    }

def main():
    df=load_data()
    if len(df)!=840 or df["individual"].nunique()!=210:
        raise RuntimeError((len(df),df["individual"].nunique()))
    scenarios=[]
    for pct in (0,10,20,30,40,50):
        recs=traveler_records(df,train_factor=1-pct/100)
        r=exact_minimax_tree(recs)
        r["train_gcost_reduction_pct"]=pct
        scenarios.append(r)
    out={
      "experiment":"INSACERMO_REAL_MODECHOICE_INFO_CAPABILITY_V1",
      "dataset":{
        "name":"Travel Mode Choice",
        "rows":840,
        "travelers":210,
        "modes":list(MODES),
        "source":"statsmodels.datasets.modechoice; 1987 intercity Australia study"
      },
      "contract":"A mode is admissible for a traveler iff it is not Pareto-dominated on generalized cost and total time = wait + travel.",
      "probe_semantics":"12 fixed pairwise comparisons: six mode pairs x {generalized cost,total time}; no learned thresholds.",
      "repair_semantics":"counterfactual reduction of train generalized cost, with Pareto regions recomputed exactly.",
      "scenarios":scenarios,
      "no_ml_claim":"No statistical model is trained and no out-of-sample generalization is claimed; this is exact planning over the declared 210-world dataset.",
      "status":"PASS" if all(s["all_leaves_certified"] for s in scenarios) else "PARTIAL"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("REAL_MODECHOICE_INFO_CAPABILITY_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
