#!/usr/bin/env python3
import json, statistics, functools
from collections import Counter
from itertools import product

MODES=("air","train","bus","car")
MODE_CODE={1:"air",2:"train",3:"bus",4:"car"}

def load_data():
    import statsmodels.api as sm
    d=sm.datasets.modechoice.load_pandas().data.copy()
    d["individual"]=d["individual"].astype(int)
    d["mode_name"]=d["mode"].astype(int).map(MODE_CODE)
    return d

def records(df, repair=None):
    out=[]
    for pid,g in df.groupby("individual",sort=True):
        rows={r["mode_name"]:r for _,r in g.iterrows()}
        vals={}
        for m in MODES:
            r=rows[m]
            gc=float(r["gc"])
            tm=float(r["ttme"])+float(r["invt"])
            if repair and repair["mode"]==m:
                factor=1-repair["reduction_pct"]/100
                if repair["criterion"]=="gcost": gc*=factor
                else: tm*=factor
            vals[m]={"gcost":gc,"time":tm}
        out.append((pid,vals))
    return out

def acceptable(recs, slack):
    # slack=0.25 means <=1.25x best on BOTH criteria.
    result=[]
    f=1+slack
    for pid,vals in recs:
        mg=min(v["gcost"] for v in vals.values())
        mt=min(v["time"] for v in vals.values())
        adm=tuple(m for m in MODES
                  if vals[m]["gcost"] <= f*mg and vals[m]["time"] <= f*mt)
        atoms={}
        for m in MODES:
            atoms[(m,"gcost")]=vals[m]["gcost"] <= f*mg
            atoms[(m,"time")]=vals[m]["time"] <= f*mt
        result.append((pid,vals,adm,atoms))
    return result

def action_masks(rows):
    am={}
    for m in MODES:
        z=0
        for i,(_,_,adm,_) in enumerate(rows):
            if m in adm: z|=1<<i
        am[m]=z
    return am

def probe_masks(rows):
    # The eight atomic contract predicates; thresholds are declared by contract,
    # not fitted from labels.
    ps=[]
    for m in MODES:
        for crit in ("gcost","time"):
            z=0
            for i,(_,_,_,atoms) in enumerate(rows):
                if atoms[(m,crit)]: z|=1<<i
            ps.append((f"{m}_{crit}_within_contract",z))
    return ps

def common_actions(mask,am):
    return tuple(m for m,M in am.items() if mask & ~M == 0)

def exact_tree(rows):
    n=len(rows); full=(1<<n)-1
    am=action_masks(rows); ps=probe_masks(rows)
    unserviceable=[rows[i][0] for i in range(n)
                   if not any((am[m]>>i)&1 for m in MODES)]
    if unserviceable:
        return {
          "all_worlds_pointwise_serviceable":False,
          "unserviceable_count":len(unserviceable),
          "unserviceable_examples":unserviceable[:10],
          "exact_probe_result":"REFUSE",
          "reason":"At least one world has no acceptable action; information alone cannot rescue it."
        }
    @functools.lru_cache(None)
    def sol(mask,avail):
        acts=common_actions(mask,am)
        if acts: return (0,None,acts[0])
        best=None
        for p,(name,ym) in enumerate(ps):
            if not (avail>>p)&1: continue
            y=mask&ym; no=mask&~ym
            if not y or not no: continue
            nxt=avail&~(1<<p)
            a=sol(y,nxt)[0]; b=sol(no,nxt)[0]
            if a>=999 or b>=999: continue
            key=(1+max(a,b),1+a+b,p)
            if best is None or key<best[0]: best=(key,p,None)
        return (999,None,None) if best is None else (best[0][0],best[1],None)
    allbits=(1<<len(ps))-1
    depth,root,_=sol(full,allbits)
    if depth>=999:
        return {
          "all_worlds_pointwise_serviceable":True,
          "unserviceable_count":0,
          "exact_probe_result":"REFUSE",
          "reason":"Declared probe library cannot separate ambiguity into actionable fibers."
        }
    depths={}
    selected=Counter()
    def walk(mask,avail,d):
        acts=common_actions(mask,am)
        if acts:
            for i in range(n):
                if (mask>>i)&1: depths[rows[i][0]]=d
            selected[acts[0]] += mask.bit_count()
            return
        _,p,_=sol(mask,avail)
        ym=ps[p][1]; y=mask&ym; no=mask&~ym
        nxt=avail&~(1<<p)
        walk(y,nxt,d+1); walk(no,nxt,d+1)
    walk(full,allbits,0)
    return {
      "all_worlds_pointwise_serviceable":True,
      "unserviceable_count":0,
      "exact_probe_result":"ACT_AFTER_PROBE",
      "probe_library_size":len(ps),
      "worst_case_depth":depth,
      "mean_depth":statistics.mean(depths.values()),
      "median_depth":statistics.median(depths.values()),
      "root_probe":ps[root][0] if root is not None else None,
      "selected_mode_counts":dict(selected)
    }

def scenario(df, slack, repair=None):
    rs=acceptable(records(df,repair),slack)
    counts={m:sum(m in adm for _,_,adm,_ in rs) for m in MODES}
    r=exact_tree(rs)
    r.update({
      "slack_pct":round(slack*100),
      "action_region_sizes":counts,
      "repair":repair
    })
    return r

def main():
    df=load_data()
    assert len(df)==840 and df["individual"].nunique()==210
    slacks=(0.10,0.25,0.50,1.00,2.00)
    baseline=[scenario(df,s) for s in slacks]

    # Exhaustive declared single-repair library: improve one mode on one criterion
    # by 10..50%; no data-fitted continuous optimization.
    repairs=[]
    for m,crit,p in product(MODES,("gcost","time"),(10,20,30,40,50)):
        repairs.append({"mode":m,"criterion":crit,"reduction_pct":p})

    rescue={}
    for s in slacks:
        base=scenario(df,s)
        if base["exact_probe_result"]!="REFUSE":
            rescue[str(round(s*100))]={"needed":False}
            continue
        candidates=[]
        for rep in repairs:
            rr=scenario(df,s,rep)
            if rr["exact_probe_result"]=="ACT_AFTER_PROBE":
                candidates.append(rr)
        candidates.sort(key=lambda x:(x["repair"]["reduction_pct"],
                                      x["worst_case_depth"],
                                      x["mean_depth"],
                                      x["repair"]["mode"],
                                      x["repair"]["criterion"]))
        rescue[str(round(s*100))]={
          "needed":True,
          "single_repair_candidates_found":len(candidates),
          "best_single_repair":candidates[0] if candidates else None
        }

    out={
      "experiment":"INSACERMO_REAL_MODECHOICE_STRESS_CONTRACT_V1",
      "dataset":{"rows":840,"travelers":210,"modes":list(MODES)},
      "contract":"Mode m is acceptable iff its generalized cost and total time are each <= (1+slack) times the traveler-specific minimum for that criterion.",
      "probe_library":"8 declared contract atoms: for each mode, within-contract on cost and on time; no learned thresholds.",
      "baseline_sweep":baseline,
      "single_repair_search":rescue,
      "repair_library":"4 modes x 2 criteria x reductions {10,20,30,40,50} percent.",
      "scientific_guardrail":"If any traveler has no acceptable mode, PROBE is declared unable to help; only REPAIR/contract change may rescue. No ML or out-of-sample claim.",
      "status":"PASS"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("REAL_MODECHOICE_STRESS_CONTRACT_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
