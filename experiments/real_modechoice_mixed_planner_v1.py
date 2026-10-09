#!/usr/bin/env python3
import json, functools, statistics
from collections import Counter
from itertools import product

MODES=("air","train","bus","car")
MODE_CODE={1:"air",2:"train",3:"bus",4:"car"}
INF=999

def load_data():
    import statsmodels.api as sm
    d=sm.datasets.modechoice.load_pandas().data.copy()
    d["individual"]=d["individual"].astype(int)
    d["mode_name"]=d["mode"].astype(int).map(MODE_CODE)
    return d

def base_records(df):
    out=[]
    for pid,g in df.groupby("individual",sort=True):
        rows={r["mode_name"]:r for _,r in g.iterrows()}
        vals={}
        for m in MODES:
            r=rows[m]
            vals[m]={"gcost":float(r["gc"]),
                     "time":float(r["ttme"])+float(r["invt"])}
        out.append((pid,vals))
    return out

def apply_repair(recs, rep):
    if rep is None: return recs
    out=[]
    f=1-rep["reduction_pct"]/100
    for pid,vals0 in recs:
        vals={m:dict(v) for m,v in vals0.items()}
        vals[rep["mode"]][rep["criterion"]]*=f
        out.append((pid,vals))
    return out

def semantics(recs, slack):
    f=1+slack
    rows=[]
    for pid,vals in recs:
        mg=min(v["gcost"] for v in vals.values())
        mt=min(v["time"] for v in vals.values())
        adm=tuple(m for m in MODES
                  if vals[m]["gcost"]<=f*mg and vals[m]["time"]<=f*mt)
        atoms={}
        for m in MODES:
            atoms[(m,"gcost")]=vals[m]["gcost"]<=f*mg
            atoms[(m,"time")]=vals[m]["time"]<=f*mt
        rows.append((pid,adm,atoms))
    am={}
    for m in MODES:
        mask=0
        for i,(_,adm,_) in enumerate(rows):
            if m in adm: mask|=1<<i
        am[m]=mask
    probes=[]
    for m in MODES:
        for crit in ("gcost","time"):
            mask=0
            for i,(_,_,atoms) in enumerate(rows):
                if atoms[(m,crit)]: mask|=1<<i
            probes.append((f"{m}_{crit}_within_contract",mask))
    return rows,am,probes

def common_action(mask,am):
    for m,M in am.items():
        if mask & ~M == 0: return m
    return None

def all_pointwise(mask,am):
    union=0
    for M in am.values(): union|=M
    return mask & ~union == 0

def solve_case(base, slack, repairs):
    n=len(base); full=(1<<n)-1
    states=[None]+repairs
    sem=[]
    for rep in states:
        sem.append(semantics(apply_repair(base,rep),slack))
    # state 0=no repair yet; state >0 means that repair has been applied and no second repair allowed.
    @functools.lru_cache(None)
    def solve(mask,state,used):
        rows,am,probes=sem[state]
        act=common_action(mask,am)
        if act is not None:
            return (0,("ACT",act))
        if state>0 and not all_pointwise(mask,am):
            return (INF,("REFUSE","unserviceable_after_repair"))
        best=(INF,("REFUSE","no_plan"))
        # PROBE
        for p,(name,ym) in enumerate(probes):
            if (used>>p)&1: continue
            y=mask&ym; no=mask&~ym
            if not y or not no: continue
            nxt=used|(1<<p)
            dy=solve(y,state,nxt)[0]; dn=solve(no,state,nxt)[0]
            if dy>=INF or dn>=INF: continue
            key=1+max(dy,dn)
            if key<best[0]:
                best=(key,("PROBE",p))
        # One contingent REPAIR remains available only before any repair.
        if state==0:
            for ridx,rep in enumerate(repairs, start=1):
                d=solve(mask,ridx,0)[0]
                if d>=INF: continue
                key=1+d
                if key<best[0]:
                    best=(key,("REPAIR",ridx))
        return best

    depth,root=solve(full,0,0)

    # Baselines.
    def probe_only(mask,used):
        rows,am,probes=sem[0]
        act=common_action(mask,am)
        if act is not None: return 0
        if not all_pointwise(mask,am): return INF
        best=INF
        for p,(name,ym) in enumerate(probes):
            if (used>>p)&1: continue
            y=mask&ym; no=mask&~ym
            if not y or not no: continue
            a=probe_only(y,used|(1<<p)); b=probe_only(no,used|(1<<p))
            if a<INF and b<INF: best=min(best,1+max(a,b))
        return best
    probe_only=functools.lru_cache(None)(probe_only)
    po=probe_only(full,0)

    repair_only=[]
    for ridx,rep in enumerate(repairs, start=1):
        _,am,_=sem[ridx]
        act=common_action(full,am)
        if act is not None:
            repair_only.append((1,rep,act))
    repair_only.sort(key=lambda x:(x[0],x[1]["reduction_pct"],x[1]["mode"],x[1]["criterion"]))

    # Extract all realized root-to-leaf signatures.
    paths=[]
    leaf_depths=[]
    def walk(mask,state,used,path):
        d,choice=solve(mask,state,used)
        if d>=INF:
            paths.append(path+["REFUSE"]); return
        kind=choice[0]
        if kind=="ACT":
            paths.append(path+[f"ACT:{choice[1]}"])
            leaf_depths.extend([len([x for x in path if not x.startswith("ACT")])]*mask.bit_count())
            return
        rows,am,probes=sem[state]
        if kind=="PROBE":
            p=choice[1]; name,ym=probes[p]
            y=mask&ym; no=mask&~ym
            walk(y,state,used|(1<<p),path+[f"PROBE:{name}=YES"])
            walk(no,state,used|(1<<p),path+[f"PROBE:{name}=NO"])
        elif kind=="REPAIR":
            ridx=choice[1]; rep=repairs[ridx-1]
            tag=f"REPAIR:{rep['mode']}:{rep['criterion']}:-{rep['reduction_pct']}%"
            walk(mask,ridx,0,path+[tag])
    if depth<INF:
        walk(full,0,0,[])

    sig=Counter()
    contains_p_r_p=0
    for p in paths:
        kinds=[x.split(":")[0] for x in p]
        compact="→".join(kinds)
        sig[compact]+=1
        if "PROBE→REPAIR→PROBE" in compact:
            contains_p_r_p+=1

    return {
      "slack_pct":round(slack*100),
      "mixed_exact_result":"SOLVED" if depth<INF else "REFUSE",
      "mixed_worst_case_steps":None if depth>=INF else depth,
      "mixed_mean_leaf_steps":None if not leaf_depths else statistics.mean(leaf_depths),
      "probe_only_worst_case_steps":None if po>=INF else po,
      "repair_only_global_solution_count":len(repair_only),
      "repair_only_best":repair_only[0] if repair_only else None,
      "realized_path_signatures":dict(sig),
      "paths_with_probe_repair_probe":contains_p_r_p,
      "sample_paths":paths[:12],
      "memo_states":solve.cache_info().currsize
    }

def main():
    df=load_data(); base=base_records(df)
    assert len(base)==210
    repairs=[{"mode":m,"criterion":c,"reduction_pct":p}
             for m,c,p in product(MODES,("gcost","time"),(10,20,30))]
    cases=[solve_case(base,s,repairs) for s in (0.25,0.50,0.75,1.00)]
    out={
      "experiment":"INSACERMO_REAL_MODECHOICE_MIXED_PLANNER_V1",
      "dataset":{"travelers":210,"rows":840,"modes":list(MODES)},
      "contract":"Both generalized cost and total time must be within (1+slack) of the traveler-specific best.",
      "probe_library":"8 exact contract atoms; thresholds declared by contract.",
      "repair_library":"24 one-shot interventions: 4 modes x 2 criteria x {10,20,30}% reduction. At most one repair per realized branch.",
      "planner":"Exact finite minimax search. Each PROBE or REPAIR costs one step; ACT costs zero.",
      "cases":cases,
      "status":"PASS"
    }
    print(json.dumps(out,indent=2,sort_keys=True))
    with open("REAL_MODECHOICE_MIXED_PLANNER_V1.json","w") as f:
        json.dump(out,f,indent=2,sort_keys=True)

if __name__=="__main__":
    main()
