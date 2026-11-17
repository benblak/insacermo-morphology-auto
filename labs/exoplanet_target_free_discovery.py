#!/usr/bin/env python3
"""Target-free, unknown exponent, NASA exoplanet catalogue experiment.
Preregistered af1c43d3a5e47e830bb2bfeccba2a26da58b964b.
Independent lab. Historical INSACERMO/C3 kernel remains frozen.
"""
from __future__ import annotations
import csv,hashlib,io,json,math,sys,urllib.parse,urllib.request
from pathlib import Path
import numpy as np
COLS=("pl_orbper","pl_orbsmax","st_mass","st_teff","st_rad","sy_dist")
SQL="SELECT pl_name,hostname,discoverymethod,pl_orbper,pl_orbsmax,st_mass,st_teff,st_rad,sy_dist FROM pscomppars ORDER BY pl_name"
API="https://exoplanetarchive.ipac.caltech.edu/TAP/sync"
SEEDS=(17,31,43,59,71,89,101,127)
PREREG="af1c43d3a5e47e830bb2bfeccba2a26da58b964b"
BUDGET=24
def stable(s):return hashlib.sha256((s+":insacermo:20261117").encode()).digest()
def model_params(L,target,source):
    A=np.column_stack([np.ones(len(L))]+[L[:,j] for j in source])
    return np.linalg.lstsq(A,L[:,target],rcond=None)[0]
def predict(L,source,b):
    return b[0]+sum(b[k+1]*L[:,j] for k,j in enumerate(source))
def exprs(n,j):
    v=[(k,) for k in range(n) if k!=j]
    v.extend((k,l) for k in range(n) for l in range(k+1,n) if k!=j and l!=j)
    return v
def rank(L,target=None):
    results=[]
    for j in ([target] if target is not None else range(L.shape[1])):
        std=float(np.std(L[:,j]))
        if std<=.2:continue
        for src in exprs(L.shape[1],j):
            e=[]
            for fold in range(3):
                test=np.arange(fold,len(L),3,dtype=int)
                train=np.asarray([i for i in range(len(L)) if i%3!=fold],dtype=int)
                b=model_params(L[train],j,src)
                e.extend(np.abs(predict(L[test],src,b)-L[test,j]).tolist())
            score=(float(np.median(e))+.2*float(np.percentile(e,90)))/std+.005*len(src)
            results.append((score,j,src))
    return sorted(results,key=lambda t:(t[0],t[1],t[2]))
def explanation(t):
    return {"score":t[0],"target":t[1],"sources":list(t[2])}
def load(out):
    url=API+"?"+urllib.parse.urlencode({"query":SQL,"format":"csv"})
    req=urllib.request.Request(url,headers={"User-Agent":"INSACERMO-Physics-audit/1.0"})
    with urllib.request.urlopen(req,timeout=300) as f:raw=f.read()
    if len(raw)<1000:raise RuntimeError("NASA TAP response too small: "+repr(raw[:400]))
    (out/"nasa_source.csv").write_bytes(raw)
    reader=csv.DictReader(io.StringIO(raw.decode("utf-8-sig")))
    required=["pl_name","hostname","discoverymethod"]+list(COLS)
    assert all(c in reader.fieldnames for c in required),reader.fieldnames
    source_rows=list(reader)
    valid=[]
    for d in source_rows:
        if d["discoverymethod"] not in ("Transit","Radial Velocity"):continue
        try:nums=np.asarray([float(d[k]) for k in COLS])
        except (TypeError,ValueError):continue
        if not np.all(np.isfinite(nums)) or not np.all(nums>0):continue
        valid.append({"planet":d["pl_name"],"host":d["hostname"],"method":d["discoverymethod"],"v":nums.tolist()})
    unique={}
    for item in valid:
        if item["host"] not in unique:unique[item["host"]]=item
    tr=sorted((r for r in unique.values() if r["method"]=="Transit"),key=lambda r:stable(r["host"]))
    rv=sorted((r for r in unique.values() if r["method"]=="Radial Velocity"),key=lambda r:stable(r["host"]))
    a,b=int(len(tr)*.6),int(len(tr)*.8)
    arrays={"discovery":tr[:a],"challenge":tr[a:b],"transit_test":tr[b:],"rv_test":rv}
    summary={"all_catalogue_rows":len(source_rows),"valid_all_feature_rows":len(valid),
       "unique_host_rows":len(unique),"source_sha256":hashlib.sha256(raw).hexdigest(),
       "counts":{k:len(v) for k,v in arrays.items()}}
    return arrays,summary
def query_policy(name,seed,L,H,target,initial,mu,sd):
    chosen=[];trace=[];rng=np.random.default_rng(seed) if seed is not None else None
    ranking=initial
    for step in range(BUDGET):
        avail=np.asarray([i for i in range(len(H)) if i not in set(chosen)],int)
        train=np.vstack((L,H[chosen])) if chosen else L
        if seed is None:
            # Zero target access in challenge candidate arrays used for choice.
            blind=H.copy();blind[:,target]=np.nan
            candidate=[]
            for _,_,p in ranking[:5]:
                beta=model_params(train,target,p)
                candidate.append(predict(blind[avail],p,beta))
            disagreement=np.std(np.asarray(candidate),axis=0)
            if chosen:
                x=(np.delete(blind,target,axis=1)-mu)/sd
                d=x[avail,None,:]-x[np.asarray(chosen),:][None,:,:]
                nearest=np.min(np.linalg.norm(d,axis=2),axis=1)
                utility=disagreement*(1+.2*np.minimum(3,nearest))
            else:utility=disagreement
            row=int(avail[np.argmax(utility)])
            uncertainty=float(np.max(utility))
        else:
            row=int(rng.choice(avail));uncertainty=None
        best=ranking[0]
        forecast=float(predict(H[[row]],best[2],model_params(train,target,best[2]))[0])
        # This is the ONLY oracle-target read on the challenge pool in this round.
        observed=float(H[row,target])
        trace.append({"round":step+1,"row":row,"before":explanation(best),
            "forecast_log":forecast,"observed_log":observed,"uncertainty":uncertainty})
        chosen.append(row)
        ranking=rank(np.vstack((L,H[chosen])),target)
    final=np.vstack((L,H[chosen]));best=ranking[0]
    base=next(r for r in ranking if len(r[2])==1)
    return {"name":name,"seed":seed,"queried_challenge_rows":chosen,"trace":trace,
        "model":explanation(best),"coef":model_params(final,target,best[2]).tolist(),
        "one_input":explanation(base),"one_input_coef":model_params(final,target,base[2]).tolist()}
def assess(H,target,src,beta):
    with np.errstate(over="ignore",invalid="ignore"):
        guessed=np.exp(np.clip(predict(H,src,beta),-700,700))
        truth=np.exp(H[:,target])
        errors=np.abs(guessed-truth)/truth
    return {"n":len(errors),"median_relative_pct":float(np.median(errors)*100),
        "p90_relative_pct":float(np.percentile(errors,90)*100),
        "fraction_within_15pct":float(np.mean(errors<=.15)),
        "mean_relative_pct":float(np.mean(errors)*100),
        "rmse":float(np.sqrt(np.mean((guessed-truth)**2)))}
def run(folder):
    out=Path(folder);out.mkdir(parents=True,exist_ok=True)
    rows,summary=load(out)
    (out/"provenance.json").write_text(json.dumps(summary,indent=2)+"\n")
    c=summary["counts"]
    if c["discovery"]<250 or c["challenge"]<35 or c["rv_test"]<50:
        r={"verdict":"INFEASIBLE","reason":"frozen minimum sample sizes unmet","provenance":summary}
        (out/"audit.json").write_text(json.dumps(r,indent=2)+"\n")
        print("EXOPLANET_INFEASIBLE",json.dumps(r),flush=True)
        return
    V={k:np.log(np.asarray([row["v"] for row in arr],float)) for k,arr in rows.items()}
    D,H=V["discovery"],V["challenge"]
    candidates=rank(D);assert candidates
    j=candidates[0][1];alternative=[v for v in candidates if v[1]==j]
    xx=np.delete(D,j,axis=1);mu=xx.mean(axis=0);sd=np.maximum(xx.std(axis=0),1e-10)
    policies=[query_policy("ACTIVE",None,D,H,j,alternative,mu,sd)]
    policies += [query_policy("RANDOM_"+str(seed),seed,D,H,j,alternative,mu,sd) for seed in SEEDS]
    sealed={"preregistered_commit":PREREG,"provenance":summary,
        "target_idx":j,"initial_candidate_models":[explanation(x) for x in candidates[:10]],
        "hostnames":{key:[r["host"] for r in arr] for key,arr in rows.items()},
        "policies":policies}
    (out/"sealed_before_holdout.json").write_text(json.dumps(sealed,indent=2)+"\n")
    # Only now evaluate withheld Transit and entirely unseen RV methods.
    results=[]
    for p in policies:
        a=assess(V["rv_test"],j,p["model"]["sources"],p["coef"])
        b=assess(V["rv_test"],j,p["one_input"]["sources"],p["one_input_coef"])
        t=assess(V["transit_test"],j,p["model"]["sources"],p["coef"])
        yes=(a["median_relative_pct"]<=5 and a["fraction_within_15pct"]>=.9
            and a["median_relative_pct"]<=.75*b["median_relative_pct"]
            and t["median_relative_pct"]<=5)
        results.append({"policy":p["name"],"rv":a,"rv_single_feature":b,"transit_test":t,
            "verdict":"ACCEPT_CATALOGUE_INVARIANT_TRANSFER" if yes else "REFUSE_CATALOGUE_INVARIANT"})
    active=policies[0]
    rng=np.random.default_rng(20261117)
    with np.errstate(over="ignore",invalid="ignore"):
        pred=np.exp(np.clip(predict(V["rv_test"],active["model"]["sources"],active["coef"]),-700,700))
    actual=np.exp(V["rv_test"][:,j]);observed=float(np.median(np.abs(pred-actual)/actual))
    null=[]
    for _ in range(100):
        permuted=actual[rng.permutation(len(actual))]
        null.append(float(np.median(np.abs(pred-permuted)/permuted)))
    report={"verdict":results[0]["verdict"],"relation":{
        "target":COLS[j],"predictors":[COLS[i] for i in active["model"]["sources"]],
        "exponents":active["coef"][1:],"multiplier":math.exp(active["coef"][0])},
        "provenance":summary,"results":results,
        "active_better_than_random_count":sum(results[0]["rv"]["median_relative_pct"]<r["rv"]["median_relative_pct"] for r in results[1:]),
        "shuffle_control_less_or_equal_median":sum(v<=observed for v in null),
        "shuffle_control_trials":100,"sealed_model_sha256":hashlib.sha256((out/"sealed_before_holdout.json").read_bytes()).hexdigest(),
        "caveats":["Known catalogue features may contain Kepler-derived computed values, making relation circular.",
           "Not novel physical law; multipower syntax provided; no new observations collected.",
           "Historical INSACERMO C3 and Lean proofs not changed."]}
    (out/"audit.json").write_text(json.dumps(report,indent=2)+"\n")
    print("EXOPLANET_RESULT",json.dumps({"verdict":report["verdict"],
          "relation":report["relation"],"rv":results[0]["rv"],
          "baseline":results[0]["rv_single_feature"],"n":summary["counts"]}),flush=True)
if __name__=="__main__":run(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_exoplanet")
