#!/usr/bin/env python3
"""INSACERMO: preregistered no-target fresh NOAA NDBC ocean forecasting law hunt.
NOAA source may fail; never fabricate observations or substitute stations.
Historical MAX TOTAL/C3 kernel is unchanged.
"""
from __future__ import annotations
import gzip,hashlib,io,json,math,sys,urllib.request,time
from pathlib import Path
import numpy as np
import pandas as pd

COLS=("WSPD","GST","WVHT","APD","PRES","ATMP","WTMP")
TARGETS=("WSPD","WVHT","PRES","ATMP","WTMP")
BOUNDS={"WSPD":(0,75),"GST":(0,95),"WVHT":(0,40),
 "APD":(1,25),"PRES":(870,1085),"ATMP":(-45,50),"WTMP":(-5,40)}
SOURCES=("41002","42002","46002")
HOLDOUT=("41004","42001","46005")
DISCOVERY_YEAR=2023
VALIDATION_YEAR=2024
HOLDOUT_YEAR=2025
SEED=20261117
URL="https://www.ndbc.noaa.gov/data/historical/stdmet/{}h{}.txt.gz"
PREREG_COMMIT="3252c6ef494206d74fc02ee20ed1a076e8469d4f"
RAW=[]

def fetch(station,year,root):
    url=URL.format(station,year)
    req=urllib.request.Request(url,headers={"User-Agent":"INSACERMO scientific noncommercial provenance-bounded lab / 1.0"})
    error=None
    for delay in (0,2,6):
        if delay:time.sleep(delay)
        try:
            with urllib.request.urlopen(req,timeout=60) as f:
                gz=f.read()
            raw=gzip.decompress(gz)
            if len(raw)<5000:raise RuntimeError("Very small decompressed source")
            name=f"{station}_{year}.txt.gz"
            (root/name).write_bytes(gz)
            RAW.append(dict(station=station,year=year,url=url,gzip_sha256=hashlib.sha256(gz).hexdigest(),
                            raw_sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw)))
            return parse(raw,station,year)
        except Exception as e:error=f"{type(e).__name__}: {e}"
    raise RuntimeError(f"DATA_UNAVAILABLE {station} {year} {url}: {error}")

def parse(raw,station,year):
    lines=raw.decode("utf-8-sig",errors="replace").splitlines()
    header=next((line for line in lines[:12] if line.startswith("#") and "WSPD" in line),None)
    if header is None:raise RuntimeError(f"UNKNOWN_COLUMN_FORMAT {station} {year}")
    fields=header.lstrip("#").split()
    if "PRES" not in fields and "BAR" in fields:
        fields=[x if x!="BAR" else "PRES" for x in fields]
    if "YY" not in fields and "YYYY" not in fields:
        raise RuntimeError(f"UNKNOWN_YEAR_FORMAT {station} {year}")
    if not all(x in fields for x in COLS):
        raise RuntimeError(f"MISSING_REQUIRED_CHANNEL {station} {year}, fields={fields}")
    d=pd.read_csv(io.StringIO("\n".join(x for x in lines if x.strip() and not x.startswith("#"))),
       sep=r"\s+",header=None,names=fields[:len(fields)],on_bad_lines="skip",engine="python")
    for k in fields:d[k]=pd.to_numeric(d[k],errors="coerce")
    yr="YYYY" if "YYYY" in fields else "YY"
    years=d[yr].astype("float64")
    if yr=="YY":years=np.where(years>=100,years,np.where(years<70,years+2000,years+1900))
    minute="mm" if "mm" in fields else None
    required=["MM","DD","hh"]
    if not all(x in fields for x in required):raise RuntimeError("NO_DATE_FIELDS")
    # Create datetimes via complete valid numeric records.
    ts=pd.to_datetime(dict(year=years,month=d["MM"],day=d["DD"],
             hour=d["hh"],minute=d[minute] if minute else np.zeros(len(d))),errors="coerce",utc=True)
    v=d[list(COLS)].copy()
    for k in COLS:
        lo,hi=BOUNDS[k]
        v[k]=v[k].where((v[k]>=lo)&(v[k]<=hi))
    v["time"]=ts
    print("NOAA_PARSE_DIAGNOSTIC",station,year,"header",fields,
        "raw_rows",len(v),"valid_time",int(v["time"].notna().sum()),
        "per_sensor_valid",{k:int(v[k].notna().sum()) for k in COLS},
        "all_sensor_complete",int(v.dropna(subset=["time"]+list(COLS)).shape[0]),
        "first_line",repr(lines[2][:200] if len(lines)>2 else ""),flush=True)
    v=v.dropna(subset=["time"]+list(COLS))
    v=v.sort_values("time").drop_duplicates("time",keep="last")
    v=v.set_index("time")
    v=v.loc[v.index.year==year]
    v=v.resample("1h").last().dropna(subset=list(COLS))
    # strictly require t-6 and t+6 in the same continuous time frame
    curr=v[list(COLS)]
    prev=curr.reindex(curr.index-pd.Timedelta(hours=6)).set_axis(curr.index)
    nxt=curr.reindex(curr.index+pd.Timedelta(hours=6)).set_axis(curr.index)
    good=prev.notna().all(axis=1)&nxt.notna().all(axis=1)
    curr=curr[good];prev=prev[good];nxt=nxt[good]
    if len(curr)<1000:raise RuntimeError(f"TOO_FEW_COMPLETE_6H_OBSERVATIONS {station} {year}: {len(curr)}")
    return dict(current=curr.to_numpy(dtype=float),prev=prev.to_numpy(dtype=float),
                future=nxt.to_numpy(dtype=float),time=[x.isoformat() for x in curr.index],
                count=len(curr),station=station,year=year)

def encode(arrays,mu=None,sd=None):
    x=np.vstack([np.hstack((a["current"],a["current"]-a["prev"])) for a in arrays])
    if mu is None:mu=x.mean(axis=0)
    if sd is None:sd=np.maximum(x.std(axis=0),1e-4)
    z=np.clip((x-mu)/sd,-12,12)
    names=[f"{c}@t" for c in COLS]+[f"delta6({c})" for c in COLS]
    cols=[z[:,i] for i in range(len(names))]
    for i in range(z.shape[1]):cols.append(z[:,i]**2);names.append(f"square({i})")
    nbase=z.shape[1]
    for i in range(nbase):
        for j in range(i+1,nbase):
            cols.append(z[:,i]*z[:,j]);names.append(f"product({i},{j})")
    return np.column_stack(cols),names,mu,sd

def split_rows(arrays):
    n=[len(a["current"]) for a in arrays]
    return np.concatenate([np.full(k,i,int) for i,k in enumerate(n)]),n

def fit(X,y,indices):
    A=np.column_stack([np.ones(len(X)),X[:,indices]])
    gram=A.T@A
    gram[1:,1:]+=np.eye(len(indices))*1e-3
    rhs=A.T@y
    try:return np.linalg.solve(gram,rhs)
    except np.linalg.LinAlgError:return np.linalg.lstsq(A,y,rcond=None)[0]

def prediction(X,coeff,indices):
    return coeff[0]+np.dot(X[:,indices],coeff[1:]) if indices else np.full(len(X),coeff[0])

def primary(arrays,target):
    j=COLS.index(target)
    return np.concatenate([a["future"][:,j]-a["current"][:,j] for a in arrays])

def baseline_X(arrays,target,mu=None,sd=None):
    j=COLS.index(target)
    X=np.vstack([np.column_stack((a["current"][:,j],a["current"][:,j]-a["prev"][:,j]))
                 for a in arrays])
    if mu is None:mu=X.mean(axis=0)
    if sd is None:sd=np.maximum(X.std(axis=0),1e-4)
    return np.clip((X-mu)/sd,-12,12),mu,sd

def station_scores(true,pred,station,nstations):
    rmse=np.array([float(np.sqrt(np.mean((true[station==i]-pred[station==i])**2)))
                      for i in range(nstations)])
    return rmse

def optimize(disc,val):
    xd,terms,mu,sd=encode(disc)
    xv,_,_,_=encode(val,mu,sd)
    ind_d,_=split_rows(disc);ind_v,_=split_rows(val)
    results=[]
    for target in TARGETS:
        y=primary(disc,target);v=primary(val,target)
        d0,mean0,scale0=baseline_X(disc,target)
        v0,_,_=baseline_X(val,target,mean0,scale0)
        bc=fit(d0,y,[0,1])
        # Keep intercept and target's autoregressive terms in every candidate.
        predicted_b=prediction(v0,bc,[0,1])
        station_ref=station_scores(v,predicted_b,ind_v,len(val))
        station_ref=np.maximum(station_ref,1e-8)
        # Fit EXTRA improvements to baseline residual, then evaluate on 2024.
        residue=y-prediction(d0,bc,[0,1])
        p0=predicted_b
        eligible=[i for i in range(len(terms)) if terms[i] not in
                  (f"{target}@t",f"delta6({target})")]
        feature_normalizers={}
        feature_scores=[]
        for j in eligible:
            # residual regression avoids reprocessing baseline and is fixed by preregistered grammar
            coeff=fit(xd,residue,[j])
            vpred=p0+prediction(xv,coeff,[j])
            errs=station_scores(v,vpred,ind_v,len(val))
            gain=float(np.mean(1-errs/station_ref))-.01
            feature_scores.append((gain,j,coeff))
        feature_scores.sort(key=lambda z:(-z[0],z[1]))
        best_gain=0.0;selected=[];regr=None
        if feature_scores and feature_scores[0][0]>best_gain:
            best_gain=feature_scores[0][0];selected=[feature_scores[0][1]]
            regr=feature_scores[0][2]
        # Deterministic second term greedily tests 8 best first terms only
        seedset=feature_scores[:8]
        for first in seedset:
            for j in eligible:
                if j==first[1]:continue
                coef=fit(xd,residue,[first[1],j])
                vpred=p0+prediction(xv,coef,[first[1],j])
                errs=station_scores(v,vpred,ind_v,len(val))
                gain=float(np.mean(1-errs/station_ref))-.02
                if gain>best_gain:
                    best_gain=gain;selected=[first[1],j];regr=coef
        vals=station_scores(v,p0+(prediction(xv,regr,selected) if selected else 0),ind_v,len(val))
        results.append(dict(target=target,selected_indices=selected,selected_terms=[terms[i] for i in selected],
            score=best_gain,station_baseline_rmse=station_ref.tolist(),station_candidate_rmse=vals.tolist(),
            baseline_coeff=bc.tolist(),baseline_center=mean0.tolist(),baseline_scale=scale0.tolist(),
            extra_coeff=regr.tolist() if regr is not None else None,
            feature_center=mu.tolist(),feature_scale=sd.tolist()))
    results.sort(key=lambda r:(-r["score"],r["target"]))
    return results,terms

def sample_errors(arrays,model,termnames):
    target=model["target"];y=primary(arrays,target)
    X0,_,_=baseline_X(arrays,target,np.array(model["baseline_center"]),np.array(model["baseline_scale"]))
    full,_,_,_=encode(arrays,np.array(model["feature_center"]),np.array(model["feature_scale"]))
    baseline=prediction(X0,np.array(model["baseline_coeff"]),[0,1])
    pred=baseline+(prediction(full,np.array(model["extra_coeff"]),model["selected_indices"])
            if model["selected_indices"] else 0)
    lab,n=split_rows(arrays)
    per=[]
    rng=np.random.default_rng(SEED)
    for idx,a in enumerate(arrays):
        mask=(lab==idx); ey=y[mask]-pred[mask]; eb=y[mask]-baseline[mask]
        r=np.sqrt(np.mean(ey**2));b=np.sqrt(np.mean(eb**2))
        zero=np.sqrt(np.mean(y[mask]**2))
        block=24*7
        N=len(ey)
        reductions=[]
        for _ in range(300):
            start=rng.integers(0,max(1,N-block+1),size=max(1,int(np.ceil(N/block))))
            sampled=np.concatenate([np.arange(j,min(j+block,N)) for j in start])[:N]
            numer=float(np.mean(ey[sampled]**2));denom=float(np.mean(eb[sampled]**2))
            reductions.append(1-numer/denom)
        per.append(dict(station=a["station"],year=a["year"],n=N,
            candidate_rmse=float(r),baseline_rmse=float(b),
            zero_change_rmse=float(zero),rmse_gain=float(1-r/b),
            squared_error_reduction_ci_95=list(map(float,np.quantile(reductions,[.025,.975])))))
    pooled=1-float(np.sqrt(np.mean((y-pred)**2)))/float(np.sqrt(np.mean((y-baseline)**2)))
    verdict="EMPIRICAL_CANDIDATE_PASS" if pooled>=.15 and all(
      z["n"]>=1000 and z["rmse_gain"]>=.10 and z["squared_error_reduction_ci_95"][0]>0 for z in per
    ) else "REFUSE_NOVEL_LAW_CANDIDATE"
    return {"verdict":verdict,"selected_target":target,"pooled_rmse_gain":pooled,"holdout_stations":per}

def main(path):
    root=Path(path);root.mkdir(parents=True,exist_ok=True)
    rawdir=root/"source_gz";rawdir.mkdir(exist_ok=True)
    base={"prereg_commit":PREREG_COMMIT,"station_2023":SOURCES,"station_2024":SOURCES,"station_2025":HOLDOUT}
    try:
        disc=[fetch(s,DISCOVERY_YEAR,rawdir) for s in SOURCES]
        valid=[fetch(s,VALIDATION_YEAR,rawdir) for s in SOURCES]
        models,names=optimize(disc,valid)
        selected=models[0]
        sealed=dict(protocol=base,raw_training=RAW.copy(),discovery_counts={a["station"]:a["count"] for a in disc},
                    validation_counts={a["station"]:a["count"] for a in valid},
                    candidate_target_validation_rankings=models,selected_model=selected,all_features=names)
        (root/"sealed_before_holdout.json").write_text(json.dumps(sealed,indent=2)+"\n")
        # A real binary filesystem barrier between selection and held-out downloads.
        with open(root/"sealed_before_holdout.json","rb") as fp:hash_before=hashlib.sha256(fp.read()).hexdigest()
        print("SEALED_PRE_HOLDOUT",hash_before,selected["target"],selected["selected_terms"],flush=True)
        test=[fetch(s,HOLDOUT_YEAR,rawdir) for s in HOLDOUT]
        evaluated=sample_errors(test,selected,names)
        evaluated.update(dict(model_seal_sha256=hash_before,raw_downloads=RAW,
            strict_2025_holdout_after_seal=True,all_candidate_2024_scores=[
             dict(target=x["target"],score=x["score"],terms=x["selected_terms"]) for x in models],
            source="NOAA_NDBC_RAW_HOURLY_OBSERVATIONS",
            warning="This is a sensor forecasting pattern and NOT proof of causal novelty."))
        (root/"audit.json").write_text(json.dumps(evaluated,indent=2)+"\n")
        print("REAL_OCEAN_RESULT",json.dumps(evaluated)[:6000],flush=True)
    except Exception as e:
        result=dict(verdict="INFEASIBLE",reason=str(e),raw_downloads=RAW,
          pre_holdout_sealed=(root/"sealed_before_holdout.json").exists())
        (root/"audit.json").write_text(json.dumps(result,indent=2)+"\n")
        print("INFEASIBLE",json.dumps(result),flush=True)
if __name__=="__main__":
    main(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_novel_ocean")
