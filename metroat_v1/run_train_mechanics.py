#!/usr/bin/env python3
from __future__ import annotations
import argparse, hashlib, json, math, os, re
from pathlib import Path
import numpy as np
import pandas as pd
import pyarrow.parquet as pq

FUTURE = ["TRAIN_IS_IN_FAILURE","TRAIN_FAILURE_TYPE","TRAIN_IS_IN_MAINTENANCE","TRAIN_MAINTENANCE_TYPE"]
TIME = ["TIMESTAMP","year","month","day"]
AGG = ["AMBIENT_TEMPERATURE","TRAIN_SPEED_ACTUAL"]
OP = ["TRAIN_BRAKE_SIGNAL","TRAIN_AUTOMATIC_MODE","TRAIN_MANUAL_MODE","TRAIN_EMERGENCY_MODE",
      "TRAIN_LINE","TRAIN_CURRENT_SECTION","TRAIN_IS_SPECIAL_SECTION"]
PREFIXES=[4,8,16,32,64,128]
HOURS=[1,6,24,72,168]

def is_binary(n):
    return (n.endswith("_COMPRESSOR_RUNNING") or
            "_SPRING_BRAKE_ACTIVE_BOGIE" in n or
            n.endswith("_PNEUMATIC_BRAKE_ACTIVE") or
            "_PROPORTIONAL_VALVE_PRESSURE_AVAILABLE_BOGIE" in n)

def feature_order(cols):
    return sorted(cols, key=lambda x: hashlib.sha256(x.encode()).hexdigest())

def classify(cols):
    obs=[c for c in cols if c not in FUTURE+TIME]
    binary=[c for c in obs if is_binary(c)]
    operational=[c for c in OP if c in obs]
    aggregated=[c for c in AGG if c in obs]
    continuous=[c for c in obs if c not in set(binary+operational+aggregated)]
    exp=(len(continuous),len(binary),len(operational),len(aggregated),len(obs))
    if exp != (72,20,7,2,101):
        raise RuntimeError(f"schema count mismatch {exp}")
    return continuous,binary,operational,aggregated

def last_nonnull(s):
    x=s.dropna()
    return x.iloc[-1] if len(x) else np.nan

def minute_table(dayfile, cont, binary, op, agg):
    cols=FUTURE+["TIMESTAMP"]+cont+binary+op+agg
    df=pq.read_table(dayfile, columns=cols).to_pandas()
    df["TIMESTAMP"]=pd.to_datetime(df["TIMESTAMP"])
    df=df.sort_values("TIMESTAMP")
    df["MINUTE"]=df["TIMESTAMP"].dt.floor("min")
    g=df.groupby("MINUTE", sort=True)
    out=pd.DataFrame(index=g.size().index)
    # current values: last non-null observed in minute
    for c in cont+agg+binary+op:
        out[c+"__current"]=g[c].agg(last_nonnull)
    # event flags over raw 1Hz rows inside minute
    out["EV_FAIL"]=g["TRAIN_IS_IN_FAILURE"].agg(lambda s: bool(pd.Series(s).fillna(False).astype(bool).any()))
    out["EV_FAILTYPE"]=g["TRAIN_FAILURE_TYPE"].agg(lambda s: bool((pd.Series(s).dropna().astype(str).str.strip().ne("")) & (pd.Series(s).dropna().astype(str).str.strip().ne("No Failure"))).any())
    out["EV_MAINT"]=g["TRAIN_IS_IN_MAINTENANCE"].agg(lambda s: bool(pd.Series(s).fillna(False).astype(bool).any()))
    out["EV_MAINTTYPE"]=g["TRAIN_MAINTENANCE_TYPE"].agg(lambda s: bool((pd.Series(s).dropna().astype(str).str.strip().ne("")) & (pd.Series(s).dropna().astype(str).str.strip().ne("No Revision"))).any())
    return out

def build_split(root):
    files=sorted(Path(root).rglob("*.parquet"))
    if not files: raise RuntimeError("no parquet files")
    schema=pq.read_schema(files[0])
    cont,binary,op,agg=classify(schema.names)
    chunks=[]
    for i,f in enumerate(files,1):
        chunks.append(minute_table(f,cont,binary,op,agg))
        if i%25==0: print("DAYS",i,"/",len(files),flush=True)
    m=pd.concat(chunks).sort_index()
    m=m[~m.index.duplicated(keep="last")]
    # trailing features on minute grid; gaps remain gaps
    for c in cont+agg:
        cur=m[c+"__current"]
        m[c+"__mean60"]=cur.rolling(window=60,min_periods=1).mean()
        m[c+"__delta60"]=cur-cur.shift(60)
    for c in binary+op:
        cur=m[c+"__current"]
        # any change in last 60 observed minute states
        m[c+"__changed60"]=cur.ne(cur.shift()).rolling(window=60,min_periods=1).max().astype(float)
    derived=[c for c in m.columns if "__" in c]
    derived=feature_order(derived)
    return m,derived,{"continuous":cont,"binary":binary,"operational":op,"aggregated":agg}

def future_bits(m,Hmin):
    # strict continuity: every minute t+1..t+H exists.
    idx=m.index
    full=pd.date_range(idx.min(),idx.max(),freq="min")
    x=m.reindex(full)
    present=pd.Series(x.index.isin(idx),index=full).astype(int)
    # require current + next H minutes all present
    need=present.iloc[::-1].rolling(Hmin+1,min_periods=Hmin+1).sum().iloc[::-1].eq(Hmin+1)
    bits=[]
    for c in ["EV_FAIL","EV_FAILTYPE","EV_MAINT","EV_MAINTTYPE"]:
        s=x[c].fillna(False).astype(int)
        # events strictly after t, through t+H
        fut=s.shift(-1).iloc[::-1].rolling(Hmin,min_periods=Hmin).max().iloc[::-1].fillna(0).astype(int)
        bits.append(fut)
    sig=(bits[0]+2*bits[1]+4*bits[2]+8*bits[3]).astype("Int64")
    sig[~need]=pd.NA
    return sig.reindex(idx)

def fit_thresholds(m,features):
    out={}
    for f in features:
        s=pd.to_numeric(m[f],errors="coerce").dropna()
        out[f]={"q2":[float(s.quantile(.5))] if len(s) else [],
                "q4":[float(s.quantile(.25)),float(s.quantile(.5)),float(s.quantile(.75))] if len(s) else []}
    return out

def encode(m,features,thresholds,q):
    arr=np.empty((len(m),len(features)),dtype=np.int16)
    for j,f in enumerate(features):
        s=m[f]
        vals=pd.to_numeric(s,errors="coerce").to_numpy(dtype=float)
        cuts=np.array(thresholds[f][q],dtype=float)
        code=np.searchsorted(cuts,vals,side="right").astype(np.int16)
        code[np.isnan(vals)]=-1
        arr[:,j]=code
    return arr

def homogeneous_flags(code,sig,k):
    valid=~pd.isna(sig).to_numpy()
    if k=="ALL": kk=code.shape[1]
    else: kk=min(int(k),code.shape[1])
    if valid.sum()==0: return np.zeros(len(sig),dtype=bool)
    df=pd.DataFrame(code[valid,:kk])
    df["_sig"]=sig.to_numpy()[valid].astype(int)
    nun=df.groupby(list(range(kk)),dropna=False)["_sig"].transform("nunique").to_numpy()
    out=np.zeros(len(sig),dtype=bool); out[np.where(valid)[0]]=nun==1
    return out

def train_report(m,features,thresholds):
    report={"n_minutes":len(m),"n_features":len(features),"horizons":{}}
    codes={q:encode(m,features,thresholds,q) for q in ["q2","q4"]}
    settings=[]
    for q in ["q2","q4"]:
        for k in PREFIXES+["ALL"]:
            settings.append((q,k))
    for Hh in HOURS:
        sig=future_bits(m,Hh*60)
        flags={(q,str(k)):homogeneous_flags(codes[q],sig,k) for q,k in settings}
        current=flags[("q2","16")]
        # probe if any later frozen refinement resolves
        resolver=np.zeros(len(m),dtype=bool)
        for q,k in settings:
            if q=="q2" and k in [4,8,16]: continue
            resolver |= flags[(q,str(k))]
        valid=~pd.isna(sig).to_numpy()
        act=current & valid
        probe=(~current)&resolver&valid
        refuse=(~current)&(~resolver)&valid
        report["horizons"][str(Hh)]={
            "support_status":"SUPPORTED" if int(valid.sum())>0 else "UNSUPPORTED_BY_CONTINUITY",
            "eligible":int(valid.sum()),
            "ACT":int(act.sum()),"PROBE":int(probe.sum()),"REFUSE":int(refuse.sum()),
            "event_signature_counts":{str(k):int(v) for k,v in pd.Series(sig.dropna().astype(int)).value_counts().sort_index().items()}
        }
    return report

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--root",required=True); ap.add_argument("--out",required=True)
    a=ap.parse_args()
    out=Path(a.out); out.mkdir(parents=True,exist_ok=True)
    m,features,cats=build_split(a.root)
    thresholds=fit_thresholds(m,features)
    rep=train_report(m,features,thresholds)
    (out/"TRAIN_THRESHOLDS.json").write_text(json.dumps(thresholds,indent=2))
    (out/"FEATURE_ORDER.json").write_text(json.dumps(features,indent=2))
    (out/"CATEGORY_RECEIPT.json").write_text(json.dumps(cats,indent=2))
    (out/"TRAIN_MECHANICS_REPORT.json").write_text(json.dumps(rep,indent=2))
    print(json.dumps(rep,indent=2))
if __name__=="__main__": main()
