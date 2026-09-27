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

    parts=[]
    ca=cont+agg
    bo=binary+op

    # Continuous/aggregate 60-second features from raw samples within each calendar minute.
    if ca:
        last=g[ca].agg(last_nonnull).add_suffix("__current")
        mean=g[ca].mean(numeric_only=True).add_suffix("__mean60s")
        first=g[ca].agg(lambda s: (lambda x: x.iloc[0] if len(x) else np.nan)(s.dropna()))
        last_raw=g[ca].agg(last_nonnull)
        delta=(last_raw-first).add_suffix("__delta60s")
        parts.extend([last,mean,delta])

    # Binary/operational current + within-minute change indicator.
    if bo:
        lastbo=g[bo].agg(last_nonnull).add_suffix("__current")
        changed=g[bo].nunique(dropna=True).gt(1).astype(float).add_suffix("__changed60s")
        parts.extend([lastbo,changed])

    out=pd.concat(parts,axis=1)

    # Event channels are future labels only, never predictors.
    out["EV_FAIL"]=g["TRAIN_IS_IN_FAILURE"].agg(lambda s: bool(pd.Series(s).fillna(False).astype(bool).any()))
    out["EV_FAILTYPE"]=g["TRAIN_FAILURE_TYPE"].agg(
        lambda s: bool(((pd.Series(s).dropna().astype(str).str.strip().ne("")) &
                        (pd.Series(s).dropna().astype(str).str.strip().ne("No Failure"))).any()))
    out["EV_MAINT"]=g["TRAIN_IS_IN_MAINTENANCE"].agg(lambda s: bool(pd.Series(s).fillna(False).astype(bool).any()))
    out["EV_MAINTTYPE"]=g["TRAIN_MAINTENANCE_TYPE"].agg(
        lambda s: bool(((pd.Series(s).dropna().astype(str).str.strip().ne("")) &
                        (pd.Series(s).dropna().astype(str).str.strip().ne("No Revision"))).any()))
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
    kvals=PREFIXES+["ALL"]
    settings=[(q,k) for q in ["q2","q4"] for k in kvals]

    for Hh in HOURS:
        sig=future_bits(m,Hh*60)
        flags={(q,str(k)):homogeneous_flags(codes[q],sig,k) for q,k in settings}
        valid=~pd.isna(sig).to_numpy()

        current=flags[("q2","16")]
        # Legal refinements from current: larger prefix at q2, or q4 at k>=16.
        legal=[("q2","32"),("q2","64"),("q2","128"),("q2","ALL"),
               ("q4","16"),("q4","32"),("q4","64"),("q4","128"),("q4","ALL")]
        resolver=np.zeros(len(m),dtype=bool)
        for key in legal: resolver |= flags[key]

        act=current & valid
        probe=(~current)&resolver&valid
        refuse=(~current)&(~resolver)&valid

        # Minimal information frontier in the 2D partial order (q2<q4, k increasing).
        finite=np.zeros(len(m),dtype=bool)
        frontier_counts={}
        for qi,q in enumerate(["q2","q4"]):
            for ki,k in enumerate(kvals):
                key=(q,str(k))
                h=flags[key] & valid
                dominated=np.zeros(len(m),dtype=bool)
                for qj,q0 in enumerate(["q2","q4"]):
                    for kj,k0 in enumerate(kvals):
                        if qj<=qi and kj<=ki and (qj<qi or kj<ki):
                            dominated |= flags[(q0,str(k0))] & valid
                minimal=h & (~dominated)
                if minimal.any():
                    frontier_counts[f"{q},k={k}"]=int(minimal.sum())
                finite |= h
        inf=valid & (~finite)

        # Information destruction relative to intact q4,ALL.
        intact=flags[("q4","ALL")] & valid
        destruction={}
        for k in [4,8,16,32,64,128]:
            destroyed=intact & (~flags[("q4",str(k))])
            destruction[str(k)]=int(destroyed.sum())

        # Refinement monotonicity: homogeneous coarse state may not become heterogeneous finer.
        violations={}
        edges=[]
        for q in ["q2","q4"]:
            for a,b in zip(kvals[:-1],kvals[1:]):
                edges.append(((q,str(a)),(q,str(b))))
        for k in kvals:
            edges.append((("q2",str(k)),("q4",str(k))))
        for a,b in edges:
            v=flags[a] & (~flags[b]) & valid
            violations[f"{a}->{b}"]=int(v.sum())

        report["horizons"][str(Hh)]={
            "support_status":"SUPPORTED" if int(valid.sum())>0 else "UNSUPPORTED_BY_CONTINUITY",
            "eligible":int(valid.sum()),
            "ACT":int(act.sum()),"PROBE":int(probe.sum()),"REFUSE":int(refuse.sum()),
            "finite_D_info":int((finite & valid).sum()),
            "INF_D_info":int(inf.sum()),
            "minimal_frontier_counts":frontier_counts,
            "destruction_vs_q4_ALL":destruction,
            "monotonicity_violations":violations,
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
