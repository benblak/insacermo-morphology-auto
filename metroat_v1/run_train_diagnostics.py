#!/usr/bin/env python3
import json
from pathlib import Path
import pandas as pd
import pyarrow.parquet as pq

FILES=["TRAIN_IS_IN_FAILURE","TRAIN_FAILURE_TYPE","TRAIN_IS_IN_MAINTENANCE","TRAIN_MAINTENANCE_TYPE","TIMESTAMP"]

def main(root,outdir):
    files=sorted(Path(root).rglob("*.parquet"))
    rows=[]
    mins=[]
    fail_types={}
    maint_types={}
    cross_fail={}
    cross_maint={}
    for i,f in enumerate(files,1):
        df=pq.read_table(f,columns=FILES).to_pandas()
        df["TIMESTAMP"]=pd.to_datetime(df["TIMESTAMP"])
        mins.extend(df["TIMESTAMP"].dt.floor("min").dropna().unique().tolist())
        ft=df["TRAIN_FAILURE_TYPE"].astype("string").fillna("<NA>")
        mt=df["TRAIN_MAINTENANCE_TYPE"].astype("string").fillna("<NA>")
        fb=df["TRAIN_IS_IN_FAILURE"].fillna(False).astype(bool)
        mb=df["TRAIN_IS_IN_MAINTENANCE"].fillna(False).astype(bool)
        for k,v in ft.value_counts(dropna=False).items(): fail_types[str(k)]=fail_types.get(str(k),0)+int(v)
        for k,v in mt.value_counts(dropna=False).items(): maint_types[str(k)]=maint_types.get(str(k),0)+int(v)
        for k,v in pd.crosstab(fb,ft).stack().items(): cross_fail[str(k)]=cross_fail.get(str(k),0)+int(v)
        for k,v in pd.crosstab(mb,mt).stack().items(): cross_maint[str(k)]=cross_maint.get(str(k),0)+int(v)
        if i%25==0: print("DAYS",i,"/",len(files),flush=True)
    idx=pd.DatetimeIndex(sorted(pd.unique(pd.to_datetime(mins))))
    diffs=idx.to_series().diff().dropna()
    gaps=diffs[diffs>pd.Timedelta(minutes=1)]
    # contiguous segment lengths in minutes
    seg_lengths=[]
    start=idx[0]; prev=idx[0]
    for t in idx[1:]:
        if t-prev>pd.Timedelta(minutes=1):
            seg_lengths.append(int((prev-start)/pd.Timedelta(minutes=1))+1)
            start=t
        prev=t
    seg_lengths.append(int((prev-start)/pd.Timedelta(minutes=1))+1)
    receipt={
      "n_parquet_files":len(files),
      "n_unique_minutes":len(idx),
      "time_min":str(idx.min()),
      "time_max":str(idx.max()),
      "n_gaps_gt_1min":int(len(gaps)),
      "max_gap_minutes":float(gaps.max()/pd.Timedelta(minutes=1)) if len(gaps) else 0,
      "segment_count":len(seg_lengths),
      "max_contiguous_segment_minutes":max(seg_lengths) if seg_lengths else 0,
      "segments_ge_60m":sum(x>=60 for x in seg_lengths),
      "segments_ge_360m":sum(x>=360 for x in seg_lengths),
      "segments_ge_1440m":sum(x>=1440 for x in seg_lengths),
      "segments_ge_4320m":sum(x>=4320 for x in seg_lengths),
      "segments_ge_10080m":sum(x>=10080 for x in seg_lengths),
      "failure_type_counts":dict(sorted(fail_types.items(), key=lambda kv:-kv[1])[:50]),
      "maintenance_type_counts":dict(sorted(maint_types.items(), key=lambda kv:-kv[1])[:50]),
      "failure_bool_x_type":dict(sorted(cross_fail.items())),
      "maintenance_bool_x_type":dict(sorted(cross_maint.items()))
    }
    out=Path(outdir); out.mkdir(parents=True,exist_ok=True)
    (out/"TRAIN_DIAGNOSTICS.json").write_text(json.dumps(receipt,indent=2))
    print(json.dumps(receipt,indent=2))
if __name__=="__main__":
    import sys
    main(sys.argv[1],sys.argv[2])
