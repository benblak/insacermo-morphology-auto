#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path

import numpy as np
import pandas as pd

from run_train_mechanics import build_split, future_bits, encode

COMPONENTS = ("CW1","CW2","MW1","MW2","MW3","MW4")
GLOBAL_RAW = {
    "TRAIN_BRAKE_SIGNAL","TRAIN_AUTOMATIC_MODE","TRAIN_MANUAL_MODE",
    "TRAIN_EMERGENCY_MODE","TRAIN_LINE","TRAIN_CURRENT_SECTION",
    "TRAIN_IS_SPECIAL_SECTION","AMBIENT_TEMPERATURE","TRAIN_SPEED_ACTUAL",
}
CQ = ("q2","q4")
MQ = ("q2","q4")
CDEPTHS = (1,2,4,8,16,"ALL")
MDEPTHS = (1,2,4,8,16,32,"ALL")
HOURS = (1,6)

def sha256_file(path: Path) -> str:
    h=hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda:f.read(1024*1024), b""):
            h.update(chunk)
    return h.hexdigest()

def raw_name(feature: str) -> str:
    return feature.split("__",1)[0]

def group_features(features):
    context=[]
    local={c:[] for c in COMPONENTS}
    unknown=[]
    for f in features:
        raw=raw_name(f)
        if raw in GLOBAL_RAW or raw.startswith("TRAIN_"):
            context.append(f); continue
        matched=False
        for c in COMPONENTS:
            if raw.startswith(c+"_"):
                local[c].append(f); matched=True; break
        if not matched:
            unknown.append(f)
    return context,local,unknown

def effective_prefix(items, depth):
    if depth=="ALL":
        return tuple(items)
    return tuple(items[:min(int(depth),len(items))])

def exact_row_labels(arr: np.ndarray) -> np.ndarray:
    arr=np.ascontiguousarray(arr)
    if arr.ndim != 2:
        raise ValueError("expected 2D array")
    if arr.shape[1]==0:
        return np.zeros(arr.shape[0],dtype=np.int64)
    packed=arr.view(np.dtype((np.void, arr.dtype.itemsize*arr.shape[1]))).ravel()
    _, inv=np.unique(packed, return_inverse=True)
    return inv.astype(np.int64, copy=False)

def homogeneous_flags_pair(ctx, msg, sig, valid):
    idx=np.where(valid)[0]
    out=np.zeros(len(valid),dtype=bool)
    if len(idx)==0:
        return out,0
    c=ctx[idx].astype(np.int64,copy=False)
    m=msg[idx].astype(np.int64,copy=False)
    s=sig.to_numpy()[idx].astype(np.int16,copy=False)
    mbase=int(m.max())+1
    pair=c*mbase+m
    _, inv=np.unique(pair,return_inverse=True)
    mn=np.full(int(inv.max())+1, 32767, dtype=np.int16)
    mx=np.full(int(inv.max())+1, -32768, dtype=np.int16)
    np.minimum.at(mn,inv,s)
    np.maximum.at(mx,inv,s)
    homo=mn==mx
    out[idx]=homo[inv]
    return out,len(mn)

def homogeneous_flags_single(labels, sig, valid):
    zeros=np.zeros(len(labels),dtype=np.int64)
    return homogeneous_flags_pair(labels,zeros,sig,valid)[0]

def setting_key(cq,cd,mq,md):
    return f"{cq},c={cd}|{mq},m={md}"

def level_q(q):
    return 0 if q=="q2" else 1

def level_depth(depth, depths):
    return list(depths).index(depth)

def setting_leq(a,b):
    cq,cd,mq,md=a
    bq,bd,bmq,bmd=b
    return (
        level_q(cq)<=level_q(bq)
        and level_depth(cd,CDEPTHS)<=level_depth(bd,CDEPTHS)
        and level_q(mq)<=level_q(bmq)
        and level_depth(md,MDEPTHS)<=level_depth(bmd,MDEPTHS)
    )

def covers():
    settings=[(cq,cd,mq,md) for cq in CQ for cd in CDEPTHS for mq in MQ for md in MDEPTHS]
    edges=[]
    for a in settings:
        for dim in range(4):
            b=list(a)
            if dim==0 and a[0]=="q2":
                b[0]="q4"
            elif dim==1:
                i=level_depth(a[1],CDEPTHS)
                if i+1<len(CDEPTHS): b[1]=CDEPTHS[i+1]
                else: continue
            elif dim==2 and a[2]=="q2":
                b[2]="q4"
            elif dim==3:
                i=level_depth(a[3],MDEPTHS)
                if i+1<len(MDEPTHS): b[3]=MDEPTHS[i+1]
                else: continue
            else:
                continue
            edges.append((a,tuple(b)))
    return settings,edges

def analyze_component(m, features, thresholds, component, context_features, local_features, codes):
    result={"component":component,"n_context_features":len(context_features),
            "n_local_features":len(local_features),"horizons":{}}

    # Precompute exact observed symbols for every frozen setting on all minute states.
    ctx_labels={}
    msg_labels={}
    feature_pos={f:i for i,f in enumerate(features)}
    for q in CQ:
        full=codes[q]
        for d in CDEPTHS:
            fs=effective_prefix(context_features,d)
            cols=[feature_pos[f] for f in fs]
            ctx_labels[(q,d)]=exact_row_labels(full[:,cols])
        for d in MDEPTHS:
            fs=effective_prefix(local_features,d)
            cols=[feature_pos[f] for f in fs]
            msg_labels[(q,d)]=exact_row_labels(full[:,cols])

    settings,edges=covers()

    for hh in HOURS:
        sig=future_bits(m,hh*60)
        valid=~pd.isna(sig).to_numpy()
        eligible=int(valid.sum())
        flags={}
        setting_rows=[]

        for st in settings:
            cq,cd,mq,md=st
            cf=ctx_labels[(cq,cd)]
            mf=msg_labels[(mq,md)]
            h,joint_cells=homogeneous_flags_pair(cf,mf,sig,valid)
            flags[st]=h
            q_eff=int(np.unique(cf[valid]).size) if eligible else 0
            m_eff=int(np.unique(mf[valid]).size) if eligible else 0
            certified=int(h.sum())
            setting_rows.append({
                "setting":setting_key(*st),
                "context_q":cq,"context_depth":str(cd),
                "message_q":mq,"message_depth":str(md),
                "q_eff":q_eff,"m_eff":m_eff,
                "joint_cells":int(joint_cells),
                "certified_count":certified,
                "certified_rate": certified/eligible if eligible else None,
                "globally_safe": bool(eligible>0 and certified==eligible),
            })

        resolver=np.zeros(len(m),dtype=bool)
        for h in flags.values(): resolver |= h
        finite=resolver & valid
        refuse=valid & ~resolver

        # Minimal settings per state in the representation lattice.
        minimal_counts={}
        for st in settings:
            if not flags[st].any():
                continue
            dominated=np.zeros(len(m),dtype=bool)
            for coarser in settings:
                if coarser==st: continue
                if setting_leq(coarser,st):
                    dominated |= flags[coarser]
            minimal=flags[st] & valid & ~dominated
            n=int(minimal.sum())
            if n:
                minimal_counts[setting_key(*st)]=n

        violations={}
        total_viol=0
        for a,b in edges:
            v=flags[a] & valid & ~flags[b]
            n=int(v.sum())
            violations[f"{setting_key(*a)} -> {setting_key(*b)}"]=n
            total_viol += n

        # Constructed globally-safe resource points and Pareto minima by effective alphabets.
        safe_rows=[r for r in setting_rows if r["globally_safe"]]
        unique_points=sorted({(r["q_eff"],r["m_eff"]) for r in safe_rows})
        pareto=[]
        for p in unique_points:
            if not any(r!=p and r[0]<=p[0] and r[1]<=p[1] for r in unique_points):
                pareto.append(p)

        # Context-only / component-only secondary diagnostics.
        context_only={}
        for cq in CQ:
            for cd in CDEPTHS:
                h=homogeneous_flags_single(ctx_labels[(cq,cd)],sig,valid)
                context_only[f"{cq},c={cd}"]={"certified_count":int(h.sum()),
                    "certified_rate":float(h.sum()/eligible) if eligible else None}
        component_only={}
        for mq in MQ:
            for md in MDEPTHS:
                h=homogeneous_flags_single(msg_labels[(mq,md)],sig,valid)
                component_only[f"{mq},m={md}"]={"certified_count":int(h.sum()),
                    "certified_rate":float(h.sum()/eligible) if eligible else None}

        # Centralized q4,ALL reference, reconstructed exactly from frozen all-feature code.
        central=exact_row_labels(codes["q4"])
        central_flags=homogeneous_flags_single(central,sig,valid)
        central_cert=int(central_flags.sum())

        result["horizons"][str(hh)]={
            "eligible":eligible,
            "finite_interface_D":int(finite.sum()),
            "finite_interface_D_rate":float(finite.sum()/eligible) if eligible else None,
            "REFUSE_interface":int(refuse.sum()),
            "REFUSE_interface_rate":float(refuse.sum()/eligible) if eligible else None,
            "monotonicity_violations_total":int(total_viol),
            "monotonicity_violations":violations,
            "per_state_minimal_frontier_counts":minimal_counts,
            "globally_safe_candidate_settings":safe_rows,
            "constructed_globally_safe_resource_points":[list(x) for x in unique_points],
            "constructed_globally_safe_pareto_points":[list(x) for x in pareto],
            "context_only":context_only,
            "component_only":component_only,
            "centralized_q4_ALL":{
                "certified_count":central_cert,
                "certified_rate":float(central_cert/eligible) if eligible else None,
            },
            "settings":setting_rows,
        }
    return result

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--root",required=True)
    ap.add_argument("--frozen-train",required=True)
    ap.add_argument("--split-name",choices=["TRAIN","TEST"],required=True)
    ap.add_argument("--out",required=True)
    args=ap.parse_args()

    frozen=Path(args.frozen_train)
    tpath=frozen/"TRAIN_THRESHOLDS.json"
    fpath=frozen/"FEATURE_ORDER.json"
    thresholds=json.loads(tpath.read_text())
    features=json.loads(fpath.read_text())

    # Strict provenance invariants.
    if sha256_file(tpath)!="980c95f2cdbdea6ac8c7840d25b9a8e020ffbf18df80a9c4dc00c5a7888fea09":
        raise RuntimeError("frozen TRAIN threshold hash mismatch")
    if sha256_file(fpath)!="1c7f643034d3fd6d76154bd49d5a874ae08c0141f12620a81edb5f9ad5557d5d":
        raise RuntimeError("frozen TRAIN feature order hash mismatch")

    m,test_features,cats=build_split(args.root)
    if set(test_features)!=set(features):
        raise RuntimeError("split feature set differs from frozen TRAIN feature set")

    context_features,locals_map,unknown=group_features(features)
    if unknown:
        raise RuntimeError(f"unassigned frozen features: {unknown[:20]}")
    if set(context_features).intersection(*(set(locals_map[c]) for c in COMPONENTS)):
        raise RuntimeError("context/local overlap")
    flat=set(context_features)
    for c in COMPONENTS: flat.update(locals_map[c])
    if flat!=set(features):
        raise RuntimeError("frozen component partition does not cover all 276 features")

    codes={q:encode(m,features,thresholds,q) for q in CQ}

    report={
        "status":"COMPUTED_UNDER_FROZEN_INTERFACE_PROTOCOL",
        "split":args.split_name,
        "n_minutes":len(m),
        "n_features":len(features),
        "provenance":{
            "retuned_on_this_split":False,
            "thresholds_sha256":sha256_file(tpath),
            "feature_order_sha256":sha256_file(fpath),
            "topology_rule":"COLUMN_PREFIX_FROZEN_BEFORE_ENDPOINT",
        },
        "topology":{
            "context_feature_count":len(context_features),
            "component_feature_counts":{c:len(locals_map[c]) for c in COMPONENTS},
            "context_features":context_features,
        },
        "components":{},
    }
    for c in COMPONENTS:
        print("ANALYZE",c,flush=True)
        report["components"][c]=analyze_component(
            m,features,thresholds,c,context_features,locals_map[c],codes
        )

    out=Path(args.out); out.mkdir(parents=True,exist_ok=True)
    (out/f"{args.split_name}_INTERFACE_PARETO_REPORT.json").write_text(
        json.dumps(report,indent=2)
    )

    # Compact summary CSV.
    rows=[]
    for c,cr in report["components"].items():
        for hh,hr in cr["horizons"].items():
            rows.append({
                "split":args.split_name,"component":c,"horizon_h":int(hh),
                "eligible":hr["eligible"],
                "finite_interface_D":hr["finite_interface_D"],
                "finite_interface_D_rate":hr["finite_interface_D_rate"],
                "REFUSE_interface":hr["REFUSE_interface"],
                "monotonicity_violations_total":hr["monotonicity_violations_total"],
                "centralized_q4_ALL_rate":hr["centralized_q4_ALL"]["certified_rate"],
                "n_globally_safe_candidate_settings":len(hr["globally_safe_candidate_settings"]),
                "n_constructed_pareto_points":len(hr["constructed_globally_safe_pareto_points"]),
                "constructed_pareto_points":json.dumps(hr["constructed_globally_safe_pareto_points"]),
            })
    pd.DataFrame(rows).to_csv(out/f"{args.split_name}_INTERFACE_PARETO_SUMMARY.csv",index=False)
    print(json.dumps({"split":args.split_name,"summary":rows},indent=2))

if __name__=="__main__":
    main()
