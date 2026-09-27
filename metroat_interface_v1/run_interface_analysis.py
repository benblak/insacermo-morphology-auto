#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
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
            context.append(f)
            continue
        hit=False
        for c in COMPONENTS:
            if raw.startswith(c+"_"):
                local[c].append(f)
                hit=True
                break
        if not hit:
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
    packed=arr.view(np.dtype((np.void,arr.dtype.itemsize*arr.shape[1]))).ravel()
    _,inv=np.unique(packed,return_inverse=True)
    return inv.astype(np.int64,copy=False)

def homogeneous_flags_pair(ctx,msg,sig_array,valid):
    idx=np.flatnonzero(valid)
    out=np.zeros(len(valid),dtype=bool)
    if len(idx)==0:
        return out,0
    c=ctx[idx].astype(np.int64,copy=False)
    m=msg[idx].astype(np.int64,copy=False)
    s=sig_array[idx].astype(np.int16,copy=False)
    mbase=int(m.max())+1
    pair=c*mbase+m
    _,inv=np.unique(pair,return_inverse=True)
    ng=int(inv.max())+1
    mn=np.full(ng,32767,dtype=np.int16)
    mx=np.full(ng,-32768,dtype=np.int16)
    np.minimum.at(mn,inv,s)
    np.maximum.at(mx,inv,s)
    homo=mn==mx
    out[idx]=homo[inv]
    return out,ng

def homogeneous_flags_single(labels,sig_array,valid):
    zeros=np.zeros(len(labels),dtype=np.int64)
    return homogeneous_flags_pair(labels,zeros,sig_array,valid)[0]

def setting_key(cq,cd,mq,md):
    return f"{cq},c={cd}|{mq},m={md}"

def qlevel(q):
    return 0 if q=="q2" else 1

def dlevel(d,levels):
    return list(levels).index(d)

def all_settings():
    return [(cq,cd,mq,md) for cq in CQ for cd in CDEPTHS for mq in MQ for md in MDEPTHS]

SETTINGS=all_settings()

def immediate_predecessors(st):
    cq,cd,mq,md=st
    out=[]
    if cq=="q4":
        out.append(("q2",cd,mq,md))
    ci=dlevel(cd,CDEPTHS)
    if ci>0:
        out.append((cq,CDEPTHS[ci-1],mq,md))
    if mq=="q4":
        out.append((cq,cd,"q2",md))
    mi=dlevel(md,MDEPTHS)
    if mi>0:
        out.append((cq,cd,mq,MDEPTHS[mi-1]))
    return out

def immediate_successor_edges():
    edges=[]
    for st in SETTINGS:
        cq,cd,mq,md=st
        if cq=="q2":
            edges.append((st,("q4",cd,mq,md)))
        ci=dlevel(cd,CDEPTHS)
        if ci+1<len(CDEPTHS):
            edges.append((st,(cq,CDEPTHS[ci+1],mq,md)))
        if mq=="q2":
            edges.append((st,(cq,cd,"q4",md)))
        mi=dlevel(md,MDEPTHS)
        if mi+1<len(MDEPTHS):
            edges.append((st,(cq,cd,mq,MDEPTHS[mi+1])))
    return edges

EDGES=immediate_successor_edges()

def topo_key(st):
    return (
        qlevel(st[0])+dlevel(st[1],CDEPTHS)+
        qlevel(st[2])+dlevel(st[3],MDEPTHS),
        qlevel(st[0]),dlevel(st[1],CDEPTHS),
        qlevel(st[2]),dlevel(st[3],MDEPTHS),
    )

def exact_minimal_flags(flags,nrows):
    """Exact union of all strict coarser settings via lattice DP."""
    all_coarser={}
    minimal={}
    for st in sorted(SETTINGS,key=topo_key):
        union=np.zeros(nrows,dtype=bool)
        for pred in immediate_predecessors(st):
            union |= flags[pred]
            union |= all_coarser[pred]
        all_coarser[st]=union
        minimal[st]=flags[st] & ~union
    return minimal

def precompute_group_labels(codes,features,group_features_list,depths):
    pos={f:i for i,f in enumerate(features)}
    out={}
    for q in ("q2","q4"):
        full=codes[q]
        for d in depths:
            fs=effective_prefix(group_features_list,d)
            cols=[pos[f] for f in fs]
            out[(q,d)]=exact_row_labels(full[:,cols])
    return out

def analyze_component(component,local_features,ctx_labels,msg_labels,
                      sigs,valids,central_flags):
    nrows=len(next(iter(ctx_labels.values())))
    result={
        "component":component,
        "n_local_features":len(local_features),
        "horizons":{}
    }
    for hh in HOURS:
        sig=sigs[hh]
        valid=valids[hh]
        eligible=int(valid.sum())
        flags={}
        setting_rows=[]
        for st in SETTINGS:
            cq,cd,mq,md=st
            cf=ctx_labels[(cq,cd)]
            mf=msg_labels[(mq,md)]
            h,joint_cells=homogeneous_flags_pair(cf,mf,sig,valid)
            flags[st]=h
            certified=int(h.sum())
            setting_rows.append({
                "setting":setting_key(*st),
                "context_q":cq,"context_depth":str(cd),
                "message_q":mq,"message_depth":str(md),
                "q_eff":int(np.unique(cf[valid]).size) if eligible else 0,
                "m_eff":int(np.unique(mf[valid]).size) if eligible else 0,
                "joint_cells":int(joint_cells),
                "certified_count":certified,
                "certified_rate":certified/eligible if eligible else None,
                "globally_safe":bool(eligible>0 and certified==eligible),
            })

        resolver=np.zeros(nrows,dtype=bool)
        for h in flags.values():
            resolver |= h
        finite=resolver & valid
        refuse=valid & ~resolver

        minflags=exact_minimal_flags(flags,nrows)
        minimal_counts={}
        for st,h in minflags.items():
            n=int((h&valid).sum())
            if n:
                minimal_counts[setting_key(*st)]=n

        violations={}
        total_viol=0
        for a,b in EDGES:
            n=int((flags[a] & valid & ~flags[b]).sum())
            violations[f"{setting_key(*a)} -> {setting_key(*b)}"]=n
            total_viol += n

        safe_rows=[r for r in setting_rows if r["globally_safe"]]
        points=sorted({(r["q_eff"],r["m_eff"]) for r in safe_rows})
        pareto=[
            p for p in points
            if not any(r!=p and r[0]<=p[0] and r[1]<=p[1] for r in points)
        ]

        context_only={}
        for cq in CQ:
            for cd in CDEPTHS:
                h=homogeneous_flags_single(ctx_labels[(cq,cd)],sig,valid)
                n=int(h.sum())
                context_only[f"{cq},c={cd}"]={
                    "certified_count":n,
                    "certified_rate":n/eligible if eligible else None,
                }
        component_only={}
        for mq in MQ:
            for md in MDEPTHS:
                h=homogeneous_flags_single(msg_labels[(mq,md)],sig,valid)
                n=int(h.sum())
                component_only[f"{mq},m={md}"]={
                    "certified_count":n,
                    "certified_rate":n/eligible if eligible else None,
                }

        cc=int(central_flags[hh].sum())
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
            "constructed_globally_safe_resource_points":[list(x) for x in points],
            "constructed_globally_safe_pareto_points":[list(x) for x in pareto],
            "context_only":context_only,
            "component_only":component_only,
            "centralized_q4_ALL":{
                "certified_count":cc,
                "certified_rate":cc/eligible if eligible else None,
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

    if sha256_file(tpath)!="980c95f2cdbdea6ac8c7840d25b9a8e020ffbf18df80a9c4dc00c5a7888fea09":
        raise RuntimeError("frozen TRAIN threshold hash mismatch")
    if sha256_file(fpath)!="1c7f643034d3fd6d76154bd49d5a874ae08c0141f12620a81edb5f9ad5557d5d":
        raise RuntimeError("frozen TRAIN feature order hash mismatch")

    m,split_features,cats=build_split(args.root)
    if set(split_features)!=set(features):
        raise RuntimeError("split feature set differs from frozen TRAIN feature set")

    context_features,locals_map,unknown=group_features(features)
    if unknown:
        raise RuntimeError(f"unassigned frozen features: {unknown[:20]}")
    flat=set(context_features)
    for c in COMPONENTS:
        if flat.intersection(locals_map[c]):
            raise RuntimeError(f"feature overlap at {c}")
        flat.update(locals_map[c])
    if flat!=set(features):
        raise RuntimeError("frozen component partition does not cover all features")

    print("TOPOLOGY",json.dumps({
        "context":len(context_features),
        **{c:len(locals_map[c]) for c in COMPONENTS}
    },sort_keys=True),flush=True)

    codes={q:encode(m,features,thresholds,q) for q in ("q2","q4")}
    ctx_labels=precompute_group_labels(codes,features,context_features,CDEPTHS)
    local_labels={
        c:precompute_group_labels(codes,features,locals_map[c],MDEPTHS)
        for c in COMPONENTS
    }

    sigs={}
    valids={}
    for hh in HOURS:
        s=future_bits(m,hh*60)
        arr=s.to_numpy()
        valid=~pd.isna(arr)
        sig=np.zeros(len(arr),dtype=np.int16)
        sig[valid]=arr[valid].astype(np.int16)
        sigs[hh]=sig
        valids[hh]=valid

    central_labels=exact_row_labels(codes["q4"])
    central_flags={
        hh:homogeneous_flags_single(central_labels,sigs[hh],valids[hh])
        for hh in HOURS
    }

    report={
        "status":"COMPUTED_UNDER_FROZEN_INTERFACE_PROTOCOL",
        "implementation":"OPTIMIZED_EXACT_V2_SAME_FROZEN_ENDPOINTS",
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
        cr=analyze_component(
            c,locals_map[c],ctx_labels,local_labels[c],
            sigs,valids,central_flags
        )
        cr["n_context_features"]=len(context_features)
        report["components"][c]=cr

    out=Path(args.out)
    out.mkdir(parents=True,exist_ok=True)
    (out/f"{args.split_name}_INTERFACE_PARETO_REPORT.json").write_text(
        json.dumps(report,indent=2)
    )

    rows=[]
    for c,cr in report["components"].items():
        for hh,hr in cr["horizons"].items():
            rows.append({
                "split":args.split_name,
                "component":c,
                "horizon_h":int(hh),
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
    pd.DataFrame(rows).to_csv(
        out/f"{args.split_name}_INTERFACE_PARETO_SUMMARY.csv",index=False
    )
    print(json.dumps({"split":args.split_name,"summary":rows},indent=2))

if __name__=="__main__":
    main()
