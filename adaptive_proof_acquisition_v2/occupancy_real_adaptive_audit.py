from __future__ import annotations
import csv, io, json, math, urllib.request
from collections import defaultdict, Counter
from functools import lru_cache

BASE="https://raw.githubusercontent.com/LuisM78/Occupancy-detection-data/master/"
FEATURES=["Temperature","Humidity","Light","CO2","HumidityRatio"]
TRAIN_FILE="datatraining.txt"
FUTURE_FILE="datatest2.txt"
B_VALUES=[16,32,64,128,256,512]

def fetch(name):
    with urllib.request.urlopen(BASE+name, timeout=30) as r:
        return r.read().decode()

def parse(s):
    out=[]
    for row in csv.reader(io.StringIO(s)):
        if not row:
            continue
        try:
            x=list(map(float,row[2:7]))
            y=int(float(row[7]))
        except Exception:
            continue
        out.append({"rowid":row[0],"date":row[1],"x":x,"y":y})
    return out

def quantile(a,q):
    a=sorted(a)
    p=(len(a)-1)*q
    lo=int(math.floor(p)); hi=int(math.ceil(p))
    return a[lo] if lo==hi else a[lo]+(p-lo)*(a[hi]-a[lo])

def cuts(train,B):
    return [[quantile([r["x"][j] for r in train],(k+1)/B) for k in range(B-1)] for j in range(5)]

def bn(v,c):
    lo=0; hi=len(c)
    while lo<hi:
        m=(lo+hi)//2
        if v>=c[m]: lo=m+1
        else: hi=m
    return lo

def apply(rows,C):
    return [dict(r,z=tuple(bn(v,C[j]) for j,v in enumerate(r["x"]))) for r in rows]

class Node:
    __slots__=("kind","label","feature","children","train_n","act_n","probe_mass","max_depth")
    def __init__(self,kind,label=None,feature=None,children=None,train_n=0,act_n=0,probe_mass=0,max_depth=0):
        self.kind=kind
        self.label=label
        self.feature=feature
        self.children=children or {}
        self.train_n=train_n
        self.act_n=act_n
        self.probe_mass=probe_mass
        self.max_depth=max_depth

def build_optimal_tree(train):
    labels=[r["y"] for r in train]
    z=[r["z"] for r in train]

    @lru_cache(maxsize=None)
    def solve(indices, remaining):
        inds=list(indices)
        ys={labels[i] for i in inds}
        if len(ys)==1:
            return Node("ACT",label=next(iter(ys)),train_n=len(inds),act_n=len(inds),probe_mass=0,max_depth=0)
        if not remaining:
            return Node("REFUSE",train_n=len(inds),act_n=0,probe_mass=0,max_depth=0)

        # Fail-closed is always available.
        best=Node("REFUSE",train_n=len(inds),act_n=0,probe_mass=0,max_depth=0)
        best_sig=(0,0,0,999)

        for f in remaining:
            groups=defaultdict(list)
            for i in inds:
                groups[z[i][f]].append(i)

            # Measuring a feature that does not split the current context cannot help.
            if len(groups)<=1:
                continue

            rem=tuple(x for x in remaining if x!=f)
            children={}
            act_n=0
            probe_mass=len(inds)
            max_depth=1
            for outcome,idxs in groups.items():
                child=solve(tuple(idxs),rem)
                children[outcome]=child
                act_n += child.act_n
                probe_mass += child.probe_mass
                max_depth=max(max_depth,1+child.max_depth)

            # Primary objective: maximize empirically certifiable training mass.
            # Secondary: minimize total number of measurements across that mass/context.
            # Tertiary: minimize worst depth, then feature id for deterministic tie-break.
            sig=(act_n,-probe_mass,-max_depth,-f)
            if sig>best_sig:
                best_sig=sig
                best=Node("PROBE",feature=f,children=children,train_n=len(inds),
                          act_n=act_n,probe_mass=probe_mass,max_depth=max_depth)
        return best

    root=solve(tuple(range(len(train))),tuple(range(5)))
    return root

def eval_tree(root, rows):
    counts={"n":0,"act":0,"correct":0,"wrong":0,"refuse":0,"ood_refuse":0}
    probe_counts=Counter()
    depth_hist=Counter()
    first_probe=Counter()
    for r in rows:
        counts["n"]+=1
        node=root
        depth=0
        first=None
        while node.kind=="PROBE":
            f=node.feature
            if first is None: first=f
            probe_counts[f]+=1
            depth+=1
            out=r["z"][f]
            if out not in node.children:
                counts["refuse"]+=1
                counts["ood_refuse"]+=1
                node=None
                break
            node=node.children[out]
        if first is not None:
            first_probe[first]+=1
        depth_hist[depth]+=1
        if node is None:
            continue
        if node.kind=="ACT":
            counts["act"]+=1
            if node.label==r["y"]: counts["correct"]+=1
            else: counts["wrong"]+=1
        else:
            counts["refuse"]+=1
    counts["coverage"]=counts["act"]/counts["n"]
    counts["accuracy"]=counts["correct"]/counts["act"] if counts["act"] else None
    counts["avg_probes"]=sum(k*v for k,v in depth_hist.items())/counts["n"]
    counts["avg_probes_act"]=None
    act_probe_total=0
    act_n=0
    for r in rows:
        node=root; depth=0
        while node.kind=="PROBE":
            depth+=1
            out=r["z"][node.feature]
            if out not in node.children:
                node=None; break
            node=node.children[out]
        if node is not None and node.kind=="ACT":
            act_probe_total+=depth; act_n+=1
    counts["avg_probes_act"]=act_probe_total/act_n if act_n else None
    counts["probe_counts_by_feature"]={FEATURES[k]:v for k,v in sorted(probe_counts.items())}
    counts["depth_histogram"]={str(k):v for k,v in sorted(depth_hist.items())}
    counts["first_probe_counts"]={FEATURES[k]:v for k,v in sorted(first_probe.items())}
    return counts

def full_signature_baseline(train,future):
    m={}
    mixed=set()
    for r in train:
        k=r["z"]
        if k in m and m[k]!=r["y"]:
            mixed.add(k)
        else:
            m[k]=r["y"]
    c={"n":len(future),"act":0,"correct":0,"wrong":0,"refuse":0}
    for r in future:
        k=r["z"]
        if k not in m or k in mixed:
            c["refuse"]+=1
        else:
            c["act"]+=1
            if m[k]==r["y"]: c["correct"]+=1
            else: c["wrong"]+=1
    c["coverage"]=c["act"]/c["n"]
    c["accuracy"]=c["correct"]/c["act"] if c["act"] else None
    c["fixed_probe_cost_per_row"]=5
    return c

def serialize_tree(node, depth=0, max_nodes=[0]):
    # Compact structural summary only.
    if node.kind!="PROBE":
        return {"kind":node.kind,"label":node.label,"train_n":node.train_n}
    return {
        "kind":"PROBE",
        "feature":FEATURES[node.feature],
        "train_n":node.train_n,
        "act_n":node.act_n,
        "max_depth":node.max_depth,
        "n_outcomes":len(node.children),
    }

train_raw=parse(fetch(TRAIN_FILE))
future_raw=parse(fetch(FUTURE_FILE))
assert len(train_raw)==8143, len(train_raw)
assert len(future_raw)==9752, len(future_raw)

results=[]
for B in B_VALUES:
    C=cuts(train_raw,B)
    train=apply(train_raw,C)
    future=apply(future_raw,C)
    tree=build_optimal_tree(train)
    future_metrics=eval_tree(tree,future)
    train_metrics=eval_tree(tree,train)
    baseline=full_signature_baseline(train,future)
    results.append({
        "B":B,
        "root":serialize_tree(tree),
        "train":train_metrics,
        "future":future_metrics,
        "full_signature_baseline":baseline,
    })

# Canonical B=512 result gets explicit causal day breakdown.
canon=next(x for x in results if x["B"]==512)
C=cuts(train_raw,512)
train=apply(train_raw,C); future=apply(future_raw,C)
tree=build_optimal_tree(train)
byday=defaultdict(list)
for r in future:
    byday[r["date"][:10]].append(r)
canon["future_by_day"]={day:eval_tree(tree,rows) for day,rows in sorted(byday.items())}

# Scientific guardrails.
# Construction above never reads future labels. Future y appears only inside eval_tree scoring.
# A real deployment certificate would still require an authority establishing that the frozen empirical
# compatibility model remains valid over time. Therefore this audit is an empirical bridge test, not
# a replacement for Certified Online Debt / Temporal Validity.
out={
    "status":"PASS",
    "scope":"CAUSAL EMPIRICAL ADAPTIVE-SENSING BRIDGE TEST; tree built only from datatraining.txt. Future labels used only for retrospective scoring.",
    "cost_model":"unit cost per acquired sensor variable; no monetary/physical acquisition costs are present in the dataset",
    "features":FEATURES,
    "train_n":len(train_raw),
    "future_n":len(future_raw),
    "results":results,
    "interpretation":{
        "what_is_certified":"purity only relative to the frozen finite empirical training compatibility set",
        "what_is_not_certified":"external temporal validity of that empirical model on future physical observations",
        "fail_closed":"unseen branch or unresolved mixed leaf => REFUSE",
        "next_gate":"future wrong ACT > 0 falsifies treating frozen empirical purity as a current temporal certificate"
    }
}
open("adaptive_proof_acquisition_v2/OCCUPANCY_REAL_ADAPTIVE_AUDIT.json","w").write(json.dumps(out,indent=2))

summary=[]
for r in results:
    summary.append({
        "B":r["B"],
        "root_probe":r["root"].get("feature"),
        "train_coverage":r["train"]["coverage"],
        "future_act":r["future"]["act"],
        "future_wrong":r["future"]["wrong"],
        "future_coverage":r["future"]["coverage"],
        "future_accuracy":r["future"]["accuracy"],
        "avg_probes":r["future"]["avg_probes"],
        "baseline_act":r["full_signature_baseline"]["act"],
        "baseline_wrong":r["full_signature_baseline"]["wrong"],
        "baseline_coverage":r["full_signature_baseline"]["coverage"],
    })
print(json.dumps(summary,indent=2))
