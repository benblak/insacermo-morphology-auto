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


def predict_with_path(root,r):
    node=root
    path=[]
    depth=0
    while node.kind=="PROBE":
        f=node.feature
        out=r["z"][f]
        path.append((f,out))
        depth+=1
        if out not in node.children:
            return {"decision":"REFUSE","label":None,"path":tuple(path),"depth":depth,"ood":True}
        node=node.children[out]
    if node.kind=="ACT":
        return {"decision":"ACT","label":node.label,"path":tuple(path),"depth":depth,"ood":False}
    return {"decision":"REFUSE","label":None,"path":tuple(path),"depth":depth,"ood":False}

def metrics(rows, allow_fn):
    c={"n":0,"act":0,"correct":0,"wrong":0,"refuse":0}
    for r,p in rows:
        c["n"]+=1
        if p["decision"]!="ACT" or not allow_fn(r,p):
            c["refuse"]+=1
        else:
            c["act"]+=1
            if p["label"]==r["y"]: c["correct"]+=1
            else: c["wrong"]+=1
    c["coverage"]=c["act"]/c["n"]
    c["accuracy"]=c["correct"]/c["act"] if c["act"] else None
    return c

train_raw=parse(fetch(TRAIN_FILE))
future_raw=parse(fetch(FUTURE_FILE))
assert len(train_raw)==8143 and len(future_raw)==9752

B=512
C=cuts(train_raw,B)
train=apply(train_raw,C)
future=apply(future_raw,C)
future=sorted(future,key=lambda r:(r["date"],r["rowid"]))
tree=build_optimal_tree(train)

seq=[(r,predict_with_path(tree,r)) for r in future]
base=metrics(seq,lambda r,p: True)

# Causal replay with feedback available after each row.
seen_sig=defaultdict(list)
seen_path=defaultdict(list)
blocked_sig=set()
blocked_path=set()
prev_label=None

guards={
 "exact_signature_confirmed":{"n":0,"act":0,"correct":0,"wrong":0,"refuse":0},
 "leaf_path_confirmed":{"n":0,"act":0,"correct":0,"wrong":0,"refuse":0},
 "previous_label_agrees":{"n":0,"act":0,"correct":0,"wrong":0,"refuse":0},
 "fracture_registry_signature":{"n":0,"act":0,"correct":0,"wrong":0,"refuse":0},
 "fracture_registry_path":{"n":0,"act":0,"correct":0,"wrong":0,"refuse":0},
 "confirmed_path_plus_previous":{"n":0,"act":0,"correct":0,"wrong":0,"refuse":0},
}

wrong_details=[]
wrong_sig_first=0
wrong_path_first=0
wrong_prev_disagrees=0
wrong_prev_agrees=0
wrong_unique_sigs=set()
wrong_unique_paths=set()

def tally(name,allow,r,p):
    g=guards[name]; g["n"]+=1
    if p["decision"]!="ACT" or not allow:
        g["refuse"]+=1
    else:
        g["act"]+=1
        if p["label"]==r["y"]: g["correct"]+=1
        else:g["wrong"]+=1

for i,(r,p) in enumerate(seq):
    sig=r["z"]
    path=p["path"]
    pred=p["label"]
    if p["decision"]=="ACT":
        sig_hist=seen_sig[sig]
        path_hist=seen_path[path]
        sig_confirmed=bool(sig_hist) and all(y==pred for y in sig_hist)
        path_confirmed=bool(path_hist) and all(y==pred for y in path_hist)
        prev_agree=(prev_label is not None and prev_label==pred)
        tally("exact_signature_confirmed",sig_confirmed,r,p)
        tally("leaf_path_confirmed",path_confirmed,r,p)
        tally("previous_label_agrees",prev_agree,r,p)
        tally("fracture_registry_signature",sig not in blocked_sig,r,p)
        tally("fracture_registry_path",path not in blocked_path,r,p)
        tally("confirmed_path_plus_previous",path_confirmed and prev_agree,r,p)

        if pred!=r["y"]:
            first_sig_wrong=not any(y!=pred for y in sig_hist)
            first_path_wrong=not any(y!=pred for y in path_hist)
            if first_sig_wrong: wrong_sig_first+=1
            if first_path_wrong: wrong_path_first+=1
            if prev_label is not None and prev_label!=pred: wrong_prev_disagrees+=1
            if prev_label is not None and prev_label==pred: wrong_prev_agrees+=1
            wrong_unique_sigs.add(sig)
            wrong_unique_paths.add(path)
            if len(wrong_details)<100:
                wrong_details.append({
                    "i":i,"rowid":r["rowid"],"date":r["date"],"true":r["y"],"pred":pred,
                    "path":[[FEATURES[f],out] for f,out in path],
                    "signature":list(sig),
                    "prior_signature_labels":list(sig_hist[-10:]),
                    "prior_path_labels":list(path_hist[-10:]),
                    "previous_label":prev_label,
                    "first_signature_wrong":first_sig_wrong,
                    "first_path_wrong":first_path_wrong,
                })
            blocked_sig.add(sig)
            blocked_path.add(path)
    else:
        for name in guards:
            guards[name]["n"]+=1; guards[name]["refuse"]+=1

    # Feedback arrives only after the current decision.
    seen_sig[sig].append(r["y"])
    seen_path[path].append(r["y"])
    prev_label=r["y"]

for g in guards.values():
    g["coverage"]=g["act"]/g["n"]
    g["accuracy"]=g["correct"]/g["act"] if g["act"] else None

# Retrospective diagnostics only: blacklist from time zero every path/signature that EVER generated
# a wrong ACT. This uses future truth and is NOT deployable. It quantifies how concentrated the failure is.
bad_paths={p["path"] for r,p in seq if p["decision"]=="ACT" and p["label"]!=r["y"]}
bad_sigs={r["z"] for r,p in seq if p["decision"]=="ACT" and p["label"]!=r["y"]}
oracle_path_blacklist=metrics(seq,lambda r,p:p["path"] not in bad_paths)
oracle_sig_blacklist=metrics(seq,lambda r,p:r["z"] not in bad_sigs)

# Day breakdown for base and path-fracture registry.
byday=defaultdict(list)
for rp in seq: byday[rp[0]["date"][:10]].append(rp)

def replay_path_registry(rows):
    blocked=set(); c={"n":0,"act":0,"correct":0,"wrong":0,"refuse":0}
    for r,p in rows:
        c["n"]+=1
        if p["decision"]!="ACT" or p["path"] in blocked:
            c["refuse"]+=1
        else:
            c["act"]+=1
            if p["label"]==r["y"]: c["correct"]+=1
            else:
                c["wrong"]+=1; blocked.add(p["path"])
    c["coverage"]=c["act"]/c["n"]; c["accuracy"]=c["correct"]/c["act"] if c["act"] else None
    return c

out={
 "status":"PASS",
 "scope":"CAUSAL TEMPORAL-AUTHORITY FALSIFICATION AUDIT. Current row truth is revealed only after its decision and can affect later rows.",
 "B":B,
 "base":base,
 "causal_guards":guards,
 "wrong_analysis":{
   "wrong_total":base["wrong"],
   "wrong_unique_signatures":len(wrong_unique_sigs),
   "wrong_unique_paths":len(wrong_unique_paths),
   "wrong_that_are_first_counterexample_for_signature":wrong_sig_first,
   "wrong_that_are_first_counterexample_for_path":wrong_path_first,
   "wrong_with_previous_label_disagreeing_with_prediction":wrong_prev_disagrees,
   "wrong_with_previous_label_agreeing_with_prediction":wrong_prev_agrees,
 },
 "retrospective_DIAGNOSTIC_ONLY":{
   "blacklist_all_ever_bad_paths_from_start":oracle_path_blacklist,
   "blacklist_all_ever_bad_signatures_from_start":oracle_sig_blacklist,
   "n_ever_bad_paths":len(bad_paths),
   "n_ever_bad_signatures":len(bad_sigs),
 },
 "path_registry_by_day_reset_each_day":{day:replay_path_registry(rows) for day,rows in sorted(byday.items())},
 "first_wrong_examples":wrong_details[:20],
 "interpretation":{
   "hard_certificate_status":"NONE_FOUND_FROM_DATASET_ALONE",
   "reason":"Every causal guard tested is an empirical history rule. It can react after a counterexample but cannot certify that the next compatible observation will preserve the same label without an additional invariance/dynamics assumption.",
   "safe_architecture":"Adaptive Proof Acquisition may propose measurements; Certified Online Debt must still reject these empirical guards as hard authorities unless an external guarantee is supplied."
 }
}
open("adaptive_proof_acquisition_v2/OCCUPANCY_TEMPORAL_AUTHORITY_AUDIT.json","w").write(json.dumps(out,indent=2))
print(json.dumps({
 "base":base,
 "causal_guards":guards,
 "wrong_analysis":out["wrong_analysis"],
 "retrospective":out["retrospective_DIAGNOSTIC_ONLY"]
},indent=2))
