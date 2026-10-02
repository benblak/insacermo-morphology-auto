from __future__ import annotations
import csv, io, json, math, urllib.request
from collections import defaultdict
from temporal_runtime_v1 import Runtime,DebtEvidence,h

BASE="https://raw.githubusercontent.com/LuisM78/Occupancy-detection-data/master/"
FILES=["datatraining.txt","datatest2.txt"]
def fetch(name):
    with urllib.request.urlopen(BASE+name,timeout=30) as r:return r.read().decode()
def parse(s):
    out=[]
    for row in csv.reader(io.StringIO(s)):
        if not row or row[0]=="" or row[0]=="": continue
        try:
            x=list(map(float,row[2:7])); y=str(int(float(row[7])))
        except Exception: continue
        out.append({"rowid":row[0],"date":row[1],"x":x,"y":y})
    return out
def quantile(a,q):
    a=sorted(a);p=(len(a)-1)*q;lo=int(math.floor(p));hi=int(math.ceil(p))
    return a[lo] if lo==hi else a[lo]+(p-lo)*(a[hi]-a[lo])
def cuts(train,B):
    return [[quantile([r["x"][j] for r in train],(k+1)/B) for k in range(B-1)] for j in range(5)]
def bn(v,c):
    lo=0;hi=len(c)
    while lo<hi:
        m=(lo+hi)//2
        if v>=c[m]:lo=m+1
        else:hi=m
    return lo
def apply(rows,C):
    return [dict(r,z=[bn(v,C[j]) for j,v in enumerate(r["x"])]) for r in rows]
def l1(a,b):return sum(abs(x-y) for x,y in zip(a,b))
def mindist(z,pts):return min(l1(z,p) for p in pts)
def unique_train(rows):
    m={}
    for r in rows:
        k=tuple(r["z"])
        if k in m and m[k]!=r["y"]: raise RuntimeError("mixed TRAIN signature at B512")
        m[k]=r["y"]
    return [{"z":list(k),"y":y} for k,y in m.items()]

train_raw=parse(fetch("datatraining.txt")); future_raw=parse(fetch("datatest2.txt"))
B=512;C=cuts(train_raw,B);train=apply(train_raw,C);future=apply(future_raw,C);worlds=unique_train(train)
bad0={a:[w["z"] for w in worlds if w["y"]!=a] for a in ("0","1")}
contract_hash=h({"task":"occupancy","actions":["0","1"]})
observer_hash=h({"B":B,"features":["Temperature","Humidity","Light","CO2","HumidityRatio"],"cuts":C})
byday=defaultdict(list)
for r in future:byday[r["date"][:10]].append(r)

# Discover future observer fractures independently of the debt audit.
sig=defaultdict(lambda:{"labels":set(),"rows":[]})
for r in future:
    e=sig[tuple(r["z"])];e["labels"].add(r["y"])
    if len(e["rows"])<4:e["rows"].append({"date":r["date"],"y":r["y"],"rowid":r["rowid"]})
fractures=[{"signature":list(k),"labels":sorted(v["labels"]),"rows":v["rows"]} for k,v in sig.items() if len(v["labels"])>1]

# Oracle audit: current-day labels are deliberately used ONLY to build a true debt upper bound.
# This is a theorem-validation audit, not a deployable online detector.
oracle_days=[];oracle_total={"n":0,"act":0,"correct":0,"wrong":0,"refuse":0,"ambiguous":0}
for day,rows in sorted(byday.items()):
    D={}
    for a in ("0","1"):
        current_bad=[r for r in rows if r["y"]!=a]
        D[a]=max([mindist(r["z"],bad0[a]) for r in current_bad],default=0)
    counts={"n":len(rows),"act":0,"correct":0,"wrong":0,"refuse":0,"ambiguous":0}
    for r in rows:
        admiss=[]
        for a in ("0","1"):
            rho=mindist(r["z"],bad0[a])
            if rho>D[a]:admiss.append(a)
        if len(admiss)==1:
            counts["act"]+=1
            if admiss[0]==r["y"]:counts["correct"]+=1
            else:counts["wrong"]+=1
        elif len(admiss)==0:counts["refuse"]+=1
        else:counts["ambiguous"]+=1
    counts["debt"]=D;counts["coverage"]=counts["act"]/counts["n"];counts["accuracy"]=counts["correct"]/counts["act"] if counts["act"] else None
    oracle_days.append({"day":day,**counts})
    for k in ("n","act","correct","wrong","refuse","ambiguous"):oracle_total[k]+=counts[k]
oracle_total["coverage"]=oracle_total["act"]/oracle_total["n"];oracle_total["accuracy"]=oracle_total["correct"]/oracle_total["act"] if oracle_total["act"] else None
assert oracle_total["wrong"]==0, oracle_total

# Delayed audit: yesterday's exact debt is reused today. This is intentionally NOT a certified current upper bound.
# We measure whether such stale evidence would be unsafe if misrepresented as current.
delayed=[];prev=None
for day,rows in sorted(byday.items()):
    if prev is None:
        delayed.append({"day":day,"status":"NO_PRIOR_DEBT"}); prev=oracle_days[0]["debt"]; continue
    c={"n":len(rows),"act":0,"correct":0,"wrong":0,"refuse":0,"ambiguous":0}
    for r in rows:
        admiss=[a for a in ("0","1") if mindist(r["z"],bad0[a])>prev[a]]
        if len(admiss)==1:
            c["act"]+=1;c["correct"]+=admiss[0]==r["y"];c["wrong"]+=admiss[0]!=r["y"]
        elif len(admiss)==0:c["refuse"]+=1
        else:c["ambiguous"]+=1
    c["used_previous_day_debt"]=prev;c["coverage"]=c["act"]/c["n"];c["accuracy"]=c["correct"]/c["act"] if c["act"] else None
    delayed.append({"day":day,**c})
    prev=next(x["debt"] for x in oracle_days if x["day"]==day)

out={"status":"PASS","scope":"RETROSPECTIVE THEOREM AUDIT; oracle debt uses current-day outcomes and is not deployable online",
     "B":B,"train_n":len(train),"future_n":len(future),"train_unique":len(worlds),
     "contract_hash":contract_hash,"observer_hash":observer_hash,
     "oracle_total":oracle_total,"oracle_days":oracle_days,
     "delayed_previous_day_debt":delayed,
     "future_observer_fractures":fractures}
open("temporal_runtime/OCCUPANCY_ORACLE_AUDIT.json","w").write(json.dumps(out,indent=2))
print(json.dumps({"oracle_total":oracle_total,"n_observer_fractures":len(fractures),"delayed":delayed},indent=2))
