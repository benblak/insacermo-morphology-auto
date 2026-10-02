from __future__ import annotations
import csv, io, json, math, urllib.request
from collections import defaultdict

BASE="https://raw.githubusercontent.com/LuisM78/Occupancy-detection-data/master/"
FILES=["datatraining.txt","datatest2.txt"]
B=512
ACTIONS=("0","1")

def fetch(name):
    with urllib.request.urlopen(BASE+name,timeout=30) as r:
        return r.read().decode()

def parse(s):
    out=[]
    for row in csv.reader(io.StringIO(s)):
        if not row:
            continue
        try:
            x=list(map(float,row[2:7])); y=str(int(float(row[7])))
        except Exception:
            continue
        out.append({"rowid":row[0],"date":row[1],"x":x,"y":y})
    return out

def quantile(a,q):
    a=sorted(a); p=(len(a)-1)*q; lo=int(math.floor(p)); hi=int(math.ceil(p))
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
    return [dict(r,z=[bn(v,C[j]) for j,v in enumerate(r["x"])]) for r in rows]

def l1(a,b): return sum(abs(x-y) for x,y in zip(a,b))

class KD:
    __slots__=("p","axis","left","right","mn","mx")
    def __init__(self,points,depth=0):
        axis=depth%5; points=sorted(points,key=lambda p:p[axis]); m=len(points)//2
        self.p=points[m]; self.axis=axis
        self.left=KD(points[:m],depth+1) if m else None
        self.right=KD(points[m+1:],depth+1) if m+1<len(points) else None
        self.mn=list(self.p); self.mx=list(self.p)
        for c in (self.left,self.right):
            if c:
                for j in range(5):
                    self.mn[j]=min(self.mn[j],c.mn[j]); self.mx[j]=max(self.mx[j],c.mx[j])

def bboxdist(z,n):
    s=0
    for j in range(5):
        if z[j]<n.mn[j]: s+=n.mn[j]-z[j]
        elif z[j]>n.mx[j]: s+=z[j]-n.mx[j]
    return s

def mindist_kd(z,n,best=10**18):
    if n is None or bboxdist(z,n)>=best: return best
    d=l1(z,n.p)
    if d<best: best=d
    first,second=(n.left,n.right) if z[n.axis]<=n.p[n.axis] else (n.right,n.left)
    best=mindist_kd(z,first,best)
    return mindist_kd(z,second,best)

def unique_train(rows):
    m={}
    for r in rows:
        k=tuple(r["z"])
        if k in m and m[k]!=r["y"]:
            raise RuntimeError("mixed TRAIN signature at B512")
        m[k]=r["y"]
    return [{"z":list(k),"y":y} for k,y in m.items()]

train_raw=parse(fetch("datatraining.txt"))
future_raw=parse(fetch("datatest2.txt"))
C=cuts(train_raw,B)
train=apply(train_raw,C)
future=apply(future_raw,C)
worlds=unique_train(train)

bad0={a:[w["z"] for w in worlds if w["y"]!=a] for a in ACTIONS}
bad0_kd={a:KD(bad0[a]) for a in ACTIONS}

byday=defaultdict(list)
for r in future:
    byday[r["date"][:10]].append(r)
days=sorted(byday)

# Cache rho_0(z,a) for every future row. This uses only frozen training data and the current observation.
for r in future:
    r["rho"]={a:mindist_kd(r["z"],bad0_kd[a]) for a in ACTIONS}

# Evaluation-only oracle daily debt. Never fed into the strict or empirical policy for the same day.
oracle_debt={}
for day in days:
    rows=byday[day]
    oracle_debt[day]={}
    for a in ACTIONS:
        current_bad=[r for r in rows if r["y"]!=a]
        oracle_debt[day][a]=max([r["rho"][a] for r in current_bad],default=0)

def score_day(rows,bounds):
    c={"n":len(rows),"act":0,"correct":0,"wrong":0,"refuse":0,"ambiguous":0}
    for r in rows:
        admiss=[a for a in ACTIONS if r["rho"][a] > bounds[a]]
        if len(admiss)==1:
            c["act"]+=1
            if admiss[0]==r["y"]: c["correct"]+=1
            else: c["wrong"]+=1
        elif len(admiss)==0:
            c["refuse"]+=1
        else:
            c["ambiguous"]+=1
    c["coverage"]=c["act"]/c["n"] if c["n"] else None
    c["accuracy"]=c["correct"]/c["act"] if c["act"] else None
    return c

def aggregate(day_records):
    t={"n":0,"act":0,"correct":0,"wrong":0,"refuse":0,"ambiguous":0}
    for rec in day_records:
        if rec.get("status")=="NO_CERTIFIED_CURRENT_BOUND":
            t["n"]+=rec["n"]; t["refuse"]+=rec["n"]
            continue
        for k in t: t[k]+=rec[k]
    t["coverage"]=t["act"]/t["n"] if t["n"] else None
    t["accuracy"]=t["correct"]/t["act"] if t["act"] else None
    return t

# POLICY 1 — strict deployable reading of Certified Online Debt V1:
# yesterday's exact debt is not a current certificate, and this dataset supplies no exogenous
# physical/regime growth guarantee. Therefore the adapter has no legitimate D_t to pass to ACT.
strict=[]
for day in days:
    strict.append({"day":day,"n":len(byday[day]),"status":"NO_CERTIFIED_CURRENT_BOUND",
                   "reason":"dataset supplies labels after observation but no certified current-debt source or exogenous drift bound"})
strict_total=aggregate(strict)

# POLICY 2 — tempting but uncertified causal empirical cap:
# at start of day t, only debts of previous completed days may be used.
# Growth cap = largest positive daily increase observed so far. Until at least one transition exists,
# there is no cap and we refuse. This is deliberately NOT called certified.
empirical=[]
past_days=[]
for i,day in enumerate(days):
    rows=byday[day]
    if i<2:
        empirical.append({"day":day,"n":len(rows),"status":"NO_EMPIRICAL_GROWTH_HISTORY"})
        past_days.append(day)
        continue
    g={}
    for a in ACTIONS:
        inc=[]
        for j in range(1,i):
            d0=oracle_debt[days[j-1]][a]; d1=oracle_debt[days[j]][a]
            inc.append(max(0,d1-d0))
        g[a]=max(inc) if inc else 0
    prev=oracle_debt[days[i-1]]
    bounds={a:prev[a]+g[a] for a in ACTIONS}
    sc=score_day(rows,bounds)
    empirical.append({"day":day,**sc,"previous_exact_debt":prev,"empirical_growth_cap":g,"bounds":bounds,
                      "certified":False})
    past_days.append(day)
empirical_total=aggregate(empirical)

# POLICY 3 — diagnostic: smallest constant action-specific per-day growth cap that would
# upper-bound ALL observed future day-to-day debt increases. This is computed with future labels
# and is therefore NOT deployable; it quantifies the external guarantee that would have been sufficient.
required_g={}
for a in ACTIONS:
    required_g[a]=max([max(0,oracle_debt[days[i]][a]-oracle_debt[days[i-1]][a]) for i in range(1,len(days))], default=0)

required_cap_days=[]
for i,day in enumerate(days):
    rows=byday[day]
    if i==0:
        required_cap_days.append({"day":day,"n":len(rows),"status":"NO_PRIOR_DEBT"})
        continue
    prev=oracle_debt[days[i-1]]
    bounds={a:prev[a]+required_g[a] for a in ACTIONS}
    sc=score_day(rows,bounds)
    required_cap_days.append({"day":day,**sc,"previous_exact_debt":prev,
                              "required_external_growth_cap":required_g,"bounds":bounds,
                              "deployable_if_and_only_if_cap_is_guaranteed_exogenously":True})
required_cap_total=aggregate(required_cap_days)

# Shared-cap diagnostic for comparison.
shared_g=max(required_g.values())
shared_days=[]
for i,day in enumerate(days):
    rows=byday[day]
    if i==0:
        shared_days.append({"day":day,"n":len(rows),"status":"NO_PRIOR_DEBT"})
        continue
    prev=oracle_debt[days[i-1]]
    bounds={a:prev[a]+shared_g for a in ACTIONS}
    sc=score_day(rows,bounds)
    shared_days.append({"day":day,**sc,"previous_exact_debt":prev,"shared_external_growth_cap":shared_g,"bounds":bounds})
shared_total=aggregate(shared_days)

# Observation-only causal envelope at the instant of decision.
# U_t(a)=max rho_a among observations seen so far including current row. It is label-free and safe
# for the seen prefix because bad_seen is a subset of all_seen, but strict rho>U can never hold
# for the current row. This experimentally mirrors No-Free-Debt.
prefix={"n":0,"act":0,"correct":0,"wrong":0,"refuse":0,"ambiguous":0}
prefix_days=[]
for day in days:
    running={a:0 for a in ACTIONS}
    c={"day":day,"n":0,"act":0,"correct":0,"wrong":0,"refuse":0,"ambiguous":0}
    for r in byday[day]:
        c["n"]+=1
        for a in ACTIONS:
            running[a]=max(running[a],r["rho"][a])
        admiss=[a for a in ACTIONS if r["rho"][a] > running[a]]
        if len(admiss)==1:
            c["act"]+=1
            if admiss[0]==r["y"]: c["correct"]+=1
            else: c["wrong"]+=1
        elif len(admiss)==0: c["refuse"]+=1
        else: c["ambiguous"]+=1
    c["coverage"]=c["act"]/c["n"]; c["accuracy"]=c["correct"]/c["act"] if c["act"] else None
    prefix_days.append(c)
    for k in ("n","act","correct","wrong","refuse","ambiguous"): prefix[k]+=c[k]
prefix["coverage"]=prefix["act"]/prefix["n"]; prefix["accuracy"]=prefix["correct"]/prefix["act"] if prefix["act"] else None

# Verify the external-cap diagnostic is theorem-consistent.
for i in range(1,len(days)):
    for a in ACTIONS:
        assert oracle_debt[days[i]][a] <= oracle_debt[days[i-1]][a] + required_g[a]
assert required_cap_total["wrong"]==0, required_cap_total
assert shared_total["wrong"]==0, shared_total
assert prefix["act"]==0, prefix

out={
 "status":"PASS",
 "scope":"ONLINE NO-ORACLE AUDIT. Current-day labels are used only after decisions for scoring and for next-day delayed debt.",
 "B":B,
 "train_n":len(train),
 "future_n":len(future),
 "days":days,
 "oracle_debt_for_evaluation_only":oracle_debt,
 "strict_no_external_authority":{"days":strict,"total":strict_total},
 "observation_only_prefix_envelope":{"days":prefix_days,"total":prefix},
 "causal_empirical_growth_cap_NOT_CERTIFIED":{"days":empirical,"total":empirical_total},
 "retrospective_required_external_growth_cap_DIAGNOSTIC_ONLY":{
    "required_action_specific_growth_cap":required_g,
    "days":required_cap_days,
    "total":required_cap_total
 },
 "retrospective_required_shared_growth_cap_DIAGNOSTIC_ONLY":{
    "required_shared_growth_cap":shared_g,
    "days":shared_days,
    "total":shared_total
 },
 "interpretation":{
   "strict":"No legitimate current debt certificate exists in the supplied dataset alone, so old ACT is not recycled.",
   "observation_only":"A safe unlabeled prefix envelope includes the current point and therefore cannot satisfy the strict reserve inequality for that point.",
   "empirical":"A growth cap inferred only from past observed days is a heuristic, not a proof; any wrong ACT falsifies treating it as certified.",
   "external_cap":"The retrospective cap is not a deployable estimate. It quantifies the strength of an exogenous guarantee that, if independently certified before deployment, would make delayed debt transport sound."
 }
}
open("certified_online_debt_v1/OCCUPANCY_ONLINE_NO_ORACLE_AUDIT.json","w").write(json.dumps(out,indent=2))
print(json.dumps({
 "strict_total":strict_total,
 "prefix_total":prefix,
 "empirical_total":empirical_total,
 "required_g":required_g,
 "required_cap_total":required_cap_total,
 "shared_g":shared_g,
 "shared_cap_total":shared_total
},indent=2))
