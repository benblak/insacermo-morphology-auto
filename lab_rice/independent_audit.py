#!/usr/bin/env python3
"""Independent frozen-results audit. Recompute conservative one-sided exact
Clopper-Pearson bounds via a different numerical formula. No refit or tuning.
Explicitly assert positive and negative real decisions in hidden holdout.
"""
import sys,json,math
from pathlib import Path

def exact_cdf(n,k,p):
    if p<=0:return 1.
    if p>=1:return float(k>=n)
    return sum(math.comb(n,j)*(p**j)*((1-p)**(n-j)) for j in range(k+1))

def cp_upper(n,k,alpha):
    if n==0 or k==n:return 1.
    lo=0.; hi=1.
    for _ in range(70):
        mid=(lo+hi)/2
        if exact_cdf(n,k,mid)>alpha:
            lo=mid
        else:
            hi=mid
    return (lo+hi)/2

d=json.loads(Path(sys.argv[1]).read_text())
assert d["data"]["n"]==3810
assert d["split"]=={"train":2286,"calibration":762,"test":762}
assert d["preregistration"]["n_models"]==12
assert d["preregistration"]["target_conditional_error"]==0.05
assert abs(d["preregistration"]["alpha_per_policy"]-0.05/12)<1e-12
C=d["calibration"]; assert len(C)==12
for m in C:
    c=m["calibration"]; n=c["acted"];e=c["errors"]
    exact=cp_upper(n,e,0.05/12)
    assert abs(m["upper"]-exact)<1e-10,(m["name"],m["upper"],exact)
    assert m["certified"]==(exact<=0.05)
    assert n+c["refused"]==c["n"]==762
    assert c["positive_actions"]+c["negative_actions"]==n
    assert c["false_positive_actions"]+c["false_negative_actions"]==e
for kind in ("INSACERMO_SIG","BASELINE_CENTROID"):
    eligible=[m for m in C if m["kind"]==kind and m["certified"]]
    eligible.sort(key=lambda m:(-m["calibration"]["acted"],m["name"]))
    expected=eligible[0]["name"] if eligible else None
    assert d["holdout"][kind]["selected"]==expected
s=d["holdout"]["INSACERMO_SIG"]
assert s["selected"]=="sig3_support20"
t=s["results"]
assert t["acted"]==268 and t["errors"]==3 and t["positive_actions"]==120
assert t["true_positive_actions"]==118 and t["false_positive_actions"]==2
assert t["negative_actions"]==148 and t["false_negative_actions"]==1
assert t["acted"]+t["refused"]==t["n"]==762
assert d["holdout"]["BASELINE_CENTROID"]["selected"] is None
print("CONFIRMATORY PROTOCOL: PASS")
print("INDEPENDENT CP INTERVALS: PASS (all 12, alpha 0.05/12)")
print("SELECTION FROZEN: sig3_support20 (276 calibrated decisions, 3 errors)")
print("PRIMARY 95% simultaneous upper risk bound:",format(next(m["upper"] for m in C if m["name"]=="sig3_support20"),".8f"))
print("UNSEEN: 268 acts; 120 Cammeo predictions, of which 118 correct; 3 total errors.")
print("SELECTED CENTROID BASELINE: none eligible at risk 5%; REFUSE.")
print("LIMIT: result specific to this UCI benchmark and predeclared policy family.")
