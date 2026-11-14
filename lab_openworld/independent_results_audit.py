#!/usr/bin/env python3
"""Independent posthoc audit on the FROZEN JSON outputs.
No classifier modifications. Recomputes Clopper-Pearson using an alternate
binomial formula (math.comb) and checks test/selection consistency.

This adds an independent arithmetic check but does not add a scientific
validation dataset or turn statistical confidence into logical certainty.
"""
import json, math, pathlib, sys

def binom_cdf_direct(n,x,p):
    if p<=0:return 1.0
    if p>=1:return float(x>=n)
    return sum(math.comb(n,i)*(p**i)*((1-p)**(n-i))
               for i in range(x+1))

def upper_bound(n,k,alpha=0.0125):
    if n==0 or k==n:return 1.0
    lo=0.;hi=1.
    for _ in range(75):
        p=(lo+hi)/2
        if binom_cdf_direct(n,k,p)>alpha:lo=p
        else:hi=p
    return (lo+hi)/2

for path in sys.argv[1:]:
    data=json.loads(pathlib.Path(path).read_text())
    assert data["split"]["train"]+data["split"]["calibration"]+data["split"]["holdout"] == data["source"]["rows"]
    assert data["predetermined"]["thresholds"]==[1,5,20,50]
    assert data["predetermined"]["risk_target"]==0.02
    assert data["predetermined"]["bonferroni_alpha_single"]==0.0125
    c=data["calibration"]
    for policy in c:
        independent=upper_bound(policy["acted"],policy["errors"])
        assert abs(independent-policy["risk_ub_95pct_familywise"])<1e-10,(policy,independent)
        assert policy["risk_ub_95pct_familywise"] <=0.02 if policy["certifies_risk_2pct"] else policy["risk_ub_95pct_familywise"]>0.02
    qualifying=[p for p in c if p["risk_ub_95pct_familywise"]<=0.02]
    qualifying.sort(key=lambda p:(-p["acted"],p["min_reference_support"]))
    intended=qualifying[0]["min_reference_support"] if qualifying else None
    assert intended==data["selected_k"]
    t=data["holdout"]
    assert t["acted"]+t["refused"]==t["n"]
    assert t["errors"]==t["wrong_negatives"]+t["wrong_positives"]
    if intended is None:assert t["acted"]==0 and t["errors"]==0
    assert t["n"]==data["split"]["holdout"]
    print(data["dataset"],"PASS INDEPENDENT INTERVALS & SELECTION",
          "selected_k",intended,"test",t["acted"],"accepted",
          t["errors"],"errors; calibration min UBs",
          [round(p["risk_ub_95pct_familywise"],5) for p in c])
print("EXTERNAL_ARITHMETIC_CHECK=PASS")
