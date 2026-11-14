#!/usr/bin/env python3
# coding: utf-8
"""POST-HOC ADVERSARIAL AUDIT of preregistered exoplanet experiment.
No re-selection of exponents; do not claim a novel law or independent
measurement. Partition previously frozen test by discovery method and
compare whether residuals differ; inspect 1-sigma disjoint cases.
"""
import collections,json,sys,statistics,math,random
from pathlib import Path
from exoplanet_law import filter_data,fit_c,score,interval,SEED
rows,info=filter_data(sys.argv[1])
train=[r for r in rows if r["split"]=="train"]
test=[r for r in rows if r["split"]=="test"]
c=fit_c(train,1.5,-.5)
grouped=collections.defaultdict(list)
for r in test:grouped[r["discoverymethod"]].append(r)
methods=[]
for method,subset in sorted(grouped.items(),key=lambda x:-len(x[1])):
    if len(subset)<10:continue
    value=score(subset,1.5,-.5,c)
    interval_valid=0; disjoint=0
    for r in subset:
        b=interval(r)
        if b is None:continue
        interval_valid+=1
        disjoint+=not (b[0]<=1<=b[1])
    methods.append({
        "discoverymethod":method,
        "n":len(subset),
        "median_abs_log_error":value["median_abs_log_error"],
        "within_5pct":value["within_5pct"],
        "1sigma_interval_available":interval_valid,
        "1sigma_disjoint":disjoint
    })
# Compare two common possible circularity signatures:
# number of exactly Kepler-implied a within several thresholds
abs_errs=[abs(math.log(r["P_years"]**2*r["m"]/r["a"]**3)) for r in test]
ratio_spikes={str(t):sum(err<t for err in abs_errs) for t in (1e-5,1e-4,.001,.005,.01,.05,.1)}
# Check known Kepler explicit constant (P in yrs, a in AU, M in solar masses).
# For multiphase/binary/planet mass, this is only an approximation.
outliers=sorted(test,key=lambda r:abs(r["y"]-(c+1.5*r["x"]-.5*r["z"])),reverse=True)[:10]
outlier_rows=[{
    "name":r["pl_name"],"method":r["discoverymethod"],
    "a_au":r["a"],"p_days":r["pl_orbper"],"stellar_mass_solar":r["m"],
    "ratio_R":r["P_years"]**2*r["m"]/r["a"]**3,
    "error_abs_log":abs(r["y"]-(c+1.5*r["x"]-.5*r["z"]))
} for r in outliers]
output={"source":info,"posthoc":True,
        "method_groups":methods,"log_ratio_near_zero_counts":ratio_spikes,
        "outlier_examples":outlier_rows,
        "interpretation":"Method groups and outliers do not prove that a and P were independently measured. The catalogue may be algebraically circular; a real discovery needs original measurement provenance."}
Path(sys.argv[2]).write_text(json.dumps(output,indent=2,ensure_ascii=False)+"\n")
print("POSTHOC METHOD AUDIT")
for m in methods:print("GROUP",m)
print("NEAR_EXACT_RATIO",ratio_spikes)
print("TOP_OUTLIERS",outlier_rows[:4])
print("CRITICAL_CIRCULARITY_WARNING: source publication derivation must be established")
