#!/usr/bin/env python3
"""Independent posthoc numerical audit for PRE-REGISTERED Dry Bean trial.
No model changes, no holdout tuning.

Uses scipy.stats.beta.ppf, a different mathematical route from the original
finite binomial-series bisection. Checks all 17 one-sided Clopper-Pearson
confidence bounds, all group choices, and class totals.
"""
import json,sys,math
from pathlib import Path
from scipy.stats import beta

d=json.loads(Path(sys.argv[1]).read_text())
assert d["dataset"]["n"]==13611
assert d["split"]=={"train":8166,"calibration":2722,"holdout":2723}
assert d["protocol"]["bonferroni_candidates"]==17
assert d["protocol"]["same_features_for_all_methods"]==8
alpha=.05/17
rows=d["calibration"]
assert len(rows)==17
for r in rows:
    z=r["calibration"];n=z["acted"];k=z["errors"]
    upper=1.0 if n==0 or k==n else float(beta.ppf(1-alpha,k+1,n-k))
    assert abs(upper-r["upper_error"])<1e-10,(r["name"],upper,r["upper_error"])
    assert r["eligible"]==(upper<=.05)
    assert z["acted"]+z["refused"]==z["n"]==2722
    assert sum(g["n"] for g in z["true_class_results"].values())==2722
    assert sum(g["acted"] for g in z["true_class_results"].values())==n
    assert sum(g["errors"] for g in z["true_class_results"].values())==k

for method in ("FINITE_REF","LOGISTIC","RANDOM_FOREST"):
    options=[r for r in rows if r["method"]==method and r["eligible"]]
    options.sort(key=lambda r:(-r["calibration"]["acted"],r["name"]))
    expected=options[0]["name"] if options else None
    assert d["selected"][method]==expected
    test=d["holdout"][method]
    assert test["acted"]+test["refused"]==test["n"]==2723
    assert sum(g["n"] for g in test["true_class_results"].values())==2723
    assert sum(g["acted"] for g in test["true_class_results"].values())==test["acted"]
    assert sum(g["errors"] for g in test["true_class_results"].values())==test["errors"]
    assert sum(test["predicted_class_counts"].values())==test["acted"]
    selection=next((r for r in rows if r["name"]==expected),None)
    print(method,"selected",expected,
          "CAL_upper",selection["upper_error"] if selection else "REFUSE_ALL",
          "test_act",test["acted"],"test_errors",test["errors"],
          "test_error_rate",test["conditional_error"],
          "test_coverage",test["coverage"])
    print("CLASS COUNTS",json.dumps(test["true_class_results"],sort_keys=True))
assert d["holdout"]["FINITE_REF"]["acted"]==557
assert d["holdout"]["FINITE_REF"]["errors"]==5
assert len([v for v in d["holdout"]["FINITE_REF"]["true_class_results"].values() if v["correct"]>0])==5
assert d["holdout"]["LOGISTIC"]["acted"]==2007
assert d["holdout"]["RANDOM_FOREST"]["acted"]==2068
print("INDEPENDENT 17-WAY EXACT BINOMIAL AUDIT: PASS")
print("IMPORTANT: all risk statements are statistical under IID; no Lean generalization proof.")
