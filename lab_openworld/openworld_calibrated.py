#!/usr/bin/env python3
# coding: utf-8
"""
INSACERMO OPEN-WORLD TEST: frozen protocol written BEFORE any of the target data
are loaded. 2026-11-14. Deliberately separate from frozen MAX TOTAL / C3.

OBJECTIVE: finite-reference logical purity + calibrated statistical risk for
unseen i.i.d. candidates. Not a distribution-free logical guarantee.

Datasets: Official UCI HTRU2 #372 and Online Shoppers #468, no synthetic labels.
Eight numerical features, >= TRAIN median gives binary signature of 8 bits.
Random.Random(20261114 + dataset_code), shuffle rows, 60% train, 20%
calibration, 20% holdout. No stratification or cross-validation.

Four predeclared policies with training signature count >= K in [1, 5, 20, 50]
and exactly one training class; all other signatures REFUSE. No ML model.
Use calibration for one-sided Clopper-Pearson upper 98.75% confidence bound
on P(error | ACT), Bonferroni 4-way at familywise 95% confidence.
Select MAXIMUM calibration coverage of policies with UPPER <= 2%.
If none passes, refuse ALL. Never use holdout for policy selection.

RISK INTERPRETATION: conditional on i.i.d/exchangeability and identical
sampling distribution for calibration and deployment, frozen policy, fixed
candidates, the conditional error of the selected policy is bounded at 2%
with >=95% confidence, via simultaneous intervals. It is not 0-error,
not a guarantee under distribution shift, and can yield low coverage.
Comparative ordinary baselines are mandatory; the protocol has no ML-training
except label-informed signature dictionary and optimized threshold selection.

Holdout is opened once at the very end, after selecting K. Counts, errors,
positive actions, refusals and class-specific recall reported. No retuning.
"""
import collections, csv, hashlib, io, json, math, random, sys, zipfile
from pathlib import Path

ALPHA_TOTAL = 0.05
ALPHA_SINGLE = ALPHA_TOTAL/4
TARGET_RISK = 0.02
KS=(1,5,20,50)
SEED=20261114

CONFIGS = {
  "htru2": {
    "filename":"HTRU_2.csv",
    "uci_url":"https://archive.ics.uci.edu/static/public/372/htru2.zip",
    "feature_indices":tuple(range(8)),
    "rows_expected":17898, "positives_expected":1639,
    "label_col":8,
  },
  "shoppers":{
    "filename":"online_shoppers_intention.csv",
    "uci_url":"https://archive.ics.uci.edu/static/public/468/online+shoppers+purchasing+intention+dataset.zip",
    "columns":("Administrative","Administrative_Duration","Informational",
               "Informational_Duration","ProductRelated","ProductRelated_Duration",
               "BounceRates","ExitRates"),
    "label_col":"Revenue",
    "rows_expected":12330, "positives_expected":1908,
  }
}

def load(which,location):
    config=CONFIGS[which]
    blob=Path(location).read_bytes()
    with zipfile.ZipFile(io.BytesIO(blob)) as z:
        matches=[name for name in z.namelist()
                 if name.lower().endswith(config["filename"].lower())]
        if len(matches)!=1:
            raise RuntimeError("Expected CSV not found uniquely: "+str(z.namelist()))
        raw=z.read(matches[0]).decode("utf-8-sig")
    X=[]; y=[]
    if which=="htru2":
        for record in csv.reader(raw.splitlines()):
            if not record:continue
            X.append(tuple(float(t) for t in record[:8]))
            y.append(int(record[8]))
    else:
        dr=csv.DictReader(io.StringIO(raw))
        for rec in dr:
            X.append(tuple(float(rec[c]) for c in config["columns"]))
            v=rec["Revenue"].strip().upper()
            if v not in ("TRUE","FALSE"):raise ValueError("Invalid revenue "+v)
            y.append(int(v=="TRUE"))
    if len(X)!=config["rows_expected"] or sum(y)!=config["positives_expected"]:
        raise ValueError(f"Dataset mismatch: {which} {len(X)} rows, {sum(y)} positives")
    if not all(math.isfinite(x) for row in X for x in row):
        raise ValueError("Non-finite input")
    return X,y,{
        "archive_sha256":hashlib.sha256(blob).hexdigest(),
        "extracted_csv_sha256":hashlib.sha256(raw.encode("utf-8")).hexdigest(),
        "source":config["uci_url"],
        "rows":len(X), "positives":sum(y),
    }

def median(vals):
    s=sorted(vals);n=len(s)
    return s[n//2] if n%2 else (s[n//2-1]+s[n//2])/2

def signature(row,medians):
    return sum(1<<i for i,v in enumerate(row) if v>=medians[i])

def fit_dict(X,y,train):
    medians=[median([X[i][j] for i in train]) for j in range(8)]
    hist=[[0,0] for _ in range(256)]
    for i in train:hist[signature(X[i],medians)][y[i]]+=1
    return medians,hist

def classify(hist, sig, k):
    a,b=hist[sig]
    if a>=k and b==0:return 0
    if b>=k and a==0:return 1
    return None

def evaluate(data_sig,y,inds,hist,k):
    n=len(inds);acted=err=pos_acted=act_1=wrong_pos=wrong_neg=0
    for ix in inds:
        pred=classify(hist,data_sig[ix],k)
        if pred is None:continue
        acted+=1
        act_1+=pred
        pos_acted+=y[ix]
        if pred!=y[ix]:
            err+=1
            if y[ix]==1:wrong_neg+=1
            else:wrong_pos+=1
    return {
        "n":n, "positives":sum(y[i] for i in inds),"acted":acted,
        "coverage":acted/n,"errors":err,
        "error_given_action":err/acted if acted else None,
        "act_1":act_1,"acted_true_positives":pos_acted,
        "wrong_negatives":wrong_neg, "wrong_positives":wrong_pos,
        "refused":n-acted,
    }

def binom_cdf_at_most(x,n,p):
    if p==0:return 1.0
    if p==1:return float(x>=n)
    t=(1-p)**n
    total=t
    for i in range(x):
        t=t*(n-i)/(i+1)*p/(1-p)
        total+=t
    return min(1.0,total)

def upper_cp(x,n,alpha):
    if n==0 or x==n:return 1.0
    lo=0.0;hi=1.0
    for _ in range(70):
        mid=(lo+hi)/2
        if binom_cdf_at_most(x,n,mid)>alpha:
            lo=mid
        else:
            hi=mid
    return (lo+hi)/2

def execute(which,zip_path,out_path):
    X,y,source=load(which,zip_path)
    rowids=list(range(len(y)))
    rng=random.Random(SEED+(372 if which=="htru2" else 468))
    rng.shuffle(rowids)
    n=len(y)
    train=rowids[:n*6//10]
    calibration=rowids[n*6//10:n*8//10]
    holdout=rowids[n*8//10:]
    medians,hist=fit_dict(X,y,train)
    sig=[signature(row,medians) for row in X]
    calib=[]
    for k in KS:
        result=evaluate(sig,y,calibration,hist,k)
        ub=upper_cp(result["errors"],result["acted"],ALPHA_SINGLE)
        calib.append({"min_reference_support":k,**result,
                      "risk_ub_95pct_familywise":ub,
                      "certifies_risk_2pct":ub<=TARGET_RISK})
    eligible=[r for r in calib if r["certifies_risk_2pct"]]
    eligible.sort(key=lambda r:(-r["acted"],r["min_reference_support"]))
    selected_k=eligible[0]["min_reference_support"] if eligible else None
    if selected_k is None:
        final={"n":len(holdout),"positives":sum(y[i] for i in holdout),
               "acted":0,"coverage":0,"errors":0,"error_given_action":None,
               "act_1":0,"acted_true_positives":0,
               "wrong_negatives":0,"wrong_positives":0,"refused":len(holdout)}
    else:
        final=evaluate(sig,y,holdout,hist,selected_k)
    # Zero-label and always-classify-negative baselines do not depend on calibration.
    always_zero={
        "accepted":len(holdout),
        "errors":sum(y[i] for i in holdout),
        "error_rate":sum(y[i] for i in holdout)/len(holdout)
    }
    result={
        "test":"INSACERMO OPEN WORLD with strictly separate calibration",
        "dataset":which,
        "source":source,
        "split":{"seed":SEED+(372 if which=="htru2" else 468),
                 "train":len(train),"calibration":len(calibration),
                 "holdout":len(holdout)},
        "predetermined":{"thresholds":KS,"alpha_total":ALPHA_TOTAL,
                         "bonferroni_alpha_single":ALPHA_SINGLE,
                         "risk_target":TARGET_RISK,
                         "rule":"pure training 8-bit signature with at least K examples; else REFUSE",
                         "selection":"highest calibration coverage with CP upper<=2%, else all REFUSE"},
        "training":{"reference_signatures_nonempty":sum(bool(a+b) for a,b in hist),
                    "reference_signatures_mixed":sum(a>0 and b>0 for a,b in hist),
                    "reference_signatures_pure_positive":sum(a==0 and b>0 for a,b in hist),
                    "reference_signatures_pure_negative":sum(b==0 and a>0 for a,b in hist),
                    "medians":medians},
        "calibration":calib,"selected_k":selected_k,
        "holdout":final,"holdout_baseline_always_negative":always_zero,
        "interpretation":"Calibration confidence is probabilistic under i.i.d. deployment, not deterministic safety or guaranteed performance under shift."
    }
    Path(out_path).parent.mkdir(parents=True,exist_ok=True)
    Path(out_path).write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    print("DATASET",which,"TRAIN",len(train),"CAL",len(calibration),"TEST",len(holdout))
    for v in calib:
        print("CAL_K",v["min_reference_support"],"acted",v["acted"],
              "errors",v["errors"],"upper",round(v["risk_ub_95pct_familywise"],6),
              "risk_2pct_certified",v["certifies_risk_2pct"])
    print("SELECTED_K",selected_k if selected_k is not None else "REFUSE_ALL")
    print("HOLDOUT",json.dumps(final,sort_keys=True))
    print("ALWAYS_NEGATIVE_BASELINE",json.dumps(always_zero,sort_keys=True))
    print("DECLARED_LIMTS: no logical safety outside reference; confidence conditional on iid")
    print("RESULTS",out_path)

if __name__=="__main__":
    if len(sys.argv)!=4:
        sys.exit("usage: python openworld_calibrated.py htru2|shoppers uci_dataset.zip output.json")
    execute(sys.argv[1],sys.argv[2],sys.argv[3])
