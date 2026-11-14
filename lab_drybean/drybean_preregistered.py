#!/usr/bin/env python3
# coding: utf-8
"""
INSACERMO — DRY BEAN multi-class out-of-domain experiment.
PRE-REGISTERED before downloading/reading UCI Dry Bean dataset in this branch.

DATA: UCI Dry Bean Dataset #602, https://archive.ics.uci.edu/static/public/602/dry+bean+dataset.zip
13,611 instances, 16 numerical geometric features, 7 real bean varieties.
Scientific origin: Koklu & Ozkan, Multiclass classification of dry beans using computer vision.
Split random.Random(20261114) shuffle ALL row indices: 60% train, 20% calibration, 20% untouched holdout.
No stratification, no inspection of test labels during policy selection.

FAIR PRIMARY COMPARISON: SAME FIRST EIGHT original numeric features across methods.
- INSACERMO-like finite-world policies: fixed TRAIN quantiles bin counts
  2, 3, 4 for each of 8 features, signature (8-tuple);
  act c iff cell has >=k training members ALL of same class, otherwise REFUSE.
  k in (3, 10, 30) -> exactly 9 predeclared policies. No learned weights/NN.
- Logistic Regression: train StandardScaler + LogisticRegression max_iter 600;
  take argmax posterior only if max posterior >= t in (.55,.70,.85,.95).
- Random Forest: 250 trees, min_samples_leaf=3, random_state=20261114,
  n_jobs=1; same t in (.55,.70,.85,.95).
  These ML competitors are deliberately stronger, and use same eight features.
- 17 total frozen candidate policies (9+4+4), family-wise 95% confidence:
  upper exact Clopper-Pearson conditional error at alpha=.05/17.
- Target maximum conditional error <= .05. Per method group, select policy
  of greatest CALIBRATION action coverage among eligible; tie deterministic
  by lexicographic policy name. If none eligible, all REFUSE.
- Holdout only evaluated for the 3 selected policies after calibration.
- Report coverage, acted, errors, predicted classes, classwise correct and
  errors (and full per-class refusals), plus majority and class frequencies.
- The threshold was chosen in advance. No data-driven revision of model family.
- This is an experiment in *statistical selective classification* under
  iid/exchangeable deployment. A Clopper-Pearson confidence statement is
  NOT a logical guarantee for unknown/future observations or distribution shift.
- Counting questions/energy savings is NOT part of this experiment.

Source ARFF is preferred; if the UCI package only supplies XLSX, use openpyxl.
Credit UCI Dry Bean #602 (https://doi.org/10.24432/C50S4B).
The full INSACERMO MAX TOTAL engine is NOT run here or modified.
"""
import csv,io,zipfile,hashlib,random,math,json,sys,collections
from pathlib import Path

SOURCE="https://archive.ics.uci.edu/static/public/602/dry+bean+dataset.zip"
SEED=20261114
RISK=0.05
CANDIDATES=17
ALPHA=0.05/CANDIDATES
FEATURES=8
QS=(2,3,4)
KS=(3,10,30)
THRESHOLDS=(.55,.70,.85,.95)
LABELS=("BARBUNYA","BOMBAY","CALI","DERMASON","HOROZ","SEKER","SIRA")

def read_uci(path):
    raw=Path(path).read_bytes()
    with zipfile.ZipFile(io.BytesIO(raw)) as z:
        names=z.namelist()
        arff=[n for n in names if n.lower().endswith(".arff") and "dry" in n.lower()]
        if not arff:
            arff=[n for n in names if n.lower().endswith(".arff")]
        if arff:
            lines=z.read(arff[0]).decode("utf-8-sig",errors="replace").splitlines()
            in_data=False; records=[]
            for line in lines:
                line=line.strip()
                if not line or line.startswith("%"):continue
                if line.lower()=="@data":
                    in_data=True;continue
                if in_data:
                    records.append(next(csv.reader([line])))
            picked=arff[0]
        else:
            xlsx=[n for n in names if n.lower().endswith(".xlsx")]
            if not xlsx:raise RuntimeError("Cannot find ARFF/XLSX. Members: "+repr(names))
            import openpyxl
            wb=openpyxl.load_workbook(io.BytesIO(z.read(xlsx[0])),read_only=True,data_only=True)
            rows=list(wb.active.iter_rows(values_only=True))
            records=rows[1:]
            picked=xlsx[0]
    X=[];Y=[]
    for record in records:
        if not record or record[0] is None:continue
        if len(record)<17:raise ValueError("Expected sixteen features plus label: "+repr(record))
        x=tuple(float(v) for v in record[:FEATURES])
        if not all(math.isfinite(v) for v in x):raise ValueError("Nonfinite feature")
        label=str(record[16]).strip().strip('"').strip("'").upper()
        if label not in LABELS:raise ValueError("Unexpected label "+repr(label))
        X.append(x);Y.append(LABELS.index(label))
    if len(X)!=13611:raise ValueError(f"Expected 13611 instances; got {len(X)}")
    return X,Y,{"original_zip_sha256":hashlib.sha256(raw).hexdigest(),
         "source":SOURCE,"chosen_source_member":picked,
         "original_features":16,"used_features":FEATURES,"n":len(X),
         "class_counts":dict(collections.Counter(LABELS[y] for y in Y))}

def quantile(sorted_values,p):
    n=len(sorted_values);t=(n-1)*p
    a=math.floor(t);b=math.ceil(t)
    if a==b:return sorted_values[a]
    return sorted_values[a]*(b-t)+sorted_values[b]*(t-a)

def signature_models(X,Y,train):
    output=[]
    for bins in QS:
        quantiles=tuple(tuple(quantile(sorted(X[i][j] for i in train),k/bins)
                            for k in range(1,bins)) for j in range(FEATURES))
        def sig(row,qq=quantiles):
            return tuple(sum(v>=x for x in thresholds)
                         for v,thresholds in zip(row,qq))
        hist={}
        for i in train:
            key=sig(X[i]);arr=hist.setdefault(key,[0]*len(LABELS));arr[Y[i]]+=1
        for k in KS:
            def pred(row,sig=sig,hist=hist,k=k):
                counts=hist.get(sig(row),[0]*len(LABELS))
                if sum(counts)<k:return None
                winners=[c for c,n in enumerate(counts) if n>0]
                return winners[0] if len(winners)==1 else None
            output.append((f"sig{bins}_k{k}","FINITE_REF",pred,
                           {"bins":bins,"min_support":k,
                            "n_reference_cells":len(hist),
                            "pure_cells":sum(sum(x)>0 and sum(v>0 for v in x)==1 for x in hist.values()),
                            "mixed_cells":sum(sum(v>0 for v in x)>1 for x in hist.values())}))
    return output

def baseline_models(X,Y,train):
    import numpy as np
    from sklearn.pipeline import make_pipeline
    from sklearn.preprocessing import StandardScaler
    from sklearn.linear_model import LogisticRegression
    from sklearn.ensemble import RandomForestClassifier
    A=np.asarray(X,dtype=float);B=np.asarray(Y,dtype=int)
    models=[
        ("LOGISTIC",make_pipeline(StandardScaler(),LogisticRegression(max_iter=600,random_state=SEED))),
        ("RANDOM_FOREST",RandomForestClassifier(n_estimators=250,min_samples_leaf=3,random_state=SEED,n_jobs=1))
    ]
    out=[]
    for name,model in models:
        model.fit(A[train],B[train])
        prob=model.predict_proba(A)
        classes=list(model.classes_)
        predclass=[classes[int(np.argmax(row))] for row in prob]
        maxprob=[float(max(row)) for row in prob]
        # Map object identity of X[i] to row index (same objects passed to pred).
        identity={id(row):i for i,row in enumerate(X)}
        for t in THRESHOLDS:
            def pred(row,t=t,pc=predclass,mp=maxprob,idx=identity):
                i=idx[id(row)]
                return int(pc[i]) if mp[i]>=t else None
            out.append((f"{name}_confidence{t}",name,pred,
                        {"confidence_threshold":t,"trained":True}))
    return out

def evaluate(X,Y,indices,fn):
    classes={label:{"n":0,"acted":0,"correct":0,"errors":0,"refused":0} for label in LABELS}
    acted=errors=pos=0; pred_counts=collections.Counter()
    for i in indices:
        y=Y[i];cc=classes[LABELS[y]];cc["n"]+=1
        prediction=fn(X[i])
        if prediction is None:
            cc["refused"]+=1
            continue
        acted+=1;cc["acted"]+=1
        pred_counts[LABELS[prediction]]+=1
        if prediction==y: cc["correct"]+=1
        else:cc["errors"]+=1;errors+=1
    return {"n":len(indices),"acted":acted,"errors":errors,
            "refused":len(indices)-acted,
            "coverage":acted/len(indices),
            "conditional_error":(errors/acted if acted else None),
            "predicted_class_counts":dict(pred_counts),
            "true_class_results":classes}

def cdf_small(n,x,p):
    if p<=0:return 1.0
    if p>=1:return float(x>=n)
    term=(1-p)**n
    val=term
    for j in range(x):
        term=term*(n-j)/(j+1)*(p/(1-p))
        val+=term
    return min(1.,val)

def cp_upper(n,x,alpha=ALPHA):
    if n==0 or x==n:return 1.0
    lo,hi=0.,1.
    for _ in range(64):
        mid=(lo+hi)/2
        if cdf_small(n,x,mid)>alpha:lo=mid
        else:hi=mid
    return (lo+hi)/2

def main():
    if len(sys.argv)!=3:sys.exit("usage: drybean_preregistered.py official_uci.zip output.json")
    X,Y,source=read_uci(sys.argv[1])
    indices=list(range(len(Y)))
    random.Random(SEED).shuffle(indices)
    n=len(indices);train=indices[:n*6//10];cal=indices[n*6//10:n*8//10];test=indices[n*8//10:]
    models=signature_models(X,Y,train)+baseline_models(X,Y,train)
    assert len(models)==CANDIDATES
    cal_results=[]
    for name,method,fn,details in models:
        r=evaluate(X,Y,cal,fn)
        ub=cp_upper(r["acted"],r["errors"])
        cal_results.append({"name":name,"method":method,"details":details,
                            "calibration":r,"upper_error":ub,"eligible":ub<=RISK})
    chosen={}
    test_results={}
    for method in ("FINITE_REF","LOGISTIC","RANDOM_FOREST"):
        valid=[r for r in cal_results if r["method"]==method and r["eligible"]]
        valid.sort(key=lambda r:(-r["calibration"]["acted"],r["name"]))
        choice=valid[0]["name"] if valid else None
        chosen[method]=choice
        if choice is None:
            test_results[method]={"n":len(test),"acted":0,"errors":0,"refused":len(test),"coverage":0.,
                "true_class_results":{label:{"n":sum(Y[i]==j for i in test),"acted":0,"errors":0,
                    "correct":0,"refused":sum(Y[i]==j for i in test)} for j,label in enumerate(LABELS)}}
        else:
            fn=next(fn for name,m,fn,details in models if name==choice and m==method)
            test_results[method]=evaluate(X,Y,test,fn)
    output={"protocol":{"registration":"source committed before data download",
             "dataset_id":602,"seed":SEED,"split":"60/20/20 random shuffle",
             "same_features_for_all_methods":FEATURES,
             "risk_target":RISK,"familywise_confidence":0.95,
             "bonferroni_candidates":CANDIDATES,
             "alpha_per_candidate":ALPHA,
             "model_families":["FINITE_REF","LOGISTIC","RANDOM_FOREST"],
             "policy_selection":"max calibration acted among eligible within group; else refuse all",
             "holdout_never_used_to_select":True,
             "limit":"statistical guarantee requires iid; not Lean proof of generalization"},
            "dataset":source,"split":{"train":len(train),"calibration":len(cal),"holdout":len(test)},
            "calibration":cal_results,"selected":chosen,"holdout":test_results}
    Path(sys.argv[2]).parent.mkdir(parents=True,exist_ok=True)
    Path(sys.argv[2]).write_text(json.dumps(output,ensure_ascii=False,indent=2)+"\n")
    print("SOURCE",json.dumps(source,sort_keys=True))
    print("SPLIT",len(train),len(cal),len(test))
    for r in cal_results:
        c=r["calibration"]
        print("CAL",r["name"],"acted",c["acted"],"errors",c["errors"],
              "cp_upper",round(r["upper_error"],6),"eligible",r["eligible"])
    for method in chosen:
        r=test_results[method]
        print("HOLDOUT",method,"selected",chosen[method],"coverage",r["coverage"],
              "acted",r["acted"],"errors",r["errors"],
              "predicted_classes",r.get("predicted_class_counts",{}),
              "classes_with_at_least_one_correct_action",
              sum(c["correct"]>0 for c in r["true_class_results"].values()))
    print("FROZEN_PROTOCOL_COMPLETED")
    print("OUTPUT_FILE",sys.argv[2])

if __name__=="__main__":
    main()
