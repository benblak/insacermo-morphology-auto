#!/usr/bin/env python3
# coding: utf-8
"""
INSACERMO prospective rice experiment, PRE-REGISTERED before dataset download.

Domain: UCI Rice (Cammeo and Osmancik), id=545, 3810 records and 7 measured
geometric features (real images processed into measurements).
Sources: https://archive.ics.uci.edu/static/public/545/rice+cammeo+and+osmancik.zip
(also a fallback official URL https://archive.ics.uci.edu/static/public/545/rice.zip)
Only the original dataset is used, not preprocessed class balances.

Seed 20261114. Deterministic random split 60/20/20 train / calibration / test.
No retuning after viewing calibration or test.

PRIMARY TARGET: conditional action error <= 5% with at least 95% simultaneous
confidence for 12 predeclared policy candidates. Intervals: one-sided
Clopper-Pearson at alpha=0.05/12. Four support cutoffs K=[1,5,20,50].
Two non-learned binning schemes: TRAIN median (2 bins), TRAIN terciles (3 bins).
A cell may predict a class only when all reference observations in its cell
have that class AND sample count >=K. Otherwise REFUSE.

Baseline: continuous 7-feature standardized nearest TRAIN class centroid;
possible actions via rejection thresholds on the signed distance-margin
(minimum standardized distance difference to competing centroid, normalized
to [0,1]). Four fixed thresholds [0.0,0.1,0.2,0.4].
Baseline is not guaranteed in absence of calibration, either.
Same four policy selection rules, same calibration, same risk threshold.

Pick among candidates with confidence bound <=5% the one with greatest
calibration coverage; ties: higher bound? NO, deterministic first in declared
order. If none eligible, REFUSE ALL. Frozen choice evaluated on test.

To protect against ambiguous post-hoc winner claims: report BOTH the
best eligible binning policy and the best eligible centroid policy; compare
coverage under separately selected strategies with conservative familywise
bounds, test held out.

THINGS NOT PROVED:
- iid may fail in real deployment;
- no logical certainty beyond reference cells;
- 5% is a conditional risk statement, not a per-individual guarantee;
- no proof novelty compared to selective classifiers or calibration.
"""
import csv,io,zipfile,hashlib,math,random,json,sys
from pathlib import Path

SEED=20261114
TARGET=0.05
ALPHA=0.05/12
KS=(1,5,20,50)
BINS=(2,3)
CENTROID_THRESHOLDS=(0.0,0.1,0.2,0.4)
URL="https://archive.ics.uci.edu/static/public/545/rice+cammeo+and+osmancik.zip"

def load(path):
    blob=Path(path).read_bytes()
    with zipfile.ZipFile(io.BytesIO(blob)) as z:
        files=z.namelist()
        arffs=[n for n in files if n.lower().endswith(".arff")]
        csvs=[n for n in files if n.lower().endswith(".csv")]
        xlsx=[n for n in files if n.lower().endswith(".xlsx")]
        if arffs:
            data=z.read(arffs[0]).decode("utf-8-sig",errors="replace")
            records=[]
            in_data=False
            for line in data.splitlines():
                line=line.strip()
                if not line or line.startswith("%"): continue
                if line.lower()=="@data":in_data=True;continue
                if in_data:records.append(next(csv.reader([line])))
        elif csvs:
            data=z.read(csvs[0]).decode("utf-8-sig",errors="replace")
            records=list(csv.reader(data.splitlines()))
            if records and not is_number(records[0][0]):records=records[1:]
        elif xlsx:
            import openpyxl
            x=openpyxl.load_workbook(io.BytesIO(z.read(xlsx[0])),read_only=True,data_only=True)
            sheet=x.active
            records=[list(row) for row in sheet.iter_rows(values_only=True)]
            if records and not is_number(records[0][0]):records=records[1:]
        else:
            raise ValueError("No ARFF, CSV, or XLSX in zip: "+repr(files))
    X=[];labels=[]
    for row in records:
        if not row or row[0] is None:continue
        if len(row)<8:raise ValueError("Expected seven numeric features and label: "+str(row))
        v=tuple(float(z) for z in row[:7])
        if not all(math.isfinite(a) for a in v):raise ValueError("Nonfinite")
        target=str(row[7]).strip().strip('"').strip("'").lower()
        if target not in ("cammeo","osmancik"):raise ValueError("Unexpected target: "+target)
        X.append(v); labels.append(int(target=="cammeo"))
    if len(X)!=3810:
        raise ValueError(f"Expected 3810 rows, got {len(X)}")
    return X,labels,dict(zip_name=Path(path).name,source=URL,zip_sha256=hashlib.sha256(blob).hexdigest(),
                        zip_members=files,n=len(X),class_1=sum(labels))

def is_number(value):
    try: float(value);return True
    except (TypeError,ValueError):return False

def quantile(sorted_values,fraction):
    t=(len(sorted_values)-1)*fraction
    lo=math.floor(t);hi=math.ceil(t)
    return sorted_values[lo]*(hi-t)+sorted_values[hi]*(t-lo) if hi!=lo else sorted_values[lo]

def discretizer(X,train,n_bins):
    thresholds=[]
    for j in range(7):
        values=sorted(X[i][j] for i in train)
        thresholds.append(tuple(quantile(values,k/n_bins) for k in range(1,n_bins)))
    def encode(row):
        return tuple(sum(x>=q for q in qs) for x,qs in zip(row,thresholds))
    return encode,thresholds

def dictionary_predictor(X,y,train,bins,k):
    encode,thresholds=discretizer(X,train,bins)
    h={}
    for i in train:
        key=encode(X[i])
        counts=h.setdefault(key,[0,0])
        counts[y[i]]+=1
    def predict(row):
        a,b=h.get(encode(row),(0,0))
        if a>=k and b==0:return 0
        if b>=k and a==0:return 1
        return None
    return predict,dict(num_cells=len(h),
                        pure_0=sum(a and not b for a,b in h.values()),
                        pure_1=sum(b and not a for a,b in h.values()),
                        mixed=sum(a and b for a,b in h.values()),
                        thresholds=thresholds)

def centroid_model(X,y,train,margin_threshold):
    mean=[sum(X[i][j] for i in train)/len(train) for j in range(7)]
    stdev=[math.sqrt(sum((X[i][j]-mean[j])**2 for i in train)/len(train)) for j in range(7)]
    stdev=[v if v>0 else 1 for v in stdev]
    groups=[[i for i in train if y[i]==c] for c in (0,1)]
    centroids=[tuple(sum((X[i][j]-mean[j])/stdev[j] for i in groups[c])/len(groups[c]) for j in range(7))
               for c in (0,1)]
    def predict(row):
        z=tuple((row[j]-mean[j])/stdev[j] for j in range(7))
        ds=[math.sqrt(sum((z[j]-cen[j])**2 for j in range(7))) for cen in centroids]
        winner=0 if ds[0]<=ds[1] else 1
        # A signed normalized gap in [0,1]; strictly greater than threshold.
        gap=abs(ds[0]-ds[1])/(ds[0]+ds[1]+1e-12)
        return winner if gap > margin_threshold else None
    return predict,{"margin_threshold":margin_threshold,"train_centroids":centroids}

def evaluate(X,y,indices,predict):
    out=dict(n=len(indices),acted=0,errors=0,refused=0,positive_actions=0,
             true_positive_actions=0,false_positive_actions=0,
             false_negative_actions=0,negative_actions=0,
             positives=sum(y[i] for i in indices),negatives=sum(1-y[i] for i in indices))
    for i in indices:
        a=predict(X[i])
        if a is None:out["refused"]+=1;continue
        out["acted"]+=1
        out["positive_actions"]+=int(a==1)
        out["negative_actions"]+=int(a==0)
        out["true_positive_actions"]+=int(a==y[i]==1)
        out["false_positive_actions"]+=int(a==1 and y[i]==0)
        out["false_negative_actions"]+=int(a==0 and y[i]==1)
        out["errors"]+=int(a!=y[i])
    out["coverage"]=out["acted"]/out["n"]
    out["conditional_error"]=out["errors"]/out["acted"] if out["acted"] else None
    return out

def cdf_le(x,n,p):
    if p<=0:return 1.
    if p>=1:return float(x==n)
    # n <= 800; stable starting from (1-p)^n, p in small range near 0.05.
    term=(1-p)**n
    total=term
    for j in range(x):
        term=term*(n-j)/(j+1)*p/(1-p)
        total+=term
    return min(1.,total)

def cp_upper(x,n):
    if n==0 or x==n:return 1.
    lo=0.;hi=1.
    for _ in range(70):
        mid=(lo+hi)/2
        if cdf_le(x,n,mid)>ALPHA:lo=mid
        else:hi=mid
    return (lo+hi)/2

def main():
    if len(sys.argv)!=3:sys.exit("usage: rice.py official_uci_rice.zip output.json")
    X,y,source=load(sys.argv[1])
    ids=list(range(len(y)));random.Random(SEED).shuffle(ids)
    n=len(y);train=ids[:n*6//10];cal=ids[n*6//10:n*8//10];test=ids[n*8//10:]
    models=[]
    for bins in BINS:
        for k in KS:
            predict,details=dictionary_predictor(X,y,train,bins,k)
            models.append((f"sig{bins}_support{k}","INSACERMO_SIG",predict,details))
    for threshold in CENTROID_THRESHOLDS:
        predict,details=centroid_model(X,y,train,threshold)
        models.append((f"centroid_margin{threshold}","BASELINE_CENTROID",predict,details))
    assert len(models)==12
    cals=[]
    for name,kind,predict,details in models:
        r=evaluate(X,y,cal,predict)
        ub=cp_upper(r["errors"],r["acted"])
        cals.append(dict(name=name,kind=kind,calibration=r,upper=ub,
                         certified=ub<=TARGET,details=details))
    def choose(kind):
        eligible=[r for r in cals if r["kind"]==kind and r["certified"]]
        eligible.sort(key=lambda r:(-r["calibration"]["acted"],r["name"]))
        return eligible[0] if eligible else None
    holdout={}
    for kind in ("INSACERMO_SIG","BASELINE_CENTROID"):
        chosen=choose(kind)
        if chosen is None:
            holdout[kind]=dict(selected=None,results=dict(
                n=len(test),acted=0,refused=len(test),coverage=0,errors=0,
                positive_actions=0,false_positive_actions=0,false_negative_actions=0))
        else:
            selected=next((predict for name,k,predict,_ in models if name==chosen["name"] and kind==k))
            holdout[kind]=dict(selected=chosen["name"],results=evaluate(X,y,test,selected))
    majority=int(sum(y[i] for i in train) > len(train)/2)
    baseline_majority=evaluate(X,y,test,lambda row:majority)
    outcome=dict(
      preregistration=dict(seed=SEED,split="60/20/20 shuffled seed 20261114",
        n_models=12,target_conditional_error=TARGET,familywise_confidence=0.95,
        alpha_per_policy=ALPHA,
        primary="risk-qualified coverage, both target classes",
        classification_criterion="reference-pure bin median/tercile cells with min K",
        selection="best eligible calibration coverage by method; otherwise refuse all",
        holdout_not_used_for_selection=True,
        comparator="standardized nearest train centroid with four fixed margins"),
      data=source,split=dict(train=len(train),calibration=len(cal),test=len(test)),
      calibration=cals,holdout=holdout,
      baseline_majority_test=baseline_majority)
    path=Path(sys.argv[2]);path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(outcome,indent=2,ensure_ascii=False)+"\n")
    print("DATA_SOURCE",source)
    print("SPLIT",len(train),len(cal),len(test),"class1",source["class_1"])
    for m in cals:
        r=m["calibration"]
        print("CAL",m["name"],"ACT",r["acted"],"POSITIVES",r["positive_actions"],
              "ERRORS",r["errors"],"UB",round(m["upper"],6),"PASS",m["certified"])
    for kind,res in holdout.items():
        print("TEST",kind,"SELECTED",res["selected"],
              "RESULTS",json.dumps(res["results"],sort_keys=True))
    print("MAJORITY_BASELINE",json.dumps(baseline_majority,sort_keys=True))
    print("PROTOCOL_FROZEN_PASS")
    print("RESULT_JSON",path)

if __name__=="__main__":
    main()
