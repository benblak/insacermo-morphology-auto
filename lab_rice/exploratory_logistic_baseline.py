#!/usr/bin/env python3
"""
POST-HOC COMPETITOR (not part of preregistered primary benchmark).
StandardScaler + LogisticRegression fitted TRAIN ONLY.
Four predeclared acceptance confidence cutoffs [.70,.80,.90,.95].
Calibration selection using one-sided 95% FWER Clopper-Pearson alpha=.05/4.
Evaluate the SAME holdout used in preregistered report, with FULL TRANSPARENCY:
This extra comparator was chosen after initial primary results were known,
so comparison is exploratory, not independent scientific confirmation.
"""
import json,random,io,zipfile,math,sys
from pathlib import Path
import numpy as np
from sklearn.pipeline import make_pipeline
from sklearn.preprocessing import StandardScaler
from sklearn.linear_model import LogisticRegression
from prospective_rice import cdf_le

def cp_upper(n,k,alpha):
    if n==0 or k==n:return 1.0
    lo=0.0;hi=1.0
    for _ in range(70):
        mid=(lo+hi)/2
        if cdf_le(k,n,mid)>alpha:lo=mid
        else:hi=mid
    return (lo+hi)/2
from prospective_rice import load

def main():
    X,y,_=load(sys.argv[1]);X=np.asarray(X);y=np.asarray(y)
    ids=list(range(len(y)));random.Random(20261114).shuffle(ids)
    n=len(y);train=ids[:n*6//10];cal=ids[n*6//10:n*8//10];test=ids[n*8//10:]
    model=make_pipeline(StandardScaler(),LogisticRegression(max_iter=400,random_state=20261114))
    model.fit(X[train],y[train])
    prob=model.predict_proba(X)[:,1]
    thresholds=(.70,.80,.90,.95)
    def evaluate(t,idx):
        acts=[i for i in idx if max(prob[i],1-prob[i])>=t]
        er=sum(int((prob[i]>=.5)!=bool(y[i])) for i in acts)
        pos=sum(prob[i]>=.5 for i in acts)
        tp=sum((prob[i]>=.5) and y[i]==1 for i in acts)
        return dict(acted=len(acts),total=len(idx),coverage=len(acts)/len(idx),
                    errors=er,error_rate=er/len(acts) if acts else None,
                    positive_actions=pos,true_positive_actions=tp,
                    false_positive_actions=pos-tp,
                    false_negative_actions=sum((prob[i]<.5) and y[i]==1 for i in acts),
                    refused=len(idx)-len(acts))
    cals=[]
    for t in thresholds:
        c=evaluate(t,cal)
        ub=cp_upper(c["acted"],c["errors"],0.05/4)
        cals.append(dict(threshold=t,result=c,cp_upper=ub,eligible=ub<=.05))
    eligible=[r for r in cals if r["eligible"]]
    eligible.sort(key=lambda r:(-r["result"]["acted"],r["threshold"]))
    choice=eligible[0]["threshold"] if eligible else None
    hold=evaluate(choice,test) if choice is not None else dict(acted=0,total=len(test),errors=0,refused=len(test),coverage=0)
    out=dict(kind="EXPLORATORY LOGISTIC REGRESSION COMPARATOR AFTER PRIMARY",
             training_count=len(train),calibration_count=len(cal),test_count=len(test),
             thresholds=thresholds,calibration=cals,chosen=choice,holdout=hold,
             limitation="not preregistered; comparator chosen after seeing primary results; not an independent future dataset")
    Path(sys.argv[2]).write_text(json.dumps(out,indent=2,default=lambda x: x.item() if hasattr(x, 'item') else str(x))+"\n")
    print("POSTHOC_LOGISTIC_NOT_CONFIRMATORY")
    for c in cals:
        print("CAL threshold",c["threshold"],"acted",c["result"]["acted"],
              "errors",c["result"]["errors"],"upper",round(c["cp_upper"],6),
              "eligible",c["eligible"])
    print("LOGISTIC_SELECTED",choice,"TEST",json.dumps(hold,default=lambda x: x.item() if hasattr(x, "item") else str(x)))
if __name__=="__main__":
    main()
