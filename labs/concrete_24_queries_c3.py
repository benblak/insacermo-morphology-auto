#!/usr/bin/env python3
"""INSACERMO isolated lab: actual UCI Concrete measured compressive strength.

Predeclared protocol: Group by ALL seven chemical/material composition fields;
hold out 30% of recipes entirely, selecting ONLY 24 labels in development
recipes; test on unfamiliar formulations. Compare a deterministic active
uncertainty sampler to 30 randomly chosen 24-label samples, plus a median
constant baseline; evaluate after selection. Fit limited physically interpretable
additive basis by ridge with LOOCV on 24 points (statistical regression, NOT
autonomous fundamental-law discovery or training-free entire pipeline).
C3 unchanged: verify posthoc failure of 10-MPa individual accuracy guarantee
from three coarse features even when average fit appears useful. No Lean proof
of regression accuracy or data provenance.
"""
from __future__ import annotations
import csv,hashlib,io,json,math,random,statistics,urllib.request
from pathlib import Path
import numpy as np
from insacermo_one_engine import decide,replay,validate

MIRROR="https://raw.githubusercontent.com/HansenHan/ML_UCI_Concrete_Compressive_Strength/105792bdae94c122f7e5bab77d1085f00c840e7b/Concrete_Data.csv"
MIRROR_BLOB="97cc8ffa7e0f128e0cc46ad25be1329d3beb2912"
FROZEN_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
SEED=20261117
BUDGET=24
N_RANDOM=30
FEATURES=("cement","slag","fly_ash","water","superplasticizer","coarse","fine","ln_age",
          "water_to_binder","ln_age*water_to_binder","ln_age*cement","ln_age^2")
GRAMMAR=[
 (0,3,7),(0,3,7,8),(0,1,2,3,7),(0,1,2,3,7,8),
 (0,1,2,3,4,7,8),(0,1,2,3,4,7,8,9),
 (0,1,2,3,4,5,6,7),(0,1,2,3,4,5,6,7,8),
 (0,1,2,3,4,5,6,7,8,9),
 (0,1,2,3,4,5,6,7,8,9,10),
 (0,1,2,3,4,5,6,7,8,9,10,11),
]
RIDGES=(1.0,10.0,100.0)
def git_blob(data):
    return hashlib.sha1(b"blob "+str(len(data)).encode()+bytes([0])+data).hexdigest()

def read_data(out):
    req=urllib.request.Request(MIRROR,headers={"User-Agent":"INSACERMO-independent-concrete-lab/1.0"})
    with urllib.request.urlopen(req,timeout=70) as r:data=r.read()
    assert git_blob(data)==MIRROR_BLOB,("DATA_SOURCE_BLOB_CHANGED",git_blob(data))
    (out/"concrete_source.csv").write_bytes(data)
    rows=list(csv.reader(io.StringIO(data.decode("utf-8-sig"))))
    assert len(rows)==1031,(len(rows))
    obs=np.array([[float(x.strip()) for x in row] for row in rows[1:]],dtype=float)
    assert obs.shape==(1030,9) and np.isfinite(obs).all()
    assert (obs[:,8]>0).all() and (obs[:,7]>0).all()
    return obs,hashlib.sha256(data).hexdigest()

def split_by_recipe(a):
    # A recipe is ALL first seven material amounts, regardless of curing age.
    recipes={}
    for i,row in enumerate(a):
        recipe=tuple(float(x) for x in row[:7])
        recipes.setdefault(recipe,[]).append(i)
    sorted_recipes=sorted(recipes)
    random.Random(SEED).shuffle(sorted_recipes)
    holdout_count=round(len(sorted_recipes)*.30)
    holdout=set(sorted_recipes[:holdout_count])
    train=np.array([i for i,row in enumerate(a) if tuple(row[:7]) not in holdout],dtype=int)
    test=np.array([i for i,row in enumerate(a) if tuple(row[:7]) in holdout],dtype=int)
    assert not {tuple(a[i,:7]) for i in train}&{tuple(a[i,:7]) for i in test}
    assert len(train)>300 and len(test)>150,(len(train),len(test))
    return train,test,len(recipes),holdout_count

def basis(a):
    c,s,ash,w,sup,coarse,fine,age=[a[:,i] for i in range(8)]
    age=np.log1p(age)
    binder=np.maximum(c+s+ash,1.)
    ratio=w/binder
    return np.column_stack([c,s,ash,w,sup,coarse,fine,age,ratio,age*ratio,age*c,age*age])

def features(train,hold):
    x=basis(train);z=basis(hold)
    means=x.mean(axis=0);std=x.std(axis=0)
    std[std<1e-8]=1
    return (x-means)/std,(z-means)/std

def fit_models(X,ids,y):
    ids=np.array(ids,dtype=int)
    target=y[ids]
    found=[]
    for cols in GRAMMAR:
        D=np.column_stack([np.ones(len(ids)),X[np.ix_(ids,list(cols))]])
        for ridge in RIDGES:
            R=ridge*np.eye(D.shape[1]);R[0,0]=1e-7
            inv=np.linalg.inv(D.T@D+R)
            coef=inv@D.T@target
            residual=target-D@coef
            lever=np.einsum("ij,jk,ik->i",D,inv,D)
            loo=residual/np.maximum(.12,1-lever)
            rmse=float(np.sqrt(np.mean(np.minimum(loo*loo,10000))))
            found.append((rmse+.10*len(cols),tuple(cols),ridge,coef))
    found.sort(key=lambda t:(t[0],len(t[1]),t[1],t[2]))
    return found

def predict(X,model):
    _,cols,_,coef=model
    return coef[0]+X[:,list(cols)]@coef[1:]

def diversity_anchor(X,n=8):
    # Unlabelled feature coverage only. No measured target values used.
    first=min(range(len(X)),key=lambda i:hashlib.sha256(
        ("initial:"+str(SEED)+":"+str(i)).encode()).digest())
    chosen=[first]
    distances=np.full(len(X),np.inf)
    while len(chosen)<n:
        distances=np.minimum(distances,np.sum((X-X[chosen[-1]])**2,axis=1))
        distances[chosen]=-1
        chosen.append(int(np.argmax(distances)))
    assert len(chosen)==len(set(chosen))
    return chosen

def active(X,y):
    selected=diversity_anchor(X)
    events=[]
    for step in range(len(selected),BUDGET):
        ranked=fit_models(X,selected,y)
        committee=ranked[:8]
        preds=np.column_stack([predict(X,m) for m in committee])
        disagreement=np.std(preds,axis=1)
        disagreement[selected]=-1
        idx=int(np.argmax(disagreement))
        assert idx not in selected
        events.append(dict(reading_number=step+1,local_training_row=idx,
            ensemble_disagreement_mpa=float(disagreement[idx]),
            measured_strength_mpa=float(y[idx]),
            previous_model_terms=[FEATURES[t] for t in ranked[0][1]]))
        selected.append(idx)
    return selected,events

def metrics(est,truth):
    err=est-truth;ab=np.abs(err)
    return dict(n=len(truth),mae_mpa=float(np.mean(ab)),
        median_absolute_error_mpa=float(np.median(ab)),
        rmse_mpa=float(np.sqrt(np.mean(err*err))),
        fraction_within_5mpa=float(np.mean(ab<=5)),
        fraction_within_10mpa=float(np.mean(ab<=10)),
        p90_absolute_error_mpa=float(np.quantile(ab,.9)),
        max_absolute_error_mpa=float(np.max(ab)))

def signature(r):
    # Three coarse pre-prediction measurements, no target strength:
    return (int(r[0]>=300),int(r[3]>=180),int(r[7]>=28))

def contract(rows,accurate):
    n=len(rows);assert n<=8
    sg=[signature(r) for r in rows]
    m=dict(worldCount=n,actionCount=2,probeCount=3,
      good=[[not bool(accurate[w]),bool(accurate[w])] for w in range(n)],
      sense=[[2 if sg[w][p] else 1 for w in range(n)] for p in range(3)],
      nextFalse=[list(range(n)) for _ in range(3)],
      nextTrue=[list(range(n)) for _ in range(3)],
      actionCost=[0,0],probeCost=[1,1,1],
      lowerWorld=list(range(n)),upperWorld=list(range(n)),
      mustActions=[0,1],mayActions=[0,1],probeKinds=["PROBE"]*3,
      depth=3,budget=3,reserve=8,debt=0)
    validate(m)
    return m

def c3_audit(out,test,pred):
    delta=np.abs(pred-test[:,8])
    candidates={}
    for i,r in enumerate(test):candidates.setdefault(signature(r),[]).append(i)
    pairs=[]
    for sig in sorted(candidates):
        indices=candidates[sig]
        bad=sorted((i for i in indices if delta[i]>=15),key=lambda i:(-delta[i],i))
        good=sorted((i for i in indices if delta[i]<=5),key=lambda i:(delta[i],i))
        for b,g in zip(bad,good):
            pairs.append((b,g,sig))
            if len(pairs)==4:break
        if len(pairs)==4:break
    assert len(pairs)==4,("NO_FOUR_MATCHED_OPPOSITE_PAIRS",len(pairs))
    result=[]
    for idx,(b,g,sig) in enumerate(pairs):
        folder=out/"C3_Lean"/("pair_%d"%idx)
        m=contract(test[[b,g]],delta[[b,g]]<=10)
        r=decide(m,folder)
        assert r["verdict"]=="REFUSE_ROBUST" and not r["authorized"],r
        assert replay(folder)
        result.append(dict(bad_id=int(b),good_id=int(g),bad_abs_mpa=float(delta[b]),
            good_abs_mpa=float(delta[g]),same_signature=list(sig),verdict=r["verdict"]))
        print("CONCRETE_C3_REFUSE",idx,int(b),int(g),flush=True)
    folder=out/"C3_Lean"/"eight_world_refusal"
    picks=[b for b,g,s in pairs]+[g for b,g,s in pairs]
    r=decide(contract(test[picks],delta[picks]<=10),folder)
    assert r["verdict"]=="REFUSE_ROBUST" and replay(folder)
    folder=out/"C3_Lean"/"eight_good_act"
    good_ids=np.where(delta<=5)[0][:8]
    assert len(good_ids)==8
    r=decide(contract(test[good_ids],delta[good_ids]<=10),folder)
    assert r["verdict"]=="ACT" and r["authorized"] and replay(folder)
    assert not replay(folder,lean_binary="/missing-lean")
    p=folder/"receipt.json";original=p.read_bytes()
    altered=original.replace(b'"authorized":true',b'"authorized":false')
    assert altered!=original
    try:
        p.write_bytes(altered)
        assert not replay(folder)
    finally:p.write_bytes(original)
    assert replay(folder)
    return dict(certificates_replayed=6,matched_indiscernible_pairs=result,
      combined_eight_world_verdict="REFUSE_ROBUST",all_good_verdict="ACT",
      caveat="Witnesses deliberately selected post hoc on holdout errors; only finite declared set proven")

def run(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    source=(Path(__file__).resolve().parents[1]/"insacermo_one_engine.py").read_bytes()
    assert git_blob(source)==FROZEN_BLOB,"FROZEN_C3_RUNTIME_CHANGED"
    a,sha=read_data(out)
    train_ids,test_ids,nrecipes,heldrecipes=split_by_recipe(a)
    train=a[train_ids];test=a[test_ids]
    X,Z=features(train,test);y=train[:,8];t=test[:,8]
    selection,events=active(X,y)
    best=fit_models(X,selection,y)[0]
    pred=predict(Z,best)
    measured=metrics(pred,t)
    baseline_constant=metrics(np.full(len(t),float(np.median(y[selection]))),t)
    comparisons=[]
    for i in range(N_RANDOM):
        chosen=random.Random(SEED+100+i).sample(range(len(train)),BUDGET)
        candidate=fit_models(X,chosen,y)[0]
        pred_random=predict(Z,candidate)
        comparisons.append(dict(seed=SEED+100+i,
          mae_mpa=metrics(pred_random,t)["mae_mpa"],
          terms=[FEATURES[j] for j in candidate[1]],
          ridge=candidate[2]))
    c3=c3_audit(out,test,pred)
    random_mae=[r["mae_mpa"] for r in comparisons]
    result=dict(experiment="Concrete lab physically measured strength: held out entire recipes",
      repository="HansenHan/ML_UCI_Concrete_Compressive_Strength",
      mirror_url=MIRROR,mirror_blob=MIRROR_BLOB,source_sha256=sha,
      original_c3_blob=FROZEN_BLOB,
      total_rows=len(a),distinct_recipes=nrecipes,heldout_recipes=heldrecipes,
      training_rows=len(train),heldout_rows=len(test),
      observed_target_budget=BUDGET,initial_feature_only_anchors=8,
      later_active_target_queries=16,
      chosen_law_terms=[FEATURES[i] for i in best[1]],ridge=best[2],
      coefficient_standardized_features=best[3].tolist(),
      active_holdout=measured,constant_baseline=baseline_constant,
      random_trial_count=N_RANDOM,
      random_baseline_mean_mae_mpa=float(statistics.mean(random_mae)),
      random_baseline_median_mae_mpa=float(statistics.median(random_mae)),
      random_trials_beaten=sum(measured["mae_mpa"]<v for v in random_mae),
      C3=c3,
      limitations=[
        "Actual laboratory strength measurements; no fresh experiments were commissioned.",
        "All recipes in the heldout split are composition-disjoint from development recipes.",
        "Only 24 target strengths exposed to the fitting code; other composition features are visible.",
        "The selected formulas are from a supplied expression grammar, fitted using ridge regression and LOOCV.",
        "Statistical regression is ML by broad definitions; no deep-learning/neural training was performed.",
        "C3 unchanged certifies small finite decisions about outcome distinguishability, NOT the empirical regression formula.",
        "Post hoc witness selection is a diagnosis, not an unbiased prospective performance estimate.",
        "No guarantee of universal generalization to all real-world formulations or curing conditions."
      ])
    (out/"report.json").write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    (out/"acquisition_log.json").write_text(json.dumps(events,indent=2)+"\n")
    (out/"random_baselines.json").write_text(json.dumps(comparisons,indent=2)+"\n")
    np.savetxt(out/"hidden_recipe_predictions.csv",
      np.column_stack([test,pred,pred-t]),delimiter=",",fmt="%.9g",
      header="cement,slag,fly_ash,water,superplasticizer,coarse,fine,age,strength_measured_mpa,strength_predicted_mpa,error_mpa",
      comments="")
    print("CONCRETE_REAL",len(a),"RECIPES",nrecipes,"TRAIN",len(train),"HOLD",len(test),flush=True)
    print("DISCOVERY_TERMS",result["chosen_law_terms"],"ridge",best[2],flush=True)
    print("HELDOUT",measured,"CONSTANT",baseline_constant["mae_mpa"],
      "RANDOM_MEDIAN_MAE",result["random_baseline_median_mae_mpa"],
      "ACTIVE_BEATS",result["random_trials_beaten"],"of",N_RANDOM,flush=True)
    print("CONCRETE_C3_LEAN_PASS",c3["certificates_replayed"],flush=True)
    return result

if __name__=="__main__":
    import sys
    run(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_concrete")
