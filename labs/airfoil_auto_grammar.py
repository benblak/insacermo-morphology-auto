#!/usr/bin/env python3
"""INSACERMO exploratory real airfoil acoustics laboratory.
Pre-registered protocol: AIRFOIL_AUTONOMOUS_GRAMMAR_PREREG_20261117.md
External Python research, NOT historical C3 kernel, NOT Lean proof.
"""
import hashlib, json, math, urllib.request
from pathlib import Path
import numpy as np

SOURCE=("https://raw.githubusercontent.com/rupakc/UCI-Data-Analysis/"
"b2937bc0f36f570b5a6bb4049656f5239a1f334c/"
"Airfoil%20Dataset/airfoil_self_noise.dat")
EXPECTED_BLOB="9f6fdafab6a323514c2a0407dea680fcb23d6795"
FEATURE_NAMES=["frequency","attack_angle","chord","wind_speed","displacement_thickness"]
COST=40
SPEED_HOLD=31.7
PREREG="08efec5710224a45069da2ee1375e750142bf52b"
RIDGE=1.
def digest(b):
    return hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()
def rmse(y,p):
    return float(np.sqrt(np.mean((np.asarray(y)-p)**2)))
def fit(Z,y,cols,lam=RIDGE):
    A=np.column_stack([np.ones(len(Z)),Z[:,cols]]) if cols else np.ones((len(Z),1))
    P=np.eye(A.shape[1])*lam; P[0,0]=0
    return np.linalg.solve(A.T@A+P,A.T@y)
def pred(Z,cols,coef):
    A=np.column_stack([np.ones(len(Z)),Z[:,cols]]) if cols else np.ones((len(Z),1))
    return A@coef
def grammar(X,mu,sd):
    z=(X-mu)/sd
    columns=[]; names=[]
    def add(v,n):
        columns.append(np.clip(v,-100,100));names.append(n)
    for i,n in enumerate(FEATURE_NAMES):add(z[:,i],n)
    for i,n in enumerate(FEATURE_NAMES):
        x=X[:,i]
        if i==1: value=np.log1p(np.maximum(x,0))
        else: value=np.log(np.maximum(x,1e-12))
        add(value,n+":log")
    for i,n in enumerate(FEATURE_NAMES):add(z[:,i]**2,n+":square")
    for i in range(5):
        for j in range(i+1,5):
            add(z[:,i]*z[:,j],FEATURE_NAMES[i]+"*"+FEATURE_NAMES[j])
    for i,n in enumerate(FEATURE_NAMES):
        for hinge in (-.5,0,.5):
            add(np.maximum(0,z[:,i]-hinge),n+":hinge"+str(hinge))
    return np.column_stack(columns),names
def search(Z,y,speeds):
    # Greedy forward selection with 3 held-out-speed folds.
    folds=[(np.flatnonzero(speeds!=sp),np.flatnonzero(speeds==sp))
           for sp in sorted(set(speeds))]
    assert len(folds)==3
    def cv(cols):
        errs=[]
        for a,b in folds:
            coef=fit(Z[a],y[a],cols)
            errs.extend((pred(Z[b],cols,coef)-y[b]).tolist())
        return float(np.sqrt(np.mean(np.square(errs))))
    selected=[]; best=cv([])
    progress=[dict(k=0,cv_rmse=best)]
    for _ in range(7):
        options=[]
        for i in range(Z.shape[1]):
            if i in selected:continue
            val=cv(selected+[i])
            options.append((val,i))
        score,j=min(options)
        if best-score < .05:break
        selected.append(j);best=score
        progress.append(dict(k=len(selected),cv_rmse=best,selected=list(selected)))
    return selected,progress
def model_fit(Z,X,y,selected):
    coef=fit(Z,y,selected)
    return coef
def main(output):
    out=Path(output);out.mkdir(parents=True,exist_ok=True)
    data=urllib.request.urlopen(urllib.request.Request(SOURCE,headers={"User-Agent":"INSACERMO-airfoil/1.0"}),timeout=80).read()
    assert digest(data)==EXPECTED_BLOB,("SOURCE_UNEXPECTED",digest(data))
    rows=np.asarray([[float(v) for v in line.split()] for line in data.decode().splitlines() if line.strip()],float)
    assert rows.shape==(1503,6),rows.shape
    (out/"source_data_sha256.txt").write_text(hashlib.sha256(data).hexdigest()+"\n")
    X=rows[:,:5]; y=rows[:,5];speeds=X[:,3]
    hold=np.flatnonzero(np.isclose(speeds,SPEED_HOLD))
    known=np.flatnonzero(~np.isclose(speeds,SPEED_HOLD))
    assert len(hold)>0 and set(np.unique(speeds[known]))=={39.6,55.5,71.3},sorted(set(speeds))
    known=sorted(known,key=lambda i:hashlib.sha256(f"20261117:airfoil:{i}".encode()).digest())
    n=int(.6*len(known)); discovery=np.asarray(known[:n],int);pool=np.asarray(known[n:],int)
    assert len(discovery)>COST and len(pool)>=COST
    mu=X[discovery].mean(axis=0);sd=X[discovery].std(axis=0);sd[sd<1e-8]=1
    Z,names=grammar(X,mu,sd)
    # Model selection on discovery only; no holdout response used.
    selected,search_trace=search(Z[discovery],y[discovery],speeds[discovery])
    chosen=[]; query_trace=[]
    for step in range(COST):
        ids=np.asarray([int(i) for i in pool if int(i) not in set(chosen)])
        train=np.asarray(list(discovery)+chosen,int)
        c=fit(Z[train],y[train],selected)
        # fixed committee: selected grammar, raw ridge, log ridge
        rawcols=list(range(5));logcols=list(range(5,10))
        a=pred(Z[ids],selected,c)
        b=pred(Z[ids],rawcols,fit(Z[train],y[train],rawcols))
        d=pred(Z[ids],logcols,fit(Z[train],y[train],logcols))
        disagreement=np.std(np.column_stack([a,b,d]),axis=1)
        chosen_idx=int(ids[np.argmax(disagreement)])
        query_trace.append(dict(step=step+1,row_id=chosen_idx,
            predicted_dB=float(a[np.argmax(disagreement)]),
            acquired_dB=float(y[chosen_idx]),
            committee_disagreement=float(max(disagreement))))
        chosen.append(chosen_idx)
        if len(chosen) in (10,20,30,40):
            ids_train=np.asarray(list(discovery)+chosen,int)
            selected,trace=search(Z[ids_train],y[ids_train],speeds[ids_train])
            search_trace.append(dict(query_round=len(chosen),trajectory=trace))
    train=np.asarray(list(discovery)+chosen,int)
    coef=fit(Z[train],y[train],selected)
    # model sealed PRIOR to any holdout score access
    sealed=dict(prereg_commit=PREREG,selected_indices=[int(i) for i in selected],
        expressions=[names[i] for i in selected], coefficients=coef.tolist(),
        mean=mu.tolist(),std=sd.tolist(),challenge_indices=chosen,
        discovery_indices=discovery.tolist(),holdout_row_ids=hold.tolist(),
        dataset_git_blob=EXPECTED_BLOB)
    (out/"sealed_model_before_holdout.json").write_text(json.dumps(sealed,indent=2)+"\n")
    (out/"query_trace.json").write_text(json.dumps(query_trace,indent=2)+"\n")
    # The first holdout access is here.
    ph=pred(Z[hold],selected,coef)
    linear_coef=fit(Z[train],y[train],list(range(5)))
    baseline=pred(Z[hold],list(range(5)),linear_coef)
    constant=float(np.mean(y[train]));r=rmse(y[hold],ph);b=rmse(y[hold],baseline)
    improvement=(1-r/b)*100
    result=dict(data_records=len(rows),train_known_speeds=sorted(set(speeds[train].tolist())),
        holdout_speed=SPEED_HOLD,holdout_records=len(hold),discovery_records=len(discovery),
        challenge_pool_records=len(pool),challenge_queries=COST,
        selected_terms=[names[i] for i in selected],coefficients=coef.tolist(),
        holdout_rmse_dB=r,holdout_mae_dB=float(np.mean(np.abs(y[hold]-ph))),
        linear_rmse_dB=b,constant_rmse_dB=rmse(y[hold],np.repeat(constant,len(hold))),
        improvement_vs_linear_pct=improvement,
        transfer_accepted=bool(r<=5 and improvement>=10),
        verdict="ACCEPT_EMPIRICAL_TRANSFER" if r<=5 and improvement>=10 else "REFUSE_UNSEEN_CONDITION",
        historical_kernel_modified=False,Lean_certification_of_law=False,
        sealed_model_file="sealed_model_before_holdout.json",
        source_sha256=hashlib.sha256(data).hexdigest(),
        caveats=["Synthetic query budget on archived responses; not new wind tunnel experiments",
        "Restricted programmer-defined basis grammar, not unconstrained discovery",
        "No Lean verification of learned aerodynamic model",
        "Absolute errors and predictive transfer are empirical, not mathematical proofs"])
    (out/"audit.json").write_text(json.dumps(result,indent=2)+"\n")
    (out/"search_trace.json").write_text(json.dumps(search_trace,indent=2)+"\n")
    print("AIRFOIL_RESULT",json.dumps({k:result[k] for k in ("holdout_records","holdout_rmse_dB","linear_rmse_dB","improvement_vs_linear_pct","verdict")}),flush=True)
if __name__=="__main__":
    import sys
    main(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_airfoil")
