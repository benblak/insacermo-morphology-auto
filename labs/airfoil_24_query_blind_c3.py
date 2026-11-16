#!/usr/bin/env python3
"""Independent NASA wind-tunnel acoustics with strict 24-target-query budget.
Actual target: measured airfoil sound pressure in dB, not a column derived from
a target law. Symbolic feature grammar and coefficients fitted by ordinary
least squares are specified; this is statistical parameter fitting, not
autonomous creation of arbitrary physical equations. Fixed holdout is ALL
71.3 m/s records, an entirely unseen velocity. Original C3 source is frozen.
"""
from __future__ import annotations
import csv,hashlib,io,itertools,json,math,random,statistics,urllib.request
from pathlib import Path
import numpy as np
from insacermo_one_engine import decide,replay,validate

DATA_SOURCE=("https://raw.githubusercontent.com/rupakc/UCI-Data-Analysis/"
 "b2937bc0f36f570b5a6bb4049656f5239a1f334c/Airfoil%20Dataset/airfoil_self_noise.dat")
DATA_BLOB="9f6fdafab6a323514c2a0407dea680fcb23d6795"
ENGINE_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
EXP_BUDGET=24
ANCHORS=8
RANDOM_REPEATS=30
SEED=20261116
FEATURE_NAMES=["ln(frequency)","angle","ln(chord)","ln(velocity)","ln(thickness)",
 "ln(frequency)^2","angle^2","ln(frequency)*ln(velocity)",
 "ln(frequency)*ln(thickness)","ln(velocity)*angle"]
TERMS=tuple(tuple(x) for k in (1,2,3) for x in itertools.combinations(range(10),k))

def git_blob(content):
    return hashlib.sha1(b"blob "+str(len(content)).encode()+b"\\0"+content).hexdigest()

def dataset(out):
    with urllib.request.urlopen(urllib.request.Request(
        DATA_SOURCE,headers={"User-Agent":"INSACERMO-Airfoil-Research/1.0"}),timeout=70) as r:
        raw=r.read()
    assert git_blob(raw)==DATA_BLOB,("UCI_MIRROR_CHANGED",git_blob(raw))
    rows=[]
    for idx,line in enumerate(raw.decode("utf-8").splitlines()):
        parts=[float(x) for x in line.strip().split()]
        assert len(parts)==6,(idx,parts)
        rows.append(parts)
    assert len(rows)==1503,(len(rows))
    A=np.array(rows,dtype=float)
    assert np.isfinite(A).all() and (A[:,[0,2,3,4]]>0).all()
    assert np.isclose(A[:,3],71.3).sum()==465
    (out/"source_airfoil_self_noise.dat").write_bytes(raw)
    return A,hashlib.sha256(raw).hexdigest()

def basis(x):
    # x columns frequency, attack, chord, velocity, thickness
    f=np.log(x[:,0]);angle=x[:,1];c=np.log(x[:,2])
    v=np.log(x[:,3]);t=np.log(x[:,4])
    return np.column_stack([f,angle,c,v,t,f*f,angle*angle,f*v,f*t,v*angle])

def score_features(train,test):
    # Unlabelled input features may be seen throughout the training pool.
    X0=basis(train[:,:5]);X1=basis(test[:,:5])
    mu=np.mean(X0,axis=0);sd=np.std(X0,axis=0);sd[sd<1e-12]=1
    return (X0-mu)/sd,(X1-mu)/sd

def fit_models(X,seen,y):
    sample=X[list(seen),:]
    target=y[list(seen)]
    n=len(seen)
    ranked=[]
    for terms in TERMS:
        cols=(0,)+tuple(t+1 for t in terms)
        D=np.column_stack([np.ones(n),sample[:,list(terms)]])
        # Regression only on the observed target values. Stable small ridge.
        G=D.T@D
        ridge=1e-6*np.eye(len(cols));ridge[0,0]=1e-9
        inv=np.linalg.inv(G+ridge)
        beta=inv@D.T@target
        residual=target-D@beta
        leverage=np.einsum("ij,jk,ik->i",D,inv,D)
        loo=residual/np.maximum(.08,1-leverage)
        # Penalize algebraic size to stop arbitrary interpolation at 24 points
        val=float(np.sqrt(np.mean(np.minimum(loo*loo,10000)))+.22*len(terms))
        ranked.append((val,terms,beta))
    ranked.sort(key=lambda z:(z[0],len(z[1]),z[1]))
    return ranked

def predict(X,model):
    _,terms,beta=model
    return beta[0]+X[:,list(terms)]@beta[1:]

def anchor_points(X):
    # Query locations chosen without seeing any sound-pressure values.
    rng=random.Random(SEED)
    selected=[rng.randrange(len(X))]
    d=np.full(len(X),float("inf"))
    while len(selected)<ANCHORS:
        last=X[selected[-1]]
        d=np.minimum(d,np.sum((X-last)**2,axis=1))
        d[selected]=-1.
        selected.append(int(np.argmax(d)))
    assert len(set(selected))==ANCHORS
    return selected

def active_selection(X,y):
    selected=anchor_points(X)
    log=[]
    for step in range(ANCHORS,EXP_BUDGET):
        ranked=fit_models(X,selected,y)
        best=ranked[0]
        # Disagreement between 8 best declarative symbolic descriptions.
        candidates=np.column_stack([predict(X,f) for f in ranked[:8]])
        dis=np.std(candidates,axis=1)
        dis[selected]=-1
        chosen=int(np.argmax(dis))
        assert chosen not in selected
        log.append(dict(measurement_number=step+1,row_id=chosen,
            chosen_disagreement_db=float(dis[chosen]),
            prior_terms=[FEATURE_NAMES[t] for t in best[1]],
            actual_sound_db=float(y[chosen])))
        selected.append(chosen)
    return selected,log

def performance(pred,truth):
    errors=np.abs(pred-truth)
    return dict(n=int(len(truth)),mae_db=float(np.mean(errors)),
        median_abs_db=float(np.median(errors)),rmse_db=float(np.sqrt(np.mean((pred-truth)**2))),
        fraction_within_3db=float(np.mean(errors<=3.)),
        fraction_within_5db=float(np.mean(errors<=5.)),
        fraction_within_10db=float(np.mean(errors<=10.)),
        p90_abs_db=float(np.quantile(errors,.9)),max_abs_db=float(np.max(errors)))

def C3model(records):
    n=len(records)
    assert 1<=n<=8
    # Three coarse observations accessible before knowing true dB:
    # frequency >= 2kHz; attack >= 5 deg; thickness >= 0.005 m.
    patterns=[(int(x[0]>=2000),int(x[1]>=5.),int(x[4]>=.005)) for x in records]
    good=[[not bool(x[6]),bool(x[6])] for x in records]
    m=dict(worldCount=n,actionCount=2,probeCount=3,good=good,
      sense=[[2 if patterns[w][j] else 1 for w in range(n)] for j in range(3)],
      nextFalse=[list(range(n)) for _ in range(3)],
      nextTrue=[list(range(n)) for _ in range(3)],
      actionCost=[0,0],probeCost=[1,1,1],
      lowerWorld=list(range(n)),upperWorld=list(range(n)),
      mustActions=[0,1],mayActions=[0,1],probeKinds=["PROBE"]*3,
      depth=3,budget=3,reserve=8,debt=0)
    validate(m)
    return m,patterns

def C3audit(out,hold_raw,hold_prediction):
    # Diagnostic pair selection intentionally uses held-out errors after
    # evaluation, NOT a blind prediction or online discovery mechanism.
    diagnostic=np.column_stack([hold_raw, np.abs(hold_prediction-hold_raw[:,5])<=5.])
    groups={}
    for i,x in enumerate(diagnostic):
        pattern=(int(x[0]>=2000),int(x[1]>=5.),int(x[4]>=.005))
        groups.setdefault(pattern,[]).append((i,x))
    pairs=[];seen=set()
    for pattern in sorted(groups):
        rows=groups[pattern]
        good=sorted((z for z in rows if z[1][6] and abs(hold_prediction[z[0]]-z[1][5])<=2),
            key=lambda z:abs(hold_prediction[z[0]]-z[1][5]))
        bad=sorted((z for z in rows if not z[1][6] and abs(hold_prediction[z[0]]-z[1][5])>=8),
            key=lambda z:-abs(hold_prediction[z[0]]-z[1][5]))
        for b,g in zip(bad,good):
            if b[0] in seen or g[0] in seen:continue
            pairs.append((b,g))
            seen.add(b[0]);seen.add(g[0])
            if len(pairs)>=4:break
        if len(pairs)>=4:break
    assert len(pairs)==4,("INSUFFICIENT_OPPOSITE_OUTCOMES",len(pairs))
    verified=0
    details=[]
    for j,(bad,good) in enumerate(pairs):
        folder=out/"C3_Lean"/f"pair_{j}_refusal"
        m,s=C3model([bad[1],good[1]])
        result=decide(m,folder)
        assert result["verdict"]=="REFUSE_ROBUST" and not result["authorized"],result
        assert replay(folder)
        verified+=1
        details.append(dict(pair=j,metadata_signature=s[0],bad_index=int(bad[0]),
            good_index=int(good[0]),bad_error_db=float(abs(hold_prediction[bad[0]]-bad[1][5])),
            good_error_db=float(abs(hold_prediction[good[0]]-good[1][5])),
            verdict="REFUSE_ROBUST"))
        print("AIRFOIL_C3_LEAN_PAIR",j,"bad",int(bad[0]),"good",int(good[0]),flush=True)
    m,_=C3model([b[1] for b,g in pairs]+[g[1] for b,g in pairs])
    folder=out/"C3_Lean"/"eight_world_refusal"
    result=decide(m,folder)
    assert result["verdict"]=="REFUSE_ROBUST" and replay(folder)
    verified+=1
    # Positive control is a preselected all-safe set of eight observed rows.
    goods=[x for x in diagnostic if x[6] and abs(float(x[5])-hold_prediction[np.where((hold_raw==x[:6]).all(axis=1))[0][0]])<=2]
    # Simpler, deterministic row-index selection avoids accidental duplicate rows.
    safe_ids=np.where(np.abs(hold_prediction-hold_raw[:,5])<=2)[0]
    assert len(safe_ids)>=8
    safe_rows=diagnostic[safe_ids[:8]]
    assert all(bool(x[6]) for x in safe_rows)
    folder=out/"C3_Lean"/"eight_safe_act_control"
    result=decide(C3model(safe_rows)[0],folder)
    assert result["verdict"]=="ACT" and result["authorized"] and replay(folder)
    verified+=1
    assert verified==6
    assert not replay(folder,lean_binary="/no-lean-available")
    receipt=folder/"receipt.json";old=receipt.read_bytes()
    changed=old.replace(b'"authorized":true',b'"authorized":false')
    assert changed!=old
    try:
        receipt.write_bytes(changed)
        assert not replay(folder)
    finally:receipt.write_bytes(old)
    assert replay(folder)
    return dict(Lean_receipts=verified,refusal_pairs=details,
        eight_world="REFUSE_ROBUST",positive_control="ACT",
        selection="post-hoc selected matched cases, no generalization guarantee")

def run(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    source=(Path(__file__).resolve().parents[1]/"insacermo_one_engine.py").read_bytes()
    blob=git_blob(source)
    assert blob==ENGINE_BLOB,("C3_FROZEN_SOURCE_CHANGED",blob)
    A,digest=dataset(out)
    held=np.isclose(A[:,3],71.3)
    train=A[~held];test=A[held]
    assert train.shape==(1038,6) and test.shape==(465,6)
    X,Z=score_features(train,test)
    y=train[:,5];truth=test[:,5]
    select,history=active_selection(X,y)
    assert len(select)==EXP_BUDGET and len(set(select))==EXP_BUDGET
    final_models=fit_models(X,select,y)
    winner=final_models[0]
    pred=predict(Z,winner)
    active_eval=performance(pred,truth)
    random_scores=[]
    for i in range(RANDOM_REPEATS):
        sample=random.Random(SEED+i+100).sample(range(len(train)),EXP_BUDGET)
        random_winner=fit_models(X,sample,y)[0]
        base_pred=predict(Z,random_winner)
        met=performance(base_pred,truth)
        random_scores.append(dict(i=i,mae_db=met["mae_db"],
            fraction_within_5db=met["fraction_within_5db"],
            terms=[FEATURE_NAMES[t] for t in random_winner[1]]))
    median_y=float(np.median(y[select]))
    constant=performance(np.full(len(test),median_y),truth)
    audit=C3audit(out,test,pred)
    s=dict(experiment="Independent measured wind-tunnel acoustic response",
      origin="NASA airfoil self noise tests; Brooks/Pope/Marcolini 1989, UCI doi:10.24432/C5VW2C",
      data_source=DATA_SOURCE,mirror_git_blob=DATA_BLOB,source_sha256=digest,
      original_C3_git_blob=blob,n_total=1503,n_train_pool=1038,n_heldout=465,
      never_seen_velocity_m_s=71.3,budget_acoustic_target_queries=EXP_BUDGET,
      anchor_queries=ANCHORS,adaptive_queries=EXP_BUDGET-ANCHORS,
      initial_grammar_terms=FEATURE_NAMES,
      candidate_equations=len(TERMS),selected_formula_terms=[FEATURE_NAMES[i] for i in winner[1]],
      standardized_feature_coefficients=winner[2].tolist(),
      active_heldout=active_eval,constant_baseline_heldout=constant,
      random_baseline_trials=RANDOM_REPEATS,
      random_baseline_median_mae_db=float(statistics.median(s["mae_db"] for s in random_scores)),
      random_baseline_mean_mae_db=float(statistics.mean(s["mae_db"] for s in random_scores)),
      random_trials_beaten_by_active=sum(active_eval["mae_db"]<s["mae_db"] for s in random_scores),
      C3=audit,
      limitations=[
          "Original published data consist of wind-tunnel physical/acoustic experiments; results are retrospective, not new physical acquisitions.",
          "Sound-pressure target is independently measured, not derived algebraically from tested explanatory features.",
          "The 24 observation budget limits exposure to observed sound-pressure labels, not access to all unlabelled input settings.",
          "All speed 71.3 m/s data are withheld; this tests extrapolation to an unseen velocity, not random in-distribution accuracy.",
          "OLS regression and held-out model selection are forms of statistical fitting: do not claim the entire lab has no machine learning.",
          "The outer lab constructs and fits the symbolic formulas; original INSACERMO C3 does not invent their syntax.",
          "The family of up to three terms is preset and not all laws are explored.",
          "C3 counterexamples were intentionally selected after inspecting the held-out errors and do not prove performance on unseen physical systems.",
          "Lean certifies the declared small finite C3 models, not the acoustics regression or sensor provenance.",
          "No guarantee of 5dB accuracy on arbitrary unseen wind-tunnel conditions.",
          "Random baseline is a sampling comparison, not proof of best possible exploration algorithm."
      ])
    (out/"report.json").write_text(json.dumps(s,ensure_ascii=False,indent=2)+"\n")
    (out/"acquisition_log.json").write_text(json.dumps(history,ensure_ascii=False,indent=2)+"\n")
    (out/"random_baselines.json").write_text(json.dumps(random_scores,ensure_ascii=False,indent=2)+"\n")
    np.savetxt(out/"holdout_predictions.csv",np.column_stack([test,pred,pred-truth]),
      delimiter=",",fmt="%.9g",header="frequency_hz,angle_deg,chord_m,velocity_m_s,thickness_m,sound_measured_db,sound_predicted_db,error_db",
      comments="")
    print("NASA_WIND_TUNNEL_REAL",len(A),"train",len(train),"holdout",len(test),flush=True)
    print("LEARNED_SYMBOLIC_TERMS",s["selected_formula_terms"],flush=True)
    print("HELDOUT_SCORE",active_eval,"RANDOM_BEATEN",s["random_trials_beaten_by_active"],
          "of",RANDOM_REPEATS,"random_median_MAE",s["random_baseline_median_mae_db"],flush=True)
    print("FROZEN_C3_AIRFOIL_LEAN_SUCCESS",audit["Lean_receipts"],flush=True)
    return s

if __name__=="__main__":
    import sys
    run(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_airfoil")
