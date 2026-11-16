#!/usr/bin/env python3
"""INSACERMO MAX external scientific-discovery laboratory: real NOx emissions.

Registration before exposing test labels:
  - source: UCI turbine emissions 2011--2015 (GitHub archival copy pinned)
  - target: NOX (real hourly observed emissions, mg/m3). NEVER input CO.
  - 2011--2013: unlabeled settings available; reveal at most 24 NOx labels
  - 2014: reveal exactly 24 NOx labels for predeclared local error calibration
  - 2015: entire year's labels completely withheld until predictions frozen
  - policy: external, non-neural sparse symbolic ridge / LOOCV committee
  - comparisons: 30 random strategies with same 24-target-query budget
  - selected formula: single best among declared 1/2/3 feature expressions
  - reporting: all year-2015 errors including tails and out-of-support.
  - original historical C3 unmodified: Lean guarantees only on declared finite
    diagnostic worlds/probes; never a guarantee of physical NOx.
No new experiments are made: these are archival, historical sensor readings.
The regression is statistical fitting and *not* universal law discovery.
"""
from __future__ import annotations
import csv,hashlib,io,itertools,json,math,random,statistics,urllib.request
from pathlib import Path
import numpy as np
from insacermo_one_engine import decide,replay,validate

SOURCE="https://raw.githubusercontent.com/MarkLee7925/Gas-Turbine-Emissions/cb411da49edabfe1cbf8cb43650e612b1c88695c/data/"
SOURCES={2011:"403de0df000bedaffa99eae75b496b646200d953",
         2012:"23c61066bff8c85d1525b8c262a233aacec4a01e",
         2013:"597b4b89e5485e88bb7f04ef0898190d96af795f",
         2014:"e99eb7d166b7198febc32842edb8e463d26873b6",
         2015:"654a113d7721faf087a50bb1101002ccd3d2a7a5"}
N_PER_YEAR={2011:7411,2012:7628,2013:7152,2014:7158,2015:7384}
COLS=("AT","AP","AH","AFDP","GTEP","TIT","TAT","TEY","CDP","CO","NOX")
INPUTS=COLS[:9]
HISTORY_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
SEED=20261117
TRAIN_BUDGET=24
CAL_BUDGET=24
RANDOM_BASELINES=30
SUBPOOL=2048
GRAMMAR_INDICES=tuple(itertools.chain.from_iterable(
    itertools.combinations(range(13),k) for k in (1,2,3)))
RIDGE=2.5
SIMILARITY_FEATURES=("AT_high","TIT_high","TEY_high")
ERROR_TOLERANCE=15.

def blob(raw):
    return hashlib.sha1(b"blob "+str(len(raw)).encode()+bytes([0])+raw).hexdigest()

def source_data(out):
    arr={}
    digests={}
    for year in sorted(SOURCES):
        url=SOURCE+"gt_"+str(year)+".csv"
        req=urllib.request.Request(url,headers={"User-Agent":"INSACERMO-openworld-discovery-research/1.0"})
        with urllib.request.urlopen(req,timeout=90) as fd:raw=fd.read()
        assert blob(raw)==SOURCES[year],("SOURCE_CHANGED",year,blob(raw))
        assert len(raw)>500000 and raw.startswith(b"AT,AP,AH,")
        lines=list(csv.DictReader(io.StringIO(raw.decode("utf-8-sig"))))
        assert len(lines)==N_PER_YEAR[year],(year,len(lines))
        assert tuple(lines[0])==COLS,(year,tuple(lines[0]))
        data=np.array([[float(row[c]) for c in COLS] for row in lines],dtype=float)
        assert data.shape==(N_PER_YEAR[year],11) and np.isfinite(data).all()
        arr[year]=data
        digests[year]=hashlib.sha256(raw).hexdigest()
        # Store only sample and SHA in artifact (source publicly pinned).
        print("LOCKED_UCI_DATA",year,len(data),digests[year],flush=True)
    return arr,digests

def expressions(a):
    # 9 physical operational observations plus 4 non-neural, declared
    # cross-/curvature terms; both output emission columns excluded.
    z=a[:,:9]
    return np.column_stack([z,
       z[:,0]*z[:,5],z[:,0]*z[:,2],z[:,5]*z[:,4],z[:,7]*z[:,8]])

def normalized(data):
    tr=expressions(np.vstack([data[2011],data[2012],data[2013]]))
    mu=tr.mean(axis=0);sd=tr.std(axis=0);sd=np.where(sd<1e-10,1,sd)
    return {year:(expressions(data[year])-mu)/sd for year in data},mu,sd

def choose_unlabeled_pool(X):
    # Fixed deterministic hash, stratified 5 x TEY-quantile, no NOx data.
    vals=X[:,7]
    limits=np.quantile(vals,[.2,.4,.6,.8])
    buckets=np.searchsorted(limits,vals,side="right")
    rng=random.Random(SEED)
    sel=[]
    for b in range(5):
        choices=np.where(buckets==b)[0].tolist()
        sel+=rng.sample(choices,min(len(choices),SUBPOOL//5))
    # pad to fixed 2048
    chosen=set(sel)
    rest=[i for i in range(len(X)) if i not in chosen]
    sel+=rng.sample(rest,SUBPOOL-len(sel))
    assert len(sel)==len(set(sel))==SUBPOOL
    return sorted(sel)

def ridge_models(X,points,target):
    idx=np.array(points,dtype=int)
    xx=X[idx]
    yy=target[idx]
    n=len(idx)
    out=[]
    for terms in GRAMMAR_INDICES:
        D=np.column_stack([np.ones(n),xx[:,list(terms)]])
        gram=D.T@D+np.diag([1e-7]+[RIDGE]*len(terms))
        mat=np.linalg.inv(gram)
        coef=mat@D.T@yy
        residual=yy-D@coef
        leverage=np.einsum("ij,jk,ik->i",D,mat,D)
        loo=residual/np.maximum(.12,1-leverage)
        # Evaluation criterion fixed before holdout: clipped LOOCV + parsimony
        loss=float(np.sqrt(np.mean(np.minimum(loo*loo,2500)))+.20*len(terms))
        out.append((loss,terms,coef))
    out.sort(key=lambda m:(m[0],len(m[1]),m[1]))
    return out

def forecast(X,model):
    loss,terms,coef=model
    return coef[0]+X[:,list(terms)]@coef[1:]

def active_policy(X,available,y):
    # Eight anchor picks spread across input-feature space, then
    # sixteen rounds of disagreement weighted by input density.
    # Only 24 y-values ever read. No 2014/2015 target values passed here.
    candidates=np.asarray(available,dtype=int)
    # Select non-extreme start to reduce outlier-only experimental designs.
    rng=random.Random(SEED)
    initial=rng.sample(candidates.tolist(),8)
    seen=list(initial)
    selected=set(seen)
    events=[]
    # Fixed, unlabeled feature weights derived without labels.
    Z=X[candidates]
    freq=np.sum((Z[:,None,:9]-Z[None,::25,:9])**2,axis=2) # subsampled density reference
    k=min(5,freq.shape[1]-1)
    densities=np.partition(freq,k,axis=1)[:,k]
    density_weight=1/np.sqrt(1+densities)
    for t in range(8,TRAIN_BUDGET):
        models=ridge_models(X,seen,y)
        pred=np.column_stack([forecast(Z,m) for m in models[:8]])
        sd=np.std(pred,axis=1)
        # Predictive disagreement discounted by local input sparsity.
        utility=sd*density_weight
        utility=np.asarray(utility)
        utility[np.isin(candidates,seen)]=-1.
        take=int(candidates[int(np.argmax(utility))])
        assert take not in selected
        events.append({"reading":t+1,"training_id":take,
            "prior_formula_terms":list(models[0][1]),
            "committee_disagreement":float(sd[np.where(candidates==take)[0][0]]),
            "measured_nox":float(y[take])})
        seen.append(take);selected.add(take)
    assert len(seen)==TRAIN_BUDGET
    return seen,events

def summary(est,truth):
    err=np.abs(est-truth)
    return dict(n=len(truth),mae=float(np.mean(err)),
      median_abs=float(np.median(err)),rmse=float(np.sqrt(np.mean((est-truth)**2))),
      p90_abs=float(np.quantile(err,.90)),p99_abs=float(np.quantile(err,.99)),
      fraction_error_gt_15=float(np.mean(err>15)),
      fraction_error_gt_25=float(np.mean(err>25)),
      max_abs=float(np.max(err)))

def sensor_signature(inputs,centers):
    # Three coarse real operational readings; never NOx.
    return (int(inputs[0]>=centers[0]),
            int(inputs[5]>=centers[5]),
            int(inputs[7]>=centers[7]))

def model_for(rows,correct,sig):
    n=len(rows)
    assert 1<=n<=8
    m=dict(worldCount=n,actionCount=2,probeCount=3,
       good=[[not bool(correct[i]),bool(correct[i])] for i in range(n)],
       sense=[[2 if sig[i][q] else 1 for i in range(n)] for q in range(3)],
       nextFalse=[list(range(n)) for _ in range(3)],
       nextTrue=[list(range(n)) for _ in range(3)],
       actionCost=[0,0],probeCost=[1,1,1],
       lowerWorld=list(range(n)),upperWorld=list(range(n)),
       mustActions=[0,1],mayActions=[0,1],probeKinds=["PROBE"]*3,
       depth=3,budget=3,reserve=8,debt=0)
    validate(m)
    return m

def c3_certificates(out,x2015,estimate,truth,centers):
    errors=np.abs(estimate-truth)
    sig=[sensor_signature(x,centers) for x in x2015]
    grouped={}
    for i,s in enumerate(sig):grouped.setdefault(s,[]).append(i)
    pairs=[]
    for label in sorted(grouped):
        idx=grouped[label]
        bad=sorted((i for i in idx if errors[i]>=25),key=lambda i:(-errors[i],i))
        good=sorted((i for i in idx if errors[i]<=5),key=lambda i:(errors[i],i))
        for b,g in zip(bad,good):
            pairs.append((b,g))
            if len(pairs)==4:break
        if len(pairs)==4:break
    assert len(pairs)==4,("INSUFFICIENT_DECLARED_DIAGNOSTIC_PAIRS",len(pairs))
    certified=[]
    for number,(b,g) in enumerate(pairs):
        folder=out/"lean_receipts"/f"opposing_pair_{number}"
        world=[b,g]
        r=decide(model_for(world,[False,True],[sig[b],sig[g]]),folder)
        assert r["verdict"]=="REFUSE_ROBUST" and not r["authorized"] and replay(folder),r
        certified.append({"bad_record_2015":b,"good_record_2015":g,
          "bad_abs_NOx_error":float(errors[b]),"good_abs_NOx_error":float(errors[g]),
          "identical_three_sensor_bits":sig[b],"verdict":r["verdict"]})
        print("NOX_C3_LEAN_REFUSE",number,b,g,flush=True)
    first=[b for b,g in pairs]+[g for b,g in pairs]
    folder=out/"lean_receipts"/"eight_world_refusal"
    r=decide(model_for(first,[bool(errors[i]<=ERROR_TOLERANCE) for i in first],
        [sig[i] for i in first]),folder)
    assert r["verdict"]=="REFUSE_ROBUST" and replay(folder),r
    folder=out/"lean_receipts"/"eight_good_world_act"
    good=np.where(errors<=5)[0][:8].tolist()
    assert len(good)==8
    r=decide(model_for(good,[True]*8,[sig[i] for i in good]),folder)
    assert r["verdict"]=="ACT" and r["authorized"] and replay(folder),r
    # Evidence integrity: fail closed if Lean missing or receipt altered
    assert not replay(folder,lean_binary="/missing-lean")
    p=folder/"receipt.json";original=p.read_bytes()
    try:
        changed=original.replace(b'"authorized":true',b'"authorized":false')
        assert changed!=original
        p.write_bytes(changed)
        assert not replay(folder)
    finally:p.write_bytes(original)
    assert replay(folder)
    return {"lean_certificates":6,"diagnostic_pairs":certified,
      "eight_worlds":"REFUSE_ROBUST","eight_good":"ACT",
      "restriction":"posthoc deliberately chosen real contrasting samples; NOT a prospective reliability certificate"}

def run(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    engine=(Path(__file__).resolve().parents[1]/"insacermo_one_engine.py").read_bytes()
    assert blob(engine)==HISTORY_BLOB,"FROZEN_ENGINE_CHANGED"
    full,digests=source_data(out)
    xz,mu,sd=normalized(full)
    X=np.vstack([xz[2011],xz[2012],xz[2013]])
    # Training labels are accessible only to the training selection function.
    y=np.concatenate([full[y][:,10] for y in (2011,2012,2013)])
    pool=choose_unlabeled_pool(X)
    active_ids,log=active_policy(X,pool,y)
    winner=ridge_models(X,active_ids,y)[0]
    # 2014 is used solely for calibration, not for fitting/changing winner.
    Xcal=xz[2014]
    cal_ids=random.Random(SEED+1).sample(range(len(Xcal)),CAL_BUDGET)
    cal_predictions=forecast(Xcal[cal_ids],winner)
    cal_errors=np.abs(cal_predictions-full[2014][cal_ids,10])
    # conservative predeclared calibration, exchangeability is UNPROVEN across years.
    quantile=float(np.quantile(cal_errors,.9))
    # Collect blind predictions for 2015 before any 2015 labels are inspected.
    predictions=forecast(xz[2015],winner)
    pred_sha=hashlib.sha256(predictions.tobytes()).hexdigest()
    cal_gating_thresholds=[10,15,20,30]
    # Gate is uniform because calibration set too small for feature-dependent bound.
    # Either every 2015 case is ACT or every case abstains at a given threshold;
    # honest demonstration that aggregate calibration is NOT a personalized bound.
    guards={str(k):"ACT_ALL" if quantile<=k else "REFUSE_ALL" for k in cal_gating_thresholds}
    # Real evaluation below: ONLY now access withheld 2015 labels.
    t=full[2015][:,10]
    holdout=summary(predictions,t)
    constant_val=float(np.median(y[active_ids]))
    const_error=summary(np.full(len(t),constant_val),t)
    # random baselines: each same 24-label budget, identical grammar and 2015 protocol.
    comparisons=[]
    for i in range(RANDOM_BASELINES):
        sampled=random.Random(SEED+100+i).sample(pool,TRAIN_BUDGET)
        fit=ridge_models(X,sampled,y)[0]
        measured=summary(forecast(xz[2015],fit),t)
        comparisons.append({"seed":SEED+100+i,"holdout_mae":measured["mae"],
          "formula_indices":list(fit[1])})
    # Falsification examples are identified posthoc ONLY, not used to refit.
    errs=np.abs(predictions-t)
    worst=np.argsort(errs)[-6:][::-1].tolist()
    anomalies=[{"2015_index":int(i),"measured_NOx":float(t[i]),
       "predicted_NOx":float(predictions[i]),"error_NOx":float(errs[i]),
       "AT":float(full[2015][i,0]),"TEY":float(full[2015][i,7])} for i in worst]
    center=np.median(np.vstack([full[y][:,:9] for y in (2011,2012,2013)]),axis=0)
    c3=c3_certificates(out,full[2015][:,:9],predictions,t,center)
    scores=[b["holdout_mae"] for b in comparisons]
    results={
      "study":"Unknown measured emission response, prospective chronological NOx audit",
      "dataset":"UCI Gas Turbine CO and NOx Emission Data Set, DOI 10.24432/C5WC95",
      "data_files_sha256":digests,"data_year_counts":N_PER_YEAR,
      "historical_C3_git_blob":HISTORY_BLOB,
      "label_policy":{"model_years":"2011-2013","calibration_year":2014,
        "final_locked_test_year":2015,"max_model_labels":TRAIN_BUDGET,
        "max_calibration_labels":CAL_BUDGET,"actual_train_labels":len(active_ids),
        "actual_calibration_labels":len(cal_ids),"test_samples":len(t)},
      "target":"NOX mg/m3 (measured from real turbine); CO excluded from input",
      "predeclared_symbolic_candidate_count":len(GRAMMAR_INDICES),
      "active_selected_feature_indices":list(winner[1]),
      "active_selected_feature_names":list(INPUTS)+["AT*TIT","AT*AH","TIT*GTEP","TEY*CDP"],
      "active_coefficients_standardized":winner[2].tolist(),
      "active_test":holdout,"constant_test":const_error,
      "baseline_random_count":RANDOM_BASELINES,
      "baseline_random_median_mae":float(statistics.median(scores)),
      "baseline_random_mean_mae":float(statistics.mean(scores)),
      "active_beats_random_trials":sum(holdout["mae"]<x for x in scores),
      "2014_calibration_error_p90":quantile,
      "2015_uniform_calibration_gates":guards,
      "2015_prevaluation_prediction_sha256":pred_sha,
      "posthoc_worst_2015_examples":anomalies,
      "C3":c3,
      "limitations":[
        "Measurements and emissions are from real turbine hourly aggregates; no live experiments were run.",
        "Label query budget is 24 in 2011-13 plus 24 independent 2014 calibration labels; all other features visible.",
        "A sparse symbolic regression with coefficient estimation and LOOCV is statistical fitting, not magic discovery without learning.",
        "Chosen feature grammar is supplied, not freely invented by historical C3.",
        "2015 withheld from selection and calibration; the code computes its final label evaluation after predictions are locked.",
        "Turbine temporal shift makes any exchangeability/conformal coverage guarantee unsupported.",
        "2014 uniform calibration cannot individualize 2015 uncertainty, so the guard may be all-act or all-refuse.",
        "C3 Lean certificates are about small posthoc finite worlds with declared truth values and sensor thresholds.",
        "No physical law is Lean-proven and the empirical success is not universal."
       ]}
    (out/"audit.json").write_text(json.dumps(results,indent=2,ensure_ascii=False)+"\n")
    (out/"queries.json").write_text(json.dumps({"train_ids":active_ids,"events":log,
      "calibration_2014_ids":cal_ids},indent=2,ensure_ascii=False)+"\n")
    (out/"baseline_scores.json").write_text(json.dumps(comparisons,indent=2)+"\n")
    with (out/"test_2015_predictions.csv").open("w") as f:
        f.write("index,estimated_NOx_mg_m3,actual_NOx_mg_m3,error_mg_m3\n")
        for i,v in enumerate(predictions):
            f.write(f"{i},{v:.8f},{t[i]:.8f},{v-t[i]:.8f}\n")
    print("UCI_NOX_ROWS",[N_PER_YEAR[y] for y in sorted(N_PER_YEAR)],flush=True)
    print("FROZEN_LAW",winner[1],"2015",holdout,"CONSTANT",const_error["mae"],flush=True)
    print("RANDOM_BASELINE_MEDIAN_MAE",results["baseline_random_median_mae"],
      "ACTIVE_BEATS",results["active_beats_random_trials"],"of",RANDOM_BASELINES,flush=True)
    print("CAL_2014_Q90",quantile,"GUARD",guards,flush=True)
    print("NOX_C3_LEAN_SUCCESS",c3["lean_certificates"],flush=True)
    return results

if __name__=="__main__":
    import sys
    run(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_turbine_nox")
