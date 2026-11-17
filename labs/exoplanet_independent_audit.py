#!/usr/bin/env python3
"""Independent external replay of NASA exoplanet blind law hunt.
No import from the discovery program. Refuse any difference from preregistered rows
and sealed models. The archive can contain model-derived semi-major axes.
"""
from __future__ import annotations
import csv,hashlib,io,json,math,sys
from pathlib import Path
import numpy as np
FIELDS=["pl_orbper","pl_orbsmax","st_mass","st_teff","st_rad","sy_dist"]
SEEDS=[17,31,43,59,71,89,101,127]
def h(s):return hashlib.sha256((s+":insacermo:20261117").encode()).digest()
def build(data):
    r=csv.DictReader(io.StringIO(data.decode("utf-8-sig")))
    assert all(x in r.fieldnames for x in ["hostname","pl_name","discoverymethod"]+FIELDS)
    tab=list(r);valid=[]
    for row in tab:
        if row["discoverymethod"] not in ("Transit","Radial Velocity"):continue
        try:
            x=np.array([float(row[k]) for k in FIELDS],float)
        except (ValueError,TypeError):continue
        if np.all(np.isfinite(x)) and np.min(x)>0:
            valid.append((row["hostname"],row["discoverymethod"],x,row["pl_name"]))
    hosts={}
    for x in valid:hosts.setdefault(x[0],x)
    transit=sorted([v for v in hosts.values() if v[1]=="Transit"],key=lambda v:h(v[0]))
    rv=sorted([v for v in hosts.values() if v[1]=="Radial Velocity"],key=lambda v:h(v[0]))
    n=len(transit); slices={"discovery":transit[:int(.6*n)],"challenge":transit[int(.6*n):int(.8*n)],
         "transit_test":transit[int(.8*n):],"rv_test":rv}
    return {k:np.log(np.array([v[2] for v in vals],float)) for k,vals in slices.items()},\
           {k:[v[0] for v in vals] for k,vals in slices.items()},len(tab),len(valid),len(hosts)
def coef(D,t,s):
    matrix=np.stack([np.ones(len(D))]+[D[:,i] for i in s],axis=1)
    return np.linalg.lstsq(matrix,D[:,t],rcond=None)[0]
def output(D,s,b):return b[0]+sum(b[k+1]*D[:,i] for k,i in enumerate(s))
def choices(D,target):
    out=[]
    for a in range(D.shape[1]):
        if a!=target:out.append([a])
    for a in range(D.shape[1]):
        for b in range(a+1,D.shape[1]):
            if target not in (a,b):out.append([a,b])
    return out
def score(D,t,s):
    std=float(D[:,t].std())
    if std<=.2:return None
    v=[]
    for fold in range(3):
        test=np.arange(fold,len(D),3)
        train=np.array([i for i in range(len(D)) if i%3!=fold])
        b=coef(D[train],t,s)
        v.extend(abs(D[test,t]-output(D[test],s,b)).tolist())
    return float((np.median(v)+.2*np.percentile(v,90))/std+.005*len(s))
def ranking(D,t=None):
    items=[]
    for j in range(D.shape[1]):
        if t is not None and j!=t:continue
        for p in choices(D,j):
            sc=score(D,j,p)
            if sc is not None:items.append((sc,j,p))
    return sorted(items,key=lambda z:(z[0],z[1],tuple(z[2])))
def metrics(D,t,s,betas):
    pred=np.exp(np.clip(output(D,s,betas),-700,700))
    actual=np.exp(D[:,t])
    er=abs(pred-actual)/actual
    return {"n":len(er),"median_relative_pct":100*float(np.median(er)),
        "p90_relative_pct":100*float(np.percentile(er,90)),
        "fraction_within_15pct":float(np.mean(er<=.15)),
        "mean_relative_pct":100*float(np.mean(er)),
        "rmse":float(np.sqrt(np.mean((actual-pred)**2)))}
def same_num(a,b):
    assert math.isclose(float(a),float(b),abs_tol=2e-8,rel_tol=2e-8),(a,b)
def run(folder):
    root=Path(folder)
    source=(root/"nasa_source.csv").read_bytes()
    sealed=json.loads((root/"sealed_before_holdout.json").read_text())
    original=json.loads((root/"audit.json").read_text())
    x,hosts,nall,nvalid,nhost=build(source)
    assert hashlib.sha256(source).hexdigest()==original["provenance"]["source_sha256"]
    assert [nall,nvalid,nhost]==[original["provenance"][k] for k in ("all_catalogue_rows","valid_all_feature_rows","unique_host_rows")]
    for k in hosts:
        assert hosts[k]==sealed["hostnames"][k]
    t=sealed["target_idx"]
    initial=ranking(x["discovery"])
    assert t==initial[0][1]
    D,H=x["discovery"],x["challenge"]
    mean=np.delete(D,t,axis=1).mean(axis=0)
    sd=np.maximum(np.delete(D,t,axis=1).std(axis=0),1e-10)
    assert len(sealed["policies"])==9 and len(original["results"])==9
    steps=0
    for pi,policy in enumerate(sealed["policies"]):
        observed=[]
        rng=np.random.default_rng(policy["seed"]) if policy["seed"] is not None else None
        order=[z for z in initial if z[1]==t]
        assert len(policy["trace"])==24
        for n,trace in enumerate(policy["trace"]):
            known=np.concatenate([D,H[observed]],axis=0) if observed else D
            current=ranking(known,t) if observed else order
            best=current[0];src=best[2]
            assert trace["current_model"]["target"]==t
            assert trace["current_model"]["sources"]==src
            same_num(trace["current_model"]["score"],best[0])
            available=np.array([i for i in range(len(H)) if i not in observed],int)
            if rng is not None:
                chosen=int(rng.choice(available))
            else:
                masked=H.copy()
                masked[:,t]=np.nan
                forecasts=[]
                for _,_,p in current[:5]:
                    forecasts.append(output(masked[available],p,coef(known,t,p)))
                uncert=np.std(np.asarray(forecasts),axis=0)
                if observed:
                    z=(np.delete(masked,t,axis=1)-mean)/sd
                    delta=z[available,None,:]-z[np.array(observed),:][None,:,:]
                    nearest=np.min(np.sqrt((delta**2).sum(axis=2)),axis=1)
                    uncert=uncert*(1+.2*np.minimum(3,nearest))
                chosen=int(available[np.argmax(uncert)])
            assert chosen==trace["row"]==policy["queried_challenge_rows"][n]
            beta=coef(known,t,src)
            forecast=float(output(H[[chosen]],src,beta)[0])
            same_num(forecast,trace["forecast_log"])
            same_num(H[chosen,t],trace["observed_log"])
            observed.append(chosen);steps+=1
        final=np.concatenate([D,H[observed]],axis=0)
        best=ranking(final,t)[0]
        assert best[2]==policy["model"]["sources"]
        same_num(best[0],policy["model"]["score"])
        learned=coef(final,t,best[2])
        for actual,stored in zip(learned,policy["coef"]):same_num(actual,stored)
        one=next(r for r in ranking(final,t) if len(r[2])==1)
        assert one[2]==policy["one_input"]["sources"]
        linear=coef(final,t,one[2])
        for actual,stored in zip(linear,policy["one_input_coef"]):same_num(actual,stored)
        a=metrics(x["rv_test"],t,best[2],learned)
        b=metrics(x["rv_test"],t,one[2],linear)
        c=metrics(x["transit_test"],t,best[2],learned)
        for typ,computed in (("rv",a),("rv_single_feature",b),("transit_test",c)):
            record=original["results"][pi][typ]
            for k in record:same_num(computed[k],record[k])
        acceptance=(a["median_relative_pct"]<=5 and a["fraction_within_15pct"]>=.9
            and a["median_relative_pct"]<=.75*b["median_relative_pct"] and c["median_relative_pct"]<=5)
        expected="ACCEPT_CATALOGUE_INVARIANT_TRANSFER" if acceptance else "REFUSE_CATALOGUE_INVARIANT"
        assert original["results"][pi]["verdict"]==expected
        assert len(set(observed))==24
    assert steps==216
    out={"verdict":"INDEPENDENT_SOURCE_AND_216_PROBES_AUDIT_PASS","policies":len(sealed["policies"]),
        "probe_decisions_verified":steps,"holdout_rv":len(x["rv_test"]),
        "holdout_transit":len(x["transit_test"]),
        "selected_target":FIELDS[t],"origin_SHA256":hashlib.sha256(source).hexdigest(),
        "study_verdict":original["verdict"],
        "warning":"NASA catalogue values may contain calculated orbital parameters, so does not prove a new physical law"}
    (root/"independent_receipt.json").write_text(json.dumps(out,indent=2)+"\n")
    print("INDEPENDENT_EXOPLANET_AUDIT_PASS",json.dumps(out),flush=True)
if __name__=="__main__":run(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_exoplanet")
