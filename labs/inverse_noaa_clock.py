#!/usr/bin/env python3
"""INSACERMO inverse: learn an unknown sampling clock from missing NOAA wave records.
No prior wave sampling period or station-specific phase is given.
Train ONLY on NOAA 41002 (2023); four archives are separate falsification tests.
Scientific interpretation: acquisition protocol, NOT a novel physical law.
"""
from __future__ import annotations
import gzip, hashlib, json, math, os, sys, time, urllib.request
from datetime import datetime, timezone
from pathlib import Path

TRAIN=("41002",2023)
VALID=(("42002",2023),("46002",2023),("41002",2024),("42002",2024))
PREREG_COMMIT="5f9e4e1daf21d801d08538b459608140ac06e1ad"
CHANNELS={"WVHT":(0,40),"APD":(1,25),"WSPD":(0,75)}
BASE=datetime(2000,1,1,tzinfo=timezone.utc)
def get_url(station,year):
    return f"https://www.ndbc.noaa.gov/data/historical/stdmet/{station}h{year}.txt.gz"

def retrieve(station,year,output):
    filename=f"{station}h{year}.txt.gz"
    url=get_url(station,year)
    err=None
    for attempt in range(3):
        try:
            req=urllib.request.Request(url,headers={"User-Agent":"INSACERMO research provenance audit 2026"})
            with urllib.request.urlopen(req,timeout=65) as handle:
                data=handle.read()
            raw=gzip.decompress(data)
            if len(raw)<100000:raise ValueError("Archive unexpectedly short")
            (output/filename).write_bytes(data)
            return raw,dict(station=station,year=year,url=url,
                gzip_sha256=hashlib.sha256(data).hexdigest(),
                decompressed_sha256=hashlib.sha256(raw).hexdigest(),
                decompressed_bytes=len(raw),filename=filename)
        except Exception as e:
            err=f"{type(e).__name__}: {e}"
            if "404" in err:break
            time.sleep(2*(attempt+1))
    raise RuntimeError(f"NOAA_ARCHIVE_UNAVAILABLE {station} {year}: {err}")

def parse(raw):
    rows=raw.decode("utf-8-sig",errors="strict").splitlines()
    head=next((x for x in rows if x.startswith("#") and "WSPD" in x and "WVHT" in x),None)
    if not head:raise ValueError("missing header")
    header=head.lstrip("#").split()
    yearcol="YYYY" if "YYYY" in header else "YY"
    for k in [yearcol,"MM","DD","hh","mm",*CHANNELS]:
        if k not in header:raise ValueError("missing field "+k)
    columns={k:header.index(k) for k in [yearcol,"MM","DD","hh","mm",*CHANNELS]}
    output=[]
    for text in rows:
        if not text or text.startswith("#"):continue
        a=text.split()
        if len(a)<len(header):continue
        try:
            year=int(a[columns[yearcol]])
            if year<100:year=year+2000 if year<70 else year+1900
            dt=datetime(year,int(a[columns["MM"]]),int(a[columns["DD"]]),
               int(a[columns["hh"]]),int(a[columns["mm"]]),tzinfo=timezone.utc)
            slot=int((dt-BASE).total_seconds()//600)
            bits={}
            for name,(lo,hi) in CHANNELS.items():
                val=float(a[columns[name]])
                bits[name]=int(lo<=val<=hi)
            output.append((slot,bits))
        except (ValueError,OverflowError,IndexError):continue
    if len(output)<1000:raise RuntimeError("too few rows "+str(len(output)))
    return output

def count(y,slots,p):
    c=[[0,0] for _ in range(p)]
    for t,bit in zip(slots,y):c[t%p][bit]+=1
    return c

def fit(y,slots):
    n=len(y)
    def make(p):
        c=count(y,slots,p)
        probs=[(a[1]+1)/(sum(a)+2) for a in c]
        ll=sum(a[1]*math.log(z)+a[0]*math.log1p(-z) for a,z in zip(c,probs))
        return dict(period_slots=p,bic=-2*ll+p*math.log(n),train_loglik=ll,
            phase_probability=probs,phase_counts=c)
    null=make(1)
    fitted=[make(p) for p in range(2,19)]
    winner=min(fitted,key=lambda q:(q["bic"],q["period_slots"]))
    if winner["bic"] < null["bic"] - 10:
        model=winner
        status="PERIODIC"
    else:
        model=null
        status="NULL"
    return dict(status=status,model=model,null=null,
       candidates=[dict(period_minutes=v["period_slots"]*10,bic=v["bic"]) for v in fitted],
       bic_advantage=null["bic"]-model["bic"],train_size=n,
       train_rate=float(sum(y)/n))

def metrics(y,slots,fitted):
    n=len(y)
    p=fitted["model"]["period_slots"]
    probs=fitted["model"]["phase_probability"]
    pn=fitted["null"]["phase_probability"][0]
    brier=sum((probs[t%p]-bit)**2 for t,bit in zip(slots,y))/n
    null_brier=sum((pn-bit)**2 for bit in y)/n
    logloss=-sum(bit*math.log(probs[t%p])+
            (1-bit)*math.log1p(-probs[t%p]) for t,bit in zip(slots,y))/n
    null_logloss=-sum(bit*math.log(pn)+(1-bit)*math.log1p(-pn) for bit in y)/n
    tp=fp=fn=tn=0
    for t,bit in zip(slots,y):
        pred=int(probs[t%p]>=.5)
        if pred and bit:tp+=1
        elif pred and not bit:fp+=1
        elif not pred and bit:fn+=1
        else:tn+=1
    precision=tp/(tp+fp) if tp+fp else 0
    recall=tp/(tp+fn) if tp+fn else 0
    f1=2*tp/(2*tp+fp+fn) if 2*tp+fp+fn else 0
    return dict(rows=n,actual_present=sum(y),prevalence=sum(y)/n,
        f1=f1,precision=precision,recall=recall,
        confusion=dict(tp=tp,fp=fp,fn=fn,tn=tn),
        brier=brier,null_brier=null_brier,brier_relative_gain=1-brier/null_brier,
        logloss=logloss,null_logloss=null_logloss,logloss_relative_gain=1-logloss/null_logloss,
        phase_counts=count(y,slots,p))
def split(data,name):
    return [b[name] for _,b in data],[t for t,_ in data]

def main(folder):
    root=Path(folder);root.mkdir(parents=True,exist_ok=True)
    raw=root/"raw_noaa";raw.mkdir(exist_ok=True)
    provenance=[]
    archive,src=retrieve(*TRAIN,raw)
    provenance.append(src)
    train=parse(archive)
    slots=[t for t,_ in train]
    models={}
    for channel in CHANNELS:
        labels=[b[channel] for _,b in train]
        models[channel]=fit(labels,slots)
    # Seal trained period, phase probabilities and source BEFORE reading any validation file.
    seal=dict(prereg_commit=PREREG_COMMIT,train_station=TRAIN[0],train_year=TRAIN[1],
        validation=list(VALID),train_provenance=provenance[0],models=models,
        train_checks={k:metrics(*split(train,k),v) for k,v in models.items()})
    sealed=(root/"sealed_before_validation.json")
    sealed.write_text(json.dumps(seal,indent=2,sort_keys=True)+"\n")
    digest=hashlib.sha256(sealed.read_bytes()).hexdigest()
    print("SEALED_BEFORE_VALIDATION",digest,
          {k:(v["status"],v["model"]["period_slots"]*10) for k,v in models.items()},flush=True)
    checked=[]
    for station,year in VALID:
        blob,prov=retrieve(station,year,raw);provenance.append(prov)
        data=parse(blob)
        item=dict(station=station,year=year,rows=len(data))
        item["channels"]={k:metrics(*split(data,k),v) for k,v in models.items()}
        checked.append(item)
        print("VALIDATE",station,year,"WVHT_F1",round(item["channels"]["WVHT"]["f1"],5),
              "WVHT_BRIER_GAIN",round(item["channels"]["WVHT"]["brier_relative_gain"],5),flush=True)
    wvht=models["WVHT"];apd=models["APD"];wspd=models["WSPD"]
    a,b=split(train,"WVHT")[0],split(train,"APD")[0]
    agreement=sum(x==y for x,y in zip(a,b))/len(a)
    criteria=dict(
      wave_period_found=wvht["status"]=="PERIODIC",
      same_period_wave_related=wvht["model"]["period_slots"]==apd["model"]["period_slots"],
      wave_apd_presence_agreement_99pct=agreement>=.99,
      wind_negative_control=wspd["status"]=="NULL" or wspd["bic_advantage"]<=10,
      all_four_cross_station_f1_90pct=all(r["channels"]["WVHT"]["f1"]>=.90 for r in checked),
      all_four_cross_station_brier_gain_40pct=all(
          r["channels"]["WVHT"]["brier_relative_gain"]>.40 for r in checked))
    verdict="INVERSE_OBSERVATION_CLOCK_PASS" if all(criteria.values()) else "REFUSE_CLOCK_GENERALIZATION"
    result=dict(verdict=verdict,criteria=criteria,train_source=TRAIN,validation=checked,
       all_sources=provenance,seal_sha256=digest,strict_model_freeze=True,
       wave_apd_training_agreement=agreement,
       inferred_wave_period_minutes=wvht["model"]["period_slots"]*10,
       inferred_wave_phase_response_probabilities=wvht["model"]["phase_probability"],
       statement="A reproducible data-acquisition regularity, NOT a newly discovered natural physical law.")
    (root/"audit.json").write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print("INVERSE_CLOCK_VERDICT",verdict,json.dumps(criteria,sort_keys=True),flush=True)
    return result
if __name__=="__main__":
    folder=sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_noaa_hidden_clock"
    try:main(folder)
    except Exception as e:
        root=Path(folder);root.mkdir(parents=True,exist_ok=True)
        report=dict(verdict="INFEASIBLE",reason=f"{type(e).__name__}: {e}",
            seal_created=(root/"sealed_before_validation.json").exists())
        (root/"audit.json").write_text(json.dumps(report,indent=2)+"\n")
        print("INFEASIBLE",json.dumps(report),flush=True)
