#!/usr/bin/env python3
"""Observational dropout test after an empirically discovered NOAA 30-minute clock.
All primary 2023/24 raw files verified against previous study SHA256.
Preregistered labs/INVERSE_WAVE_DROPOUT_MECHANISM_PREREG_20261117.md
"""
from __future__ import annotations
import gzip,hashlib,json,math,time,urllib.request,sys
from pathlib import Path
from datetime import datetime,timedelta,timezone
SOURCES=[("41002",2023),("42002",2023),("46002",2023),("41002",2024),("42002",2024)]
DIGEST=["187185a0fc30bb0407760703239034427be331518051ca7e5192247138b04e8e","1b9906c76b1da6cb6abccf521db4e6e59d035cf341f86f2b3351507c9db54f0b","93f488bdc6cc78a10469f20089eb337c8166f15845777de84a6c101fee7e8d04","ea3578e57bb19e68924cb543c3940c0a1bdd0bd46d76ff90a5b21c6856ac73d7","b6671bb26e0f1503d2af1a27af4d89c99f933c29dc1f3d752afef7030a1e947a"]
KIND=("previous_dropout","high_wind","low_pressure","night","high_gust")
LIM={"WSPD":(0,75),"GST":(0,95),"PRES":(870,1085),"WVHT":(0,40)}
def fetch(i,root):
 st,yr=SOURCES[i]; url=f"https://www.ndbc.noaa.gov/data/historical/stdmet/{st}h{yr}.txt.gz"; name=root/f"{st}h{yr}.txt.gz"
 for retry in range(3):
  try:
   if name.is_file():z=name.read_bytes()
   else:
    with urllib.request.urlopen(urllib.request.Request(url,headers={"User-Agent":"INSACERMO experimental data reproducibility"}),timeout=60) as f:z=f.read()
   sha=hashlib.sha256(z).hexdigest()
   if sha!=DIGEST[i]:raise RuntimeError(f"SOURCE_MISMATCH {sha} {DIGEST[i]}")
   name.write_bytes(z)
   return gzip.decompress(z)
  except Exception as exc:
   if retry==2 or "SOURCE_MISMATCH" in str(exc):raise
   time.sleep(2*(retry+1))
def parse(raw):
 fields=None;rows={}
 for line in raw.decode().splitlines():
  if line.startswith("#"):
   names=line.lstrip("#").split()
   if all(k in names for k in ("WSPD","GST","PRES","WVHT")):fields={k:i for i,k in enumerate(names)}
   continue
  if fields is None or not line.strip():continue
  a=line.split()
  if len(a)<len(fields):continue
  try:
   y=int(a[fields.get("YY",fields.get("YYYY"))])
   if y<100:y+=2000 if y<70 else 1900
   dt=datetime(y,int(a[fields["MM"]]),int(a[fields["DD"]]),int(a[fields["hh"]]),int(a[fields["mm"]]),tzinfo=timezone.utc)
   rows[dt]={k:float(a[fields[k]]) for k in LIM}
  except (ValueError,IndexError,OverflowError):pass
 assert len(rows)>1000
 return rows
def ok(r,k):
 lo,hi=LIM[k]
 return lo<=r[k]<=hi
def qtile(a,t):
 a=sorted(a);i=(len(a)-1)*t;j=int(i);return a[j]+(a[min(len(a)-1,j+1)]-a[j])*(i-j)
def extract(rows,threshold=None):
 obs=[]
 for dt,v in sorted(rows.items()):
  if dt.minute%30!=10:continue
  prev=rows.get(dt-timedelta(minutes=30))
  if prev is None or not all(ok(v,k) for k in ("WSPD","PRES","GST")):continue
  feat={"previous_dropout":int(not ok(prev,"WVHT")),"night":int(dt.hour<6)}
  if threshold is not None:
   feat.update(high_wind=int(v["WSPD"]>=threshold["wind"]),
       low_pressure=int(v["PRES"]<=threshold["pressure"]),
       high_gust=int(v["GST"]>=threshold["gust"]))
  obs.append((dt,v,int(not ok(v,"WVHT")),feat))
 return obs
def null_fit(obs):
 n=len(obs);hits=sum(z[2] for z in obs);p=(hits+1)/(n+2)
 ll=hits*math.log(p)+(n-hits)*math.log1p(-p)
 return dict(n=n,dropouts=hits,prob=p,bic=-2*ll+math.log(n))
def fit(obs,k):
 t=[[0,0],[0,0]]
 for _,_,y,f in obs:t[f[k]][y]+=1
 probs=[(a[1]+1)/(sum(a)+2) for a in t]
 ll=sum(a[1]*math.log(p)+a[0]*math.log1p(-p) for a,p in zip(t,probs))
 return dict(name=k,tables=t,probs=probs,bic=-2*ll+2*math.log(len(obs)))
def metrics(obs,feature,m,baseline):
 cp=[[0,0],[0,0]];l0=l1=b0=b1=0.
 for _,_,y,f in obs:
  j=f[feature] if feature else 0;p=m["probs"][j] if feature else baseline["prob"]
  z=baseline["prob"];cp[j][y]+=1
  l1-=y*math.log(p)+(1-y)*math.log1p(-p)
  l0-=y*math.log(z)+(1-y)*math.log1p(-z)
  b1+=(p-y)**2;b0+=(z-y)**2
 n=len(obs)
 r0=cp[0][1]/max(1,sum(cp[0]));r1=cp[1][1]/max(1,sum(cp[1]))
 return dict(n=n,dropouts=sum(o[2] for o in obs),table=cp,
    delta_event_rate=r1-r0,rate_0=r0,rate_1=r1,
    logloss=l1/n,baseline_logloss=l0/n,logloss_gain=1-l1/l0,
    brier=b1/n,baseline_brier=b0/n,brier_gain=1-b1/b0)
def experiment(root):
 out=Path(root);out.mkdir(parents=True,exist_ok=True);raw=out/"raw";raw.mkdir(exist_ok=True)
 r=parse(fetch(0,raw));plain=extract(r)
 assert len(plain)>1000
 threshold={"wind":qtile([v["WSPD"] for _,v,_,_ in plain],.9),
            "pressure":qtile([v["PRES"] for _,v,_,_ in plain],.1),
            "gust":qtile([v["GST"] for _,v,_,_ in plain],.9)}
 obs=extract(r,threshold);base=null_fit(obs)
 fitted=sorted([fit(obs,k) for k in KIND],key=lambda d:(d["bic"],d["name"]))
 best=fitted[0];chosen=best["name"] if base["bic"]-best["bic"]>10 else None
 model=best if chosen else {"name":None,"probs":[base["prob"]]*2}
 seal=dict(prereg_sha="da4e043587e01f642125034d057a543cc5b2ac01",
    fixed_sources=SOURCES,digests=DIGEST,threshold=threshold,baseline=base,
    candidates=fitted,selected=chosen,model=model,training=metrics(obs,chosen,model,base))
 target=out/"model_sealed_before_holdouts.json"
 target.write_text(json.dumps(seal,sort_keys=True,indent=2)+"\n")
 sha=hashlib.sha256(target.read_bytes()).hexdigest()
 print("SEALED_MODEL",sha,chosen,"TRAIN_DROP",base["dropouts"],"TRAIN_N",base["n"],flush=True)
 test=[]
 for i,(st,yr) in enumerate(SOURCES[1:],1):
  rows=parse(fetch(i,raw));observed=extract(rows,threshold)
  z=metrics(observed,chosen,model,base);z.update(station=st,year=yr)
  test.append(z)
  print("CHECK",st,yr,"N",z["n"],"DROPS",z["dropouts"],"LOGGAIN",round(z["logloss_gain"],5),"BRIER",round(z["brier_gain"],5),flush=True)
 if chosen is None:verdict="REFUSE_MECHANISM_NULL_SELECTED"
 else:
  same=sum(z["delta_event_rate"]*seal["training"]["delta_event_rate"]>0 for z in test)
  better=sum(z["logloss_gain"]>0 and z["brier_gain"]>0 for z in test)
  gain=1-sum(z["logloss"]*z["n"] for z in test)/sum(z["baseline_logloss"]*z["n"] for z in test)
  verdict="MECHANISM_ASSOCIATION_TRANSFER_PASS" if same>=3 and better>=3 and gain>=.05 and all(z["dropouts"]>=20 for z in test) else "REFUSE_MECHANISM_TRANSFER"
 result=dict(verdict=verdict,model_seal_sha256=sha,selected=chosen,training=seal["training"],transfer=test,
     warning="Dropout association is not causation; physical wave height at missing records remains unknowable.")
 (out/"audit.json").write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
 print("FINAL_VERDICT",verdict,flush=True)
if __name__=="__main__":
 path=sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_wave_dropout"
 try:experiment(path)
 except Exception as e:
  d={"verdict":"INFEASIBLE","error":str(e)}
  p=Path(path);p.mkdir(parents=True,exist_ok=True)
  (p/"audit.json").write_text(json.dumps(d,indent=2)+"\n")
  print("INFEASIBLE",str(e),flush=True)
