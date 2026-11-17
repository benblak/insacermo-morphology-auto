#!/usr/bin/env python3
"""NOAA inverse discovery: infer only end-to-end measured change across absent WVHT.
Preregistered before reading endpoints. Never impute missing center.
"""
import gzip,hashlib,json,random,sys,urllib.request,time
from datetime import datetime,timedelta,timezone
from collections import defaultdict
from pathlib import Path
SRC=[("41002",2023),("42002",2023),("46002",2023),("41002",2024),("42002",2024)]
SHA=["187185a0fc30bb0407760703239034427be331518051ca7e5192247138b04e8e","1b9906c76b1da6cb6abccf521db4e6e59d035cf341f86f2b3351507c9db54f0b","93f488bdc6cc78a10469f20089eb337c8166f15845777de84a6c101fee7e8d04","ea3578e57bb19e68924cb543c3940c0a1bdd0bd46d76ff90a5b21c6856ac73d7","b6671bb26e0f1503d2af1a27af4d89c99f933c29dc1f3d752afef7030a1e947a"]
SEED=20261117
def source(i,root):
 s,y=SRC[i];p=root/f"{s}h{y}.txt.gz";url=f"https://www.ndbc.noaa.gov/data/historical/stdmet/{s}h{y}.txt.gz"
 if p.exists():z=p.read_bytes()
 else:
  for k in range(3):
   try:
    with urllib.request.urlopen(urllib.request.Request(url,headers={"User-Agent":"INSACERMO independent observational audit"}),timeout=55) as r:z=r.read()
    break
   except Exception:
    if k==2:raise
    time.sleep(2*(k+1))
 assert hashlib.sha256(z).hexdigest()==SHA[i],(i,hashlib.sha256(z).hexdigest())
 p.write_bytes(z)
 return gzip.decompress(z)
def read(raw):
 fields=None;rows={}
 for line in raw.decode().splitlines():
  if line.startswith("#"):
   h=line.lstrip("#").split()
   if "WVHT" in h and "WSPD" in h:fields={k:i for i,k in enumerate(h)}
   continue
  if not fields or not line.strip():continue
  a=line.split()
  if len(a)<len(fields):continue
  try:
   y=int(a[fields.get("YY",fields.get("YYYY"))])
   if y<100:y+=2000 if y<70 else 1900
   d=datetime(y,int(a[fields["MM"]]),int(a[fields["DD"]]),int(a[fields["hh"]]),int(a[fields["mm"]]),tzinfo=timezone.utc)
   h=float(a[fields["WVHT"]])
   rows[d]=None if h<0 or h>40 else int(round(h*10))
  except (ValueError,OverflowError,IndexError):continue
 return rows
def tabulate(rows,station,year):
 daily=defaultdict(lambda:[0,0,0,0])
 n=control=gap=0;gap_min_change=gap_05=gap_10=0;ctrl_05=ctrl_10=0
 samples=[]
 for dt,mid in sorted(rows.items()):
  if dt.minute not in (10,40):continue
  a=rows.get(dt-timedelta(minutes=30))
  b=rows.get(dt+timedelta(minutes=30))
  if a is None or b is None:continue
  n+=1
  delta=abs(a-b);event=int(delta>=5)
  if mid is None:
   gap+=1;gap_min_change+=int(delta>=1);gap_05+=event;gap_10+=int(delta>=10)
   daily[dt.date().isoformat()][0]+=event
   daily[dt.date().isoformat()][1]+=1
   if len(samples)<5:samples.append({"middle_time_UTC":dt.isoformat(),"start_observed_m":a/10,
       "end_observed_m":b/10,"net_observed_change_m":delta/10,"missing_midpoint":"UNKNOWN"})
  else:
   control+=1;ctrl_05+=event;ctrl_10+=int(delta>=10)
   daily[dt.date().isoformat()][2]+=event
   daily[dt.date().isoformat()][3]+=1
 return dict(station=station,year=year,rows=len(rows),eligible=n,gaps=gap,controls=control,
   gap_nonzero_01=gap_min_change,gap_change_ge_05=gap_05,gap_change_ge_10=gap_10,
   control_change_ge_05=ctrl_05,control_change_ge_10=ctrl_10,
   gap_rate_05=gap_05/gap if gap else None,control_rate_05=ctrl_05/control if control else None,
   rate_difference=(gap_05/gap-ctrl_05/control if gap and control else None),
   rate_ratio=(gap_05/gap)/(ctrl_05/control) if gap and ctrl_05 and control else None,
   examples=samples,day_counts=dict(daily))
def bootstrap(hold):
 rng=random.Random(SEED);days=[list(item["day_counts"].values()) for item in hold]
 if any(not v for v in days):return None
 v=[]
 for _ in range(1000):
  gyes=gno=cyes=cno=0
  for ds in days:
   for _ in range(len(ds)):
    row=ds[rng.randrange(len(ds))]
    gyes+=row[0];gno+=row[1];cyes+=row[2];cno+=row[3]
  if gno and cno:v.append(gyes/gno-cyes/cno)
 v.sort()
 return dict(replicates=len(v),low=v[int(.025*len(v))] if v else None,
             high=v[int(.975*len(v))] if v else None,median=v[len(v)//2] if v else None)
def run(root):
 root=Path(root);root.mkdir(parents=True,exist_ok=True);raw=root/"raw";raw.mkdir(exist_ok=True)
 reports=[]
 for i,(s,y) in enumerate(SRC):
  rec=tabulate(read(source(i,raw)),s,y);reports.append(rec)
  print("INTERVAL",s,y,"GAPS",rec["gaps"],"GAP_GE05",rec["gap_change_ge_05"],
        "CONTROLS",rec["controls"],"CTRL_GE05",rec["control_change_ge_05"],flush=True)
 # Fix the first series as exploration, others as holdouts; no model fitted.
 hold=reports[1:];interval=bootstrap(hold)
 checks=dict(each_holdout_has_20_gaps=all(x["gaps"]>=20 for x in hold),
             at_least_3_of_4_positive_rate_diff=sum(x["rate_difference"] is not None and x["rate_difference"]>0 for x in hold)>=3,
             bootstrap_lower_bound_positive=interval is not None and interval["low"] is not None and interval["low"]>0)
 verdict="PHYSICAL_ENDPOINT_GAP_ASSOCIATION_PASS" if all(checks.values()) else "REFUSE_PHYSICAL_ASSOCIATION"
 summary=[{k:v for k,v in record.items() if k!="day_counts"} for record in reports]
 result=dict(verdict=verdict,checks=checks,exploratory_source=summary[0],
   falsification_sources=summary[1:],bootstrap_95=interval,
   total_valid_interval_endpoints=sum(x["eligible"] for x in reports),
   total_eligible_missing_midpoints=sum(x["gaps"] for x in reports),
   total_gap_measured_change_ge_05=sum(x["gap_change_ge_05"] for x in reports),
   statement="Only 60-minute endpoint differences are observed. Every missing midpoint WVHT remains UNKNOWN; no causal gap mechanism proven.",
   original_sha256=SHA)
 (root/"audit.json").write_text(json.dumps(result,indent=2)+"\n")
 (root/"day_counts.json").write_text(json.dumps([{k:v for k,v in x.items() if k!="examples"} for x in reports])+"\n")
 print("FINAL",verdict,json.dumps(checks),json.dumps(interval),flush=True)
if __name__=="__main__":
 p=sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_inverse_wave_interval"
 try:run(p)
 except Exception as e:
  out=Path(p);out.mkdir(parents=True,exist_ok=True)
  (out/"audit.json").write_text(json.dumps(dict(verdict="INFEASIBLE",reason=str(e)))+"\n")
  print("INFEASIBLE",repr(e),flush=True)
