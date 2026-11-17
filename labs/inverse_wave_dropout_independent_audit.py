#!/usr/bin/env python3
"""Independent raw byte-based recount; no imports from primary discovery code."""
import gzip,hashlib,json,math,sys
from datetime import datetime,timedelta,timezone
from pathlib import Path
SOURCES=(("41002",2023),("42002",2023),("46002",2023),("41002",2024),("42002",2024))
def rows_from_raw(raw):
 fields=None;rows={}
 for line in raw.decode("utf8").splitlines():
  if line.startswith("#"):
   names=line.lstrip("#").split()
   if "WVHT" in names and "PRES" in names:fields={k:i for i,k in enumerate(names)}
   continue
  if fields is None:continue
  a=line.split()
  if len(a)<len(fields):continue
  try:
   y=int(a[fields.get("YY",fields.get("YYYY"))])
   if y<100:y+=2000 if y<70 else 1900
   dt=datetime(y,int(a[fields["MM"]]),int(a[fields["DD"]]),int(a[fields["hh"]]),int(a[fields["mm"]]),tzinfo=timezone.utc)
   rows[dt]={k:float(a[fields[k]]) for k in ("WVHT","WSPD","PRES","GST")}
  except (ValueError,IndexError,OverflowError):pass
 return rows
def good(r,k):
 a,b={"WVHT":(0,40),"WSPD":(0,75),"PRES":(870,1085),"GST":(0,95)}[k]
 return a<=r[k]<=b
def recount(rows,model):
 base=model["baseline"]["prob"];selected=model["selected"];probs=model["model"]["probs"];t=model["threshold"]
 c=[[0,0],[0,0]];ll=bll=se=bse=0.0
 for dt,v in sorted(rows.items()):
  if dt.minute not in (10,40):continue
  old=rows.get(dt-timedelta(minutes=30))
  if old is None or not all(good(v,k) for k in ("WSPD","PRES","GST")):continue
  y=int(not good(v,"WVHT"))
  feats=dict(previous_dropout=int(not good(old,"WVHT")),night=int(dt.hour<6),
    high_wind=int(v["WSPD"]>=t["wind"]),high_gust=int(v["GST"]>=t["gust"]),
    low_pressure=int(v["PRES"]<=t["pressure"]))
  j=feats[selected] if selected else 0
  p=probs[j] if selected else base
  c[j][y]+=1
  ll-=math.log(p if y else 1-p)
  bll-=math.log(base if y else 1-base)
  se+=(p-y)**2;bse+=(base-y)**2
 n=sum(sum(x) for x in c)
 return dict(table=c,n=n,dropouts=sum(x[1] for x in c),logloss=ll/n,baseline_logloss=bll/n,brier=se/n,baseline_brier=bse/n)
def main(root):
 root=Path(root);p=root/"model_sealed_before_holdouts.json"
 raw=p.read_bytes();model=json.loads(raw);result=json.loads((root/"audit.json").read_text())
 assert hashlib.sha256(raw).hexdigest()==result["model_seal_sha256"]
 checks=[]
 for i,(st,yr) in enumerate(SOURCES):
  zipped=(root/"raw"/f"{st}h{yr}.txt.gz").read_bytes()
  assert hashlib.sha256(zipped).hexdigest()==model["digests"][i]
  observed=recount(rows_from_raw(gzip.decompress(zipped)),model)
  expected=result["training"] if i==0 else result["transfer"][i-1]
  for k in ("n","table","dropouts"):assert observed[k]==expected[k],(st,yr,k)
  for k in ("brier","baseline_brier","logloss","baseline_logloss"):
   assert abs(observed[k]-expected[k])<1e-12,(st,yr,k)
  checks.append(dict(station=st,year=yr,n=observed["n"],dropouts=observed["dropouts"],table=observed["table"]))
 rec=dict(verdict="INDEPENDENT_WAVE_DROPOUT_AUDIT_PASS",archives=5,
          real_scheduled_transitions=sum(a["n"] for a in checks),checks=checks,
          model_sha256=result["model_seal_sha256"])
 (root/"independent_receipt.json").write_text(json.dumps(rec,indent=2)+"\n")
 print("INDEPENDENT_WAVE_DROPOUT_AUDIT_PASS",rec["real_scheduled_transitions"])
if __name__=="__main__":main(sys.argv[1])
