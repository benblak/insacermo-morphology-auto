#!/usr/bin/env python3
"""Independent byte-level NOAA endpoint checker. Never imports primary learner."""
import sys,json,gzip,hashlib,urllib.request
from pathlib import Path
from datetime import datetime,timedelta,timezone
S=(("41002",2023),("42002",2023),("46002",2023),("41002",2024),("42002",2024))
def independent_intervals(raw):
 headers=None;data={}
 for line in gzip.decompress(raw).decode("utf-8").splitlines():
  if line.startswith("#"):
   hdr=line.lstrip("#").split()
   if "WVHT" in hdr and "WSPD" in hdr:headers={z:i for i,z in enumerate(hdr)}
   continue
  if not headers:continue
  parts=line.split()
  if len(parts)<len(headers):continue
  try:
   yr=int(parts[headers["YY" if "YY" in headers else "YYYY"]])
   if yr<100:yr+=2000 if yr<70 else 1900
   date=datetime(yr,int(parts[headers["MM"]]),int(parts[headers["DD"]]),int(parts[headers["hh"]]),int(parts[headers["mm"]]),tzinfo=timezone.utc)
   wave=float(parts[headers["WVHT"]])
   data[date]=round(wave*10) if 0<=wave<=40 else None
  except (ValueError,IndexError,OverflowError):pass
 events={True:{"n":0,"e5":0,"e10":0,"e1":0},False:{"n":0,"e5":0,"e10":0,"e1":0}}
 examples=[]
 for t in sorted(data):
  if t.minute%30!=10:continue
  start=t-timedelta(minutes=30);end=t+timedelta(minutes=30)
  if start not in data or end not in data:continue
  left=data[start];right=data[end]
  if left is None or right is None:continue
  gap=data[t] is None;d=abs(right-left)
  a=events[gap];a["n"]+=1;a["e5"]+=d>=5;a["e10"]+=d>=10;a["e1"]+=d>=1
  if gap and len(examples)<5:
   examples.append((t.isoformat(),left/10,right/10,d/10))
 return events,examples,len(data)
def run(folder):
 root=Path(folder);a=json.loads((root/"audit.json").read_text())
 assert a["verdict"] in ("REFUSE_PHYSICAL_ASSOCIATION","PHYSICAL_ENDPOINT_GAP_ASSOCIATION_PASS")
 checks=[]
 for i,(station,year) in enumerate(S):
  raw=(root/"raw"/f"{station}h{year}.txt.gz").read_bytes()
  assert hashlib.sha256(raw).hexdigest()==a["original_sha256"][i]
  (gap,normal),examples,n=(None,None),None,None
  table,examples,n=independent_intervals(raw)
  q=a["exploratory_source"] if i==0 else a["falsification_sources"][i-1]
  assert (n,table[True]["n"],table[False]["n"])==(q["rows"],q["gaps"],q["controls"])
  assert (table[True]["e5"],table[True]["e10"],table[True]["e1"])==(q["gap_change_ge_05"],q["gap_change_ge_10"],q["gap_nonzero_01"])
  assert (table[False]["e5"],table[False]["e10"])==(q["control_change_ge_05"],q["control_change_ge_10"])
  assert len(examples)==len(q["examples"])
  for (dt,l,r,d),e in zip(examples,q["examples"]):
   assert e["middle_time_UTC"]==dt and e["missing_midpoint"]=="UNKNOWN"
   assert all(abs(x-y)<1e-10 for x,y in [(l,e["start_observed_m"]),(r,e["end_observed_m"]),(d,e["net_observed_change_m"])])
  checks.append({"station":station,"year":year,"gaps":table[True]["n"],"measured_gap_variations_ge05":table[True]["e5"]})
 out={"result":"INDEPENDENT_WAVE_ENDPOINTS_PASS","archives":len(checks),
      "eligible_missing":sum(x["gaps"] for x in checks),
      "exact_measured_05_events":sum(x["measured_gap_variations_ge05"] for x in checks),
      "independently_verified":checks,"verdict":a["verdict"],
      "midpoints_fabricated":0}
 (root/"independent_receipt.json").write_text(json.dumps(out,indent=2)+"\n")
 print(out["result"],"gaps",out["eligible_missing"],"observed_net_changes",out["exact_measured_05_events"])
if __name__=="__main__":run(sys.argv[1])
