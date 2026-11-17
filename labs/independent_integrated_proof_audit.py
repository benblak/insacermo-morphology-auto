#!/usr/bin/env python3
"""INDEPENDENT original-archive auditor for integrated INSACERMO proof-carrying chain.
Does not import the orchestration, NOAA learner/parser, or local C3 model helper.
Rechecks exact raw NOAA bytes and recomputes three wave-reading observations.
"""
from __future__ import annotations
import sys,json,gzip,hashlib,math
from pathlib import Path
from datetime import datetime,timedelta,timezone
EXPECTED={
 "41002h2023.txt.gz":"187185a0fc30bb0407760703239034427be331518051ca7e5192247138b04e8e",
 "42002h2023.txt.gz":"1b9906c76b1da6cb6abccf521db4e6e59d035cf341f86f2b3351507c9db54f0b",
 "46002h2023.txt.gz":"93f488bdc6cc78a10469f20089eb337c8166f15845777de84a6c101fee7e8d04"}
BASE=datetime(2000,1,1,tzinfo=timezone.utc)
def independent_rows(raw):
 headers=None;out={}
 for txt in gzip.decompress(raw).decode("utf8").splitlines():
  if txt.startswith("#"):
   h=txt.lstrip("#").split()
   if "WVHT" in h and "WSPD" in h and "APD" in h:
    headers={name:i for i,name in enumerate(h)}
   continue
  if headers is None or not txt.strip():continue
  parts=txt.split()
  if len(parts)<len(headers):continue
  try:
   y=int(parts[headers["YY" if "YY" in headers else "YYYY"]])
   if y<100:y+=(2000 if y<70 else 1900)
   dt=datetime(y,int(parts[headers["MM"]]),int(parts[headers["DD"]]),
     int(parts[headers["hh"]]),int(parts[headers["mm"]]),tzinfo=timezone.utc)
   wave=float(parts[headers["WVHT"]])
   apd=float(parts[headers["APD"]])
   wind=float(parts[headers["WSPD"]])
   out[dt]=dict(wave_dm=(int(round(wave*10)) if 0<=wave<=40 else None),
     wave_present=0<=wave<=40,apd_present=1<=apd<=25,wind_present=0<=wind<=75)
  except (ValueError,OverflowError,IndexError):pass
 return out
def mean_measure(rows,monthyear):
 hourly=sorted(rows.items())
 return {"rows":len(rows),"wave_presence_count":sum(v["wave_present"] for v in rows.values())}
def check(root):
 root=Path(root)
 audit=json.loads((root/"audit.json").read_text())
 assert audit["verdict"]=="INTEGRATED_C3_LEAN_CHAIN_PASS"
 rows={}
 for fname,expected in EXPECTED.items():
  source=(root/"raw"/fname).read_bytes()
  assert hashlib.sha256(source).hexdigest()==expected,(fname,"HASH_MISMATCH")
  rows[fname]=independent_rows(source)
 train=rows["41002h2023.txt.gz"]
 val=rows["42002h2023.txt.gz"]
 assert len(train)==audit["real_noaa"]["clock_training_rows"]
 assert len(val)==audit["real_noaa"]["clock_validation_rows"]
 counts=[[0,0] for _ in range(3)]
 for dt,record in train.items():
  pos=(int((dt-BASE).total_seconds()//600))%3
  counts[pos][int(record["wave_present"])]+=1
 assert counts==audit["real_noaa"]["clock_fit"]["model"]["phase_counts"],"PHASE_COUNTS_MISMATCH"
 fit=audit["real_noaa"]["clock_fit"]
 assert fit["status"]=="PERIODIC" and fit["model"]["period_slots"]==3
 probs=fit["model"]["phase_probability"]
 vtp=vfp=vfn=vtn=0
 brier=0
 for dt,record in val.items():
  idx=int((dt-BASE).total_seconds()//600)%3
  pr=probs[idx];label=int(record["wave_present"])
  predicted=pr>=.5
  if predicted and label:vtp+=1
  elif predicted and not label:vfp+=1
  elif not predicted and label:vfn+=1
  else:vtn+=1
  brier+=(pr-label)**2
 assert abs(brier/len(val)-audit["real_noaa"]["clock_validation"]["brier"])<1e-14
 assert (vtp,vfp,vfn,vtn)==tuple(audit["real_noaa"]["clock_validation"]["confusion"][x]
                  for x in ("tp","fp","fn","tn"))
 dt=datetime(2023,2,23,10,10,tzinfo=timezone.utc)
 wave=rows["46002h2023.txt.gz"]
 before=wave[dt-timedelta(minutes=30)]["wave_dm"]
 missing=wave[dt]["wave_dm"]
 after=wave[dt+timedelta(minutes=30)]["wave_dm"]
 assert (before,missing,after)==(74,None,80)
 p=audit["real_noaa"]["endpoint"]
 assert p["measured_left_dm"]==before and p["measured_right_dm"]==after
 assert p["central_height"]=="UNKNOWN" and p["observed_minimum_net_difference_dm"]==6
 assert len(audit["c3_certificates"])==5
 expected={
 "REAL_ACT_NET_ENDPOINT_CHANGE":"ACT",
 "REAL_REFUSE_UNOBSERVED_CENTER":"REFUSE_ROBUST",
 "SYNTHETIC_PROBE":"PROBE",
 "SYNTHETIC_ACT_AFTER_PROBE":"ACT",
 "SYNTHETIC_STATE_REPAIR":"REPAIR"}
 for name,v in expected.items():
  assert audit["c3_certificates"][name]["verdict"]==v
  d=root/"C3_certificates"/name
  j=json.loads((d/"receipt.json").read_text())
  contract=(d/"contract.json").read_bytes()
  assert j["receipt_sha256"]==audit["c3_certificates"][name]["receipt_sha256"]
  assert hashlib.sha256(contract).hexdigest()==j["contract_sha256"]
  assert hashlib.sha256((d/"C3Decision.lean").read_bytes()).hexdigest()==j["source_sha256"]
  assert j["scope"]=="EXACT FINITE C3 ENVELOPES AND DECLARED PROBE/REPAIR GRAMMAR"
 assert audit["synthetic_structure"]["global_law_certified"] is False
 assert audit["unknown_physical_midpoint"]=="REFUSE_ROBUST"
 assert audit["global_law_claim"]=="REFUSE_UNCONDITIONAL"
 assert audit["n_stages"]==len(audit["stages"])
 assert audit["lean_evidence_sha256"]==hashlib.sha256((root/"NoaaEvidence.lean").read_bytes()).hexdigest()
 result=dict(verdict="INDEPENDENT_INTEGRATED_BRIDGE_PASS",
   checked_sources=list(EXPECTED),train_wave_clock_phase_counts=counts,
   holdout_f1=audit["real_noaa"]["clock_validation"]["f1"],
   true_observed_endpoints_dm=[before,after],
   unobserved_midpoint="UNKNOWN",
   c3_local_receipt_source_hashes_checked=5,
   no_universal_discovery_claim=True)
 (root/"independent_receipt.json").write_text(json.dumps(result,indent=2)+"\n")
 print(result["verdict"],"SOURCE_FILES",len(EXPECTED),
       "C3_RECEIPTS",len(audit["c3_certificates"]),flush=True)
if __name__=="__main__":check(sys.argv[1])
