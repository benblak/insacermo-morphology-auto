#!/usr/bin/env python3
"""Independent verification of actual repaired derived artifact vs ORIGINAL NOAA gzip.
No reuse of repair script's audit or CSV-generation methods.
"""
import sys,gzip,json,csv,hashlib
from pathlib import Path
from datetime import datetime,timedelta,timezone
SHA="93f488bdc6cc78a10469f20089eb337c8166f15845777de84a6c101fee7e8d04"
def digest(raw):return hashlib.sha256(raw).hexdigest()
def main(base,out):
    base=Path(base);out=Path(out)
    raw=(base/"raw"/"46002h2023.txt.gz").read_bytes()
    assert digest(raw)==SHA
    fields=None;seen={}
    for line in gzip.decompress(raw).decode("utf8").splitlines():
        if line.startswith("#"):
            a=line.lstrip("#").split()
            if "WVHT" in a and "WSPD" in a:fields={k:i for i,k in enumerate(a)}
            continue
        if not fields:continue
        a=line.split()
        if len(a)<len(fields):continue
        try:
            y=int(a[fields.get("YY",fields.get("YYYY"))])
            if y<100:y+=2000 if y<70 else 1900
            dt=datetime(y,int(a[fields["MM"]]),int(a[fields["DD"]]),
              int(a[fields["hh"]]),int(a[fields["mm"]]),tzinfo=timezone.utc)
            h=float(a[fields["WVHT"]])
            seen[dt]=h if 0<=h<=40 else None
        except (ValueError,IndexError):pass
    t=datetime(2023,2,23,10,10,tzinfo=timezone.utc)
    assert [seen[t+timedelta(minutes=m)] for m in (-30,0,30)]==[7.4,None,8.0]
    bad=out/"before_repair_bad.csv";fixed=out/"derived_wave_triplet.csv"
    before=list(csv.DictReader(bad.open(newline="")))
    after=list(csv.DictReader(fixed.open(newline="")))
    assert len(before)==len(after)==3
    assert before[1]["wave_height_m"]=="0.0" and before[1]["quality"]=="CALM_INFERRED_BAD"
    assert after[1]["wave_height_m"]=="" and after[1]["observed"]=="false"
    assert after[1]["quality"]=="MISSING_NOT_ZERO"
    assert after[0]["wave_height_m"]=="7.4" and after[2]["wave_height_m"]=="8.0"
    assert all(v["source_sha256"]==SHA for v in after+before)
    receipt=json.loads((out/"repair_receipt.json").read_text())
    assert receipt["verdict"]=="C3_LEAN_CERTIFIED_REAL_DERIVED_FILE_REPAIR_PASS"
    assert receipt["rollback_verified"] and receipt["source_immutable"] and receipt["atomic_rewrite"]
    assert receipt["faulty_derived_sha256"]==digest(bad.read_bytes())
    assert receipt["repaired_derived_sha256"]==digest(fixed.read_bytes())
    assert receipt["repaired_derived_sha256"]!=receipt["faulty_derived_sha256"]
    assert digest((base/"raw"/"46002h2023.txt.gz").read_bytes())==SHA
    verification={"verdict":"INDEPENDENT_DERIVED_CSV_REPAIR_PASS",
       "source_was_untouched":True,"wrong_zero_rejected":True,
       "true_middle_height":None,"observed_endpoints_m":[7.4,8.0],
       "source_sha256":SHA,"corrected_sha256":digest(fixed.read_bytes())}
    (out/"repair_independent_receipt.json").write_text(json.dumps(verification,indent=2)+"\n")
    print(verification["verdict"],flush=True)
if __name__=="__main__":main(sys.argv[1],sys.argv[2])
