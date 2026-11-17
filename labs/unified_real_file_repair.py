#!/usr/bin/env python3
"""REPAIR genuinely edits a DERIVED CSV file; ORIGINAL NOAA gzip never modified.
An original-C3/Lean certificate is required BEFORE atomic transformation.
It is not hardware actuation and does not invent wave heights.
"""
import os,sys,json,csv,hashlib,io,tempfile,subprocess
from pathlib import Path
from datetime import datetime,timedelta,timezone
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from insacermo_one_engine import decide,replay
from integrated_proof_carrying_runtime import model
from inverse_wave_endpoint_certificates import read as read_noaa
KNOWN_GZIP_SHA256="93f488bdc6cc78a10469f20089eb337c8166f15845777de84a6c101fee7e8d04"
CENTER=datetime(2023,2,23,10,10,tzinfo=timezone.utc)
COLS=("timestamp_utc","wave_height_m","observed","quality","source_sha256")
def digest(b):return hashlib.sha256(b).hexdigest()
def csv_bytes(rows):
    stream=io.StringIO(newline="")
    w=csv.DictWriter(stream,fieldnames=COLS,lineterminator="\n")
    w.writeheader();w.writerows(rows)
    return stream.getvalue().encode()
def atomic(path,raw):
    path=Path(path); fd,temp=tempfile.mkstemp(prefix=".repair-",dir=path.parent)
    try:
        with os.fdopen(fd,"wb") as stream:
            stream.write(raw);stream.flush();os.fsync(stream.fileno())
        os.replace(temp,path)
    finally:
        if os.path.exists(temp):os.unlink(temp)
def parsed(raw):
    return list(csv.DictReader(io.StringIO(raw.decode())))
def safe(a):
    return (
      len(a)==3 and
      a[0]["wave_height_m"]=="7.4" and a[0]["observed"]=="true" and
      a[1]["wave_height_m"]=="" and a[1]["observed"]=="false" and a[1]["quality"]=="MISSING_NOT_ZERO" and
      a[2]["wave_height_m"]=="8.0" and a[2]["observed"]=="true" and
      all(row["source_sha256"]==KNOWN_GZIP_SHA256 for row in a)
    )
def main(base,out):
    base=Path(base);out=Path(out);out.mkdir(parents=True,exist_ok=True)
    original=base/"raw"/"46002h2023.txt.gz"
    assert original.is_file(),"MISSING_RAW_SOURCE"
    original_bytes=original.read_bytes()
    assert digest(original_bytes)==KNOWN_GZIP_SHA256,"RAW_SOURCE_HASH_MISMATCH"
    import gzip
    readings=read_noaa(gzip.decompress(original_bytes))
    assert [readings.get(CENTER+timedelta(minutes=d)) for d in (-30,0,30)]==[74,None,80]
    rows=[]
    for minute,value in ((-30,74),(0,None),(30,80)):
        stamp=(CENTER+timedelta(minutes=minute)).isoformat()
        if value is None:
            rows.append(dict(timestamp_utc=stamp,wave_height_m="0.0",observed="true",quality="CALM_INFERRED_BAD",source_sha256=KNOWN_GZIP_SHA256))
        else:
            rows.append(dict(timestamp_utc=stamp,wave_height_m=f"{value/10:.1f}",observed="true",quality="OBSERVED",source_sha256=KNOWN_GZIP_SHA256))
    original_bad=csv_bytes(rows)
    derived=out/"derived_wave_triplet.csv"
    atomic(derived,original_bad)
    assert not safe(parsed(derived.read_bytes()))
    bad_sha=digest(original_bad)
    backup=out/"before_repair_bad.csv"
    backup.write_bytes(original_bad)
    # Transition semantics: 0 = unsafe derived artifact; 1 = safe corrected artifact.
    repair=model([[False],[True]],sense=[[2,2]],nfalse=[[0,1]],
       ntrue=[[1,1]],kind=["REPAIR"],depth=1,budget=1)
    cert=out/"C3_REPAIR_REAL_FILE"
    proof=decide(repair,cert)
    assert proof["verdict"]=="REPAIR" and proof["authorized"] and replay(cert)
    # Explicit real command is local atomic file rewrite, not an arbitrary state label.
    rows[1].update(wave_height_m="",observed="false",quality="MISSING_NOT_ZERO")
    replacement=csv_bytes(rows)
    assert safe(parsed(replacement)) and replacement!=original_bad
    atomic(derived,replacement)
    assert derived.read_bytes()==replacement and safe(parsed(derived.read_bytes()))
    assert digest(original.read_bytes())==KNOWN_GZIP_SHA256
    # Prove rollback works by genuinely restoring faulty state, then reapply certified repair.
    atomic(derived,backup.read_bytes())
    rollback_verified=(derived.read_bytes()==original_bad and not safe(parsed(derived.read_bytes())))
    assert rollback_verified
    assert replay(cert),"CERTIFICATE_CHANGED_BEFORE_REAPPLY"
    atomic(derived,replacement)
    assert safe(parsed(derived.read_bytes()))
    fixed_sha=digest(derived.read_bytes())
    # Mutating the receipt invalidates the proof; restore it without changing source code.
    receipt=cert/"receipt.json";saved=receipt.read_bytes()
    try:
        corrupted=saved.replace(b'"authorized":true',b'"authorized":false')
        assert corrupted!=saved
        receipt.write_bytes(corrupted)
        tampered_rejected=not replay(cert)
        assert tampered_rejected
    finally:receipt.write_bytes(saved)
    assert replay(cert)
    assert digest(original.read_bytes())==KNOWN_GZIP_SHA256
    report=dict(verdict="C3_LEAN_CERTIFIED_REAL_DERIVED_FILE_REPAIR_PASS",
        original_noaa_gzip_sha256=KNOWN_GZIP_SHA256,
        source_immutable=True,source_observed_endpoint_decimeters=[74,80],
        observed_midpoint=None,faulty_derived_sha256=bad_sha,
        repaired_derived_sha256=fixed_sha,
        bad_source_row=parsed(original_bad)[1],good_source_row=parsed(replacement)[1],
        rollback_verified=rollback_verified,atomic_rewrite=True,receipt_tamper_rejected=tampered_rejected,
        c3_receipt_sha256=proof["receipt_sha256"],c3_contract_sha256=proof["contract_sha256"],
        scope="ONE LOCAL DERIVED CSV. NOT PHYSICAL SENSOR OR NOAA SOURCE FILE MODIFICATION.")
    (out/"repair_receipt.json").write_text(json.dumps(report,indent=2)+"\n")
    print(report["verdict"],bad_sha,fixed_sha,flush=True)
    return report
if __name__=="__main__":main(sys.argv[1],sys.argv[2])
