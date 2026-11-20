#!/usr/bin/env python3
"""Final single sensitivity test in frozen INSACERMO antimatter laboratory.

NuFIT 6.1 November 2025 NORMAL ORDERING:
v61.release-TByes-NO.txt.xz WITH tabulated SK/IC atmospheric chi2
v61.release-TBoff-NO.txt.xz WITHOUT those atmospheric chi2
Source of file conventions: NuFIT 6.1 official release notes.
No fit combination, invented physics, Gaussian approximation or new engine.
Raw HTTPS unverified on runner due NuFIT certificate: explicit provenance caveat.
Original C3 *historical* engine is used unchanged; conditional Lean receipts
validate only finite comparison of source-derived reported DCP tables.
"""
from __future__ import annotations
import csv, hashlib, json, lzma, os
from decimal import Decimal as D
from pathlib import Path
from insacermo_one_engine import decide, replay

OUT=Path(os.environ.get("FINAL_NUFIT_OUT","/tmp/insacermo-final-crossfit-no"))
OUT.mkdir(exist_ok=True,parents=True)
URL_PREFIX="https://www.nu-fit.org/sites/default/files/"
FILES={
 "with_atmospheric":"v61.release-TByes-NO.txt.xz",
 "without_atmospheric":"v61.release-TBoff-NO.txt.xz",
}
PINNED_WITH_SHA256="c74bd6df84297a8429cd3b9e1239751cd0762756f1ec0c2a31248d78570b26e4"
FROZEN_C3="bd5310b3692bcbad4e874005b7dd8eda90616f74"
SCALE=10**12

def extract(filename):
    path=OUT/filename
    data=path.read_bytes()
    assert data[:6]==b'\xfd7zXZ\x00',f"invalid source format: {filename}"
    sha=hashlib.sha256(data).hexdigest()
    if filename==FILES["with_atmospheric"]:
        assert sha==PINNED_WITH_SHA256,(sha,PINNED_WITH_SHA256)
    txt=lzma.decompress(data).decode('utf-8')
    found=0; active=False; rows=[]
    for line in txt.splitlines():
        t=line.strip()
        if t.startswith('#'):
            tag=t[1:].strip().split()[0] if t[1:].strip() else ""
            if tag=='DCP':found+=1;active=True
            elif active:active=False
            continue
        if not t or not active:continue
        parts=t.split()
        if len(parts)<2:continue
        try:angle=D(parts[0]);chi=D(parts[1])
        except Exception:continue
        assert angle.is_finite() and chi.is_finite()
        angle=((angle%D(360))+D(360))%D(360)
        assert angle==int(angle)
        assert chi>=0
        scaled=chi*SCALE
        assert scaled==int(scaled)
        rows.append((int(angle),int(scaled)))
    assert found==1,(filename,found)
    assert len(rows)==73 and len(set(x for x,y in rows))==72,(filename,len(rows))
    return sha,rows

def region_min(rows,low,high):
    relevant=[(angle,chi) for angle,chi in rows if low<=angle<=high]
    assert len(relevant)>=4,(low,high,len(relevant))
    return min(relevant,key=lambda t:t[1]),len(relevant)

def lean_file(table):
    # 73-point original source-derived integer table, no manually invented chi2.
    lines=["import Lean","set_option maxHeartbeats 20000000",
           "set_option maxRecDepth 8192",
           "/-!",
           "This certifies integer arithmetic on two NuFIT 6.1 NORMAL ORDERING",
           "tabulated DCP grids only; no authentic TLS server certificate was",
           "verified; one source hash pinned to earlier successful lab,",
           "other hash recorded on first run. No interpolation or theory proof.",
           "-/","namespace INSACERMO.FinalNuFIT"]
    for name,info in table.items():
        id="withAtmos" if name=="with_atmospheric" else "withoutAtmos"
        pts=",".join("("+str(x)+","+str(y)+")" for x,y in info["rows"])
        lines.append(f"def {id} : List (Int × Nat) := [{pts}]")
        for key,lo,hi,cut in [("A",198,225,0),("Blow",5,40,9*SCALE),("Bhigh",320,355,4*SCALE)]:
            (at,val), n=region_min(info["rows"],lo,hi)
            lines.append(f"theorem {id}_{key}_witness : ({at},{val}) ∈ {id} := by decide +kernel")
            lines.append(f"theorem {id}_{key}_lower_bound : {id}.all (fun p => decide ({lo} ≤ p.1 ∧ p.1 ≤ {hi} → ({val} : Nat) ≤ p.2)) = true := by decide +kernel")
            if key!="A":
                outcome="true" if val<=cut else "false"
                lines.append(f"def {id}_{key}_inside_cutoff : Bool := decide (({val} : Nat) ≤ {cut})")
                lines.append(f"theorem {id}_{key}_cutoff : {id}_{key}_inside_cutoff = {outcome} := by decide")
    # Cross-panel conclusion itself is computed from numbers, not hardcoded.
    for key in ("Blow","Bhigh"):
        a=table["with_atmospheric"]["metrics"][key]["included"]
        b=table["without_atmospheric"]["metrics"][key]["included"]
        common=str(a==b).lower()
        lines.append(f"theorem {key}_cross_fit_agree : (withAtmos_{key}_inside_cutoff == withoutAtmos_{key}_inside_cutoff) = {common} := by decide")
    lines.append("end INSACERMO.FinalNuFIT")
    return "\n".join(lines)+"\n"

def c3_on_pair(label, values):
    src=Path('insacermo_one_engine.py').read_bytes()
    blob=hashlib.sha1(b'blob '+str(len(src)).encode()+b'\0'+src).hexdigest()
    assert blob==FROZEN_C3,blob
    # 0=exclude predicted region; 1=retain it. Label only analyses, NOT nature.
    good=[[not inside,inside] for inside in values]
    m=dict(worldCount=2,actionCount=2,probeCount=1,
       good=good,sense=[[3,3]],nextFalse=[[0,1]],nextTrue=[[0,1]],
       actionCost=[0,0],probeCost=[1],
       lowerWorld=[0,1],upperWorld=[0,1],
       mustActions=[0,1],mayActions=[0,1],
       probeKinds=["PROBE"],depth=1,budget=0,reserve=10,debt=0)
    r=decide(m,OUT/("C3_"+label))
    expected="ACT" if values[0]==values[1] else "REFUSE_ROBUST"
    assert r["verdict"]==expected,(label,r)
    assert replay(OUT/("C3_"+label))
    return {"verdict":expected,"receipt":r["source_sha256"],"replayed":True}

def main():
    table={}
    for key,filename in FILES.items():
        sha,rows=extract(filename)
        metrics={}
        for reg,lo,hi,cut in [("A",198,225,0),("Blow",5,40,9*SCALE),("Bhigh",320,355,4*SCALE)]:
            ((angle,val),n)=region_min(rows,lo,hi)
            metrics[reg]=dict(angle=angle,min_dchi2=str(D(val)/D(SCALE)),
              n_points=n,included=(val<=cut) if reg!="A" else (val==0),
              margin_to_cutoff=str(D(val-cut)/D(SCALE)) if reg!="A" else None)
        table[key]=dict(filename=filename,sha256=sha,rows=rows,metrics=metrics)
    assert table["with_atmospheric"]["metrics"]["A"]["min_dchi2"]=="0"
    assert table["with_atmospheric"]["metrics"]["Blow"]["min_dchi2"]=="9.048116"
    assert table["with_atmospheric"]["metrics"]["Bhigh"]["min_dchi2"]=="3.690221"

    out_file=OUT/"FinalNuFITTwoAtmosphere.lean"
    out_file.write_text(lean_file(table))
    if os.environ.get("FINAL_RUN_C3")=="1":
        c3={}
        for key in ("Blow","Bhigh"):
            values=[table[z]["metrics"][key]["included"] for z in ("with_atmospheric","without_atmospheric")]
            c3[key]=c3_on_pair(key,values)
    else:c3=None
    report={
      "scope":"NuFIT 6.1 NO with/without tabulated SK and IC atmospheric chi2",
      "security_note":"source retrieved with TLS verification explicitly disabled; raw bytes SHA documented; attribution not cryptographically authenticated",
      "source_sha256":{name:info["sha256"] for name,info in table.items()},
      "fits":{name:info["metrics"] for name,info in table.items()},
      "same_verdict_on_Blow_at_3sigma":table["with_atmospheric"]["metrics"]["Blow"]["included"]==table["without_atmospheric"]["metrics"]["Blow"]["included"],
      "same_verdict_on_Bhigh_at_2sigma":table["with_atmospheric"]["metrics"]["Bhigh"]["included"]==table["without_atmospheric"]["metrics"]["Bhigh"]["included"],
      "c3":c3,"theorems_generated_from_two_real_grids":True,
    }
    (OUT/"FINAL_CROSSFIT_REPORT.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))
    print("FINAL_CROSSFIT_GRID_PROCESS_SUCCESS")

if __name__=="__main__":main()
