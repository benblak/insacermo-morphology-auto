#!/usr/bin/env python3
"""INSACERMO: real 1D delta-CP profile, independent NuFIT v6.1 (Nov 2025).
DO NOT equate NuFIT with preliminary Bari 2026.a. Same published physics
intervals A/B, same frozen historical C3 (not modified or claimed to run here).
Source: NuFIT collaboration official xz chi2 grid, section '# DCP'.
Validation is on the actual published tabulated grid only; no continuous global
bound or baryogenesis proof is inferred. No synthetic chi2 data or Gaussian fit.
"""
from __future__ import annotations
import hashlib, json, lzma, os, re, urllib.request
from decimal import Decimal as D
from pathlib import Path

URL = "https://www.nu-fit.org/sites/default/files/v61.release-TByes-NO.txt.xz"
OUT = Path(os.environ.get("INSACERMO_NUFIT_OUT", "/tmp/insacermo-nufit61-real"))
OUT.mkdir(parents=True, exist_ok=True)

def download():
    dest = OUT / "v61.release-TByes-NO.txt.xz"
    if not dest.exists():
        req=urllib.request.Request(URL, headers={"User-Agent": "INSACERMO-audit/1.0 (+scientific-data-reproducibility)"})
        with urllib.request.urlopen(req, timeout=90) as response, dest.open("wb") as f:
            while True:
                b=response.read(1048576)
                if not b: break
                f.write(b)
                if f.tell()>200_000_000: raise RuntimeError("source exceeds safety bound")
    raw=dest.read_bytes()
    assert raw[:6]==b"\xfd7zXZ\x00", "not an xz source file"
    return raw

def dcp_lines(raw):
    found=0; active=False; rows=[]; tags=[]
    with lzma.open(OUT / "v61.release-TByes-NO.txt.xz",mode="rt",encoding="utf-8",errors="strict") as f:
        for line in f:
            t=line.strip()
            if not t: continue
            if t.startswith("#"):
                tag=t[1:].strip().split()[0] if t[1:].strip() else ""
                if active:
                    active=False
                if tag=="DCP":
                    found+=1;active=True
                tags.append(t[:120]);continue
            if not active: continue
            toks=t.split()
            if len(toks)>=2:
                try: angle=D(toks[0]);chi=D(toks[1])
                except Exception: continue
                rows.append((angle,chi))
    assert found==1, f"Expected one # DCP section; found {found}. Section samples: {tags[-35:]}"
    assert len(rows)>25, f"too few CP data rows: {len(rows)}; sample tags: {tags[-30:]}"
    return rows,tags

def norm_deg(a):
    return a % D(360)
def region(a, parts):
    return any(D(lo)<=a<=D(hi) for lo,hi in parts)
def calc(rows):
    # Tabulated points only; the NuFIT grid is not continuous. Preserve source's
    # printed chi2 and relative normalization separately.
    norm=[(norm_deg(a),chi,a) for a,chi in rows]
    assert all(0<=a<D(360) and v.is_finite() for a,v,orig in norm)
    assert len({a for a,_,_ in norm})>25
    globalmin=min(v for a,v,orig in norm)
    A=[(a,chi,orig) for a,chi,orig in norm if region(a,[(198,225)])]
    Blow=[(a,chi,orig) for a,chi,orig in norm if region(a,[(5,40)])]
    Bhigh=[(a,chi,orig) for a,chi,orig in norm if region(a,[(320,355)])]
    assert all(len(s)>=2 for s in [A,Blow,Bhigh]),f"coverage missing: {len(A)} {len(Blow)} {len(Bhigh)}"
    def best(xs):
        a,chi,raw_angle=min(xs,key=lambda x:x[1])
        return dict(angle_deg=str(a),grid_raw_angle_deg=str(raw_angle),
                    delta_chi2_as_published=str(chi),
                    delta_chi2_relative_to_curve_min=str(chi-globalmin),
                    grid_points=len(xs))
    r=dict(
      scope="NuFIT v6.1, TB yes, NORMAL ORDERING, November 2025. Independent comparison, NOT Bari 2026.a.",
      source_url=URL, section="# DCP",
      n_tabulated_points=len(rows), unique_angles=len({a for a,_,_ in norm}),
      global_curve_min_as_published=str(globalmin),
      A_198_225=best(A),B_low_5_40=best(Blow),B_high_320_355=best(Bhigh),
      low_B_disfavored_vs_A=str(best(Blow)["delta_chi2_relative_to_curve_min"]),
      high_B_disfavored_vs_A=str(best(Bhigh)["delta_chi2_relative_to_curve_min"]),
      observational_claim="Only a 1D profiled chi2 slice computed from a separate experiment aggregation; not an antimatter-causation verdict or exact continuous minimum.")
    return r

def main():
    raw=download()
    rows,tags=dcp_lines(raw)
    result=calc(rows)
    result["source_xz_sha256"]=hashlib.sha256(raw).hexdigest()
    result["source_size_bytes"]=len(raw)
    (OUT/"NUFIT61_NO_REAL_DCP_PROFILE_SUMMARY.json").write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    (OUT/"NUFIT61_NO_REAL_DCP_GRID.csv").write_text("angle_deg,delta_chi2\n"+
       "".join(f"{a},{v}\n" for a,v in rows))
    print(json.dumps(result,indent=2,ensure_ascii=False))
    print("NUFIT61_REAL_PROFILE_GRID_AUDIT_SUCCESS")

if __name__=="__main__":main()
