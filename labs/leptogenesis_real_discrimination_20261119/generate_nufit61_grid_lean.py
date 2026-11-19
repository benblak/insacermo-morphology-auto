#!/usr/bin/env python3
"""Generate reproducible Lean theorem on real tabulated NuFIT 6.1 DCP values.

Input CSV MUST originate from the exact SHA256-pinned XZ download, which was
retrieved from the NuFIT domain despite unverified HTTPS certificate.
No scientific authenticity guarantee: source channel certificate warning must
remain in any public claims. Lean proves finite-grid arithmetic, not physics.
"""
import csv,hashlib,os,lzma
from decimal import Decimal as D
from pathlib import Path

OUT=Path(os.environ.get("INSACERMO_NUFIT_OUT", "/tmp/insacermo-nufit61-real"))
XZ=OUT/"v61.release-TByes-NO.txt.xz"
CSV=OUT/"NUFIT61_NO_REAL_DCP_GRID.csv"
EXPECTED="c74bd6df84297a8429cd3b9e1239751cd0762756f1ec0c2a31248d78570b26e4"

def main():
    assert hashlib.sha256(XZ.read_bytes()).hexdigest()==EXPECTED,"source SHA changed"
    rows=[]
    with CSV.open(newline="") as f:
        for r in csv.DictReader(f):
            angle=D(r["angle_deg"])
            chi=D(r["delta_chi2"])
            assert angle.is_finite() and chi.is_finite()
            normalized=((angle % D(360))+D(360))%D(360)
            assert normalized==normalized.to_integral_value(),("noninteger angle",angle)
            assert chi>=0
            scaled=chi*1_000_000_000_000
            assert scaled==scaled.to_integral_value(),("precision more than twelve decimals",chi)
            rows.append((int(normalized),int(scaled)))
    assert len(rows)==73 and len(set(a for a,c in rows))==72,len(rows)
    assert min(c for a,c in rows if 198<=a<=225)==0
    assert min(c for a,c in rows if 5<=a<=40)==90481160000000
    assert min(c for a,c in rows if 320<=a<=355)==36902210000000
    pairs=",".join(f"({a},{c})" for a,c in rows)
    lean=f'''import Lean

/-!
INSACERMO independent NuFIT 6.1 real finite-grid audit.
Source URL: https://www.nu-fit.org/sites/default/files/v61.release-TByes-NO.txt.xz
Source SHA-256: {EXPECTED}
HTTPS certificate was not verified when downloading the xz archive.
73 tabulated rows (72 unique phases), NO, atmospheric TB yes.
A = [198°,225°], B-low=[5°,40°], B-high=[320°,355°].
Theorems are conditional on supplied source bytes, DO NOT certify provenance,
continuous interpolation, likelihood coverage, or theory truth.
-/
set_option maxHeartbeats 20000000
set_option maxRecDepth 8192
namespace INSACERMO.NuFIT61RealGrid

def grid : List (Int × Nat) := [{pairs}]

theorem witnessed_A_zero :
    (210,0) ∈ grid := by decide +kernel

theorem lower_bound_A :
    grid.all (fun p => decide (198 ≤ p.1 ∧ p.1 ≤ 225 → (0 : Nat) ≤ p.2)) = true := by
  decide +kernel

theorem witnessed_B_low :
    (5,9048116000000) ∈ grid := by decide +kernel

theorem lower_bound_B_low :
    grid.all (fun p => decide (5 ≤ p.1 ∧ p.1 ≤ 40 → (9048116000000 : Nat) ≤ p.2)) = true := by
  decide +kernel

theorem witnessed_B_high :
    (320,3690221000000) ∈ grid := by decide +kernel

theorem lower_bound_B_high :
    grid.all (fun p => decide (320 ≤ p.1 ∧ p.1 ≤ 355 → (3690221000000 : Nat) ≤ p.2)) = true := by
  decide +kernel

theorem different_B_branch_minima :
    (3690221000000 : Nat) < 9048116000000 := by omega

end INSACERMO.NuFIT61RealGrid
'''
    path=OUT/"NuFIT61GridCertification.lean"
    path.write_text(lean)
    print("GENERATED_LEAN_GRID",path,"source_sha",EXPECTED,"points",len(rows))
    print("NUFIT61_REAL_GRID_LEAN_GENERATOR_SUCCESS")
if __name__=="__main__":main()
