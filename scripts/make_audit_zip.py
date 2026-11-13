#!/usr/bin/env python3
"""Make the reproducible INSACERMO audit ZIP from GitHub checkout.
This intentionally includes ONLY the isolated audit sources, not the frozen motor.
"""
from pathlib import Path
from hashlib import sha256
from zipfile import ZipFile, ZIP_DEFLATED
import json, sys

ROOT=Path(__file__).resolve().parents[1]
FILES=[
    "DOSSIER_AUDIT_INSACERMO_2026-11-13.md",
    "berge_core_audit/InsacermoBergeCore.lean",
    "berge_core_audit/InsacermoProbeCriterion.lean",
    "berge_core_audit/InsacermoFiveWorld.lean",
    "berge_core_audit/lean-toolchain",
    "berge_core_audit/lakefile.toml",
    "berge_core_audit/five_world_probe_audit.py",
    "berge_lean420_audit/InsacermoBerge.lean",
    "berge_lean420_audit/lean-toolchain",
    "berge_lean420_audit/lakefile.toml",
    "benchmarks/insacermo_etalon_renyi_ulam.py",
    ".github/workflows/berge-core-420.yml",
    ".github/workflows/berge-lean420-independent.yml",
]
DEST=ROOT/"dist"/"INSACERMO_AUDIT_COMPLET_LEAN420_2026-11-13.zip"
DEST.parent.mkdir(parents=True, exist_ok=True)
missing=[p for p in FILES if not (ROOT/p).is_file()]
if missing:
    raise SystemExit(f"Missing audited file(s): {missing}")
metadata={"scope":"independent laboratory audit; not original Claude or frozen engine",
          "lean":"4.20.0",
          "verified_run_ids":[43425229350,43428649926,43436284491,43437488745],
          "sha256_files":{p:sha256((ROOT/p).read_bytes()).hexdigest() for p in FILES}}
with ZipFile(DEST,"w",compression=ZIP_DEFLATED,compresslevel=9) as z:
    for p in FILES:
        z.write(ROOT/p,arcname="INSACERMO_AUDIT_COMPLET/"+p)
    z.writestr("INSACERMO_AUDIT_COMPLET/MANIFEST_SHA256.json",
               json.dumps(metadata,ensure_ascii=False,indent=2)+"\n")
with ZipFile(DEST) as z:
    bad=z.testzip()
    if bad: raise SystemExit(f"ZIP corrupted at: {bad}")
    assert len(z.namelist())==len(FILES)+1
print(f"PASS ZIP: {DEST}")
print(f"FILES {len(FILES)} + MANIFEST 1")
print(f"BYTES {DEST.stat().st_size}")
print(f"SHA256 {sha256(DEST.read_bytes()).hexdigest()}")
