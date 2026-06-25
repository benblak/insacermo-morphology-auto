from pathlib import Path
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
source = ROOT / "synthetic_overfit_log.csv"

with tempfile.TemporaryDirectory() as tmp:
    run = subprocess.run([
        sys.executable,
        str(ROOT / "insacermo_morphology_auto_v28.py"),
        str(source),
        "--out", tmp,
        "--surrogates", "19",
        "--no-plots",
    ], capture_output=True, text=True)

    if run.returncode != 0:
        print(run.stdout)
        print(run.stderr)
        raise SystemExit(run.returncode)

    manifest = json.loads((Path(tmp) / "batch_manifest.json").read_text())
    result = manifest["results"][0]

    assert result["dominant_morphology"] in {
        "OVERFIT_DRIFT", "FAVORABLE_GAP_WARNING", "MIXED"
    }
    assert 0.0 <= result["Dhidden"] <= 1.0
    print("SMOKE_TEST: PASS")
