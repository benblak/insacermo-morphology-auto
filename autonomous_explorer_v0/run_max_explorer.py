#!/usr/bin/env python3
from pathlib import Path
import json

from max_explorer import FreeExplorer, verify_run

HERE = Path(__file__).resolve().parent
fx = json.loads((HERE / "fixtures" / "erdos302_frontier_734.json").read_text())

ex = FreeExplorer(fx["exact_n"], fx["exact_k"], set(fx["witness"]))
out = ex.run(max_frontier_steps=6)
assert verify_run(out)

(HERE / "autonomous_max_run.json").write_text(
    json.dumps(out, indent=2, ensure_ascii=False) + "\n"
)

print(json.dumps({
    "version": out["version"],
    "final_exact_n": out["final_exact_n"],
    "final_exact_k": out["final_exact_k"],
    "acts": [
        {
            "n": e["n"],
            "operator": e["operator"],
            "status": e["status"],
            "k": e["details"].get("new_exact_k"),
            "proof_status": e["details"].get("proof_status"),
        }
        for e in out["trace"] if e["phase"] == "ACT"
    ],
    "run_hash": out["run_hash"],
}, indent=2, ensure_ascii=False))
