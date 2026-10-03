#!/usr/bin/env python3
from pathlib import Path
import json
from max_explorer import FreeExplorer, verify_run

HERE=Path(__file__).resolve().parent
fx=json.loads((HERE/"fixtures"/"erdos302_frontier_734.json").read_text())
ex=FreeExplorer(fx["exact_n"],fx["exact_k"],set(fx["witness"]),max_swap_depth=4)
out=ex.run(max_frontier_steps=8)
assert verify_run(out)
(HERE/"autonomous_max_run.json").write_text(json.dumps(out,indent=2,ensure_ascii=False)+"\n")
print(json.dumps({
  "version":out["version"],
  "final_exact_n":out["final_exact_n"],
  "final_exact_k":out["final_exact_k"],
  "events":[[e["phase"],e["n"],e["operator"],e["status"]] for e in out["trace"]],
  "run_hash":out["run_hash"],
},indent=2,ensure_ascii=False))
