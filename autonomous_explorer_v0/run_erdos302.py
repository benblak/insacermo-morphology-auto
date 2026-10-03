#!/usr/bin/env python3
import json
from pathlib import Path

from explorer import FrontierState, AutonomousFrontierExplorer, reciprocal_endpoint_edges, verify_trace

HERE=Path(__file__).resolve().parent
fx=json.loads((HERE/"fixtures"/"erdos302_frontier_734.json").read_text())
state=FrontierState(fx["exact_n"],fx["exact_k"],set(fx["witness"]))
engine=AutonomousFrontierExplorer(state,reciprocal_endpoint_edges)
result=engine.run_until_refuse(max_steps=8)
assert verify_trace(result)["valid"]
out=HERE/"autonomous_run_erdos302.json"
out.write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
print(json.dumps({
    "version":result["version"],
    "final_exact_n":result["final_exact_n"],
    "final_exact_k":result["final_exact_k"],
    "phases":[[e["phase"],e["n"],e["status"]] for e in result["trace"]],
    "run_hash":result["run_hash"],
},indent=2))
