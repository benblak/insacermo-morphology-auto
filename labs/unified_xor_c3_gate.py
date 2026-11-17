#!/usr/bin/env python3
"""Original C3 Lean-certified gate for XOR representation, with fail-closed universal refusal.
MUST be run after independent oracle audit and genuine forall-x Lean proof compile.
"""
import sys,json,hashlib
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from integrated_proof_carrying_runtime import model
from insacermo_one_engine import decide,replay

def main(out):
    out=Path(out)
    external=json.loads((out/"xor_independent_receipt.json").read_text())
    identity=json.loads((out/"XorIdentities.json").read_text())
    assert external["result"]=="INDEPENDENT_XOR_UNIFIED_PASS"
    assert len(identity["verified_models"])==7
    assert external["hidden_counterexample"]==978436
    models={
      "XOR_ACT_EXACT_WITHIN_DECLARED_QUADRATIC":(model([[True],[True]]),"ACT"),
      "XOR_REFUSE_UNRESTRICTED_ORACLE_LAW":(model([[True,False],[False,True]]),"REFUSE_ROBUST")
    }
    verdicts={}
    for name,(contract,expected) in models.items():
        folder=out/"C3_XOR_GATE"/name
        receipt=decide(contract,folder)
        assert receipt["verdict"]==expected and replay(folder)
        verdicts[name]={
          "verdict":receipt["verdict"],"receipt_sha256":receipt["receipt_sha256"],
          "contract_sha256":receipt["contract_sha256"],
          "Lean_proof_sha256":receipt["source_sha256"]}
    report=dict(verdict="XOR_LEAN_AND_C3_SCOPED_VERDICTS_PASS",
       all_quadratic_identical_for_all_24bit_inputs_under_declared_model=True,
       original_oracle_global_truth_certified=False,
       c3=verdicts,source_seal_sha256=identity["source_seal_sha256"],
       proof_source_sha256=identity["proof_sha256"])
    (out/"xor_c3_receipts.json").write_text(json.dumps(report,indent=2)+"\n")
    print(report["verdict"],flush=True)
if __name__=="__main__":main(sys.argv[1])
