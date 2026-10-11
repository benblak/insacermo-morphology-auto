#!/usr/bin/env python3
"""Fail-closed C3 decision gate. No ACT/REFUSE_PROVEN without checking the
exact emitted Lean file in a pinned toolchain. Only the declared finite model.
Dependencies must have been compiled separately from checked source.
"""
import argparse,hashlib,json,os,subprocess,sys,tempfile
from pathlib import Path
from experiments.c3_raw_dynamic_autoplan_lean import require,synth,emit

class GateError(RuntimeError):pass
def digest(v):return hashlib.sha256(v).hexdigest()
def canonical(v):return json.dumps(v,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()

def gate(contract,*,lean="lean",lean_path=".:lean",timeout=180):
    # Reject malformed values before hashing or executing external checker.
    require(contract)
    source=canonical(contract); contract_hash=digest(source)
    result=synth(contract)
    verdict=result["verdict"]
    receipt={"runtime":"INSACERMO_EXACT_C3_LEAN_GATE_V1",
        "contract_sha256":contract_hash,"verdict":"UNKNOWN_UNCERTIFIED",
        "claim_scope":"finite stated C3 laws, transitions, action grammar, costs and future worlds",
        "candidate_verdict":verdict,"lean_certificate_sha256":None,
        "lean_checked":False,"failure":None}
    if verdict not in ("ACT","REFUSE_PROVEN"):
        receipt["failure"]="NO_PROOF_GENERATED"
    else:
        lean_text=emit(contract,result,0)
        receipt["lean_certificate_sha256"]=digest(lean_text.encode())
        with tempfile.TemporaryDirectory(prefix="insacermo_c3_gate_") as tmp:
            p=Path(tmp)/"Certificate.lean"
            p.write_text(lean_text)
            try:
                env=dict(os.environ,LEAN_PATH=lean_path)
                run=subprocess.run([lean,str(p)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                    text=True,timeout=timeout,env=env,check=False)
                if run.returncode==0 and "sorryAx" not in run.stdout:
                    receipt["verdict"]=verdict
                    receipt["lean_checked"]=True
                else: receipt["failure"]="LEAN_REJECTED_OR_NONZERO"
            except (FileNotFoundError,subprocess.TimeoutExpired,OSError):
                receipt["failure"]="LEAN_UNAVAILABLE_OR_TIMEOUT"
    receipt["receipt_sha256"]=digest(canonical(receipt))
    return receipt

def verify_receipt(contract,receipt,*,lean="lean",lean_path=".:lean"):
    # Rebuild and rerun the exact instance; hashes alone never authorize ACT.
    try:return gate(contract,lean=lean,lean_path=lean_path)==receipt
    except Exception:return False

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("contract_json")
    parser.add_argument("--lean",default="lean")
    parser.add_argument("--lean-path",default=".:lean")
    a=parser.parse_args()
    try:
        data=json.loads(Path(a.contract_json).read_text())
        assert type(data)==dict
        answer=gate(data,lean=a.lean,lean_path=a.lean_path)
    except Exception as exc:
        print(json.dumps({"verdict":"UNKNOWN_UNCERTIFIED","failure":"INVALID_INPUT_OR_GATE_ERROR",
            "exception_type":type(exc).__name__}))
        sys.exit(2)
    print(json.dumps(answer,indent=2))
    sys.exit(0 if answer["lean_checked"] or answer["candidate_verdict"]=="UNKNOWN_BOUNDED" else 3)
