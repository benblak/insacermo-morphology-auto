"""INSACERMO: exact same-instance C3 Lean verification, fail-closed authorization."""
import hashlib,json,os,subprocess,tempfile
from pathlib import Path
from experiments.c3_raw_dynamic_autoplan_lean import require,synth,emit
def b(x):return json.dumps(x,sort_keys=True,separators=(",",":"),ensure_ascii=False).encode()
def h(x):return hashlib.sha256(x).hexdigest()
def deny(reason,d):return {"verdict":"VALIDITY_REFUSE","authorization":False,"reason":reason,"contract_sha256":d}
def decide_verified(contract,outdir,*,lean="lean",timeout=180):
    d=h(b(contract))
    try:
        require(contract); res=synth(contract)
        if res["verdict"]=="UNKNOWN_BOUNDED":
            return {"verdict":"EPISTEMIC_OPEN","authorization":False,"contract_sha256":d}
        source=emit(contract,res,0)
    except (AssertionError,KeyError,TypeError,ValueError,IndexError,RecursionError) as e:
        return deny("INVALID_CONTRACT",d)
    outdir=Path(outdir);outdir.mkdir(parents=True,exist_ok=True)
    (outdir/"DynamicCase0.lean").write_text(source)
    env=dict(os.environ,LEAN_PATH=".:lean")
    try:
        ver=subprocess.run([lean,"--version"],text=True,capture_output=True,timeout=15,cwd=Path(__file__).parent,env=env)
        chk=subprocess.run([lean,str((outdir/"DynamicCase0.lean").resolve())],text=True,capture_output=True,timeout=timeout,cwd=Path(__file__).parent,env=env)
    except (OSError,subprocess.TimeoutExpired):
        return deny("LEAN_UNAVAILABLE",d)
    if ver.returncode or chk.returncode or "sorryAx" in chk.stdout:
        return deny("LEAN_REJECTED",d)
    receipt={"verdict":res["verdict"],"authorization":res["verdict"]=="ACT",
        "proof_status":"LEAN_CHECKED_ON_THIS_INPUT","contract_sha256":d,
        "plan_sha256":h(b(res)),"lean_source_sha256":h(source.encode()),
        "lean_version":ver.stdout.strip(),"proof_file":"DynamicCase0.lean"}
    receipt["receipt_sha256"]=h(b(receipt))
    (outdir/"contract.json").write_bytes(b(contract))
    (outdir/"result.json").write_bytes(b(res))
    (outdir/"receipt.json").write_bytes(b(receipt))
    return receipt
def verify_receipt(outdir,*,lean="lean",timeout=180):
    try:
        p=Path(outdir); r=json.loads((p/"receipt.json").read_text())
        c=json.loads((p/"contract.json").read_text()); actual=json.loads((p/"result.json").read_text())
        if r.get("receipt_sha256")!=h(b({k:v for k,v in r.items() if k!="receipt_sha256"})):return False
        if actual!=synth(c):return False
        if r.get("contract_sha256")!=h(b(c)) or r.get("plan_sha256")!=h(b(actual)):return False
        if r.get("lean_source_sha256")!=h((p/"DynamicCase0.lean").read_bytes()):return False
        if (p/"DynamicCase0.lean").read_text()!=emit(c,actual,0):return False
        fresh=decide_verified(c,p/"independent_replay",lean=lean,timeout=timeout)
        return fresh==r
    except (ValueError,KeyError,OSError,TypeError,AssertionError,RecursionError):return False
