#!/usr/bin/env python3
"""Strict expected-contract trust-boundary regression tests."""
import hashlib,json,shutil,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from insacermo_one_engine import canonical,replay
from audit.inrc2_e2e_20261012.bound_verifier import verify_bound
base=ROOT/"audit/inrc2_e2e_20261012/evidence/receipts"
names=["01_PROBE","02_ACT_0","03_ACT_1","04_REFUSE","05_EPISTEMIC_OPEN"]
contracts={n:json.loads((base/n/"contract.json").read_text()) for n in names}
hashes={n:hashlib.sha256(canonical(v)).hexdigest() for n,v in contracts.items()}
for n in names:
    assert replay(base/n)
    assert verify_bound(base/n,hashes[n])
    assert not verify_bound(base/n,"0"*64)
    assert not verify_bound(base/n,"invalid")
    assert not verify_bound(base/n,hashes[n].upper())
rejected=0
for a in names:
    for b in names:
        if a==b:continue
        assert hashes[a]!=hashes[b]
        assert not verify_bound(base/b,hashes[a]),(a,b)
        rejected+=1
testroot=ROOT/"audit/inrc2_e2e_20261012/evidence/bound_tests"
shutil.copytree(base/"03_ACT_1",testroot/"whole_foreign",dirs_exist_ok=True)
assert replay(testroot/"whole_foreign")
assert not verify_bound(testroot/"whole_foreign",hashes["01_PROBE"])
assert verify_bound(testroot/"whole_foreign",hashes["03_ACT_1"])
assert not verify_bound(base/"01_PROBE",hashes["01_PROBE"],lean_binary="/missing-lean-executable")
# CLI with a separate trusted contract file
trusted=testroot/"trusted_original_contract.json"
trusted.write_text(json.dumps(contracts["01_PROBE"]))
program=ROOT/"audit/inrc2_e2e_20261012/bound_verifier.py"
def run(*args):
    return subprocess.run([sys.executable,str(program),*map(str,args)],capture_output=True,text=True)
good=run(base/"01_PROBE","--expected-contract-file",trusted)
assert good.returncode==0 and "BOUND_CERTIFICATE_ACCEPTED" in good.stdout,good.stderr
bad=run(testroot/"whole_foreign","--expected-contract-file",trusted)
assert bad.returncode==2 and "CERTIFICATE_REJECTED" in bad.stdout
bad2=run(base/"01_PROBE","--expected-contract-sha256","not-a-digest")
assert bad2.returncode==2
missing=run(base/"01_PROBE")
assert missing.returncode!=0
print(f"BOUND_VERIFIER_SUCCESS 5_SELF_MATCHES 20_CROSS_CONTRACT_REJECTIONS {rejected=} FOREIGN_VALID_BUNDLE_REJECTED WITH_TRUSTED_REFERENCE",flush=True)
