#!/usr/bin/env python3
"""Positive canonical-JSON acceptance tests and semantic-change rejection.

Audit-only. Works on five original Lean receipts generated from pinned INRC-II
source; it does not modify frozen INSACERMO C3.
"""
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT))
sys.path.insert(0,str(HERE))

from insacermo_one_engine import canonical,replay
from bound_verifier import verify_bound

receipts=HERE/"evidence"/"receipts"
scratch=HERE/"evidence"/"canon_tests"
scratch.mkdir(parents=True,exist_ok=True)
cases=("01_PROBE","02_ACT_0","03_ACT_1","04_REFUSE","05_EPISTEMIC_OPEN")
cli=HERE/"bound_verifier.py"
accepted=0
rejected=0
cli_positive=0
report=[]

def reverse_objects(x):
    if isinstance(x,dict):
        return {k:reverse_objects(v) for k,v in reversed(list(x.items()))}
    if isinstance(x,list):
        return [reverse_objects(v) for v in x]
    return x

for name in cases:
    src=receipts/name
    original=json.loads((src/"contract.json").read_text())
    expected=hashlib.sha256(canonical(original)).hexdigest()
    assert replay(src)
    assert verify_bound(src,expected)

    # Independent expectation stays outside the candidate receipt directory.
    reference=scratch/f"expected_{name}.json"
    reference.write_text(json.dumps(reverse_objects(original),indent=3,ensure_ascii=False)+"\n")
    assert hashlib.sha256(canonical(json.loads(reference.read_text()))).hexdigest()==expected
    cli_run=subprocess.run([sys.executable,str(cli),str(src),
        "--expected-contract-file",str(reference)],capture_output=True,text=True)
    assert cli_run.returncode==0 and "BOUND_CERTIFICATE_ACCEPTED" in cli_run.stdout, cli_run.stderr
    cli_positive+=1

    for variant in ("pretty_reordered","compact_reordered","all_json_pretty"):
        trial=scratch/f"{name}_{variant}"
        shutil.copytree(src,trial,dirs_exist_ok=True)
        obj=reverse_objects(json.loads((trial/"contract.json").read_text()))
        if variant=="compact_reordered":
            text=json.dumps(obj,ensure_ascii=False,separators=(",",":"))
        else:
            text=json.dumps(obj,indent=5,ensure_ascii=False)+"\n"
        (trial/"contract.json").write_text(text)
        if variant=="all_json_pretty":
            for fn in ("candidate.json","receipt.json"):
                other=reverse_objects(json.loads((trial/fn).read_text()))
                (trial/fn).write_text(json.dumps(other,indent=4,ensure_ascii=False)+"\n")
        assert (trial/"contract.json").read_bytes() != (src/"contract.json").read_bytes()
        assert hashlib.sha256(canonical(json.loads((trial/"contract.json").read_text()))).hexdigest()==expected
        assert verify_bound(trial,expected),(name,variant)
        assert replay(trial),(name,variant)
        accepted+=1

    wrong=scratch/f"{name}_genuine_semantic_mutation"
    shutil.copytree(src,wrong,dirs_exist_ok=True)
    changed=json.loads((wrong/"contract.json").read_text())
    changed["budget"]=0 if changed["budget"]!=0 else 1
    assert changed!=original
    (wrong/"contract.json").write_text(json.dumps(changed,indent=4))
    assert not verify_bound(wrong,expected)
    rejected+=1
    # Positive test also verifies that an expected hash is mandatory:
    absent=subprocess.run([sys.executable,str(cli),str(src)],capture_output=True,text=True)
    assert absent.returncode!=0
    report.append({"case":name,"canonical_expected_sha256":expected,
      "independent_reformatted_reference_accepted":True,
      "reformatted_bundle_variants_accepted":3,
      "semantic_mutation_rejected":True})

assert accepted==15 and rejected==5 and cli_positive==5
output={"reformatted_receipts_accepted":accepted,"reformatted_independent_references_accepted":cli_positive,
    "semantic_mutations_rejected":rejected,
    "scope":"Finite C3 contract/receipt JSON semantic canonicalization only; does not authenticate an external caller or source.",
    "cases":report}
(scratch/"CANONICALIZATION_AUDIT.json").write_text(json.dumps(output,indent=2,ensure_ascii=False,sort_keys=True)+"\n")
print("CANONICALIZATION_ACCEPTANCE_SUCCESS reformatted_bundles=15 reformatted_trusted_references=5 semantic_changes_rejected=5",flush=True)
