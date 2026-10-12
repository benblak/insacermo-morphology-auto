#!/usr/bin/env python3
"""Cross-bundle binding tests. Original C3 and its receipts are unmodified."""
import copy,json,shutil,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
import insacermo_one_engine as c3
base=ROOT/"audit/inrc2_e2e_20261012/evidence/receipts"
names=["01_PROBE","02_ACT_0","03_ACT_1","04_REFUSE","05_EPISTEMIC_OPEN"]
for n in names: assert c3.replay(base/n),(n,"original rejected")
print("ORIGINAL_BUNDLES_VALID",len(names),flush=True)
out=ROOT/"audit/inrc2_e2e_20261012/evidence/cross_swap"
out.mkdir(exist_ok=True)
files=["contract.json","candidate.json","receipt.json","C3Decision.lean"]
rejected=0
for dst in names:
    for src in names:
        if src==dst:continue
        for fname in files:
            trial=out/f"{dst}__from__{src}__{fname.replace('.','_')}"
            shutil.copytree(base/dst,trial,dirs_exist_ok=True)
            shutil.copy2(base/src/fname,trial/fname)
            assert not c3.replay(trial),("CROSS_SWAP_ACCEPTED",dst,src,fname)
            rejected+=1
print("CROSS_SWAP_REJECTIONS",rejected,flush=True)
# Fully valid alternate bundle: replay checks self-consistency, NOT caller's
# externally expected contract identity.
whole=out/"entire_other_valid_bundle"
shutil.copytree(base/"03_ACT_1",whole,dirs_exist_ok=True)
assert c3.replay(whole),"valid other complete bundle unexpectedly rejected"
expected=json.loads((base/"01_PROBE"/"contract.json").read_text())
actual=json.loads((whole/"contract.json").read_text())
assert c3.sha(c3.canonical(expected)) != c3.sha(c3.canonical(actual))
def replay_for_expected_contract(folder,expected_sha256):
    if c3.sha(c3.canonical(json.loads((folder/"contract.json").read_text()))) != expected_sha256:
        return False
    return c3.replay(folder)
assert not replay_for_expected_contract(whole,c3.sha(c3.canonical(expected)))
print("ENTIRE_VALID_OTHER_BUNDLE_ACCEPTED_BY_GENERIC_REPLAY_BUT_REJECTED_BY_EXTERNAL_EXPECTED_CONTRACT_PIN",flush=True)
result=dict(originals_valid=5,individual_cross_swaps_rejected=rejected,
            entire_valid_alternative_accepted_by_replay=True,
            external_contract_pin_rejects_other_bundle=True,
            explanation="Generic replay verifies internal consistency, not intended transaction identity. Consumers must bind an expected contract digest outside the candidate bundle.")
(out/"CROSS_BUNDLE_REPORT.json").write_text(json.dumps(result,indent=2)+"\n")
