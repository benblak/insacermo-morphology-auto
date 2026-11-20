#!/usr/bin/env python3
"""C3 ORIGINAL (frozen): abstract decision boundary under declared sensitivity worlds.

Not a physical sensor forecast. Worlds encode four POSSIBLE outcomes from future
changes in the NuFIT 6.1 sampled-grid minima. Two ideal binary probes disclose
high-B and low-B statuses. Neither probe is an actual neutrino experiment.
This demonstrates information requirements relative to the declared 4/5 worlds
and action repertoire, not a theorem of universal optimal physics.
"""
from pathlib import Path
from hashlib import sha1
import json,os
from insacermo_one_engine import decide,replay,solve

ORIGINAL_BLOB='bd5310b3692bcbad4e874005b7dd8eda90616f74'
OUT=Path(os.environ.get("SENSITIVITY_C3_OUT","/tmp/insacermo-joint-margins"))
OUT.mkdir(parents=True,exist_ok=True)

def model(budget, rival=False, robust=False):
    # Worlds 0..3 represent four combinations of two status bits
    # 0: high in, low out; 1: high out, low out;
    # 2: high in, low in; 3: high out, low in.
    # The rival 4 has same sensor reports as 0 but a distinct required action.
    n=5 if rival else 4
    if robust:
        good=[[True] for _ in range(n)]
    else:
        good=[[i==j for j in range(n)] for i in range(n)]
    sense=[[1,2,1,2]+([1] if rival else []),
           [1,1,2,2]+([1] if rival else [])]
    return dict(worldCount=n,actionCount=len(good[0]),probeCount=2,
       good=good,sense=sense,
       nextFalse=[list(range(n)),list(range(n))],
       nextTrue=[list(range(n)),list(range(n))],
       actionCost=[0]*len(good[0]),probeCost=[1,1],
       lowerWorld=list(range(n)),upperWorld=list(range(n)),
       mustActions=list(range(len(good[0]))),mayActions=list(range(len(good[0]))),
       probeKinds=['PROBE','PROBE'],depth=2,budget=budget,reserve=10,debt=0)

def main():
    source=Path("insacermo_one_engine.py").read_bytes()
    blob=sha1(b'blob '+str(len(source)).encode()+b'\0'+source).hexdigest()
    assert blob==ORIGINAL_BLOB,blob
    cases=[
      ('STABLE_DECLARED_MARGIN_POLICY',model(0,robust=True),'ACT'),
      ('FOUR_POSSIBLE_OUTCOMES_NO_PROBE',model(0),'REFUSE_ROBUST'),
      ('FOUR_POSSIBLE_OUTCOMES_ONE_PROBE_BUDGET',model(1),'REFUSE_ROBUST'),
      ('FOUR_POSSIBLE_OUTCOMES_TWO_IDEAL_BITS',model(2),'PROBE'),
      ('UNMODELLED_RIVAL_SAME_TWO_SIGNALS',model(2,rival=True),'REFUSE_ROBUST'),
    ]
    receipts=[]
    for name,m,expected in cases:
        res=decide(m,OUT/name)
        assert res['verdict']==expected,(name,res)
        assert replay(OUT/name),(name,"Lean replay failed")
        receipts.append(dict(case=name,verdict=expected,
            contract_sha256=res['contract_sha256'],
            lean_source_sha256=res['source_sha256'],replayed_by_lean=True))
        print(name,expected)
    (OUT/"SENSITIVITY_C3_RECEIPTS.json").write_text(json.dumps(receipts,indent=2)+'\n')
    print("INSACERMO_JOINT_SENSITIVITY_C3_LEAN_SUCCESS")
if __name__=="__main__":main()
