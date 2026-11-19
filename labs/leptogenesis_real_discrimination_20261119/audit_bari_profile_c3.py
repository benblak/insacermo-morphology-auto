#!/usr/bin/env python3
"""Original frozen C3 and Lean replay: missing Bari profile information.
Two worlds are CONSTRUCTED P5/P8 curves, not physical explanations.
The one-bit ideal probe means release exact value of chi2 at 320 degrees.
"""
from pathlib import Path
from hashlib import sha1
import json, os
from insacermo_one_engine import decide,replay,solve

FROZEN_BLOB='bd5310b3692bcbad4e874005b7dd8eda90616f74'
OUT=Path(os.environ.get('BARI_NONID_OUT','/tmp/insacermo-bari-nonidentifiability'))
OUT.mkdir(parents=True,exist_ok=True)

def model(budget):
    return dict(worldCount=2,actionCount=2,probeCount=1,
      good=[[True,False],[False,True]],sense=[[1,2]],
      nextFalse=[[0,1]],nextTrue=[[0,1]],actionCost=[0,0],probeCost=[1],
      lowerWorld=[0,1],upperWorld=[0,1],mustActions=[0,1],mayActions=[0,1],
      probeKinds=['PROBE'],depth=1,budget=budget,reserve=10,debt=0)

def main():
    src=Path('insacermo_one_engine.py').read_bytes()
    blob=sha1(b'blob '+str(len(src)).encode()+b'\0'+src).hexdigest()
    assert blob==FROZEN_BLOB,blob
    receipts=[]
    for name,budget,expected in [
       ('PUBLISHED_CONTOURS_ONLY',0,'REFUSE_ROBUST'),
       ('EXACT_B_POINT_LIKELIHOOD_ORACLE',1,'PROBE')]:
        case=model(budget)
        result=decide(case,OUT/name)
        assert result['verdict']==expected,(name,result)
        assert replay(OUT/name)
        receipts.append(dict(name=name,verdict=expected,
                       certificate_sha256=result['source_sha256'],replayed_by_lean=True))
    assert solve(model(0),[0,1],[0,1],1,0) is None
    assert solve(model(1),[0,1],[0,1],1,1) is not None
    (OUT/'C3_PROFILE_INFORMATION_REPORT.json').write_text(json.dumps(receipts,indent=2)+'\n')
    print(json.dumps(receipts,indent=2))
    print('BARI_PROFILE_C3_LEAN_CERTIFICATES_SUCCESS')
if __name__=='__main__':main()
