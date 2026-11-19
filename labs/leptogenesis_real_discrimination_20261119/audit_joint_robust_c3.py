#!/usr/bin/env python3
"""Original C3, two-analysis finite interpretation. NOT scientific truth validation.
Bari 2026.a preliminary normal ordering phase contours and separate
NuFIT6.1 TByes normal-ordering finite grid. Nominal 2sigma=4, 3sigma=9
only; does not assert statistical calibration or source authenticity.
Worlds 0=Bari and 1=NuFIT. Probe 'which analysis' is a purely ideal
bookkeeping distinction, not a real physical neutrino measurement.
This C3 identifies decisions ABOUT EACH ANALYSIS, not mechanisms A/B.
"""
import hashlib,json,os
from pathlib import Path
from insacermo_one_engine import decide,replay,solve

OUT=Path(os.environ.get("JOINT_OUT","/tmp/insacermo-joint-bari-nufit"))
OUT.mkdir(parents=True,exist_ok=True)
FROZEN_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"

def contract(good,budget):
    # 2 distinct analyses; two mutually exclusive declarative actions.
    return {
      "worldCount":2,"actionCount":2,"probeCount":1,
      "good":good,"sense":[[1,2]],
      "nextFalse":[[0,1]],"nextTrue":[[0,1]],
      "actionCost":[0,0],"probeCost":[1],
      "lowerWorld":[0,1],"upperWorld":[0,1],
      "mustActions":[0,1],"mayActions":[0,1],
      "probeKinds":["PROBE"],"depth":1,"budget":budget,
      "reserve":10,"debt":0
    }

def main():
    b=Path("insacermo_one_engine.py").read_bytes()
    h=hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()
    assert h==FROZEN_BLOB,h
    tests=[
      # Action0 EXCLUDE B-low at nominal 3sigma; action1 KEEP it:
      ("B_LOW_3SIGMA_BOTH_EXCLUDE",[[True,False],[True,False]],0,"ACT"),
      # Action0 RETAIN B-high at nominal 3sigma; action1 EXCLUDE it:
      ("B_HIGH_3SIGMA_BOTH_RETAIN",[[True,False],[True,False]],0,"ACT"),
      # Action0 EXCLUDE B-high at 2sigma; action1 RETAIN it:
      ("B_HIGH_2SIGMA_NO_ANALYSIS_CHOICE",[[True,False],[False,True]],0,"REFUSE_ROBUST"),
      ("B_HIGH_2SIGMA_IDEAL_ANALYSIS_LABEL",[[True,False],[False,True]],1,"PROBE")
    ]
    receipts=[]
    for name,good,budget,expected in tests:
        m=contract(good,budget)
        result=decide(m,OUT/name)
        assert result["verdict"]==expected,(name,result)
        assert replay(OUT/name),(name,"replay failed")
        assert (solve(m,[0,1],[0,1],1,budget) is None)==(expected=="REFUSE_ROBUST")
        receipts.append({"name":name,"verdict":expected,
                         "contract_sha256":result["contract_sha256"],
                         "certificate_sha256":result["source_sha256"],
                         "replayed":True})
        print(name,expected,"LEAN_RECEIPT_REPLAYED")
    (OUT/"JOINT_C3_RECEIPTS.json").write_text(json.dumps(receipts,indent=2)+"\n")
    print("JOINT_BARI_NUFIT_C3_LEAN_SUCCESS")
if __name__=="__main__":main()
