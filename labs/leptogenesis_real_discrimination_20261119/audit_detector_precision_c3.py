#!/usr/bin/env python3
"""INSACERMO same A/B neutrino CP lab: published forecast numbers as PROXIES.

Geometric oracle exhaustively enumerates 360 integer observations and all
published integer predictions. These radii are hypothetically HARD error bounds,
NOT experimental 2sigma confidence intervals. We NEVER assert actual DUNE/Hyper-K
detectors satisfy such a bound. The C3 'probe' is an ideal binary abstraction
conditional on the hard bound and exhaustive A/B catalogue.
"""
import hashlib, json, os
from pathlib import Path
from insacermo_one_engine import decide, replay

A=list(range(198,226))
B=list(range(5,41))+list(range(320,356))
OUT=Path(os.environ.get("DETECTOR_C3_OUT","/tmp/insacermo-detector-precision"))
OUT.mkdir(parents=True,exist_ok=True)
FROZEN_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"

def dist(a,b):
    x=abs(a-b)%360
    return min(x,360-x)

def regions(radius):
    obsA={z for z in range(360) if any(dist(z,a)<=radius for a in A)}
    obsB={z for z in range(360) if any(dist(z,b)<=radius for b in B)}
    return {
      "A_ONLY":sorted(obsA-obsB),
      "B_ONLY":sorted(obsB-obsA),
      "BOTH":sorted(obsA&obsB),
      "NEITHER":sorted(set(range(360))-obsA-obsB),
    }

def model(senses,good,budget):
    n=len(senses)
    na=len(good[0])
    return {
      "worldCount":n,"actionCount":na,"probeCount":1,
      "good":good,"sense":[senses],
      "nextFalse":[list(range(n))],"nextTrue":[list(range(n))],
      "actionCost":[0]*na,"probeCost":[1],
      "lowerWorld":list(range(n)),"upperWorld":list(range(n)),
      "mustActions":list(range(na)),"mayActions":list(range(na)),
      "probeKinds":["PROBE"],"depth":1,"budget":budget,
      "reserve":10,"debt":0,
    }

def main():
    raw=Path("insacermo_one_engine.py").read_bytes()
    blob=hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest()
    assert blob==FROZEN_BLOB,blob
    assert min(dist(a,b) for a in A for b in B)==95
    counts={}
    for radius in (54,44,40,36):
        reg=regions(radius)
        counts[str(radius)]={k:len(v) for k,v in reg.items()}
        assert sum(map(len,reg.values()))==360
        if radius==54:
            assert reg["BOTH"] and 272 in reg["BOTH"]
        else:
            assert not reg["BOTH"]
            assert 272 in reg["NEITHER"]
    # False observation is 1, True is 2, both is 3.
    tests=[
      ("NO_OBSERVATION_RADIUS44_AB",model([2,1],[[True,False],[False,True]],0),"REFUSE_ROBUST"),
      ("IDEAL_BOUND44_AB",model([2,1],[[True,False],[False,True]],1),"PROBE"),
      ("IDEAL_BOUND54_AMBIGUOUS",model([2,3],[[True,False],[False,True]],1),"REFUSE_ROBUST"),
      ("IDEAL_BOUND44_WITH_OTHER",model([2,1,2],[[True,False,False],[False,True,False],[False,False,True]],1),"REFUSE_ROBUST"),
    ]
    receipts=[]
    for name,m,expect in tests:
        result=decide(m,OUT/name)
        assert result["verdict"]==expect,(name,result)
        assert replay(OUT/name),(name,"failed Lean replay")
        receipts.append({"name":name,"verdict":expect,
          "source_sha256":result["source_sha256"],
          "contract_sha256":result["contract_sha256"],
          "lean_replay":True})
        print(name,expect)
    report={
     "science_scope":"HYPOTHETICAL guaranteed symmetric angle errors; published 1sigma forecasts do NOT certify hard bounds",
     "radii_deg":{"DUNE_300_2sigma_proxy":54,"DUNE_600_2sigma_proxy":44,
       "HyperK_10year_2sigma_proxy":40,"DUNE_1000_2sigma_proxy":36},
     "model_separation_deg":95,"overlap_region_counts_360_centers":counts,
     "witness_54_both":272,"witness_44_neither":272,
     "frozen_original_C3_blob":blob,
     "c3_receipts":receipts}
    (OUT/"DETECTOR_PRECISION_C3_REPORT.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(counts,indent=2))
    print("DETECTOR_PRECISION_HARD_BOUND_PROXY_C3_LEAN_SUCCESS")

if __name__=="__main__":
    main()
