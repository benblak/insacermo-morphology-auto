"""Isolated witness replay on two Rexel pairs supplied in conversation.

This is NOT a test of the full 719-day dataset. The original C3 engine is
imported unchanged at frozen commit 479676668de8bf2da33484012897274f48d3f072.
"""
from __future__ import annotations
import json
from pathlib import Path
from insacermo_one_engine import decide,replay

ROWS = {
  "refusal": [
    {"date":"2024-02-09","sig8":"11111101","p":"1100","label":0,"cents":2509},
    {"date":"2024-04-29","sig8":"11111101","p":"1100","label":1,"cents":2568},
  ],
  "probe": [
    {"date":"2024-02-13","sig8":"11101100","p":"1100","label":0,"cents":2426},
    {"date":"2024-05-24","sig8":"11101100","p":"1101","label":1,"cents":2863},
  ]
}
def contract(rows):
    assert len(rows)==2
    assert all(len(r["sig8"])==8 and len(r["p"])==4 for r in rows)
    assert len({r["sig8"] for r in rows})==1
    assert {r["label"] for r in rows}=={0,1}
    # The two actions correspond to the two mutually exclusive labels.
    # A passive binary probe returns 1 for no, 2 for yes.
    senses=[[1+int(rows[i]["p"][q]) for i in range(2)] for q in range(4)]
    # With 0 encoded as 1 and 1 as 2, the above yields 1 or 2.
    good=[[r["label"]==j for j in range(2)] for r in rows]
    return {
      "worldCount":2,"actionCount":2,"probeCount":4,
      "good":good,"sense":senses,
      "nextFalse":[[0,1] for _ in range(4)],
      "nextTrue":[[0,1] for _ in range(4)],
      "actionCost":[0,0],"probeCost":[1,1,1,1],
      "lowerWorld":[0,1],"upperWorld":[0,1],
      "mustActions":[0,1],"mayActions":[0,1],
      "probeKinds":["PROBE"]*4,
      "depth":4,"budget":4,"reserve":6,"debt":0
    }
def main():
    root=Path("/tmp/insacermo_rexel_native_pairs")
    report={"scope":"two real pairs only; NOT 719-day replication","cases":[]}
    for name,expected in [("refusal","REFUSE_ROBUST"),("probe","PROBE")]:
        rows=ROWS[name]
        x=contract(rows)
        p=root/name
        out=decide(x,p)
        print("CASE",name,"dates",rows[0]["date"],rows[1]["date"],
              "fullsignatures",[r["sig8"]+r["p"] for r in rows],
              "verdict",out["verdict"],"authorized",out["authorized"])
        assert out["verdict"]==expected, out
        assert out["authorized"]==(expected=="PROBE")
        assert replay(p),"Lean-backed replay rejected: "+name
        if name=="refusal":
            assert rows[0]["sig8"]+rows[0]["p"] == rows[1]["sig8"]+rows[1]["p"]
            assert out["plan"] is None
        else:
            assert rows[0]["p"][:3]==rows[1]["p"][:3]
            assert rows[0]["p"][3]!=rows[1]["p"][3]
            assert out["first_step_only"]
            assert out["plan"]["probe"]==3
        report["cases"].append({"case":name,"dates":[r["date"] for r in rows],
            "signature12":[r["sig8"]+r["p"] for r in rows],
            "verdict":out["verdict"],"authorized":out["authorized"],
            "contract_sha256":out["contract_sha256"],
            "proof_sha256":out["source_sha256"]})
    (root/"report.json").write_text(json.dumps(report,sort_keys=True,indent=2))
    print("NATIVE_C3_WITH_LEAN_BOTH_REXEL_WITNESSES_SUCCESS")
    print(json.dumps(report,sort_keys=True))
if __name__=="__main__":
    main()
