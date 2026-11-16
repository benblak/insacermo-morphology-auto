"""Actual frozen INSACERMO C3 on UCI Wine. No engine modifications."""
import csv,hashlib,io,json,random
from pathlib import Path
from functools import lru_cache
from sklearn.datasets import load_wine
from insacermo_one_engine import decide,replay,solve

ENGINE_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
DATA_SHA="920d51b6b09e53aa478e3c239848537e663a4f61a68b6a2f10e963b62e0fdc92"
FEATURES=[(6,2.0,0.12),(12,750.0,50.0),(10,1.0,0.06)]

def oracle(m):
    @lru_cache(None)
    def safe(ws,remaining):
        if any(all(m["good"][w][a] for w in ws) for a in range(2)): return True
        for p in remaining:
            rest=tuple(x for x in remaining if x!=p)
            low=tuple(w for w in ws if m["sense"][p][w]&1)
            high=tuple(w for w in ws if m["sense"][p][w]&2)
            if safe(low,rest) and safe(high,rest): return True
        return False
    worlds=tuple(range(m["worldCount"]))
    if any(all(m["good"][w][a] for w in worlds) for a in range(2)): return "ACT"
    return "PROBE" if safe(worlds,(0,1,2)) else "REFUSE_ROBUST"

def witness(m):
    for bits in range(8):
        ws=[w for w in range(m["worldCount"]) if all(
            m["sense"][p][w] & (2 if bits&(1<<p) else 1) for p in range(3))]
        for i in ws:
            for j in ws:
                if i<j and m["good"][i]!=m["good"][j]:
                    return {"bits":format(bits,"03b"),"worlds":[i,j]}
    return None

def make(wine,ids,regime):
    labels=[int(wine.target[i]==0) for i in ids]
    good=[[not bool(y),bool(y)] for y in labels]
    senses=[]
    for col,t,band in FEATURES:
        d=band if regime=="uncertain" else 0
        senses.append([1 if wine.data[i,col]<t-d else 2 if wine.data[i,col]>t+d else 3 for i in ids])
    n=len(ids)
    return dict(worldCount=n,actionCount=2,probeCount=3,good=good,sense=senses,
        nextFalse=[list(range(n)) for _ in range(3)],
        nextTrue=[list(range(n)) for _ in range(3)],
        actionCost=[0,0],probeCost=[1,1,1],lowerWorld=list(range(n)),upperWorld=list(range(n)),
        mustActions=[0,1],mayActions=[0,1],probeKinds=["PROBE"]*3,
        depth=3,budget=3,reserve=8,debt=0),labels

def run(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    source=(Path(__file__).resolve().parents[1]/"insacermo_one_engine.py").read_bytes()
    blob=hashlib.sha1(b"blob "+str(len(source)).encode()+bytes([0])+source).hexdigest()
    assert blob==ENGINE_BLOB, ("FROZEN_SOURCE_CHANGED",blob)
    wine=load_wine()
    assert wine.data.shape==(178,13)
    txt=io.StringIO(newline="")
    c=csv.writer(txt,lineterminator=chr(10))
    c.writerow(["sample_id","class_id","flavanoids","proline","hue"])
    for i,x in enumerate(wine.data):
        c.writerow([i,int(wine.target[i]),repr(float(x[6])),repr(float(x[12])),repr(float(x[10]))])
    data=txt.getvalue().encode()
    assert hashlib.sha256(data).hexdigest()==DATA_SHA, "WINE_SOURCE_CHANGED"
    (out/"wine_source.csv").write_bytes(data)
    ids=list(range(178));random.Random(20261116).shuffle(ids)
    counts={};rows=[];certified=0
    for regime in ("exact","uncertain"):
        tally=dict(ACT=0,PROBE=0,REFUSE_ROBUST=0)
        for g in range(45):
            sample=ids[4*g:4*g+4]
            m,labels=make(wine,sample,regime)
            expected=oracle(m)
            tree=solve(m,m["upperWorld"],m["mustActions"],m["depth"],m["budget"])
            planned="REFUSE_ROBUST" if tree is None else "ACT" if "act" in tree else "PROBE"
            assert expected==planned,(g,regime,expected,planned)
            collision=witness(m)
            assert (collision is not None)==(expected=="REFUSE_ROBUST")
            tally[expected]+=1
            row=dict(regime=regime,group=g,ids=sample,labels=labels,oracle=expected,witness=collision)
            if g<12:
                folder=out/"certificates"/regime/("group_%02d"%g)
                answer=decide(m,folder)
                assert answer["verdict"]==expected,(regime,g,answer)
                assert answer["authorized"]==(expected!="REFUSE_ROBUST")
                assert replay(folder),(regime,g,"LEAN_REPLAY_FAILED")
                row["lean_replayed"]=True
                row["receipt_sha256"]=answer["receipt_sha256"]
                certified+=1
                print("LEAN_OK",regime,g,expected,flush=True)
            rows.append(row)
        counts[regime]=tally
        print("ORACLE",regime,tally,flush=True)
    assert counts["exact"]==dict(ACT=13,PROBE=30,REFUSE_ROBUST=2)
    assert counts["uncertain"]==dict(ACT=13,PROBE=26,REFUSE_ROBUST=6)
    assert certified==24
    folder=out/"certificates"/"exact"/"group_00"
    p=folder/"receipt.json";old=p.read_bytes()
    altered=old.replace(b'"authorized":true',b'"authorized":false')
    assert altered!=old
    try:
        p.write_bytes(altered)
        assert not replay(folder)
    finally:p.write_bytes(old)
    assert replay(folder)
    assert not replay(folder,lean_binary="/missing-lean")
    summary=dict(dataset="UCI Wine 178 rows",data_sha256=DATA_SHA,engine_git_blob=blob,
        seed=20261116,features=[("flavanoids",2.0,0.12),("proline",750,50),("hue",1,0.06)],
        samples=178,groups=45,oracle_cases=90,lean_certificates=certified,counts=counts,
        caveats=["Real measurements but simulated missing sensor/uncertainty",
                 "Declared class 0 versus other labels, not learned",
                 "Four-world groups only; no out-of-sample generalization",
                 "No actual physical measurement or repair carried out",
                 "Only first 12 groups per regime have compiled Lean receipts"])
    (out/"summary.json").write_text(json.dumps(summary,indent=2)+"\n")
    (out/"decisions.json").write_text(json.dumps(rows,indent=2)+"\n")
    print("FROZEN_WINE_C3_SUCCESS",certified,counts,flush=True)

if __name__=="__main__":
    import sys
    run(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_frozen_wine")
