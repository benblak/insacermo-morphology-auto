#!/usr/bin/env python3
"""Wine cost frontier: unmodified historical C3 solver and Lean decision gate.
Original 178 UCI Wine measurements; four-row groups; simulated observation uncertainty.
The cost units (flavanoids=2, proline=3, hue=1) are declared assumptions,
not actual financial, electrical, or laboratory costs.
"""
from __future__ import annotations
import hashlib,io,csv,json,random,itertools
from pathlib import Path
from functools import lru_cache
from sklearn.datasets import load_wine
from insacermo_one_engine import decide,replay,solve,validate

FROZEN_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
WINE_SHA="920d51b6b09e53aa478e3c239848537e663a4f61a68b6a2f10e963b62e0fdc92"
PRICE=(2,3,1)
FEATURES=((6,2.0,.12),(12,750.0,50.0),(10,1.0,.06))
MAX_BUDGET=sum(PRICE)
N_LEAN=12

def input_data():
    p=Path(__file__).resolve().parents[1]/"insacermo_one_engine.py"
    d=p.read_bytes(); blob=hashlib.sha1(b"blob "+str(len(d)).encode()+bytes([0])+d).hexdigest()
    assert blob==FROZEN_BLOB,("ENGINE_CHANGED",blob)
    wine=load_wine()
    assert wine.data.shape==(178,13)
    s=io.StringIO(newline="")
    w=csv.writer(s,lineterminator=chr(10))
    w.writerow(["sample_id","class_id","flavanoids","proline","hue"])
    for i,x in enumerate(wine.data):
        w.writerow([i,int(wine.target[i]),repr(float(x[6])),repr(float(x[12])),repr(float(x[10]))])
    data=s.getvalue().encode()
    assert hashlib.sha256(data).hexdigest()==WINE_SHA
    return wine,blob,data

def model(wine, ids, regime, budget):
    n=len(ids)
    labels=tuple(int(wine.target[i]==0) for i in ids)
    good=[[not bool(v),bool(v)] for v in labels]
    senses=[]
    for col,t,band in FEATURES:
        d=band if regime=="uncertain" else 0.
        senses.append([1 if float(wine.data[i,col])<t-d else 2 if float(wine.data[i,col])>t+d else 3 for i in ids])
    m=dict(worldCount=n,actionCount=2,probeCount=3,
        good=good,sense=senses,
        nextFalse=[list(range(n)) for _ in range(3)],
        nextTrue=[list(range(n)) for _ in range(3)],
        actionCost=[0,0],probeCost=list(PRICE),
        lowerWorld=list(range(n)),upperWorld=list(range(n)),
        mustActions=[0,1],mayActions=[0,1],probeKinds=["PROBE"]*3,
        depth=3,budget=budget,reserve=10,debt=0)
    validate(m)
    return m,labels

def independent_oracle(m,labels):
    # Independent recursion: never uses original INSACERMO planner.
    @lru_cache(None)
    def dp(ws, remaining):
        if len({labels[w] for w in ws})<=1: return 0
        if not remaining: return float("inf")
        best=float("inf")
        for q in remaining:
            rest=tuple(k for k in remaining if k!=q)
            low=tuple(w for w in ws if m["sense"][q][w]&1)
            high=tuple(w for w in ws if m["sense"][q][w]&2)
            best=min(best,PRICE[q]+max(dp(low,rest),dp(high,rest)))
        return best
    return dp(tuple(range(len(labels))),(0,1,2))

def fixed_cost(m,labels,order):
    @lru_cache(None)
    def rec(ws,at):
        if len({labels[w] for w in ws})<=1:return 0
        if at==3:return float("inf")
        q=order[at]
        no=tuple(w for w in ws if m["sense"][q][w]&1)
        yes=tuple(w for w in ws if m["sense"][q][w]&2)
        return PRICE[q]+max(rec(no,at+1),rec(yes,at+1))
    return rec(tuple(range(len(labels))),0)

def first_budget_original(m):
    for b in range(MAX_BUDGET+1):
        m["budget"]=b
        t=solve(m,m["upperWorld"],m["mustActions"],m["depth"],b)
        if t is not None:return b,t
    return None,None

def tree_worst(t):
    if "act" in t:return 0
    q=t["probe"]
    return PRICE[q]+max(tree_worst(t["no"]),tree_worst(t["yes"]))

def run(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    wine,blob,raw=input_data()
    (out/"wine_source.csv").write_bytes(raw)
    order=list(range(178));random.Random(20261116).shuffle(order)
    records=[];metrics={};lean_count=0
    orders=list(itertools.permutations(range(3)))
    for regime in ("exact","uncertain"):
        counts=dict(ACT=0,PROBE=0,REFUSE_ROBUST=0)
        sums={str(o):0 for o in orders}
        adaptive_total=0
        certified_counts=dict(ACT=0,PROBE=0,REFUSE_ROBUST=0)
        for g in range(45):
            ids=order[g*4:g*4+4]
            m,labels=model(wine,ids,regime,MAX_BUDGET)
            independent=independent_oracle(m,labels)
            minbudget,plan=first_budget_original(m)
            assert (minbudget is None)==(independent==float("inf")),(regime,g,independent,minbudget)
            if minbudget is not None:
                assert independent==minbudget,(regime,g,independent,minbudget)
                assert tree_worst(plan)==minbudget
            status="REFUSE_ROBUST" if minbudget is None else "ACT" if minbudget==0 else "PROBE"
            counts[status]+=1
            if status=="PROBE":
                adaptive_total+=minbudget
                for o in orders:
                    f=fixed_cost(m,labels,o)
                    assert f!=float("inf")
                    sums[str(o)]+=f
            row=dict(regime=regime,group=g,sample_ids=ids,real_labels=list(labels),
                oracle_budget=None if independent==float("inf") else int(independent),
                original_min_budget=minbudget,verdict=status,
                fixed_order_costs={str(o):None if fixed_cost(m,labels,o)==float("inf") else int(fixed_cost(m,labels,o)) for o in orders})
            if g<N_LEAN:
                # Historical gate certifies the optimum budget, or an
                # actual REFUSE_ROBUST when even the full budget is insufficient.
                cert_budget=MAX_BUDGET if minbudget is None else minbudget
                m["budget"]=cert_budget
                folder=out/"certificates"/regime/("group_%02d"%g)
                result=decide(m,folder)
                assert result["verdict"]==status,(regime,g,result,status)
                assert replay(folder),(regime,g,"REPLAY_FAILED")
                assert result["authorized"]==(status!="REFUSE_ROBUST")
                assert result["budget"]==cert_budget
                lean_count+=1
                certified_counts[status]+=1
                row["receipt_sha256"]=result["receipt_sha256"]
                row["lean_replayed"]=True
                print("LEAN_OK",regime,g,status,"min_budget",minbudget,flush=True)
                if status=="PROBE" and g<3:
                    # Separate negative certificate at budget - 1 is
                    # genuine C3 REFUSE_ROBUST on full lower envelope.
                    m["budget"]=minbudget-1
                    nfolder=out/"lower_budget_rejections"/regime/("group_%02d"%g)
                    neg=decide(m,nfolder)
                    assert neg["verdict"]=="REFUSE_ROBUST"
                    assert replay(nfolder)
                    row["lower_budget_Lean_REFUSE"]=True
            records.append(row)
        best_order=min(sums,key=sums.get)
        metrics[regime]=dict(counts=counts,adaptive_total_worst_cost=adaptive_total,
            best_global_fixed_order=best_order,best_fixed_total_worst_cost=sums[best_order],
            all_six_fixed_orders=sums,certified_counts=certified_counts)
        print("COUNTS",regime,counts,"OPT",adaptive_total,"BEST_FIXED",sums[best_order],"ORDER",best_order,flush=True)
    assert metrics["exact"]["counts"]==dict(ACT=13,PROBE=30,REFUSE_ROBUST=2)
    assert metrics["uncertain"]["counts"]==dict(ACT=13,PROBE=26,REFUSE_ROBUST=6)
    assert metrics["exact"]["adaptive_total_worst_cost"]==67
    assert metrics["uncertain"]["adaptive_total_worst_cost"]==64
    assert metrics["exact"]["best_fixed_total_worst_cost"]==96
    assert metrics["uncertain"]["best_fixed_total_worst_cost"]==88
    assert lean_count==24
    # Fail-closed control on one historical receipt.
    p=out/"certificates"/"exact"/"group_00"
    receipt=p/"receipt.json";old=receipt.read_bytes()
    mutated=old.replace(b'"authorized":true',b'"authorized":false')
    assert mutated!=old
    try:
        receipt.write_bytes(mutated)
        assert not replay(p)
    finally:receipt.write_bytes(old)
    assert replay(p)
    assert not replay(p,lean_binary="/missing-lean")
    report=dict(title="INSACERMO frozen C3 Wine cost frontier",engine_blob=blob,
        dataset_sha256=WINE_SHA,price_units={"flavanoids":2,"proline":3,"hue":1},
        n_real_samples=178,n_groups=45,n_regimes=2,oracle_cases=90,
        certified_Lean_cases=lean_count,metrics=metrics,
        limitations=["Probe costs are declared arbitrary abstract units, not measured time, money or energy",
          "Cross-group totals sum each group's worst-case cost, not observed mean",
          "Dataset chemical measurements are real; missingness and uncertainty bands simulated",
          "Ground-truth class labels known at specification, not discovered without supervision",
          "The gate proves finite stated contract, not the accuracy of real-world physics",
          "Optimizing by repeated original solve(b) calls is an external wrapper, not inherent budget optimization",
          "Fixed-order baseline is best among six globally shared orders, restricted to solvable groups",
          "Only 24 preregistered groups compiled in Lean, remaining 66 checked by independent oracle and original solver"])
    (out/"summary.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
    (out/"decisions.json").write_text(json.dumps(records,indent=2,ensure_ascii=False)+"\n")
    print("SUCCESS_FROZEN_WINE_COST_FRONTIER",lean_count,"CERTS",flush=True)

if __name__=="__main__":
    import sys
    run(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_wine_cost")
