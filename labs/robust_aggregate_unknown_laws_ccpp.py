#!/usr/bin/env python3
"""INSACERMO experiment: ACTION without identifying an unknown physical response law.

Real measured UCI combined-cycle power-plant electrical output (PE).
Each group of 8 independently measured records has a contract: at least 6
out of 8 outputs >= 450 MW. There is NO model of how PE depends on inputs.
Every unqueried outcome may be 0 or 1 (ALL 2^r possible completions).
Sequential decision checks lower/upper count bounds exactly and stops only
if action is invariant across all completions. This is robust even for
arbitrary unknown laws on the finite group (not on unseen records).

Data are retrospective; label access is audited logically by an explicit
query object. Groups and reading orders are fixed from input indices before
reading labels. 20 random reading-order baselines have exactly the same
contract and data. C3 historical verifies tiny 2-world boundary examples.
No claim C3 itself processes all records or discovers a physical law.
"""
from __future__ import annotations
import csv,hashlib,io,json,random,statistics,urllib.request
from pathlib import Path
from insacermo_one_engine import decide,replay,validate
N=8;NEED=6
URL=("https://raw.githubusercontent.com/ashanaka/Combined-Cycle-Power-Plant/"
     "f7e8f796be2af3cdb8c3ea48904aec7f5d3e4acf/dataSet.csv")
DATA_BLOB="e1ce541fbb298951827e86081148615ce0e83e3b"
C3_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
SEED=20261117
THRESHOLD=450.0
BASELINES=20

def blob(b):
    return hashlib.sha1(b"blob "+str(len(b)).encode()+bytes([0])+b).hexdigest()
def download(root):
    req=urllib.request.Request(URL,headers={"User-Agent":"INSACERMO-robust-aggregate-v1"})
    with urllib.request.urlopen(req,timeout=100) as r:raw=r.read()
    assert blob(raw)==DATA_BLOB,("DATA_CHANGED",blob(raw))
    rows=[tuple(map(float,line.split(","))) for line in raw.decode().splitlines() if line.strip()]
    assert len(rows)==9568 and all(len(x)==5 for x in rows),(len(rows))
    assert len(rows)%8==0
    (root/"source_data.csv").write_bytes(raw)
    return rows,hashlib.sha256(raw).hexdigest()

def groups(rows):
    # Hash index deterministically to avoid drawing groups based on labels.
    indices=sorted(range(len(rows)),key=lambda i:hashlib.sha256(
        ("membership:"+str(SEED)+":"+str(i)).encode()).digest())
    return [indices[i:i+N] for i in range(0,len(indices),N)]

def ordering(ids,rows,method,seed):
    if method=="input_AT":
        return sorted(ids,key=lambda i:(rows[i][0],i))
    if method=="random":
        t=ids[:]
        random.Random(seed).shuffle(t)
        return t
    raise ValueError(method)

def target(row):
    return int(row[4]>=THRESHOLD)

def simulate(ids,rows,order):
    observed={};trace=[]
    for idx in order:
        yes=sum(observed.values())
        remaining=N-len(observed)
        if yes>=NEED:
            return "AT_LEAST_6",len(observed),trace
        if yes+remaining<NEED:
            return "LESS_THAN_6",len(observed),trace
        assert idx not in observed
        v=target(rows[idx])
        observed[idx]=v
        trace.append(dict(index=idx,observed=v,
            lower_positive_count=yes+v,
            upper_positive_count=yes+v+N-len(observed)))
    yes=sum(observed.values())
    verdict="AT_LEAST_6" if yes>=NEED else "LESS_THAN_6"
    return verdict,len(observed),trace

def exhaustive_check(prefix):
    # Independent count-based all-completions oracle.
    yes=sum(prefix);r=N-len(prefix)
    vals=set()
    for mask in range(1<<r):
        total=yes+mask.bit_count()
        vals.add(total>=NEED)
    return vals

def model(k,allow_probe):
    # 7 observed facts include k positives. The eighth is entirely unknown,
    # represented as two logical worlds, response 0 or 1. Actions:
    # A = at least six; B = fewer than six.
    good=[[k>=NEED,k<NEED],
          [k+1>=NEED,k+1<NEED]]
    q=1
    sense=[[1,2]] if allow_probe else [[3,3]]
    model=dict(worldCount=2,actionCount=2,probeCount=q,
       good=good,sense=sense,
       nextFalse=[[0,1]],nextTrue=[[0,1]],
       actionCost=[0,0],probeCost=[1],
       lowerWorld=[0,1],upperWorld=[0,1],
       mustActions=[0,1],mayActions=[0,1],probeKinds=["PROBE"],
       depth=1,budget=1,reserve=4,debt=0)
    validate(model)
    return model

def C3certs(out):
    tests=[(4,False,"ACT"),(4,True,"ACT"),
           (5,False,"REFUSE_ROBUST"),(5,True,"PROBE"),
           (6,False,"ACT"),(6,True,"ACT"),
           (7,False,"ACT"),(7,True,"ACT")]
    audited=[]
    for k,available,expect in tests:
        folder=out/"C3_Lean"/f"k_{k}_q_{int(available)}"
        r=decide(model(k,available),folder)
        assert r["verdict"]==expect,(k,available,r)
        assert replay(folder)
        if expect=="PROBE":assert r["plan"]["probe"]==0 and r["authorized"]
        if expect=="REFUSE_ROBUST":assert not r["authorized"]
        vals=exhaustive_check([1]*k+[0]*(7-k))
        assert ("ACT"==expect)==(len(vals)==1)
        audited.append(dict(positive_in_first_seven=k,
            eighth_probe_available=available,verdict=expect,
            receipt_hash=r["receipt_sha256"]))
    folder=out/"C3_Lean"/"k_5_q_1"
    assert not replay(folder,lean_binary="/missing-lean")
    p=folder/"receipt.json";b=p.read_bytes()
    try:
        a=b.replace(b'"authorized":true',b'"authorized":false')
        assert a!=b
        p.write_bytes(a);assert not replay(folder)
    finally:p.write_bytes(b)
    assert replay(folder)
    return audited

def run(root):
    out=Path(root);out.mkdir(parents=True,exist_ok=True)
    engine=(Path(__file__).resolve().parents[1]/"insacermo_one_engine.py").read_bytes()
    assert blob(engine)==C3_BLOB
    rows,sha=download(out)
    partitions=groups(rows)
    active=[];baseline=[[] for _ in range(BASELINES)]
    # Dataset labels never used to choose group membership or query order.
    for j,ids in enumerate(partitions):
        o=ordering(ids,rows,"input_AT",SEED)
        verdict,count,trace=simulate(ids,rows,o)
        actual="AT_LEAST_6" if sum(target(rows[i]) for i in ids)>=NEED else "LESS_THAN_6"
        assert verdict==actual
        # Check prefix guarantee without assuming anything about unqueried values.
        confirmed=[x["observed"] for x in trace]
        assert len(exhaustive_check(confirmed))==1
        active.append(dict(group_id=j,verdict=verdict,
            oracle_questions=count,full_identification_questions=N,
            trace=trace))
        for b in range(BASELINES):
            order=ordering(ids,rows,"random",SEED+5000+b*20000+j)
            result,n,_=simulate(ids,rows,order)
            assert result==actual
            baseline[b].append(n)
    counts=[x["oracle_questions"] for x in active]
    baseline_means=[statistics.mean(xs) for xs in baseline]
    formal=C3certs(out)
    assert len(partitions)==1196
    assert max(counts)<=8 and min(counts)>=3
    assert all(x["oracle_questions"]<=8 for x in active)
    report=dict(experiment="Robust action on measured turbine outputs under all possible unknown laws",
       dataset="UCI Combined Cycle Power Plant measured hourly electrical output PE",
       source_git_blob=DATA_BLOB,source_sha256=sha,
       historical_C3_git_blob=C3_BLOB,
       records=len(rows),groups=len(partitions),group_size=N,
       contract="At least 6 of 8 measured PE outputs >= 450 MW",
       threshold_MW=THRESHOLD,
       no_law_catalogue=True,
       all_completion_logic="Each of 8 outcomes arbitrary Boolean; action only when all completions agree",
       target_queries_for_full_identification=len(rows),
       actual_query_count=sum(counts),
       saved_queries=len(rows)-sum(counts),
       fraction_saved=(len(rows)-sum(counts))/len(rows),
       mean_questions_per_group=statistics.mean(counts),
       median_questions_per_group=statistics.median(counts),
       min_questions=min(counts),max_questions=max(counts),
       actions_at_least_6=sum(x["verdict"]=="AT_LEAST_6" for x in active),
       actions_less_than_6=sum(x["verdict"]=="LESS_THAN_6" for x in active),
       violations_against_full_labels=0,
       random_baseline_count=BASELINES,
       random_baseline_mean_questions=statistics.mean(baseline_means),
       random_baseline_median_questions=statistics.median(baseline_means),
       active_beats_random_orders=sum(statistics.mean(counts)<x for x in baseline_means),
       C3_small_world_receipts=formal,
       C3_Lean_certificates=len(formal),
       limitations=[
         "No new physical law has been reconstructed; this experiment proves actions can be determined without identifying the complete response function.",
         "Guarantee is a deterministic finite-group tautological count bound on observed records, not a future-forecast guarantee.",
         "Measured target is available in a public archive; sequential queries are simulated readings, not newly commissioned experiments.",
         "The question order is fixed from ambient temperature only, not optimized using hidden labels.",
         "Threshold 450MW and at-least-6-of-8 target are research conventions, not a regulatory or industrial operational standard.",
         "The original C3 kernel is invoked only for eight tiny two-world contracts; Python sequential decisions are independently exact verified by exhaustive 2^remaining completions.",
         "Results may differ if grouping, target threshold, or production process changes.",
         "No inference about individual unobserved output is authorized, even if an aggregate is guaranteed.",
         "No statistical generalization or independence of records is asserted."
       ])
    (out/"audit.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
    (out/"query_trace_first_20_groups.json").write_text(
       json.dumps(active[:20],indent=2)+"\n")
    (out/"baseline_means.json").write_text(json.dumps(baseline_means,indent=2)+"\n")
    print("POWER_REAL_NO_LAW_CONTRACT","GROUPS",len(partitions),"QUERY_COUNT",sum(counts),
      "SAVED",len(rows)-sum(counts),"FRACTION_SAVED",report["fraction_saved"],flush=True)
    print("BASELINE_MEAN",report["random_baseline_mean_questions"],
      "ACTIVE_MEAN",report["mean_questions_per_group"],
      "ACTIVE_BEATS_RANDOM",report["active_beats_random_orders"],"of",BASELINES,flush=True)
    print("ROBUST_AGGREGATE_ACTIONS",report["actions_at_least_6"],
      report["actions_less_than_6"],"LEAN",len(formal),flush=True)
    return report

if __name__=="__main__":
    import sys
    run(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_robust_aggregate")
