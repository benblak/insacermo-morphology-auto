#!/usr/bin/env python3
"""INSACERMO: CAN WE CHOOSE THE NEXT USEFUL MEASUREMENT?

Precommitted, retrospective, two-domain experiment. Not blind to the
researchers' *prior* CCPP investigation: CCPP results previously inspected.
This particular calibrated policy is frozen here before the CI score runs.

Same finite decision contract in both datasets:
  for eight archived measurements, certify at least six above a fixed
  output threshold, or certify fewer than six. Each unqueried outcome may
  be arbitrary: no law or predictive assumptions needed for correctness.
  Stopping requires lower positives>=6 or upper positives<6.

A cheap 256-label calibration discovers ONE input variable with the
highest absolute standardized separation of positive vs negative labels.
The predeclared reading policy sorts each evaluation group by increasing
calibrated propensity for success (likely failures FIRST). The predictor
may fail, but the decision cannot be wrong on archived groups because
unknown labels remain arbitrary.

Comparisons:
  1. full identification of every output
  2. EXACT expectation over all 8! random permutations per held-out group
     using a hypergeometric tail sum (not a noisy Monte Carlo approximation)
  3. 40 random permutations for independent numerical cross-check
  4. omniscient minimum number of queries if the true outcomes were known
  5. calibration cost charged to the proposed strategy, not to random.

Domains:
 CCPP: 9568 measured hourly output PE, 32 whole groups (256 observations)
       chosen as calibration before holdout, evaluation on other 1164 groups.
       Previously investigated: this is FOLLOW-UP not independent replication.
 Gas turbine TEY: 256 labels from YEAR 2011 only; all 7384 observations in
       YEAR 2015 evaluated (923 complete 8-point groups). Chronological shift
       tests whether ordering transfer preserves efficiency.
 No neural training; elementary supervised one-feature calibration external
 to original frozen C3. The original engine is NOT the choice policy.
"""
from __future__ import annotations
from collections import Counter
from itertools import combinations
from pathlib import Path
import csv,hashlib,io,json,math,random,statistics,urllib.request
from robust_aggregate_unknown_laws_ccpp import C3certs

CCPP=("https://raw.githubusercontent.com/ashanaka/Combined-Cycle-Power-Plant/"
 "f7e8f796be2af3cdb8c3ea48904aec7f5d3e4acf/dataSet.csv")
CCPP_BLOB="e1ce541fbb298951827e86081148615ce0e83e3b"
TURBINE=("https://raw.githubusercontent.com/MarkLee7925/Gas-Turbine-Emissions/"
 "cb411da49edabfe1cbf8cb43650e612b1c88695c/data/")
TURBINE_BLOBS={2011:"403de0df000bedaffa99eae75b496b646200d953",
               2015:"654a113d7721faf087a50bb1101002ccd3d2a7a5"}
C3_BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
SEED=20261117;N=8;NEED=6;CAL_LABELS=256;RANDOM_CHECKS=40
# Output threshold values fixed in code BEFORE observing this CI test.
CCPP_CUTOFF=450.0
TEY_CUTOFF=130.0
CCPP_FEATURES=("ambient_temperature_AT","exhaust_vacuum_V",
               "ambient_pressure_AP","humidity_RH")
TEY_FEATURES=("ambient_temperature_AT","ambient_pressure_AP",
              "ambient_humidity_AH","air_filter_diff_pressure_AFDP",
              "gas_turbine_exhaust_pressure_GTEP",
              "turbine_inlet_temperature_TIT",
              "turbine_after_temperature_TAT",
              "compressor_discharge_pressure_CDP")

def git_blob(data):
    return hashlib.sha1(b"blob "+str(len(data)).encode()+bytes([0])+data).hexdigest()

def download(url,expected,path):
    req=urllib.request.Request(url,headers={"User-Agent":"INSACERMO-Calibration-C3/1.0"})
    with urllib.request.urlopen(req,timeout=75) as res:data=res.read()
    assert git_blob(data)==expected,("SOURCE_CHANGED",url,git_blob(data))
    path.write_bytes(data)
    return data,hashlib.sha256(data).hexdigest()

def hash_order(indices,namespace):
    return sorted(indices,key=lambda i:hashlib.sha256(
        f"{namespace}:{SEED}:{i}".encode()).digest())

def partition_8(ids):
    assert len(ids)%N==0
    return [ids[i:i+N] for i in range(0,len(ids),N)]

def prepare(root):
    raw,sha=download(CCPP,CCPP_BLOB,root/"ccpp_pinned.csv")
    ccpp=[tuple(float(v) for v in s.split(",")) for s in raw.decode().splitlines() if s.strip()]
    assert len(ccpp)==9568 and all(len(r)==5 for r in ccpp)
    # Label is PE. Calibration uses full disjoint groups, not test groups.
    cgroups=partition_8(hash_order(list(range(len(ccpp))),"ccpp-evaluation-groups-v2"))
    cal_ccpp=[i for g in cgroups[:32] for i in g]
    tests_ccpp=cgroups[32:]
    assert len(cal_ccpp)==CAL_LABELS and len(tests_ccpp)==1164

    turbine_data={}
    digests={"ccpp":sha}
    for year in (2011,2015):
        d,sha=download(TURBINE+f"gt_{year}.csv",TURBINE_BLOBS[year],
                       root/f"turbine_{year}_pinned.csv")
        text=d.decode("utf-8-sig")
        rdr=csv.DictReader(io.StringIO(text))
        columns=("AT","AP","AH","AFDP","GTEP","TIT","TAT","TEY","CDP","CO","NOX")
        assert tuple(rdr.fieldnames)==columns
        # Exclude TEY, CO, NOX from the predictor inputs to avoid direct target leak.
        turbine_data[year]=[
         tuple(float(r[k]) for k in ("AT","AP","AH","AFDP","GTEP","TIT","TAT","CDP"))+
         (float(r["TEY"]),)
         for r in rdr]
        digests[f"turbine_{year}"]=sha
    assert len(turbine_data[2011])==7411 and len(turbine_data[2015])==7384
    cal_tey=hash_order(list(range(7411)),"turbine-2011-calibration")[:CAL_LABELS]
    eval_tey=partition_8(hash_order(list(range(7384)),"turbine-2015-evaluation"))
    assert len(eval_tey)==923
    return [
       dict(key="CCPP_PE",features=CCPP_FEATURES,
            calibration_rows=ccpp,calibration_ids=cal_ccpp,
            test_rows=ccpp,test_groups=tests_ccpp,threshold=CCPP_CUTOFF,
            calibration_year="same retrospective archive, disjoint groups",
            evaluation_year="other CCPP groups"),
       dict(key="TURBINE_TEY",features=TEY_FEATURES,
            calibration_rows=turbine_data[2011],calibration_ids=cal_tey,
            test_rows=turbine_data[2015],test_groups=eval_tey,threshold=TEY_CUTOFF,
            calibration_year="2011",evaluation_year="2015")
    ],digests

def calibration_policy(a,ids,features,threshold):
    # Statistically choose ONE proxy with greatest observed separation.
    # No holdout labels, no 2015 TEY labels, no target leakage.
    values=[a[i] for i in ids]
    labels=[int(r[-1]>=threshold) for r in values]
    positives=[r for r,y in zip(values,labels) if y]
    negatives=[r for r,y in zip(values,labels) if not y]
    assert len(positives)>8 and len(negatives)>8,(
        "CALIBRATION_HAS_ONLY_ONE_CLASS",len(positives),len(negatives))
    candidates=[]
    for j,name in enumerate(features):
        all_values=[r[j] for r in values]
        dev=statistics.pstdev(all_values)
        if dev<1e-12:continue
        delta=(statistics.mean(r[j] for r in positives)-
               statistics.mean(r[j] for r in negatives))/dev
        candidates.append((abs(delta),-j,j,name,delta))
    chosen=max(candidates)
    _,_,index,name,delta=chosen
    assert delta!=0
    # The score increases toward positive PE/TEY.
    sign=1 if delta>0 else -1
    ranking=[dict(feature=name,standardized_positive_minus_negative=c[-1])
             for c in sorted(candidates,reverse=True)]
    return dict(feature_index=index,feature_name=name,positive_direction=sign,
                measured_calibration=CAL_LABELS,calibration_class_positive=sum(labels),
                calibration_class_negative=len(labels)-sum(labels),ranked_features=ranking)

def label(row,threshold):
    return int(row[-1]>=threshold)

def evaluate_order(order,rows,threshold,include_trace=False):
    obs=[]; trace=[]
    for idx in order:
        p=sum(obs);remaining=N-len(obs)
        # This inequality is an exact guarantee over ALL 2^remaining futures.
        if p>=NEED:return len(obs),True,trace
        if p+remaining<NEED:return len(obs),False,trace
        y=label(rows[idx],threshold)
        obs.append(y)
        if include_trace:trace.append(dict(row_id=idx,bit=y))
    p=sum(obs)
    return N,p>=NEED,trace

def random_expectation(m):
    """Exact E[stopping observations] for UNIFORMLY randomized read order.

    At prefix size t, there are s successes with hypergeometric law:
    C(m,s)*C(8-m,t-s)/C(8,t). Not stopped iff s<6 and t-s<3.
    E[T]=sum_{t=0}^{7}P(T>t).
    """
    out=0.
    for t in range(N):
        prob=0.
        for successes in range(max(0,t-(N-m)),min(m,t)+1):
            failed=t-successes
            if successes<NEED and failed<N-NEED+1:
                prob+=math.comb(m,successes)*math.comb(N-m,failed)/math.comb(N,t)
        out+=prob
    return out

def evaluate_domain(spec,out):
    rows=spec["test_rows"];cal=spec["calibration_rows"]
    thr=spec["threshold"]
    policy=calibration_policy(cal,spec["calibration_ids"],spec["features"],thr)
    feature=policy["feature_index"];sign=policy["positive_direction"]
    groups=spec["test_groups"]
    # Measurement-selection is frozen BEFORE any evaluation labels below.
    selected_orders=[
        sorted(g,key=lambda i:(sign*rows[i][feature],i))
        for g in groups]
    reverse_orders=[list(reversed(o)) for o in selected_orders]
    # Label-based scoring begins here, after policy/ordering are fixed.
    test_records=[]
    calibration_measured=CAL_LABELS
    total=0; random_total=0.;reverse_total=0
    positive=0
    oracle_total=0
    for g,order,reverse in zip(groups,selected_orders,reverse_orders):
        p=sum(label(rows[i],thr) for i in g)
        expected=p>=NEED
        cost,status,log=evaluate_order(order,rows,thr,include_trace=True)
        assert status==expected
        # Inspect all Boolean assignments of the as-yet-unqueried labels:
        taken=[x["bit"] for x in log]
        unknown=N-cost
        possible={sum(taken)+v>=NEED for v in range(unknown+1)}
        assert len(possible)==1 and status in possible
        # independent optimality bound for omniscient feature-independent
        # order: collect 6 successes if m>=6, otherwise 3 failures.
        omniscient_min=NEED if expected else N-NEED+1
        assert cost>=omniscient_min
        opposite,opposite_status,_=evaluate_order(reverse,rows,thr)
        assert opposite_status==expected
        baseline=random_expectation(p)
        total+=cost;oracle_total+=omniscient_min
        random_total+=baseline
        reverse_total+=opposite
        positive+=int(status)
        test_records.append(dict(group_count=len(test_records),successes_full=p,
            guaranteed_action="AT_LEAST_6" if status else "LESS_THAN_6",
            queries_calibrated=cost,queries_reverse=opposite,
            exact_expected_queries_random=baseline,
            omniscient_min=omniscient_min,
            actual_observations=log[:]))
    # Monte Carlo random-order sanity check, not headline baseline:
    random_means=[]
    for rep in range(RANDOM_CHECKS):
        counted=0
        for j,g in enumerate(groups):
            order=list(g)
            random.Random(SEED+1234+rep*100000+j).shuffle(order)
            cost,result,_=evaluate_order(order,rows,thr)
            assert result==(test_records[j]["guaranteed_action"]=="AT_LEAST_6")
            counted+=cost
        random_means.append(counted/len(groups))
    mean_random=random_total/len(groups)
    assert abs(statistics.mean(random_means)-mean_random)<.1,(
        "MC_CONTROL_DEVIATES_FROM_EXACT_EXPECTATION",
         statistics.mean(random_means),mean_random)
    result=dict(
        name=spec["key"],calibration_source=spec["calibration_year"],
        holdout_source=spec["evaluation_year"],
        input_features=list(spec["features"]),threshold=thr,
        group_size=N,contract_at_least=NEED,
        calibration_model=policy,calibration_labels=CAL_LABELS,
        test_records=len(groups)*N,test_groups=len(groups),
        success_contract_groups=positive,
        failure_contract_groups=len(groups)-positive,
        actual_query_count_calibrated=total,
        mean_query_count_calibrated=total/len(groups),
        reverse_order_total=reverse_total,
        reverse_order_mean=reverse_total/len(groups),
        exact_random_total_expectation=random_total,
        exact_random_mean_query_count=mean_random,
        random_mc_repetitions=RANDOM_CHECKS,
        random_mc_mean_of_group_means=statistics.mean(random_means),
        random_mc_min_group_mean=min(random_means),
        random_mc_max_group_mean=max(random_means),
        gain_queries_vs_random_expectation=random_total-total,
        net_gain_charging_calibration=random_total-(total+calibration_measured),
        gain_vs_full_reading=len(groups)*N-total,
        net_gain_vs_full_reading=len(groups)*N-total-calibration_measured,
        fraction_saved_vs_full=(len(groups)*N-total)/(len(groups)*N),
        baseline_omniscient_min_questions=oracle_total,
        regret_vs_omniscient=total-oracle_total,
        wrong_decisions=0)
    (out/(spec["key"]+"_group_audit.json")).write_text(json.dumps(
        test_records,indent=2,ensure_ascii=False)+"\n")
    (out/(spec["key"]+"_calibration.json")).write_text(json.dumps(
       dict(policy=policy,calibration_ids=spec["calibration_ids"]),
       indent=2)+"\n")
    print("DOMAIN_CALIBRATED",spec["key"],
      "FEATURE",policy["feature_name"],"SIGN",sign,
      "CAL_POSITIVE",policy["calibration_class_positive"],flush=True)
    print("DOMAIN_RESULTS",spec["key"],"GROUPS",len(groups),
       "CALIBRATED",result["mean_query_count_calibrated"],
       "RANDOM_EXACT",mean_random,
       "REVERSE",result["reverse_order_mean"],
       "NET_GAIN_AFTER_CAL",result["net_gain_charging_calibration"],
       "WRONG",result["wrong_decisions"],flush=True)
    return result

def no_free_lunch_witness():
    # Pick any fixed ordering; adversarial response sequence "yes yes yes
    # yes yes no no no" forces read all 8 before finding 3 negatives;
    # querying the negatives first needs 3, so no fixed policy uniformly
    # dominates every other policy over arbitrary unknown labels.
    order_labels=[1]*5+[0]*3
    def cost(label_order):
        yes=0
        for t,x in enumerate(label_order,1):
            yes+=x
            if yes>=NEED or yes+(N-t)<NEED:return t
        return 8
    assert cost(order_labels)==8 and cost(list(reversed(order_labels)))==3
    return dict(no_distribution_free_optimal_order=True,adversarial_cost=8,
        alternative_order_cost=3,
        explanation="Any deterministic fixed order can be assigned five early positives and three late negatives.")

def run(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    engine=(Path(__file__).resolve().parents[1]/"insacermo_one_engine.py").read_bytes()
    assert git_blob(engine)==C3_BLOB,"FROZEN_C3_SOURCE_CHANGED"
    specs,digests=prepare(out)
    res=[evaluate_domain(s,out) for s in specs]
    c3=C3certs(out)
    result=dict(
      study="Fixed-budget calibrated probe ordering without predictive decision risk",
      date="2026-11-17",
      frozen_C3_blob=C3_BLOB,
      source_sha256=digests,
      calibrated_query_budget_per_domain=CAL_LABELS,
      policy="Single covariate chosen from 256 labelled calibration readings; rank likely negatives first",
      contract="At least 6/8 archived outputs above declared threshold; no hidden law assumptions",
      domains=res,
      exact_random_reference="Hypergeometric sum over random permutations of each labelled 8-outcome group",
      C3_local_Lean_certificates=len(c3),
      C3_receipts=c3,
      no_free_lunch=no_free_lunch_witness(),
      limitations=[
        "CCPP dataset has been examined before in this conversation; this is a precommitted follow-up, not independent first exposure.",
        "TEY 2015 inputs were previously accessed as features in a NOx experiment, though not used there as a TEY prediction target.",
        "Calibration is supervised estimation of a correlation, so the external probe-ordering policy DOES learn a parameter; original C3 does not.",
        "Calibration labels must be accounted for; net gains may be negative, and both are reported.",
        "The exact finite guarantee is only for aggregate classification of archived groups, not the quality of a law or future data.",
        "The decision always consults actual outputs until their aggregate class cannot change under arbitrary hidden outcomes.",
        "Feature selection and input-target relationships can shift across time or sites; correctness of stopping survives but efficiency may not.",
        "C3 Lean checks eight tiny declared 2-world boundary contracts and does not certify millions of sequential choices.",
        "All measurements already publicly archived; we do not trigger a physical measurement campaign.",
        "Physical power thresholds are illustrative research settings and no regulatory or operational claims are made.",
        "Random reference is mathematically averaged over random permutations; it is not the minimum possible order for each group.",
        "The policy is restricted to one preselected calibration-based feature, not an autonomous physical law-discovery method."
      ])
    (out/"audit.json").write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    print("CALIBRATED_UNKNOWN_LAW_ROBUST_ACTION_FINISHED",
      "C3_LEAN",len(c3),"DOMAINS",len(res),flush=True)
    return result
if __name__=="__main__":
    import sys
    run(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_calibrated_orders")
