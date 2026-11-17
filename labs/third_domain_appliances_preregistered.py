#!/usr/bin/env python3
"""INSACERMO: preregistered transfer of unchanged calibrated query ordering
to an independent domain: UCI Appliances Energy Prediction.

Protocol frozen at commit 743b9430 (file labs/THIRD_DOMAIN_APPLIANCES_PREREG_20261117.md).
Never optimize the threshold, calibrator, feature, cost, or dataset after viewing
held-out target labels. Historical INSACERMO and C3 Lean files remain unchanged.
"""
from __future__ import annotations
import csv, hashlib, io, json, urllib.request
from pathlib import Path
from calibrated_probe_order_two_power_domains import (
    calibration_policy, random_expectation, evaluate_order, git_blob, hash_order,
    C3_BLOB, CAL_LABELS, N, NEED)
from robust_aggregate_unknown_laws_ccpp import C3certs

URL = ("https://raw.githubusercontent.com/LuisM78/Appliances-energy-prediction-data/"
       "e3e4c27a4ae2b41b21f84b4c9ac2d822d3d0ace1/energydata_complete.csv")
THRESHOLD = 100.0
EXPECTED_ROWS = 19735
EXCLUDE = {"date", "Appliances", "lights", "rv1", "rv2"}
NAMESPACE = "appliances-third-20261117"
SOURCE_COMMIT = "e3e4c27a4ae2b41b21f84b4c9ac2d822d3d0ace1"

def load(root):
    request = urllib.request.Request(
        URL, headers={"User-Agent": "INSACERMO-third-domain-fixed-20261117"})
    with urllib.request.urlopen(request, timeout=120) as response:
        raw = response.read()
    (root / "source_energydata_pinned.csv").write_bytes(raw)
    reader = csv.DictReader(io.StringIO(raw.decode("utf-8-sig")))
    columns = reader.fieldnames
    assert columns and columns[:3] == ["date", "Appliances", "lights"], columns
    features = [x for x in columns if x not in EXCLUDE]
    assert len(features) == len(columns)-5
    values = []; dates = []
    for line in reader:
        dates.append(line["date"])
        values.append(tuple(float(line[k]) for k in features) +
                      (float(line["Appliances"]),))
    assert len(values) == EXPECTED_ROWS
    assert dates == sorted(dates), "SOURCE_NOT_CHRONOLOGICAL"
    assert all(len(x) == len(features)+1 for x in values)
    return values, features, hashlib.sha256(raw).hexdigest(), git_blob(raw), dates

def completions(prefix):
    positives = sum(prefix)
    unseen = N-len(prefix)
    return {positives+additional >= NEED for additional in range(unseen+1)}

def main(folder):
    out = Path(folder); out.mkdir(parents=True, exist_ok=True)
    engine = (Path(__file__).resolve().parents[1] / "insacermo_one_engine.py").read_bytes()
    assert git_blob(engine) == C3_BLOB, "FROZEN_ENGINE_CHANGED"
    assert CAL_LABELS == 256 and N == 8 and NEED == 6
    records, features, sha, source_blob, dates = load(out)

    # Calibration uses exactly earliest 256 true output labels.
    ids_cal = list(range(CAL_LABELS))
    policy = calibration_policy(records, ids_cal, features, THRESHOLD)
    index = policy["feature_index"]
    direction = policy["positive_direction"]

    # Precommitted group membership and ordering use INPUTS only.
    remaining = hash_order(list(range(CAL_LABELS, len(records))), NAMESPACE)
    group_count = len(remaining)//N
    excluded = remaining[group_count*N:]
    groups = [remaining[j*N:(j+1)*N] for j in range(group_count)]
    orders = [sorted(g, key=lambda i: (direction*records[i][index],i))
              for g in groups]

    actual_total=0; random_total=0.; full_total=0; contradictions=0
    success_groups=0; audit_records=[]
    for j,(group,order) in enumerate(zip(groups,orders)):
        # Heldout output labels only consulted AFTER group/order are frozen.
        count, verdict, trace = evaluate_order(order,records,THRESHOLD,include_trace=True)
        expected = sum(records[i][-1]>=THRESHOLD for i in group) >= NEED
        if verdict != expected: contradictions+=1
        assert len(trace)==count
        # Every unqueried outcome is arbitrary. Check all completion counts.
        allowed = completions([x["bit"] for x in trace])
        assert allowed=={verdict}, ("NOT_ROBUST",j)
        # Check every earlier prefix is unresolved (no unnecessary measurement).
        for t in range(len(trace)):
            assert len(completions([x["bit"] for x in trace[:t]]))==2,(
                "PREMATURE_CONTINUATION", j, t)
        m=sum(records[i][-1]>=THRESHOLD for i in group)
        expected_random=random_expectation(m)
        actual_total+=count
        random_total+=expected_random
        full_total+=len(group)
        success_groups+=int(verdict)
        audit_records.append(dict(group_id=j, positives_full=m,
            verdict="AT_LEAST_6" if verdict else "LESS_THAN_6",
            queries=count, exact_random_expectation=expected_random,
            trace=trace))
    assert contradictions==0
    assert group_count == (EXPECTED_ROWS-CAL_LABELS)//N
    assert len(excluded)==(EXPECTED_ROWS-CAL_LABELS)%N

    # Unchanged historical Lean toolchain and local 2-world certificates.
    certs=C3certs(out)
    assert len(certs)==8
    gain=random_total-actual_total
    net=gain-CAL_LABELS
    result=dict(
        study="One pre-registered independent-domain calibrated probe order transfer",
        prereg_commit="743b9430c7c804f60d65fd97530a4a2174e672a8",
        source_url=URL, source_commit=SOURCE_COMMIT,
        source_sha256=sha, source_git_blob=source_blob,
        C3_frozen_git_blob=C3_BLOB,
        source_rows=EXPECTED_ROWS, calibration_first_date=dates[0],
        calibration_last_date=dates[CAL_LABELS-1],
        holdout_first_date=dates[CAL_LABELS], holdout_last_date=dates[-1],
        threshold_wh=THRESHOLD, target="Appliances",
        excluded_proxy_columns=sorted(EXCLUDE), candidate_feature_columns=features,
        calibration_labels=CAL_LABELS, calibrated_proxy=policy,
        evaluated_groups=group_count, evaluated_rows=N*group_count,
        excluded_unmatched_rows=len(excluded),
        group_size=N, contract_positive_at_least=NEED,
        success_groups=success_groups, failure_groups=group_count-success_groups,
        queries_selected=actual_total,
        queries_random_expectation_exact=random_total,
        mean_selected=actual_total/group_count,
        mean_random_exact=random_total/group_count,
        gross_saved_vs_random=gain,
        net_saved_after_256_calibration=net,
        percent_reduction_vs_random=100*gain/random_total,
        full_reading_queries=full_total,
        contradicted_decisions=contradictions,
        all_completions_checked=True,
        independent_prefix_minimality_checked=True,
        C3_local_Lean_certificates=len(certs), C3_receipts=certs,
        transfer_pass=(net>0 and contradictions==0),
        limitations=[
            "Retrospective public archive, not a prospective physical campaign",
            "The fixed cutoff of 100 Wh is an illustrative research contract",
            "Supervised single-feature calibration is EXTERNAL to the frozen C3 engine",
            "Efficiency may fail under chronological or domain distribution shift",
            "Logical correctness only certifies the aggregate class of archived eight-record groups",
            "C3 Lean verifies eight local declared contracts, not the whole Python pipeline",
            "Input measurements of other sensors are assumed available without charging their own cost",
            "Exactly 256 labelled target calibration measurements are charged to selected policy only"
        ])
    (out/"audit.json").write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    (out/"evaluation_group_traces.json").write_text(
        json.dumps(audit_records,indent=2,ensure_ascii=False)+"\n")
    print("THIRD_DOMAIN_PRECOMMITTED", "ROWS", EXPECTED_ROWS, "GROUPS",group_count,
          "CAL_POS",policy["calibration_class_positive"],
          "FEATURE",policy["feature_name"], "SIGN",direction,flush=True)
    print("THIRD_DOMAIN_RESULTS","SELECTED",result["mean_selected"],
          "RANDOM_EXACT",result["mean_random_exact"],
          "GROSS",gain,"NET_AFTER_CAL",net,"WRONG",contradictions,
          "TRANSFER_PASS",result["transfer_pass"],flush=True)
    print("THIRD_DOMAIN_C3_LEAN",len(certs),flush=True)
    return result

if __name__=="__main__":
    import sys
    main(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_third_domain")
