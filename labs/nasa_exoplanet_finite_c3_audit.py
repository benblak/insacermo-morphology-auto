#!/usr/bin/env python3
"""Finite C3 audit: what strong astronomical average fit CANNOT guarantee.

Uses the same NASA snapshot and host-disjoint holdout produced by
nasa_exoplanet_blind_law.py. Selects four holdout planets with >20% error
and four matched <3% error planets based on 3 coarse metadata probes.
This is a deliberately label-selected diagnostic STRESS TEST (not blind
performance evaluation). Frozen C3 certifies refusal to classify accuracy
from these coarse probes and ACT on trivially all-safe sample.
"""
import csv,hashlib,io,json,math,random,statistics
from pathlib import Path
from insacermo_one_engine import decide,replay,validate

BLOB="bd5310b3692bcbad4e874005b7dd8eda90616f74"
SEED=20261116

def signature(r):
    # Only pre-observation metadata: a, stellar mass, transit/RV.
    return (int(r["a"]>=.1),int(r["m"]>=1.),int(r["method"]=="Transit"))

def load_records(snapshot,report):
    d=snapshot.read_bytes()
    assert hashlib.sha256(d).hexdigest()==report["raw_snapshot_sha256"]
    parsed=[]
    for raw in csv.DictReader(io.StringIO(d.decode("utf-8-sig"))):
        try:
            if raw["sy_snum"]!="1" or raw["cb_flag"]!="0":continue
            if raw["discoverymethod"] not in ("Transit","Radial Velocity"):continue
            if raw["pl_orbperlim"] not in ("","0") or raw["pl_orbsmaxlim"] not in ("","0"):continue
            p=float(raw["pl_orbper"]);a=float(raw["pl_orbsmax"]);m=float(raw["st_mass"])
            if not(.1<m<3 and .003<a<8 and .1<p<12000):continue
            parsed.append(dict(name=raw["pl_name"],host=raw["hostname"],p=p,
                a=a,m=m,method=raw["discoverymethod"]))
        except (ValueError,TypeError,KeyError):continue
    parsed.sort(key=lambda x:x["name"])
    assert len(parsed)==report["n_filtered"]
    hosts=sorted({r["host"] for r in parsed})
    random.Random(SEED).shuffle(hosts)
    hold=set(hosts[:round(len(hosts)*.35)])
    test=[r for r in parsed if r["host"] in hold]
    assert len(test)==report["host_disjoint_holdout_size"]
    f=report["active_formula"]
    for r in test:
        approx=365.25*math.exp(f["alpha"]*math.log(r["a"])+f["beta"]*math.log(r["m"])+f["log_scale"])
        r["relative_error"]=abs(approx/r["p"]-1)
        r["safe"]=r["relative_error"]<=.1
    return test

def choose_pairs(test):
    good={}
    for r in test:
        if r["relative_error"]<=.03:
            good.setdefault(signature(r),[]).append(r)
    for v in good.values():v.sort(key=lambda r:(r["relative_error"],r["name"]))
    bad=sorted((r for r in test if r["relative_error"]>.20),key=lambda r:(-r["relative_error"],r["name"]))
    pairs=[]
    used_hosts=set()
    for b in bad:
        if b["host"] in used_hosts:continue
        group=good.get(signature(b),[])
        match=next((x for x in group if x["host"] not in used_hosts and x["host"]!=b["host"]),None)
        if match is None:continue
        pairs.append((b,match));used_hosts|={b["host"],match["host"]}
        if len(pairs)==4:break
    assert len(pairs)==4,("NO_MATCHED_FOUR_PAIRS",len(pairs))
    return pairs

def c3_contract(rows):
    n=len(rows)
    q=3
    sigs=[signature(r) for r in rows]
    m=dict(worldCount=n,actionCount=2,probeCount=q,
        good=[[not r["safe"],r["safe"]] for r in rows],
        sense=[[2 if sigs[w][j] else 1 for w in range(n)] for j in range(q)],
        nextFalse=[list(range(n)) for _ in range(q)],
        nextTrue=[list(range(n)) for _ in range(q)],
        actionCost=[0,0],probeCost=[1,1,1],
        lowerWorld=list(range(n)),upperWorld=list(range(n)),
        mustActions=[0,1],mayActions=[0,1],
        probeKinds=["PROBE"]*3,depth=3,budget=3,reserve=8,debt=0)
    validate(m)
    return m

def summary(r):
    return {"name":r["name"],"host":r["host"],"relative_error":r["relative_error"],
        "reliable_within_10pct":r["safe"],"metadata_signature":signature(r),
        "period_days":r["p"],"a_au":r["a"],"star_mass_solar":r["m"],
        "discovery_method":r["method"]}

def run(root):
    root=Path(root)
    report=json.loads((root/"report.json").read_text())
    engine=(Path(__file__).resolve().parents[1]/"insacermo_one_engine.py").read_bytes()
    blob=hashlib.sha1(b"blob "+str(len(engine)).encode()+b"\0"+engine).hexdigest()
    assert blob==BLOB
    test=load_records(root/"nasa_pscomppars_snapshot.csv",report)
    pairs=choose_pairs(test)
    bad=[p[0] for p in pairs];good=[p[1] for p in pairs]
    allrows=bad+good
    assert len(allrows)==8 and len({r["host"] for r in allrows})==8
    assert all(signature(b)==signature(g) for b,g in pairs)
    counterexamples=[]
    # Four two-world impossible classifications on measured metadata.
    for i,(b,g) in enumerate(pairs):
        folder=root/"C3_Lean_receipts"/f"pair_{i}_indiscernible"
        r=decide(c3_contract([b,g]),folder)
        assert r["verdict"]=="REFUSE_ROBUST" and not r["authorized"],(i,r)
        assert replay(folder)
        counterexamples.append(dict(pair=i,bad=summary(b),good=summary(g),
            C3_verdict=r["verdict"],certificate_sha256=r["receipt_sha256"]))
        print("NASA_PAIR_LEAN_REFUSE",i,b["name"],g["name"],flush=True)
    # Eight-world combined model, still logically impossible.
    folder=root/"C3_Lean_receipts"/"eight_world_refusal"
    r=decide(c3_contract(allrows),folder)
    assert r["verdict"]=="REFUSE_ROBUST" and replay(folder)
    # Valid ACT for 8 strictly reliable planets, but only under declared
    # eight-row world set: not a universal claim about exoplanets.
    folder2=root/"C3_Lean_receipts"/"eight_good_world_act"
    good_more=[]; selected_hosts=set()
    for x in sorted((x for x in test if x["safe"]),key=lambda r:(r["relative_error"],r["name"])):
        if x["host"] in selected_hosts:continue
        good_more.append(x);selected_hosts.add(x["host"])
        if len(good_more)==8:break
    assert len(good_more)==8, "INSUFFICIENT_DISTINCT_HOSTS"
    act=decide(c3_contract(good_more),folder2)
    assert act["verdict"]=="ACT" and act["authorized"] and replay(folder2)
    # Negative controls
    assert not replay(folder2,lean_binary="/no-such-lean-binary")
    f=folder2/"receipt.json";old=f.read_bytes()
    altered=old.replace(b'"authorized":true',b'"authorized":false')
    assert altered!=old
    try:
        f.write_bytes(altered)
        assert not replay(folder2)
    finally:f.write_bytes(old)
    assert replay(folder2)
    audit={
        "source_dataset_sha256":report["raw_snapshot_sha256"],
        "historical_c3_blob":blob,
        "candidate_law":report["active_formula"],
        "diagnostic_note":"Deliberately selected on held-out residual labels, NOT an independent blinded evaluation",
        "probes":["semi_major_axis_au >= 0.1","host_star_mass_solar >= 1","discovery_method = Transit"],
        "four_observed_indiscernible_pairs":counterexamples,
        "eight_world_model":"REFUSE_ROBUST",
        "eight_good_world_model":"ACT_WITHIN_DECLARED_WORLD_SET",
        "C3_certificates_verified":6,
        "controls":["tampered_receipt_rejected","missing_Lean_rejected"],
        "conclusion":"Good average astrophysical fit does not imply certified reliability on a single planet from these coarse metadata",
        "limitation":"All finite guarantees are conditional on the dataset, declared labels and probes, not proof of Kepler's physics"}
    (root/"C3_nasa_audit.json").write_text(json.dumps(audit,indent=2,ensure_ascii=False)+"\n")
    print("NASA_REAL_FINITE_C3_LEAN_SUCCESS",6,"CERTIFICATES",flush=True)

if __name__=="__main__":
    import sys
    run(sys.argv[1] if len(sys.argv)>1 else "/tmp/insacermo_nasa")
