#!/usr/bin/env python3
"""CSAFE float-glass: no cherry-picking; heldout panes, repeated fragments,
and original bounded C3/Lean decisions. Original C3 unchanged.
This is retrospective external validation on 48 archived panes, NOT new
prospective sampling or an absolute physical guarantee.
"""
import csv,io,json,hashlib,statistics,urllib.request,sys
from pathlib import Path
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from insacermo_one_engine import decide,replay
COMMIT="3f62cd908963cf2ef8d6bbf417ede0193b2f3a89"
REPO="CSAFE-ISU/AOAS-2018-glass-manuscript"
URL=f"https://api.github.com/repos/{REPO}/git/trees/{COMMIT}?recursive=1"
with urllib.request.urlopen(URL,timeout=40) as r:tree=json.load(r)
files=sorted((x for x in tree["tree"] if x["type"]=="blob" and
    x["path"].startswith("glassdata/Company") and x["path"].endswith("_pane.csv")),key=lambda x:x["path"])
assert len(files)==48
def get(x):
    with urllib.request.urlopen(f"https://raw.githubusercontent.com/{REPO}/{COMMIT}/{x['path']}",timeout=45) as r:b=r.read()
    assert hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()==x["sha"]
    rows=list(csv.DictReader(io.StringIO(b.decode("utf-8-sig"))))
    assert len(rows)>20
    company=rows[0]["Company"];pane=rows[0]["pane"]
    assert all(z["Company"]==company and z["pane"]==pane for z in rows)
    cols=sorted(set(rows[0])-{"Company","pane","fragment","Rep"})
    med={c:statistics.median(float(z[c]) for z in rows) for c in cols}
    return dict(company=company,pane=pane,features=med,rows=len(rows),sha=x["sha"])
with ThreadPoolExecutor(max_workers=10) as pool:data=list(pool.map(get,files))
data.sort(key=lambda p:(p["company"],p["pane"]))
assert Counter(x["company"] for x in data)==Counter(CompanyA=31,CompanyB=17)
cols=sorted(data[0]["features"]);assert len(cols)==18
labels=("CompanyA","CompanyB")
def policy(ref,t,ff):
    possible=set(labels)
    for f in ff:
        value=t["features"][f]
        possible &= {label for label in labels if
            min(x["features"][f] for x in ref if x["company"]==label)<=value<=
            max(x["features"][f] for x in ref if x["company"]==label)}
    return next(iter(possible)) if len(possible)==1 else None
def score(ref,ff):
    # Entirely train-internal leave-one-pane-out, cost 5 per wrong vs 1 per refusal.
    s=Counter()
    for i,p in enumerate(ref):
        rest=ref[:i]+ref[i+1:]
        a=policy(rest,p,ff)
        s["REFUSE" if a is None else ("OK" if a==p["company"] else "WRONG")]+=1
    return (s["OK"]-5*s["WRONG"],s["OK"],-s["WRONG"],-len(ff)),s
def pick(ref,ffsets):
    outcomes=[]
    for ff in ffsets:
        rank,s=score(ref,ff)
        outcomes.append((rank,ff,s))
    return sorted(outcomes,key=lambda x:(-x[0][0],-x[0][1],x[0][2],-x[0][3],x[1]))[0]
singles=[(c,) for c in cols];pairs=list(combinations(cols,2))
results=[]
for i,test in enumerate(data):
    train=data[:i]+data[i+1:]
    ff1=pick(train,singles)[1];ff2=pick(train,pairs)[1]
    a1=policy(train,test,ff1)
    a2=policy(train,test,ff2)
    first=policy(train,test,ff2[:1])
    adaptive=first if first is not None else a2
    def verdict(a):return "REFUSE" if a is None else ("OK" if a==test["company"] else "WRONG")
    results.append(dict(pane=test["pane"],company=test["company"],
        single_feature=ff1[0],pair_features=ff2,
        single=verdict(a1),pair=verdict(a2),adaptive=verdict(adaptive),
        second_read=first is None))
counts={k:dict(Counter(z[k] for z in results)) for k in ("single","pair","adaptive")}
# FIXED 8-world contract without outcome-based picking: alphabetically first
# four pane IDs from A and B, with one declared chemical probe and no
# assumption that observation gives unique manufacturer.
eight=[p for label in labels for p in data if p["company"]==label][:4]
# explicitly fix four from EACH company
eight=[p for label in labels for p in [p for p in data if p["company"]==label][:4]]
assert len(eight)==8
# A single deterministic query, threshold obtained solely from first 8
# values (regardless of whether it separates companies); no cherry-picking.
f="Ce140"
vals=sorted(p["features"][f] for p in eight)
threshold=(vals[3]+vals[4])/2
good=[[p["company"]==label for label in labels] for p in eight]
sense=[[2 if p["features"][f]>threshold else 1 for p in eight]]
m=dict(worldCount=8,actionCount=2,probeCount=1,good=good,sense=sense,
       nextFalse=[list(range(8))],nextTrue=[list(range(8))],
       actionCost=[0,0],probeCost=[1],
       lowerWorld=list(range(8)),upperWorld=list(range(8)),
       mustActions=[0,1],mayActions=[0,1],probeKinds=["PROBE"],
       depth=1,budget=1,reserve=3,debt=0)
OUT=ROOT/"audit/csafe_nocherrypick_20261013/evidence";OUT.mkdir(parents=True,exist_ok=True)
verdict=decide(m,OUT/"original_c3")
assert replay(OUT/"original_c3")
# Independent oracle: robust decision exists iff an action works for every
# member of each distinguishable observation outcome.
groups={out:[i for i,p in enumerate(eight) if sense[0][i]==out] for out in (1,2)}
def common_action(ids):return any(all(good[i][a] for i in ids) for a in range(2))
oracle="ACT" if common_action(range(8)) else ("PROBE" if all(common_action(v) for v in groups.values()) else "REFUSE_ROBUST")
assert verdict["verdict"]==oracle,(verdict,oracle)
print("CSAFE_FIXED_8_C3_LEAN",verdict["verdict"],"oracle",oracle,flush=True)
print("CSAFE_48_PANE_LOPO",json.dumps(counts,sort_keys=True),flush=True)
report=dict(source_commit=COMMIT,files_authenticated=48,
    train_test="48 leave-one-entire-pane-out folds; selecting feature(s) only inside each training set",
    evaluated_panes=48,results=results,counts=counts,
    second_reads=sum(z["second_read"] for z in results),
    single_selected=dict(Counter(z["single_feature"] for z in results)),
    fixed_worlds=[dict(company=p["company"],pane=p["pane"],Ca42=p["features"]["Ca42"],
                       Ce140=p["features"][f]) for p in eight],
    fixed_query=dict(feature=f,threshold=threshold),
    original_c3=dict(verdict=verdict["verdict"],authorized=verdict["authorized"],
        lean_replay=True,contract_sha256=verdict["contract_sha256"]),
    oracle=oracle,source="CSAFE-ISU archival float-glass elemental ppm, 2016-17",
    limits=[
      "No prospective unseen manufacturer or new sample collection",
      "LOPO selection uses training pane labels, exact deterministic supervised calibration, not neural training",
      "Interval-based manufacturer decision is external and can make mistakes or abstain",
      "C3 original only evaluates a FIXED EIGHT pane model; external 48-LOPO counts are not Lean certified",
      "Ce140 threshold derives from the fixed eight, not from validation panes",
      "One chemical datum read is not priced as a physical laboratory measurement",
      "No guarantee of physical chemical laws, causality, or forensic identification"])
(OUT/"REPORT.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
# Stress: same physical eight-world contract, but probe outcome may be
# ambiguous for ONE of the worlds. A valid probe tree must be safe for either
# observation result, so it must refuse where mixed-label fibers arise.
from copy import deepcopy
assert verdict["verdict"]=="PROBE"
amb=deepcopy(m)
amb["sense"][0][0]=3
worse=decide(amb,OUT/"ambiguous_real_measure")
assert replay(OUT/"ambiguous_real_measure")
groups_noisy={out:[i for i in range(8) if amb["sense"][0][i]&out] for out in (1,2)}
oracle_noisy="ACT" if common_action(range(8)) else ("PROBE" if all(common_action(v) for v in groups_noisy.values()) else "REFUSE_ROBUST")
assert oracle_noisy=="REFUSE_ROBUST" and worse["verdict"]==oracle_noisy,(oracle_noisy,worse)
report["ambiguous_probe_stress"]=dict(original="PROBE",ambiguous="REFUSE_ROBUST",
   source="Synthetic observation uncertainty deliberately added to one genuine pane",
   lean_replay=True)
(OUT/"REPORT.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
print("CSAFE_NOISY_PROBE_C3_LEAN",worse["verdict"],"oracle",oracle_noisy,flush=True)

print("CSAFE_NOCHERRYPICK_EXPERIMENT_DONE",flush=True)
