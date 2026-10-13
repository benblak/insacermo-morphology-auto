#!/usr/bin/env python3
"""New independent float-glass cohort: exact manufacturer decision with abstention.

48 real panes of architectural float glass with ICP-MS elemental ppm values.
Unit of split and decision: GLASS PANE, never repeated readings/fragments.
Only retrospective generalization to withheld panes from SAME two manufacturers.
Does not apply UCI thresholds (those require refractive index, absent here).
Feature/pair selection uses TRAIN-only leave-one-pane-out scoring, no ML training.
No formal guarantee for unseen panes; output may have wrong decisions.
Original C3 and MAX TOTAL code are untouched.
"""
import csv,hashlib,io,json,statistics,urllib.request
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from random import Random
from itertools import combinations

ROOT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent/"evidence"
OUT.mkdir(parents=True,exist_ok=True)
COMMIT="3f62cd908963cf2ef8d6bbf417ede0193b2f3a89"
REPO="CSAFE-ISU/AOAS-2018-glass-manuscript"
TREE_URL=f"https://api.github.com/repos/{REPO}/git/trees/{COMMIT}?recursive=1"
with urllib.request.urlopen(TREE_URL,timeout=40) as u:tree=json.load(u)
files=[r for r in tree["tree"] if r["type"]=="blob" and
       r["path"].startswith("glassdata/Company") and r["path"].endswith("_pane.csv")]
assert len(files)==48,len(files)
assert sum("/CompanyA-" in r["path"] for r in files)==31
assert sum("/CompanyB-" in r["path"] for r in files)==17
def verify_download(f):
    url=f"https://raw.githubusercontent.com/{REPO}/{COMMIT}/{f['path']}"
    with urllib.request.urlopen(url,timeout=45) as u:b=u.read()
    blob=hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()
    assert blob==f["sha"],("CHANGED_SOURCE",f["path"])
    lines=list(csv.DictReader(io.StringIO(b.decode("utf-8-sig"))))
    assert lines and all(r["Company"]==("CompanyA" if "/CompanyA-" in f["path"] else "CompanyB") for r in lines)
    label=lines[0]["Company"]
    pane=lines[0]["pane"]
    assert all(z["pane"]==pane for z in lines)
    fields=[key for key in lines[0] if key not in ("Company","pane","fragment","Rep")]
    assert len(fields)==18,len(fields)
    features={}
    for key in fields:
        vals=[float(row[key]) for row in lines if row[key] not in ("","NA")]
        assert len(vals)>=5,(pane,key)
        features[key]=statistics.median(vals)
    return dict(label=label,pane=pane,path=f["path"],blob=f["sha"],n_readings=len(lines),features=features)
with ThreadPoolExecutor(max_workers=10) as pool:panes=list(pool.map(verify_download,files))
panes.sort(key=lambda x:(x["label"],x["pane"]))
assert len({x["pane"] for x in panes})==48
fields=sorted(panes[0]["features"])
assert len(fields)==18
bylabel={c:[p for p in panes if p["label"]==c] for c in ("CompanyA","CompanyB")}
rng=Random(20261013)
train=[];test=[]
for label,vs in bylabel.items():
    v=vs.copy();rng.shuffle(v)
    ntest=round(len(v)*.30)
    test.extend(v[:ntest]);train.extend(v[ntest:])
assert len(train)+len(test)==48
assert not({x["pane"] for x in train}&{x["pane"] for x in test})
train.sort(key=lambda x:x["pane"]);test.sort(key=lambda x:x["pane"])
def classify(reference,target,feature_tuple):
    possible={"CompanyA","CompanyB"}
    for f in feature_tuple:
        observed=target["features"][f]
        current=set()
        for label in ("CompanyA","CompanyB"):
            vals=[r["features"][f] for r in reference if r["label"]==label]
            assert vals
            if min(vals)<=observed<=max(vals):current.add(label)
        possible &=current
    return next(iter(possible)) if len(possible)==1 else None
def counts(reference,holdout,features):
    res=Counter()
    details=[]
    for pane in holdout:
        ans=classify(reference,pane,features)
        res["refuse" if ans is None else ("correct" if ans==pane["label"] else "wrong")]+=1
        details.append(dict(pane=pane["pane"],actual=pane["label"],predicted=ans))
    return {k:res[k] for k in ("correct","wrong","refuse")},details
def select(featuresets):
    # Use leave-one-PANE-out; penalize errors more than refusals.
    ranked=[]
    for ff in featuresets:
        score=Counter()
        for i,p in enumerate(train):
            rest=train[:i]+train[i+1:]
            x=classify(rest,p,ff)
            score["refuse" if x is None else ("correct" if x==p["label"] else "wrong")]+=1
        quality=score["correct"]-5*score["wrong"]
        ranked.append((quality,score["correct"],-score["wrong"],-len(ff),ff,dict(score)))
    ranked.sort(reverse=True)
    return ranked[0],len(ranked)
one,n1=select([(f,) for f in fields])
two,n2=select(list(combinations(fields,2)))
selected1=one[4];selected2=two[4]
result1,details1=counts(train,test,selected1)
result2,details2=counts(train,test,selected2)
# "Adaptive" plan asks second feature only if first query does not fix label;
# second stage uses joint inference, and retains first answer if unique.
def adaptive(p):
    first=classify(train,p,selected2[:1])
    return first if first is not None else classify(train,p,selected2)
ac=Counter();numsecond=0;adetails=[]
for p in test:
    first=classify(train,p,selected2[:1])
    if first is None:numsecond+=1
    ans=first if first is not None else classify(train,p,selected2)
    ac["refuse" if ans is None else ("correct" if ans==p["label"] else "wrong")]+=1
    adetails.append(dict(pane=p["pane"],actual=p["label"],predicted=ans))
resultAdaptive={k:ac[k] for k in ("correct","wrong","refuse")}
out={
 "status":"EMPIRICAL_WITHHELD_PANES_NOT_PROSPECTIVE",
 "source_repo":REPO,"source_commit":COMMIT,"files_verified_by_git_blob":48,
 "independent_from_UCI_214":True,"variables":"18 isotopic elemental concentrations, ppm (NO refractive index)",
 "data_unit":"per-pane medians over fragment/instrument repeats",
 "n_panes":48,"company_panes":{k:len(v) for k,v in bylabel.items()},
 "train_panes":len(train),"test_panes":len(test),
 "seed":20261013,"training_selection":"leave-one-pane-out, correct - 5*wrong, binary abstaining interval classifier",
 "training_candidate_single":n1,"training_candidate_pairs":n2,
 "single_feature":selected1,"two_features":selected2,
 "train_loocv_single":one[-1],"train_loocv_pair":two[-1],
 "test_single":result1,"test_pair":result2,"test_adaptive":resultAdaptive,
 "adaptive_second_measurement_needed":numsecond,
 "test_pane_ids":[(r["label"],r["pane"]) for r in test],
 "details_single":details1,"details_pair":details2,"details_adaptive":adetails,
 "pane_manifest":[{k:p[k] for k in ("label","pane","path","blob","n_readings")} for p in panes],
 "limitations":[
   "The 48 panes are archival, not prospectively collected after protocol lock",
   "No universal ACT guarantee is inferred from within-training class ranges",
   "Manufacturer classification only; not proof of matching an unknown crime-scene fragment",
   "Threshold intervals estimated from training panes; there may be test errors",
   "The selection is exact empirical enumeration external to original C3, which is UNCHANGED",
   "Manufacturer identity and pane group grouping are ground truth from the public archive",
   "A second feature already present in laboratory measurements is a logical read, not independently priced analysis",
   "This dataset cannot validate the UCI RI threshold due to missing refractive index"
 ]
}
(OUT/"REPORT.json").write_text(json.dumps(out,indent=2,ensure_ascii=False)+"\n")
print("GLASS_CSAFE_EXTERNAL_PANES_COMPLETED",json.dumps({k:out[k] for k in [
"files_verified_by_git_blob","n_panes","company_panes","train_panes","test_panes",
"training_candidate_single","training_candidate_pairs","single_feature","two_features",
"train_loocv_single","train_loocv_pair","test_single","test_pair","test_adaptive",
"adaptive_second_measurement_needed"]},ensure_ascii=False),flush=True)
