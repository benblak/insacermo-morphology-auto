"""Original finite C3 / Lean, with eight REAL CSAFE pane worlds.
Selection is explicitly RETROSPECTIVE (training panes), not external validation.
48 independent pane source files from CSAFE-ISU, authenticated by Git blob.
"""
import csv,io,json,hashlib,statistics,urllib.request,sys
from pathlib import Path
from random import Random
from concurrent.futures import ThreadPoolExecutor

ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from insacermo_one_engine import decide,replay
C="3f62cd908963cf2ef8d6bbf417ede0193b2f3a89"
repo="CSAFE-ISU/AOAS-2018-glass-manuscript"
treeurl=f"https://api.github.com/repos/{repo}/git/trees/{C}?recursive=1"
with urllib.request.urlopen(treeurl,timeout=40) as r: tree=json.load(r)
files=[f for f in tree["tree"] if f["type"]=="blob" and f["path"].startswith("glassdata/Company") and f["path"].endswith("_pane.csv")]
assert len(files)==48
def fetch(f):
    u=f"https://raw.githubusercontent.com/{repo}/{C}/{f['path']}"
    with urllib.request.urlopen(u,timeout=45) as r:b=r.read()
    digest=hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()
    assert digest==f["sha"]
    dat=list(csv.DictReader(io.StringIO(b.decode())))
    label=dat[0]["Company"];name=dat[0]["pane"]
    assert len(dat)>20 and all(d["Company"]==label and d["pane"]==name for d in dat)
    measures={k:statistics.median(float(d[k]) for d in dat) for k in dat[0] if k not in ("Company","pane","fragment","Rep")}
    assert len(measures)==18
    return dict(pane=name,label=label,measures=measures,sha=f["sha"],rows=len(dat))
with ThreadPoolExecutor(max_workers=10) as pool:allpanes=list(pool.map(fetch,files))
bylabel={z:sorted((p for p in allpanes if p["label"]==z),key=lambda x:x["pane"]) for z in ("CompanyA","CompanyB")}
rng=Random(20261013);train=[];holdout=[]
for key,group in bylabel.items():
    v=group.copy();rng.shuffle(v);nt=round(.3*len(v))
    holdout+=v[:nt];train+=v[nt:]
assert len(train)==34 and len(holdout)==14
# Construct a finite illustrative 8-pane contract. Select four from each
# manufacturer using TRAIN ONLY. Optimize separability of one declared ppm
# threshold on this selected eight-world subset; this is not a blind test.
choices=[]
for feature in sorted(train[0]["measures"]):
    a=sorted((p for p in train if p["label"]=="CompanyA"),key=lambda p:p["measures"][feature])
    b=sorted((p for p in train if p["label"]=="CompanyB"),key=lambda p:p["measures"][feature])
    for left,right in ((a,b),(b,a)):
        low=left[:4];high=right[-4:]
        lowmax=max(p["measures"][feature] for p in low)
        highmin=min(p["measures"][feature] for p in high)
        if lowmax<highmin:
            choices.append((highmin-lowmax,feature,(lowmax+highmin)/2,low+high))
assert choices,"No 8-pane separable witness"
margin,feature,threshold,chosen=max(choices,key=lambda c:(c[0],c[1]))
chosen=sorted(chosen,key=lambda p:(p["label"],p["pane"]))
good=[[p["label"]=="CompanyA",p["label"]=="CompanyB"] for p in chosen]
yes=[p["measures"][feature]>threshold for p in chosen]
assert len(set(yes))==2
assert len(set(chosen[i]["label"] for i in range(8) if yes[i]))==1
assert len(set(chosen[i]["label"] for i in range(8) if not yes[i]))==1
def contract(allow=True,lower=None):
    return dict(worldCount=8,actionCount=2,probeCount=1,
        good=good,sense=[[2 if x else 1 for x in yes]],
        nextFalse=[list(range(8))],nextTrue=[list(range(8))],
        actionCost=[0,0],probeCost=[1],
        lowerWorld=list(range(8)) if lower is None else lower,
        upperWorld=list(range(8)),mustActions=[0,1],mayActions=[0,1],
        probeKinds=["PROBE"],depth=1 if allow else 0,
        budget=1 if allow else 0,reserve=3,debt=0)
out=ROOT/"audit/csafe_c3_8pane_20261013/evidence";out.mkdir(parents=True,exist_ok=True)
cases={
    "PROBE_8_REAL_PANES":(contract(), "PROBE"),
    "REFUSE_NO_MEASUREMENT":(contract(allow=False),"REFUSE_ROBUST"),
    "EPISTEMIC_OPEN_LOWER_SUBSET":(contract(allow=False,lower=list(range(4))),"EPISTEMIC_OPEN"),
    "ACT_FOUR_KNOWN_A":(dict(contract(allow=False),lowerWorld=list(range(4)),upperWorld=list(range(4))),"ACT")
}
result={}
for name,(m,expected) in cases.items():
    r=decide(m,out/name)
    assert r["verdict"]==expected,(name,r)
    assert replay(out/name),(name,"Lean replay failed")
    result[name]={"verdict":r["verdict"],"plan":r["plan"],"authorized":r["authorized"],"contract_sha256":r["contract_sha256"]}
    print("LEAN_CERTIFIED_C3",name,expected,flush=True)
# Compare learned 8-pane policy with 14 withheld panes. C3's proof doesn't
# imply this probe is reliable outside the eight declared worlds.
train_low_class=next(p["label"] for p in chosen if p["measures"][feature]<=threshold)
train_high_class=next(p["label"] for p in chosen if p["measures"][feature]>threshold)
wrong=[];correct=[]
for p in holdout:
    guess=train_high_class if p["measures"][feature]>threshold else train_low_class
    (correct if guess==p["label"] else wrong).append(p["pane"])
report=dict(source_repo=repo,source_commit=C,source_files_verified=48,
    original_unchanged=True,declared_eight_panels=[dict(pane=p["pane"],label=p["label"],value=p["measures"][feature],blob=p["sha"]) for p in chosen],
    observed_feature=feature,declared_threshold=threshold,training_selected_margin=margin,
    scope="Finite eight-world illustrative benchmark-derived contract, not unknown-material classification.",
    cases=result,holdout_total=len(holdout),holdout_correct=len(correct),
    holdout_wrong=len(wrong),holdout_wrong_panes=wrong,
    WARNING="Eight panes were chosen retrospectively for separability; C3/Lean certifies the encoded 8-world contract only. Held-out predictions are an EXTERNAL extrapolation with no formal safety guarantee.",
    holdout_source_panes=[p["pane"] for p in holdout])
(out/"REPORT.json").write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
print("8_PANE_FROZEN_C3_FINISHED",json.dumps({k:report[k] for k in ("observed_feature","declared_threshold","holdout_total","holdout_correct","holdout_wrong")}),flush=True)
