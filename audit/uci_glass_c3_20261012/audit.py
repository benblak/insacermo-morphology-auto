#!/usr/bin/env python3
"""INSACERMO C3 on an archival, public 214-sample forensic glass dataset.
SOURCE: UCI Glass Identification, doi:10.24432/C5WW2P
Exact 2020 GitHub mirror commit: d20fcb6402ae34e653d4513b00f39257bb37ed7f
IMPORTANT: The nine binary thresholds are EXPERIMENTAL, not validated physical
assays. The best additional threshold is selected retrospectively on all 214
labeled specimens. This is an IN-SAMPLE exact audit, NOT a new-sample guarantee,
ML generalization, forensic identification, or new physical law.
"""
from __future__ import annotations
from collections import defaultdict,Counter
from decimal import Decimal as D
from pathlib import Path
import hashlib, json, sys, urllib.request

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from insacermo_one_engine import decide,replay

MIRROR_COMMIT="d20fcb6402ae34e653d4513b00f39257bb37ed7f"
BLOB="ab21361ce9fa4b168acfd331c4cfad729b9b1b8f"
URL=f"https://raw.githubusercontent.com/jbrownlee/Datasets/{MIRROR_COMMIT}/glass.data"
output=ROOT/"audit/uci_glass_c3_20261012/evidence"
output.mkdir(parents=True,exist_ok=True)
with urllib.request.urlopen(URL,timeout=35) as http:
    data=http.read()
def gitblob(x):
    return hashlib.sha1(b"blob "+str(len(x)).encode()+b"\0"+x).hexdigest()
assert gitblob(data)==BLOB, ("DATA_SOURCE_CHANGED",gitblob(data))
(output/"glass.data").write_bytes(data)
features=["RI","Na","Mg","Al","Si","K","Ca","Ba","Fe"]
# Hypothetical binary feature panel, not a validated assay kit. Strict >.
original_cutoffs=list(map(D,["1.518","13.5","2","1.5","73","0.5","8.5","0.5","0.1"]))
records=[]
for line in data.decode("utf-8").splitlines():
    parts=line.strip().split(",")
    assert len(parts)==11
    ident=int(parts[0]); x=tuple(map(D,parts[1:10])); label=int(parts[10])
    records.append((ident,x,label))
assert len(records)==214 and sorted(r[0] for r in records)==list(range(1,215))
classes=Counter(r[2] for r in records)
assert classes==Counter({1:70,2:76,3:17,5:13,6:9,7:29})
assert len(set(r[1] for r in records))==214, "unexpected duplicate full feature vector"

def panel_signature(r):
    return tuple(int(v>cutoff) for v,cutoff in zip(r[1],original_cutoffs))
sigs=[panel_signature(r) for r in records]
def grouped_summaries(signatures):
    groups=defaultdict(list)
    for r,s in zip(records,signatures): groups[s].append(r)
    pure=[r for rs in groups.values() if len({r[2] for r in rs})==1 for r in rs]
    mixed=[r for rs in groups.values() if len({r[2] for r in rs})>1 for r in rs]
    mixed_group_count=sum(len({r[2] for r in rs})>1 for rs in groups.values())
    contradictions=sum(sum(a[2]!=b[2] for k,a in enumerate(rs) for b in rs[k+1:])
        for rs in groups.values())
    return dict(total_groups=len(groups),pure_rows=len(pure),ambiguous_rows=len(mixed),
        mixed_groups=mixed_group_count,conflicting_pairs=contradictions)

base=grouped_summaries(sigs)
assert base==dict(total_groups=73,pure_rows=93,ambiguous_rows=121,mixed_groups=21,conflicting_pairs=216),base

# Search ALL distinct cuts between adjacent observed concentrations, with
# an exhaustive, deterministic search. This search is external to frozen C3.
best_n=-1;best=[]
candidates=0
for f in range(9):
    vals=sorted({r[1][f] for r in records})
    for left,right in zip(vals,vals[1:]):
        cut=(left+right)/D(2)
        candidates+=1
        extended=[s+(int(r[1][f]>cut),) for r,s in zip(records,sigs)]
        pure=grouped_summaries(extended)["pure_rows"]
        if pure>best_n:
            best_n=pure
            best=[(f,cut,left,right)]
        elif pure==best_n:
            best.append((f,cut,left,right))
assert candidates==930,(candidates,best_n)
assert best_n==141 and best[0][0]==0 and best[0][1]==D("1.51715"),(best_n,best)
print("FULL_214_EXACT_BASELINE",base,flush=True)
print("EXHAUSTIVE_ADDED_CUTOFF_SCAN",candidates,"OPTIMUM",best_n,"WINNERS",
    [(features[f],str(c)) for f,c,l,h in best],flush=True)

# INDEPENDENT COUNT: a sample is certifiable iff there is no OTHER-label
# sample with the same signature (pairwise predicate, no bucket aggregation).
f_opt,cut_opt,_,_=best[0]
best_sigs=[s+(int(r[1][f_opt]>cut_opt),) for r,s in zip(records,sigs)]
def independent_pure(signatures):
    pure=0
    for i,r in enumerate(records):
        if all(records[j][2]==r[2] or signatures[j]!=signatures[i] for j in range(len(records))):
            pure+=1
    return pure
assert independent_pure(sigs)==93
assert independent_pure(best_sigs)==141
print("INDEPENDENT_PAIRWISE_ORACLE_AGREES 93_TO_141",flush=True)

# Select the lexicographically FIRST pair of differently labeled real samples
# sharing the original complete 9-bit panel but split by the optimal added
# threshold. Witness is thus reproducible, not hand-invented.
witness=None
for i in range(len(records)):
    for j in range(i+1,len(records)):
        if records[i][2]!=records[j][2] and sigs[i]==sigs[j] and best_sigs[i]!=best_sigs[j]:
            witness=(records[i],records[j])
            break
    if witness: break
assert witness is not None
a,b=witness
assert a[0]==4 and b[0]==83,(a[0],b[0])
print("WITNESS_SAMPLES",a[0],b[0],"ORIGINAL_IDENTICAL_9_BIT_SIGNATURE",
    "".join(map(str,panel_signature(a))),flush=True)

def model(selected_features, extended=False, world_lower=None, depth=1, budget=1):
    sense=[]
    for f,cut in selected_features:
        sense.append([2 if v[1][f]>cut else 1 for v in witness])
    assert len(sense)<=8
    return dict(worldCount=2,actionCount=2,probeCount=len(sense),
       good=[[True,False],[False,True]],sense=sense,
       nextFalse=[[0,1] for _ in sense],nextTrue=[[0,1] for _ in sense],
       actionCost=[0,0],probeCost=[1]*len(sense),
       lowerWorld=[0,1] if world_lower is None else world_lower,upperWorld=[0,1],
       mustActions=[0,1],mayActions=[0,1],
       probeKinds=["PROBE"]*len(sense),depth=depth,budget=budget,reserve=3,debt=0)

# C3's bounded finite interface accepts at most 8 probes. For the real pair,
# all NINE existing measurements are exactly identical, so using eight of
# those nine is logically sufficient as a bounded illustrative sub-contract.
panel8=list(enumerate(original_cutoffs))[:8]
added=panel8[:7]+[(f_opt,cut_opt)]
cases={
    "REFUSE_8_ORIGINAL_BINARY_MEASUREMENTS":model(panel8),
    "OPEN_IF_ONE_WORLD_NOT_YET_EXCLUDED":model(panel8,world_lower=[0]),
    "PROBE_WITH_ADDITIONAL_RI_RESOLUTION":model(added),
}
results={}
for name,m in cases.items():
    folder=output/"certified"/name
    verdict=decide(m,folder)
    assert replay(folder),("LEAN_REPLAY_FAILED",name)
    expected=("REFUSE_ROBUST" if name.startswith("REFUSE") else
              "EPISTEMIC_OPEN" if name.startswith("OPEN") else "PROBE")
    assert verdict["verdict"]==expected,(name,verdict)
    if expected=="PROBE":
        # The first seven binary tests are insufficient: C3 independently
        # locates the only useful one (probe index 7).
        assert verdict["plan"]["probe"]==7,verdict["plan"]
    results[name]=dict(verdict=verdict["verdict"],authorized=verdict["authorized"],
        plan=verdict["plan"],contract_sha256=verdict["contract_sha256"],
        lean_sha256=verdict["source_sha256"])
    print("ORIGINAL_C3_LEAN",name,expected,flush=True)

# External mathematical argument beyond C3's bounded depth:
# any transcript from the original nine tests is identical on both specimens.
# Hence ANY adaptive tree using those nine deterministic queries must give
# the same terminal action on both, impossible for different labels.
assert panel_signature(a)==panel_signature(b)
assert a[2]!=b[2]
assert int(a[1][f_opt]>cut_opt)!=int(b[1][f_opt]>cut_opt)
results_report=dict(
 source="UCI Glass Identification, German 1987 (doi:10.24432/C5WW2P)",
 public_mirror=URL,git_blob_sha1=BLOB,sha256=hashlib.sha256(data).hexdigest(),
 record_count=len(records),type_count=dict(classes),
 panel_cutoffs={n:str(v) for n,v in zip(features,original_cutoffs)},
 baseline=base,additional_threshold_candidates_exhausted=candidates,
 optimum_with_one_added_binary_query=best_n,
 optimum_thresholds=[dict(feature=features[f],threshold=str(c),between=[str(l),str(h)]) for f,c,l,h in best],
 independently_recounted=(93,141),
 witness=[dict(record_id=r[0],class_label=r[2],
     RI=str(r[1][0]),original_nine_bit_signature="".join(map(str,panel_signature(r))),
     new_RI_positive=bool(r[1][f_opt]>cut_opt)) for r in witness],
 c3_certified_cases=results,
 scientific_limitations=[
   "Cutoffs are experimental declarations, not certified instrument thresholds",
   "An in-sample optimal probe is selected using all 214 measured specimens and labels",
   "93/141 are only guaranteed on the fixed 214-sample finite roster; no generalization to unseen specimens",
   "All 214 are processed by external transparent exact counting; Lean verifies only the derived two-world C3 decisions",
   "The impossibility of arbitrary-depth sensing with the nine binary queries follows from identical query signatures, independently of bounded Lean check",
   "A refractive-index cutoff does not itself identify glass chemistry or causally reveal glass origin",
   "No claim to forensic admissibility or medical/physical novelty"
 ])
(output/"REPORT.json").write_text(json.dumps(results_report,ensure_ascii=False,indent=2,default=str)+"\n")
print("GLASS_C3_SCIENCE_PILOT_COMPLETE 214_REAL 930_THRESHOLDS 3_LEAN_VERDICTS",flush=True)
