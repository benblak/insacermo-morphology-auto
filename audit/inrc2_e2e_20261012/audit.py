#!/usr/bin/env python3
"""Auditable research slice: pinned INRC-II bytes -> extracted model -> frozen C3 -> Lean.
No claim to solve the full nurse-rostering contest or certify raw parsing with Lean.
"""
import hashlib, itertools, json, re, shutil, sys, urllib.request
from pathlib import Path

SOURCE="7fbaea1c2d518c1b9c153594d8fe8dd91f8b0ab3"
PINS={
"Sc-n005w4.txt":("8b8ae0dc7ff31ba5d7865d5a82d5efac636c833013e88fead05a2eacdba8a121","a2adf45dacc4c78bffc3b9854ecd9cd94cd6c658"),
"WD-n005w4-0.txt":("d63d805cbad867f474204962ecb4f7c62a58b06f684ca2d4e8aa03b979162eba","5d1b00ab260a9203ac2a7ae4b6da29f0f1bb4699"),
"H0-n005w4-0.txt":("e32138bb9ed8075a8b9eb9e7469d97f4116f83142d99b3c10f81229ae30fb98a","b3b9e1e3e2b8e8d409619aebdff222c579fbd432"),
"H0-n005w4-1.txt":("3c4b8d51cf95360dccdbb1bd0270d625d0546cee14419b6de2dff2504b55ad7c","5ec5beb959d2e3fb8cba810b741317933c21df22"),
}
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/"audit"/"inrc2_e2e_20261012"/"evidence"
OUT.mkdir(parents=True,exist_ok=True)
DATA=OUT/"raw"
DATA.mkdir(exist_ok=True)
def sha(b): return hashlib.sha256(b).hexdigest()
def blob(b): return hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()
raw={}
for filename,(sha_expected,blob_expected) in PINS.items():
    url=f"https://raw.githubusercontent.com/lab-core/NurseScheduler/{SOURCE}/datasets/INRC2/n005w4/{filename}"
    with urllib.request.urlopen(url,timeout=35) as r: data=r.read()
    assert (sha(data),blob(data))==(sha_expected,blob_expected),("CORRUPT_SOURCE",filename)
    (DATA/filename).write_bytes(data)
    raw[filename]=data.decode("utf-8")
print("SOURCE_PINNED_SHA256_AND_GIT_BLOB_OK",flush=True)
scenario=raw["Sc-n005w4.txt"]
nurses={}
for line in scenario.split("NURSES = 5",1)[1].strip().splitlines():
    v=line.split()
    assert len(v)>=4 and int(v[2])==len(v[3:])
    nurses[v[0]]=tuple(v[3:])
assert len(nurses)==5
forbidden={}
fsection=scenario.split("FORBIDDEN_SHIFT_TYPES_SUCCESSIONS",1)[1].split("CONTRACTS",1)[0]
for line in fsection.strip().splitlines():
    v=line.split()
    assert len(v)>=2 and int(v[1])==len(v[2:])
    forbidden[v[0]]=set(v[2:])
assert set(forbidden)=={"Early","Late","Night"}
week=raw["WD-n005w4-0.txt"]
slots=[]
for line in week.split("REQUIREMENTS",1)[1].split("SHIFT_OFF_REQUESTS",1)[0].strip().splitlines():
    v=line.split()
    assert len(v)==9
    low,high=map(int,re.fullmatch(r"\((\d+),(\d+)\)",v[2]).groups())
    assert 0<=low<=high
    slots.extend([(v[0],v[1])]*low)
assert len(slots)==4
histories=[]
for idx in (0,1):
    history={}
    for line in raw[f"H0-n005w4-{idx}.txt"].split("NURSE_HISTORY",1)[1].strip().splitlines():
        v=line.split()
        assert len(v)==7
        history[v[0]]=v[3]
    assert set(history)==set(nurses)
    histories.append(history)
names=list(nurses)
def admissible(nurse,slot,hist):
    shift,skill=slot
    return skill in nurses[nurse] and shift not in forbidden.get(hist[nurse],set())
# Extractor: nurse-permutation assignment to each minimum-demand position.
worlds=[]
for h in histories:
    rosters=sorted(set(tuple(p) for p in itertools.permutations(names,len(slots))
        if all(admissible(n,s,h) for n,s in zip(p,slots))))
    worlds.append(rosters)
# Independent verifier: independently assign each nurse OFF or one of four slots.
for w,h in enumerate(histories):
    other=set()
    for selection in itertools.product(range(-1,len(slots)),repeat=len(names)):
        active=[x for x in selection if x>=0]
        if len(active)!=len(slots) or set(active)!=set(range(len(slots))):continue
        if all(admissible(n,slots[s],h) for n,s in zip(names,selection) if s>=0):
            other.add(tuple(next(n for n,s in zip(names,selection) if s==j) for j in range(len(slots))))
    assert other==set(worlds[w]),"INDEPENDENT_ROSTER_MISMATCH"
assert [len(x) for x in worlds]==[2,1]
actions=sorted(set(worlds[0])|set(worlds[1]))
good=[[a in worlds[w] for a in actions] for w in (0,1)]
assert len(actions)==3 and not any(good[0][a] and good[1][a] for a in range(3))
print("EXTRACTOR_AND_INDEPENDENT_ENUMERATOR_AGREE",len(worlds[0]),len(worlds[1]),flush=True)
# Hypothetical perfect query identifying which *published benchmark history* applies.
# This is a constructed epistemic scenario, NOT an actual INRC-II live sensor.
model=dict(worldCount=2,actionCount=len(actions),probeCount=1,good=good,
    sense=[[1,2]],nextFalse=[[0,0]],nextTrue=[[1,1]],
    actionCost=[0]*len(actions),probeCost=[1],
    lowerWorld=[0,1],upperWorld=[0,1],
    mustActions=list(range(len(actions))),mayActions=list(range(len(actions))),
    probeKinds=["PROBE"],depth=1,budget=1,reserve=3,debt=0)
cases={
 "01_PROBE":model,
 "02_ACT_0":dict(model,lowerWorld=[0],upperWorld=[0]),
 "03_ACT_1":dict(model,lowerWorld=[1],upperWorld=[1]),
 "04_REFUSE":dict(model,depth=0,budget=0),
 "05_EPISTEMIC_OPEN":dict(model,lowerWorld=[0],depth=0,budget=0)}
# Distinct one-step enumeration of all admissible action/policy combinations.
def possible(m,worldset,allowed):
    B=min(m["budget"],m["reserve"]-m["debt"]-1)
    direct=lambda ws:any(m["actionCost"][a]<=B and all(m["good"][w][a] for w in ws) for a in allowed)
    if direct(worldset):return True
    if m["depth"]==0 or m["probeCost"][0]>B:return False
    for out in (1,2):
        subset={m["nextFalse" if out==1 else "nextTrue"][0][w]
                for w in worldset if m["sense"][0][w]&out}
        if not direct(subset):return False
    return True
def oracle_verdict(m):
    if possible(m,m["upperWorld"],m["mustActions"]):
        b=min(m["budget"],m["reserve"]-m["debt"]-1)
        direct=any(m["actionCost"][a]<=b and all(m["good"][w][a] for w in m["upperWorld"]) for a in m["mustActions"])
        return "ACT" if direct else "PROBE"
    return "EPISTEMIC_OPEN" if possible(m,m["lowerWorld"],m["mayActions"]) else "REFUSE_ROBUST"
# Original unchanged Python package and Lean modules checked out by the runner.
import insacermo_one_engine as c3
original_bytes=(ROOT/"insacermo_one_engine.py").read_bytes()
assert blob(original_bytes)=="bd5310b3692bcbad4e874005b7dd8eda90616f74","ORIGINAL_ENGINE_CHANGED"
report=dict(source_commit=SOURCE,inputs={name:dict(sha256=sha((DATA/name).read_bytes()),
    git_blob=blob((DATA/name).read_bytes())) for name in PINS},
    original_engine_git_blob=blob(original_bytes),
    scope="Four Monday minimum posts, skills, Sunday-to-Monday forbidden successions, five nurses.",
    uncertain_worlds="Two DISTINCT official histories; mixing them is an experimental design.",
    probe="Constructed perfect history-ID observation; NOT a real hospital sensor.",
    benchmark_complete=False,lean_checks_raw_parser=False,
    slot_requirements=slots,history_last_shifts=histories,
    complete_monday_rosters=[len(x) for x in worlds],
    action_assignments=[list(a) for a in actions],good=good,
    cases={})
for label,m in cases.items():
    dest=OUT/"receipts"/label
    res=c3.decide(m,dest)
    oracle=oracle_verdict(m)
    assert res["verdict"]==oracle,(label,res,oracle)
    assert c3.replay(dest),(label,"Lean replay failed")
    report["cases"][label]=dict(verdict=res["verdict"],authorized=res["authorized"],
        contract_hash=res["contract_sha256"],lean_file_hash=res["source_sha256"],
        receipt_hash=res["receipt_sha256"],plan=res["plan"],lean_replay=True)
    print("VERIFIED",label,oracle,flush=True)
tamper={}
clean=OUT/"receipts"/"01_PROBE"
for fname in ("contract.json","candidate.json","receipt.json","C3Decision.lean"):
    path=OUT/"tamper_checks"/fname.replace(".","_")
    shutil.copytree(clean,path,dirs_exist_ok=True)
    target=path/fname
    target.write_text(target.read_text()+"\n") # content now differs; binding checker must reject
    tamper[fname]=not c3.replay(path)
    assert tamper[fname],("TAMPER ACCEPTED",fname)
bad=c3.decide(model,OUT/"tamper_checks"/"missing_lean",lean_binary="/not-a-real-lean-binary")
tamper["missing_lean"]=(bad["verdict"]=="REFUSE_CERTIFICATE_MISSING" and not bad["authorized"])
assert tamper["missing_lean"]
report["tamper_rejected"]=tamper
try:
    fake=(DATA/"Sc-n005w4.txt").read_bytes().replace(b"SCENARIO",b"SCENARX",1)
    assert (sha(fake),blob(fake))==PINS["Sc-n005w4.txt"]
except AssertionError: report["changed_public_input_rejected"]=True
else: raise AssertionError("INPUT TAMPER MISSED")
(OUT/"REPORT.json").write_text(json.dumps(report,indent=2,ensure_ascii=False,sort_keys=True)+"\n")
print("E2E_PINNED_DATA_TO_C3_TO_LEAN_AND_REPLAY=SUCCESS",flush=True)
