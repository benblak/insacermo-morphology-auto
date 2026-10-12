#!/usr/bin/env python3
"""Retrospective holdout audit: 214 real UCI Glass rows.
No training/test label leakage in cut selection, full label dictionary,
or per-example decision. Baseline nine binary probes are fixed BEFORE split.
One extra query re-reads RI at a finer threshold; this is a logical read cost,
not a new laboratory measurement.
"""
from decimal import Decimal as D
from collections import defaultdict,Counter
from pathlib import Path
import hashlib,random,json,urllib.request,statistics
URL="https://raw.githubusercontent.com/jbrownlee/Datasets/d20fcb6402ae34e653d4513b00f39257bb37ed7f/glass.data"
BLOB="ab21361ce9fa4b168acfd331c4cfad729b9b1b8f"
OUT=Path(__file__).resolve().parent/"evidence";OUT.mkdir(parents=True,exist_ok=True)
data=urllib.request.urlopen(URL,timeout=35).read()
assert hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()==BLOB
(OUT/"glass.data").write_bytes(data)
rows=[]
for ln in data.decode().splitlines():
    p=ln.strip().split(",")
    assert len(p)==11
    rows.append((int(p[0]),tuple(map(D,p[1:10])),int(p[-1])))
assert len(rows)==214
names=["RI","Na","Mg","Al","Si","K","Ca","Ba","Fe"]
cuts=list(map(D,["1.518","13.5","2","1.5","73","0.5","8.5","0.5","0.1"]))
def signature(r):return tuple(int(x>c) for x,c in zip(r[1],cuts))
def sigextra(r,feature,threshold):return signature(r)+(int(r[1][feature]>threshold),)
def maplabels(data, key):
    d=defaultdict(set)
    for r in data:d[key(r)].add(r[2])
    return {k:next(iter(v)) if len(v)==1 else None for k,v in d.items()}
def score(train,test,key):
    lut=maplabels(train,key);c=w=refuse=seen=0
    for r in test:
        s=key(r)
        if s in lut:seen+=1
        y=lut.get(s)
        if y is None:refuse+=1
        elif y==r[2]:c+=1
        else:w+=1
    return dict(correct=c,wrong=w,refuse=refuse,seen=seen,coverage=c+w)
def choose(train):
    base=[signature(r) for r in train]
    best=-1;candidates=[];n=0
    for f in range(9):
        values=sorted({r[1][f] for r in train})
        for a,b in zip(values,values[1:]):
            t=(a+b)/2;n+=1
            groups=defaultdict(set)
            for r,s in zip(train,base):
                groups[s+(int(r[1][f]>t),)].add(r[2])
            counts=Counter(s+(int(r[1][f]>t),) for r,s in zip(train,base))
            pure=sum(counts[k] for k,v in groups.items() if len(v)==1)
            if pure>best:
                best=pure;candidates=[(f,t)]
            elif pure==best:candidates.append((f,t))
    assert candidates
    return candidates[0],best,n,len(candidates)
def split(seed):
    rng=random.Random(seed)
    bylabel=defaultdict(list)
    for r in rows:bylabel[r[2]].append(r)
    train=[];test=[]
    for label in sorted(bylabel):
        sub=sorted(bylabel[label])
        rng.shuffle(sub)
        nt=round(len(sub)*.3)
        test+=sub[:nt];train+=sub[nt:]
    assert not ({r[0] for r in train}&{r[0] for r in test})
    return train,test
seeds=[20261012+i for i in range(20)]
results=[]
for seed in seeds:
    train,test=split(seed)
    b=score(train,test,signature)
    (f,t),trainpure,nc,ntied=choose(train)
    e=score(train,test,lambda r:sigextra(r,f,t))
    # no assumption extra is better out-of-sample: it may be worse!
    extra_on_ambiguous=0
    base_lut=maplabels(train,signature)
    refined_lut=maplabels(train,lambda r:sigextra(r,f,t))
    sel_correct=sel_wrong=sel_refuse=0
    for r in test:
        bval=base_lut.get(signature(r))
        if bval is None:
            extra_on_ambiguous+=1
            final=refined_lut.get(sigextra(r,f,t))
        else:
            final=bval
        if final is None: sel_refuse+=1
        elif final==r[2]:sel_correct+=1
        else:sel_wrong+=1
    selective=dict(correct=sel_correct,wrong=sel_wrong,refuse=sel_refuse,coverage=sel_correct+sel_wrong)
    results.append(dict(seed=seed,train_n=len(train),test_n=len(test),
        cutoff_feature=names[f],cutoff=str(t),train_certifiable=trainpure,
        search_candidates=nc,tied_train_optima=ntied,
        base=b,refined=e,selective=selective,extra_query_only_if_base_refuses=extra_on_ambiguous,
        extra_query_all_test=len(test)))
N=len(results)
def total(which,key):return sum(z[which][key] for z in results)
summary=dict(source=URL,git_blob=BLOB,record_count=214,
  note="Held-out by row (stratified 70/30); because rows/labels were inspected in earlier pilot, this is retrospective and not independent prospective validation.",
  protocol="20 fixed seeds; train-based supervised threshold and signature policy; locked 9 original thresholds; identical holdout for base and additional query.",
  test_cases=sum(z["test_n"] for z in results),
  aggregate={k:dict(correct=total(k,"correct"),wrong=total(k,"wrong"),
         refused=total(k,"refuse"),covered=total(k,"coverage"))
      for k in ("base","refined","selective")},
  selected_features=Counter(z["cutoff_feature"] for z in results),
  additional_question_counts={"always":sum(z["extra_query_all_test"] for z in results),
    "only_if_base_refuses":sum(z["extra_query_only_if_base_refuses"] for z in results)},
  limits=["Not prospectively untouched: previous pilot inspected all labels.",
          "In-sample test-set comparison does not prove zero error on unseen physical specimens.",
          "A single additional binary test on an already measured RI is only a logical information read, not an additional lab measurement.",
          "The refined lookup may abstain or make incorrect decisions on unseen specimens; report both.",
          "No claim that frozen C3 itself optimized the 214-sample threshold; the search is external.",
          "These folds reuse individuals; pooled counts are not 20 independent external studies."],
  folds=results)
assert all(z["train_n"]+z["test_n"]==214 for z in results)
(OUT/"HOLDOUT_REPORT.json").write_text(json.dumps(summary,indent=2,ensure_ascii=False,default=lambda o:dict(o))+"\n")
print("GLASS_HELDOUT_COMPLETED",json.dumps({k:v for k,v in summary.items() if k not in ("folds","limits")},default=lambda o:dict(o)),flush=True)
