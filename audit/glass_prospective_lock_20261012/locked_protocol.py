#!/usr/bin/env python3
"""Frozen retrospective glass information policy + strict external validation.
No change to original INSACERMO MAX/C3 and no prospective performance claim.
"""
import argparse,csv,hashlib,io,json,urllib.request
from collections import defaultdict,Counter
from decimal import Decimal as D
from pathlib import Path

FIELDS=('RI','Na','Mg','Al','Si','K','Ca','Ba','Fe')
CUTS=tuple(map(D,('1.518','13.5','2','1.5','73','0.5','8.5','0.5','0.1')))
ADDED_RI=D('1.51715')
UCI_REF='d20fcb6402ae34e653d4513b00f39257bb37ed7f'
UCI_BLOB='ab21361ce9fa4b168acfd331c4cfad729b9b1b8f'
MIRROR_REF='50286efc215d8df9ca67679c3672b155636f7b94'
MIRROR_BLOB='ea2849b57e8ec45ea2cc9bb3f09338de80f3a59a'
UCI=f'https://raw.githubusercontent.com/jbrownlee/Datasets/{UCI_REF}/glass.data'
MIRROR=f'https://raw.githubusercontent.com/p-sama/Glass-Classification/{MIRROR_REF}/glass.csv'
LABELS={1,2,3,5,6,7}

def blob(x):return hashlib.sha1(b'blob '+str(len(x)).encode()+b'\x00'+x).hexdigest()
def load(url,gitsha):
    with urllib.request.urlopen(url,timeout=35) as r:b=r.read()
    assert blob(b)==gitsha,(url,blob(b))
    return b
def num(x):
    d=D(str(x).strip())
    if not d.is_finite():raise ValueError('Non-finite numerical observation')
    return d
def parse_uci(b):
    out=[]
    for l in b.decode().splitlines():
        v=l.split(',')
        assert len(v)==11
        out.append((tuple(map(num,v[1:10])),int(v[10])))
    assert len(out)==214
    assert {y for _,y in out}==LABELS
    return out
def parse_external(b):
    reader=csv.DictReader(io.StringIO(b.decode('utf-8-sig')))
    if tuple(reader.fieldnames or ())!=FIELDS+('Type',):
        raise ValueError('Expected columns: '+','.join(FIELDS+('Type',)))
    out=[]
    for v in reader:
        x=tuple(num(v[f]) for f in FIELDS)
        y=int(v['Type'])
        if y not in LABELS:raise ValueError('Unknown class (outside declared contract)')
        out.append((x,y))
    if not out:raise ValueError('Empty external cohort')
    return out
def s9(x):return tuple(int(v>c) for v,c in zip(x,CUTS))
def s10(x):return s9(x)+(int(x[0]>ADDED_RI),)
def dictionaries(train):
    maps=[]
    for fn in (s9,s10):
        labels=defaultdict(set)
        for x,y in train:labels[fn(x)].add(y)
        maps.append({k:next(iter(v)) if len(v)==1 else None for k,v in labels.items()})
    return maps
def score(train,external):
    # A second GitHub link to UCI is NOT an independent test.
    old={x for x,y in train}
    overlap=sum(x in old for x,y in external)
    if overlap:
        return dict(status='REJECT_NONINDEPENDENT',overlap=overlap,count=len(external),
          reason='Complete nine-variable profile overlaps archived UCI reference')
    out={}
    for title,fn,m in zip(('9_bit','10_bit'),(s9,s10),dictionaries(train)):
        c=Counter()
        for x,y in external:
            prediction=m.get(fn(x))
            c['refuse' if prediction is None else ('correct' if prediction==y else 'wrong')]+=1
        out[title]={k:c[k] for k in ('correct','wrong','refuse')}
    return dict(status='EMPIRICAL_EVALUATION_ONLY',n=len(external),results=out,
      certified_ACT=0,epistemic='New glass world validity not certified by in-sample class uniqueness')

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--external-csv',type=Path)
    p.add_argument('--external-source',type=str)
    p.add_argument('--output',type=Path,default=Path('prospective_lock_report.json'))
    a=p.parse_args()
    reference=load(UCI,UCI_BLOB)
    train=parse_uci(reference)
    maps=dictionaries(train)
    assert [sum(m[fn(x)] is not None for x,y in train) for fn,m in zip((s9,s10),maps)]==[93,141]
    if a.external_csv is None:
        # Public external-looking data are the very same cohort: mandatory reject.
        mirror=load(MIRROR,MIRROR_BLOB)
        duplicate=score(train,parse_external(mirror))
        assert duplicate['status']=='REJECT_NONINDEPENDENT' and duplicate['overlap']==214,duplicate
        x,y=next((x,y) for x,y in train if maps[1].get(s10(x))==y)
        y_fake=next(z for z in sorted(LABELS) if z!=y)
        assert maps[1][s10(x)]!=y_fake
        assert score(train,[(x,y_fake)])['status']=='REJECT_NONINDEPENDENT'
        result=dict(status='PROTOCOL_FROZEN_AWAITING_INDEPENDENT_NEW_MEASUREMENTS',
          training_samples=214,pure_9=93,pure_10=141,
          tenth_logical_question='RI > 1.51715',
          original_data_source_git_blob=UCI_BLOB,
          independent_external_samples=0,external_accuracy=None,
          cloned_external_mirror_rejected=214,
          synthetic_wrong_label_profile_rejected=True,
          note='This fixed exact lookup is not a machine-learning neural model, but its threshold was selected using labels; no outside-world certification follows.')
        status=0
    else:
        if not a.external_source or not a.external_source.strip():
            p.error('--external-source required for provenance declaration')
        b=a.external_csv.read_bytes()
        result=score(train,parse_external(b))
        result.update(external_source=a.external_source,external_csv_sha256=hashlib.sha256(b).hexdigest())
        status=0 if result['status']=='EMPIRICAL_EVALUATION_ONLY' else 2
    a.output.write_text(json.dumps(result,sort_keys=True,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(result,sort_keys=True,ensure_ascii=False))
    raise SystemExit(status)

if __name__=='__main__':main()
