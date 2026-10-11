#!/usr/bin/env python3
"""Predeclared UCI 357 split evaluation: catalog abstention vs majority, single-sensor lookup.
Only datatraining is used to construct features, thresholds, decision rules.
No retuning after tests. Exact categorical entailment is IN-SAMPLE ONLY.
"""
from __future__ import annotations
import csv,io,json,hashlib,zipfile,collections
from pathlib import Path
import numpy as np

FEATURES=['Temperature','Humidity','Light','CO2','HumidityRatio']
STEP={'Temperature':2.0,'Humidity':10.0,'Light':100.0,'CO2':250.0,'HumidityRatio':0.002}
COST={'Temperature':1,'Humidity':1,'Light':2,'CO2':3,'HumidityRatio':1}
def getcsv(raw):
    lines=csv.reader(io.StringIO(raw.decode('utf-8-sig')))
    names=next(lines)
    names=[n.strip().strip('"').strip("'") for n in names]
    out=[]
    for values in lines:
        if not values: continue
        # UCI's date-index CSV format has an unlabeled row ID column.
        if len(values)==len(names)+1:values=values[1:]
        assert len(values)==len(names),(len(values),len(names))
        r=dict(zip(names,values))
        if not r.get('Occupancy'):continue
        out.append(([float(r[k]) for k in FEATURES],int(r['Occupancy'])))
    return out

def unpack(path):
    z=zipfile.ZipFile(path)
    files={}
    def walk(z):
        for name in z.namelist():
            if name.endswith('/'):continue
            data=z.read(name)
            if name.lower().endswith('.zip'):walk(zipfile.ZipFile(io.BytesIO(data)))
            elif name.lower().endswith(('.txt','.csv')):
                key=Path(name).name.lower()
                if key in ('datatraining.txt','datatest.txt','datatest2.txt'):
                    files[key]=data
    walk(z)
    assert set(files)=={'datatraining.txt','datatest.txt','datatest2.txt'},list(files)
    return files

def signature(row,features):
    return tuple(int(np.floor(row[0][FEATURES.index(k)]/STEP[k])) for k in features)

def train_catalog(train,features):
    counts=collections.defaultdict(lambda:[0,0])
    for r in train:counts[signature(r,features)][r[1]]+=1
    return counts

def predict(cat,row,features):
    z=cat.get(signature(row,features))
    if z is None or min(z)>0:return None
    return 1 if z[1] else 0

def evaluate(test,decide):
    correct=errors=refused=0
    for r in test:
        pred=decide(r)
        if pred is None:refused+=1
        elif pred==r[1]:correct+=1
        else:errors+=1
    n=len(test)
    return {'total':n,'correct':correct,'errors':errors,'refuse':refused,
        'coverage':round((correct+errors)/n,6),
        'selective_accuracy':round(correct/(correct+errors),6) if correct+errors else None,
        'whole_sample_accuracy':round(correct/n,6)}

def run(data):
    train=getcsv(data['datatraining.txt'])
    tests={x:getcsv(data[x]) for x in ('datatest.txt','datatest2.txt')}
    majority=collections.Counter(r[1] for r in train).most_common(1)[0][0]
    # FROZEN: probe order is declared, not chosen based on heldouts.
    order=['Light','CO2','Temperature','Humidity','HumidityRatio']
    catalogs={tuple(order[:d]):train_catalog(train,order[:d]) for d in range(1,6)}
    finalcat=catalogs[tuple(order)]
    # Dynamic stop at first prefix whose label is uniquely entailed by TRAIN reference catalog.
    def adaptive(r):
        for depth in range(1,6):
            p=predict(catalogs[tuple(order[:depth])],r,order[:depth])
            if p is not None:return p,depth
        return None,5
    res={'source':'UCI 357 Occupancy Detection','protocol':'locked thresholds, locked probe order, no test fit',
        'data_sha256':{x:hashlib.sha256(data[x]).hexdigest() for x in data},
        'train_count':len(train),'class_counts':dict(collections.Counter(r[1] for r in train)),
        'sensor_steps':STEP,'sensor_cost':COST,'probe_order':order,'test':{}}
    for k,te in tests.items():
        cur={'majority':evaluate(te,lambda r:majority)}
        cur['fixed_single']={}
        for feature in FEATURES:
            cat=train_catalog(train,[feature])
            cur['fixed_single'][feature]=evaluate(te,lambda r,f=feature,c=cat:predict(c,r,[f]))
        cur['fixed_all']=evaluate(te,lambda r:predict(finalcat,r,order))
        cur['adaptive']=evaluate(te,lambda r:adaptive(r)[0])
        stats=collections.Counter()
        for r in te:
            p,d=adaptive(r)
            stats['total_cost']+=sum(COST[x] for x in order[:d])
            stats['sensors_used']+=d
            if p is not None:stats['acts']+=1
        cur['adaptive']['average_sensor_cost']=round(stats['total_cost']/len(te),4)
        cur['adaptive']['average_sensors_used']=round(stats['sensors_used']/len(te),4)
        cur['fixed_all']['average_sensor_cost']=sum(COST.values())
        res['test'][k]=cur
    # Independent test labels never influence catalog or stop criterion.
    assert sum(len(x) for x in tests.values())>10000
    return res

def main():
    import sys
    data=unpack(Path(sys.argv[1]))
    out=run(data)
    Path(sys.argv[2]).write_text(json.dumps(out,indent=2,ensure_ascii=False))
    for key,value in out['test'].items():
        print(key, 'majority',value['majority'],'adaptive',value['adaptive'])
if __name__=='__main__':main()
