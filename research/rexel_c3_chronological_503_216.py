"""Chronological 503/216 Rexel transfer. Uses ORIGINAL frozen C3 solve/validate.

The CSV is user-supplied and not independently authenticated against exchange.
All 216 later rows are excluded from the model-building stage. Full native C3
search is run on 119 in-scope calibration cells (40 conflicts compressed to
exact negative twin witnesses, preserving impossibility but NOT the full set).
The trained plans are then *transported* to 216 unseen rows to expose
out-of-model risks; these are NOT newly Lean-certified decisions.
"""
from collections import defaultdict,Counter
from pathlib import Path
import csv,hashlib,json
from insacermo_one_engine import validate,solve

SOURCE=Path("research/rexel_719_source_20261029.csv")
EXPECTED="6b2c51bc0e28478e1d4d3c323b1e702bde2676f38c1a4dc37afddd5643334212"
TRAIN_N=503
OUT=Path("/tmp/rexel_chrono_native_c3")
def pstring(r):return ''.join(r[f'p{i}'] for i in range(1,5))
def label(r):return int(r["label_hausse_nette_1pct"])
def model(rows):
    n=len(rows); assert 1<=n<=8
    return dict(worldCount=n,actionCount=2,probeCount=4,
        good=[[label(r)==a for a in range(2)] for r in rows],
        sense=[[1+int(r[f'p{q}']) for r in rows] for q in range(1,5)],
        nextFalse=[list(range(n)) for _ in range(4)],
        nextTrue=[list(range(n)) for _ in range(4)],
        actionCost=[0,0],probeCost=[1,1,1,1],
        lowerWorld=list(range(n)),upperWorld=list(range(n)),
        mustActions=[0,1],mayActions=[0,1],probeKinds=["PROBE"]*4,
        depth=4,budget=4,reserve=6,debt=0)
def predict(tree,row):
    depth=0;t=tree
    while 'act' not in t:
        t=t['yes'] if row[f'p{t["probe"]+1}']=='1' else t['no']
        depth+=1;assert depth<=4
    return t['act'],depth
def main():
    b=SOURCE.read_bytes();assert hashlib.sha256(b).hexdigest()==EXPECTED
    rows=list(csv.DictReader(b.decode().splitlines()))
    assert len(rows)==719
    train,test=rows[:TRAIN_N],rows[TRAIN_N:]
    assert (train[-1]['date'],test[0]['date'])==('2025-12-18','2025-12-19')
    groups=defaultdict(list)
    for x in train:groups[x['signature8']].append(x)
    assert len(groups)==119
    states={}
    cell_count=Counter()
    records=[]
    for sig,group in sorted(groups.items()):
        labs={label(x) for x in group}
        twin=next(((x,y) for x in group for y in group if label(x)!=label(y) and pstring(x)==pstring(y)),None)
        expected='ACT' if len(labs)==1 else 'REFUSE_ROBUST' if twin else 'PROBE'
        # A two-world indistinguishable witness is an exact negative
        # certificate for its entire training cell, no arbitrary partition.
        selected=list(twin) if twin else group
        assert len(selected)<=8,(sig,len(selected))
        c=model(selected);validate(c)
        must=solve(c,c['upperWorld'],c['mustActions'],c['depth'],4)
        may=solve(c,c['lowerWorld'],c['mayActions'],c['depth'],4)
        observed=('ACT' if 'act' in must else 'PROBE') if must else ('REFUSE_ROBUST' if may is None else 'EPISTEMIC_OPEN')
        assert observed==expected,(sig,observed,expected)
        states[sig]=(observed,must,group)
        cell_count[observed]+=1
    day_count=Counter();first_bad={};out_rows=[]
    for r in test:
        sig=r["signature8"];source='UNSEEN_8BIT';pred='';depth='';correct='';train_n=0
        if sig not in states:day_count["out_of_scope"]+=1
        else:
            observed,plan,group=states[sig]
            source=observed;train_n=len(group)
            if observed=='REFUSE_ROBUST':day_count["refused"]+=1
            else:
                pred,depth=predict(plan,r)
                correct=int(pred==label(r))
                day_count["acted"]+=1
                day_count["correct"]+=correct
                day_count["errors"]+=1-correct
                day_count[observed+"_count"]+=1
                day_count[observed+"_error"]+=1-correct
                if not correct and observed not in first_bad:
                    first_bad[observed]=dict(date=r["date"],sig8=sig,pstring=pstring(r),
                        train_worlds=len(group),predicted=pred,actual=label(r),depth=depth)
        out_rows.append(dict(date=r["date"],sig8=sig,
            c3_train_verdict=source,predicted=pred,real_label=label(r),
            correct=correct,depth=depth,train_worlds=train_n))
    assert day_count['acted']+day_count['refused']+day_count['out_of_scope']==216,day_count
    report={'scope':'Real ORIGINAL C3 solve and validate unchanged; chronological OOS transport only; NO Lean certificate for the 119 models in this run',
        'source_sha256':EXPECTED,'train_rows':503,'test_rows':216,
        'train_end':train[-1]['date'],'test_start':test[0]['date'],
        'training_cells':dict(cell_count),'holdout':dict(day_count),
        'first_failed_transfer':first_bad}
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'report.json').write_text(json.dumps(report,sort_keys=True,indent=2))
    with (OUT/'per_day_216.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=out_rows[0].keys());w.writeheader();w.writerows(out_rows)
    print("NATIVE_C3_CHRONOLOGICAL_HOLDOUT_COMPLETE",json.dumps(report,sort_keys=True))
if __name__=='__main__':main()
