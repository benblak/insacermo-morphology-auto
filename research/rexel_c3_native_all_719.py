"""719-row Rexel -> 130 bounded instances, ORIGINAL C3 search, no source changes.

Makes no claim of 130 Lean certificates; only two witness-pair Lean receipts in
the separate workflow. Bridge theorem (12-bit twin => refusal for entire
cell) is separately checked against the WHOLE CSV, not asserted for a sample.
"""
from collections import defaultdict,Counter
from pathlib import Path
import csv,hashlib,json
from insacermo_one_engine import validate,solve

DATA=Path("research/rexel_719_source_20261029.csv")
EXPECTED_SHA="6b2c51bc0e28478e1d4d3c323b1e702bde2676f38c1a4dc37afddd5643334212"

def bits(z,prefix,num):
    return ''.join(z[f'{prefix}{k}'] for k in range(1,num+1))
def model(rows):
    n=len(rows)
    assert 1<=n<=8
    return dict(worldCount=n,actionCount=2,probeCount=4,
        good=[[z["label_hausse_nette_1pct"]==str(a) for a in range(2)] for z in rows],
        sense=[[1+int(z[f'p{q}']) for z in rows] for q in range(1,5)],
        nextFalse=[list(range(n)) for _ in range(4)],
        nextTrue=[list(range(n)) for _ in range(4)],
        actionCost=[0,0],probeCost=[1]*4,
        lowerWorld=list(range(n)),upperWorld=list(range(n)),
        mustActions=[0,1],mayActions=[0,1],probeKinds=["PROBE"]*4,
        depth=4,budget=4,reserve=6,debt=0)
def main():
    b=DATA.read_bytes()
    assert hashlib.sha256(b).hexdigest()==EXPECTED_SHA
    rows=list(csv.DictReader(b.decode().splitlines()))
    assert len(rows)==719 and len({z['date'] for z in rows})==719
    groups=defaultdict(list)
    for z in rows:
        assert z['signature8']==bits(z,"m",8)
        groups[z['signature8']].append(z)
    assert len(groups)==129
    out=[];count=Counter();matched_days=0
    for sig,group in sorted(groups.items()):
        labels={z['label_hausse_nette_1pct'] for z in group}
        predicted=group[0]['verdict_plan_complet']
        assert len(set(z['verdict_plan_complet'] for z in group))==1
        if len(labels)==1:
            assert predicted in ('ACT_NON','ACT_HAUSSE')
            sections=[group[i:i+8] for i in range(0,len(group),8)]
            assert len(group)<=9
        else:
            pair=None
            for i,a in enumerate(group):
                for q in group[i+1:]:
                    if bits(a,'p',4)==bits(q,'p',4) and a['label_hausse_nette_1pct']!=q['label_hausse_nette_1pct']:
                        pair=[a,q];break
                if pair:break
            if pair:
                assert predicted=='REFUSE_ABS'
                sections=[pair]
            else:
                assert predicted=='CERTIFIE_PAR_PLAN'
                assert len(group)<=8
                sections=[group]
        for j,s in enumerate(sections):
            m=model(s);validate(m)
            effective=min(m['budget'],m['reserve']-m['debt']-1)
            must=solve(m,m['upperWorld'],m['mustActions'],m['depth'],effective)
            may=solve(m,m['lowerWorld'],m['mayActions'],m['depth'],effective)
            verdict=('ACT' if 'act' in must else 'PROBE') if must is not None else ('REFUSE_ROBUST' if may is None else 'EPISTEMIC_OPEN')
            expected=('ACT' if len(labels)==1 else 'REFUSE_ROBUST' if pair else 'PROBE')
            assert verdict==expected,(sig,verdict,expected,m)
            count[verdict]+=1
            out.append(dict(sig8=sig,part=j,n_worlds=len(s),verdict=verdict,expected=expected,
                dates=[z['date'] for z in s],first_probe=must.get('probe') if must and 'probe' in must else None))
        matched_days+=len(group)
    assert len(out)==130 and matched_days==719
    assert count=={'ACT':54,'PROBE':19,'REFUSE_ROBUST':57},count
    path=Path("/tmp/insacermo_rexel_native_all")
    path.mkdir(exist_ok=True,parents=True)
    report={'source_sha256':EXPECTED_SHA,'dataset_rows':719,'cells':129,'instances':len(out),
            'native_search_verdicts':dict(count),
            'note':'ORIGINAL solve and validate reused unchanged; NOT 130 Lean-certified receipts',
            'instances_detail':out}
    (path/'report.json').write_text(json.dumps(report,ensure_ascii=False,sort_keys=True,indent=2))
    print("NATIVE_C3_SEARCH_130_OF_130_MATCH_CSV")
    print(json.dumps({k:v for k,v in report.items() if k!='instances_detail'},sort_keys=True))
if __name__=="__main__":main()
