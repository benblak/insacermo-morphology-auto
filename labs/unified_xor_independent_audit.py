#!/usr/bin/env python3
"""Independent synthetic oracle truth and polynomial representation audit.
Imports the hidden source ONLY after all learner models are sealed.
It never imports learner's coefficient/transport/candidate functions.
"""
import json,hashlib,random,sys,itertools
from pathlib import Path
from unified_xor_hidden_oracle import evaluate,needle,secrets
N=24;SEED=73913
SOURCES=('source_0','source_1','source_2')
TARGETS=('target_0','target_1','target_2','target_rare','target_cubic','target_rank2')
def parity(x):return x.bit_count()%2
def quadratic(x,r):
    out=r['constant']^parity(x&r['linear'])
    for i,j in r['pairs']:
        if x&(1<<i) and x&(1<<j):out^=1
    return out
def transformed(x,r):
    m=r['candidate']['coordinates']
    a,b,c,d,e=[parity(x&v) for v in m]
    return r['candidate']['output_flip']^a^b^c^d^e^(a&b)^(c&d)
def points(name,count):
    rng=random.Random(SEED+39413+sum((i+1)*ord(v) for i,v in enumerate(name)))
    xs=[];found=set()
    while len(xs)<count:
        x=rng.randrange(1<<N)
        if x not in found and x.bit_count()>2:xs.append(x);found.add(x)
    return xs
def all_low():
    return [0]+[1<<i for i in range(N)]+[(1<<i)|(1<<j) for i,j in itertools.combinations(range(N),2)]
def main(out):
    out=Path(out);raw=(out/'xor_sealed_before_holdout.json').read_bytes()
    sealed=json.loads(raw);result=json.loads((out/'xor_results.json').read_text())
    assert result['seal_sha256']==hashlib.sha256(raw).hexdigest()
    models=sealed['sources']+sealed['targets']
    assert len(models)==9 and [v['name'] for v in models]==list(SOURCES+TARGETS)
    cases=[];query_n=0
    for r in models:
        name=r['name'];tr=r['transcript'];data=tr['rows']
        assert tr['count']==len(data)==len({x for x,y in data}) and tr['count']<3000
        assert tr['sha256']==hashlib.sha256(json.dumps(data,separators=(',',':')).encode()).hexdigest()
        assert all(evaluate(name,x)==y for x,y in data),(name,'FALSE_ORACLE_TRANSCRIPT')
        query_n+=len(data)
        assert r['constant']==evaluate(name,0)
        expected_linear=sum((evaluate(name,1<<i)^r['constant'])<<i for i in range(N))
        assert r['linear']==expected_linear
        expected_pairs=[(i,j) for i,j in itertools.combinations(range(N),2) if 
            evaluate(name,(1<<i)|(1<<j))^evaluate(name,1<<i)^evaluate(name,1<<j)^evaluate(name,0)]
        assert [tuple(q) for q in r['pairs']]==expected_pairs
        candidate=r['candidate']
        if candidate['status']=='QUADRATIC_FIVE_COORDINATE_CANDIDATE':
            m=candidate['coordinates'];assert len(m)==5
            # Independent linear algebra rank of inferred masks.
            pivot=[]
            for mask in m:
                x=mask
                for y in pivot:x=min(x,x^y)
                assert x!=0;pivot.append(x);pivot.sort(reverse=True)
            # The 301 low-degree coefficients determine ANY claimed quadratic.
            for x in all_low():assert quadratic(x,r)==transformed(x,r),(name,x)
            for x in points(name+'_QUADRATIC',512):
                assert quadratic(x,r)==transformed(x,r)
            cases.append(name)
        elif name=='target_cubic':
            assert candidate['status']=='REFUSE_DEGREE_TWO_AFTER_COUNTEREXAMPLE'
            assert r['challenge_errors']>0 and candidate['observed_degree_three_monomials']>0
        elif name=='target_rank2':
            assert candidate['status']=='REFUSE_TRANSFER_REFUSE_WRONG_BILINEAR_RANK'
            assert candidate['rank']==2
        else:raise AssertionError((name,candidate['status']))
        assert r['global_verdict']=='REFUSE_UNCONDITIONAL'
    assert query_n==5309 and len(cases)==7
    for k in result['scores']:
        r=next(r for r in sealed['targets'] if r['name']==k['name'])
        known={x for x,y in r['transcript']['rows']}
        pts=[x for x in points(k['name']+'_HELDOUT',1024) if x not in known]
        while len(pts)<1024:
            x=points(k['name']+'_HELDOUT_EXTRA'+str(len(pts)),1)[0]
            if x not in pts and x not in known:pts.append(x)
        assert k['n']==len(pts)==1024
        assert k['point_hash']==hashlib.sha256(json.dumps(pts,separators=(',',':')).encode()).hexdigest()
        if r['candidate']['status']=='QUADRATIC_FIVE_COORDINATE_CANDIDATE':
            assert k['errors']==sum(transformed(x,r)!=evaluate(k['name'],x) for x in pts)==0
        else:assert k['errors'] is None
    rare=next(x for x in models if x['name']=='target_rare')
    assert needle() not in {x for x,y in rare['transcript']['rows']}
    assert evaluate('target_rare',needle())!=transformed(needle(),rare)
    receipt=dict(result='INDEPENDENT_XOR_UNIFIED_PASS',queries_replayed=query_n,
        accepted_conditional_quadratics=cases,holds_1024_each=True,
        hidden_counterexample=needle(),global_law='REFUSE_UNCONDITIONAL',
        verified_coefficients_per_model=301)
    (out/'xor_independent_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(receipt['result'],len(cases),query_n,flush=True)
    return receipt
if __name__=='__main__':main(sys.argv[1])
