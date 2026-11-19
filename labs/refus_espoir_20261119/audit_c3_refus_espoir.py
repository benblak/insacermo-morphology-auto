"""Independent bounded refusal diagnosis against UNMODIFIED historical C3.
This lab does NOT add a new verdict to INSACERMO; labels are external diagnostics.
"""
from pathlib import Path
from collections import Counter
import hashlib, itertools, json, os

from insacermo_one_engine import decide, replay, solve

OUT=Path(os.environ.get('REFUS_ESPOIR_OUT','/tmp/insacermo-refus-espoir'))
ORIGINAL='bd5310b3692bcbad4e874005b7dd8eda90616f74'
PATTERNS={'s':'0011','t':'0101'}

def original_sha():
    raw=Path('insacermo_one_engine.py').read_bytes()
    return hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()

def model(goods,probes=(),budget=0,lower=None,repair=False):
    W=len(goods); A=max(1,max(goods,default=0).bit_length())
    if repair:
        assert goods==[1,0] and W==2
        probes=('r',)
    if not probes: probes=('d',)  # C3 historically requires at least one probe; dummy costs 1, budget 0
    senses=[]; nf=[]; nt=[]; kinds=[]
    for q in probes:
        if q=='r':
            senses.append([3,3]);nf.append([0,0]);nt.append([0,0]);kinds.append('REPAIR')
        else:
            bits=('0'*W if q=='d' else PATTERNS[q])
            senses.append([1 if x=='0' else 2 for x in bits])
            nf.append(list(range(W)));nt.append(list(range(W)));kinds.append('PROBE')
    return dict(worldCount=W,actionCount=A,probeCount=len(probes),
        good=[[bool(mask&(1<<a)) for a in range(A)] for mask in goods],
        sense=senses,nextFalse=nf,nextTrue=nt,
        actionCost=[0]*A,probeCost=[1]*len(probes),
        lowerWorld=list(range(W)) if lower is None else lower,
        upperWorld=list(range(W)),
        mustActions=list(range(A)),mayActions=list(range(A)),
        probeKinds=kinds,depth=min(len(probes),4),budget=budget,reserve=10,debt=0)

def oracle_possible(goods,patterns):
    """Stand-alone proof-search: enumerate observation fibres and intersect allowed actions."""
    fibres={}
    for w,mask in enumerate(goods):
        sig=tuple(q[w] for q in patterns)
        fibres.setdefault(sig,[]).append(mask)
    for masks in fibres.values():
        intersection=masks[0]
        for m in masks[1:]:intersection &= m
        if not intersection:return False
    return True

def label(goods,probes,budget):
    if 0 in goods:return 'REFUSE_STRUCTUREL'
    if oracle_possible(goods,[]):return 'ACT'
    observed=[PATTERNS[q] for q in probes]
    if not oracle_possible(goods,observed):return 'REFUSE_OBSERVATIONNEL'
    for n in range(min(budget,len(observed))+1):
        for ids in itertools.combinations(range(len(observed)),n):
            if oracle_possible(goods,[observed[i] for i in ids]):
                return 'PROBE'
    return 'REFUSE_BUDGET'

def exhaustive():
    settings=[((),0),(('s',),2),(('s','t'),1),(('s','t'),2)]
    targets=[
        {'ACT':721,'REFUSE_OBSERVATIONNEL':1680,'REFUSE_STRUCTUREL':1695},
        {'ACT':721,'PROBE':648,'REFUSE_OBSERVATIONNEL':1032,'REFUSE_STRUCTUREL':1695},
        {'ACT':721,'PROBE':1080,'REFUSE_BUDGET':600,'REFUSE_STRUCTUREL':1695},
        {'ACT':721,'PROBE':1680,'REFUSE_STRUCTUREL':1695}]
    stats=[Counter() for _ in settings]
    for n in range(4096):
        goods=[(n>>(3*w))&7 for w in range(4)]
        for i,(probes,budget) in enumerate(settings):
            verdict=label(goods,probes,budget)
            m=model(goods,probes,budget)
            plan=solve(m,m['upperWorld'],m['mustActions'],m['depth'],budget)
            assert (plan is not None)==(verdict in ('ACT','PROBE')),(goods,probes,budget,verdict,plan)
            if plan is not None:
                assert ('act' in plan)==(verdict=='ACT')
            stats[i][verdict]+=1
    assert [dict(s) for s in stats]==targets,(stats,targets)
    return [dict(s) for s in stats]

def c3_lean_receipts():
    fixtures=[
      ('ACT',model([1,1,1,1]),'ACT'),
      ('REFUSE_INFORMATION',model([1,2,1,2],('s',),2),'REFUSE_ROBUST'),
      ('PROBE_NEW_SENSOR',model([1,2,1,2],('s','t'),2),'PROBE'),
      ('REFUSE_BUDGET',model([1,2,4,1],('s','t'),1),'REFUSE_ROBUST'),
      ('PROBE_BUDGET_EXTENDED',model([1,2,4,1],('s','t'),2),'PROBE'),
      ('REFUSE_CAPABILITY',model([1,0,1,2],('s','t'),2),'REFUSE_ROBUST'),
      ('REPAIR_CAPABILITY',model([1,0],budget=1,repair=True),'REPAIR'),
      ('EPISTEMIC_OPEN',model([1,2],lower=[0]),'EPISTEMIC_OPEN')]
    data=[]
    for name,m,expected in fixtures:
        folder=OUT/name
        r=decide(m,folder)
        assert r['verdict']==expected,(name,r)
        assert r['authorized']==(expected in ('ACT','PROBE','REPAIR')),(name,r)
        assert replay(folder),name
        data.append({'name':name,'verdict':expected,
            'contract_sha256':r['contract_sha256'],'lean_source_sha256':r['source_sha256'],
            'replay':True})
    receipt=OUT/'ACT'/'receipt.json'
    raw=receipt.read_bytes()
    tampered=json.loads(raw)
    tampered['authorized']=False
    receipt.write_text(json.dumps(tampered))
    assert not replay(OUT/'ACT'),'A falsified receipt was accepted'
    receipt.write_bytes(raw)
    assert replay(OUT/'ACT')
    missing=decide(model([1,1,1,1]),OUT/'WITHOUT_LEAN',
                   lean_binary='/nonexistent/lean')
    assert missing['verdict']=='REFUSE_CERTIFICATE_MISSING' and missing['authorized'] is False
    data.append({'name':'MISSING_LEAN_FAIL_CLOSED','verdict':missing['verdict']})
    return data

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    sha=original_sha()
    assert sha==ORIGINAL,sha
    counts=exhaustive()
    certified=c3_lean_receipts()
    result={'original_c3_blob':sha,'classifications':16384,
        'differences_with_original_c3':0,'counts':counts,
        'lean_gated_cases':certified,
        'scope':'Finite deterministic static senses; historical C3 unchanged'}
    (OUT/'RESULTATS.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
    print('AUDIT_C3_REFUS_ESPOIR_SUCCESS')

if __name__=='__main__':main()
