#!/usr/bin/env python3
"""XOR scientific-model learner integrated into the original C3/Lean runner.
Adapted from prior standalone SOURCE (does not know private oracle masks).
Synthetic black-box device only, 24-bit GF(2) quadratic structure conditional.
"""
from __future__ import annotations
import subprocess,sys,json,random,itertools,hashlib
from pathlib import Path
HERE=Path(__file__).parent
N=24;SEED=73913
SOURCES=('source_0','source_1','source_2')
TARGETS=('target_0','target_1','target_2','target_rare','target_cubic','target_rank2')
class Device:
    def __init__(self,name):
        self.name=name;self.answers={};self.order=[]
        self.p=subprocess.Popen([sys.executable,str(HERE/'unified_xor_hidden_oracle.py'),'--case',name],
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,bufsize=1)
    def ask(self,x):
        assert type(x)==int and 0<=x<1<<N
        if x not in self.answers:
            assert len(self.order)<3000
            self.p.stdin.write(json.dumps({'x':x})+'\n');self.p.stdin.flush()
            reply=json.loads(self.p.stdout.readline())
            assert reply=={'x':x,'y':reply['y']} and reply['y'] in (0,1)
            self.answers[x]=reply['y'];self.order.append(x)
        return self.answers[x]
    def done(self):
        self.p.stdin.close();assert self.p.wait(timeout=20)==0
    def transcript(self):
        data=[[x,self.answers[x]] for x in self.order]
        return dict(rows=data,count=len(data),
            sha256=hashlib.sha256(json.dumps(data,separators=(',',':')).encode()).hexdigest())
def bitparity(x):return x.bit_count()&1
def polynomial(x,constant,linear,edges):
    result=constant^bitparity(x&linear)
    for i,j in edges:result^=((x>>i)&1)&((x>>j)&1)
    return result
def ansatz(d):
    c=d.ask(0);l=0;edges=[]
    for i in range(N):l|=(d.ask(1<<i)^c)<<i
    for i,j in itertools.combinations(range(N),2):
        x=(1<<i)|(1<<j)
        if d.ask(x)^c^((l>>i)&1)^((l>>j)&1):edges.append((i,j))
    return c,l,edges
def matrix(edges):
    m=[0]*N
    for i,j in edges:m[i]^=1<<j;m[j]^=1<<i
    return m
def B(u,v,m):
    z=0
    while u:
        low=u&-u;idx=low.bit_length()-1;z^=m[idx];u^=low
    return bitparity(z&v)
def symplectic(m):
    leftover=[1<<i for i in range(N)];pairs=[]
    while True:
        which=None
        for i in range(len(leftover)):
            for j in range(i+1,len(leftover)):
                if B(leftover[i],leftover[j],m):
                    which=(i,j);break
            if which is not None:break
        if which is None:break
        i,j=which;u,v=leftover[i],leftover[j]
        rest=[]
        for k,w in enumerate(leftover):
            if k in (i,j):continue
            rest.append(w^(u if B(w,v,m) else 0)^(v if B(w,u,m) else 0))
        pairs.append((u,v));leftover=rest
    return pairs
def independent(coords):
    b={}
    for mask in coords:
        x=mask
        while x:
            pivot=x.bit_length()-1
            if pivot not in b:b[pivot]=x;break
            x^=b[pivot]
        else:return False
    return True
def canonical(x,masks,flip):
    a,b,c,d,e=[bitparity(x&v) for v in masks]
    return flip^a^b^c^d^e^(a&b)^(c&d)
def transport(c,l,edges):
    m=matrix(edges);pairs=symplectic(m)
    if len(pairs)!=2:return dict(status='REFUSE_WRONG_BILINEAR_RANK',rank=2*len(pairs))
    core=[]
    for u,v in pairs:
        mask1=sum((B(1<<i,v,m)<<i) for i in range(N))
        mask2=sum((B(1<<i,u,m)<<i) for i in range(N))
        core.extend((mask1,mask2))
    def pairpart(x):
        a,b,c,d=[bitparity(x&m) for m in core]
        return (a&b)^(c&d)
    correction=sum((polynomial(1<<i,0,l,edges)^pairpart(1<<i))<<i for i in range(N))
    extra=correction^core[0]^core[1]^core[2]^core[3]
    coords=core+[extra]
    if not independent(coords):
        return dict(status='REFUSE_COORDINATES_NOT_INDEPENDENT',rank=4)
    # Check every coefficient by exact model evaluations at 0, singleton and pair inputs.
    for x in [0]+[1<<i for i in range(N)]+[(1<<i)|(1<<j) for i,j in itertools.combinations(range(N),2)]:
        assert canonical(x,coords,c)==polynomial(x,c,l,edges),'ANF_COEFFICIENT_MISMATCH'
    return dict(status='QUADRATIC_FIVE_COORDINATE_CANDIDATE',rank=4,coordinates=coords,output_flip=c)
def samples(name,n):
    rng=random.Random(SEED+39413+sum((i+1)*ord(v) for i,v in enumerate(name)))
    points=[];seen=set()
    while len(points)<n:
        x=rng.randrange(1<<N)
        if x not in seen and x.bit_count()>2:points.append(x);seen.add(x)
    return points
def discover(name):
    dev=Device(name)
    try:
        c,l,pairs=ansatz(dev);candidate=transport(c,l,pairs)
        challenges=samples(name,64)
        mismatch=[x for x in challenges if dev.ask(x)!=polynomial(x,c,l,pairs)]
        if mismatch:
            cubes=[]
            for i,j,k in itertools.combinations(range(N),3):
                x=(1<<i)|(1<<j)|(1<<k)
                if dev.ask(x)!=polynomial(x,c,l,pairs):cubes.append((i,j,k))
            candidate=dict(status='REFUSE_DEGREE_TWO_AFTER_COUNTEREXAMPLE',
                observed_degree_three_monomials=len(cubes))
        elif candidate['status']!='QUADRATIC_FIVE_COORDINATE_CANDIDATE':
            candidate['status']='REFUSE_TRANSFER_'+candidate['status']
        return dict(name=name,constant=c,linear=l,pairs=pairs,
           candidate=candidate,challenge_errors=len(mismatch),
           transcript=dev.transcript(),global_verdict='REFUSE_UNCONDITIONAL')
    finally:dev.done()
def main(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    originals=[discover(name) for name in SOURCES+TARGETS]
    sealed=dict(
       sources=originals[:3],targets=originals[3:],
       seed=SEED,domain=1<<24,
       scope='GENERIC QUADRATIC GF2 MODELS; UNKNOWN ORACLE MAY HAVE RARE EXCEPTIONS',
       global_verdict='REFUSE_UNCONDITIONAL')
    seal_file=out/'xor_sealed_before_holdout.json'
    seal_file.write_text(json.dumps(sealed,indent=2)+'\n')
    seal_sha=hashlib.sha256(seal_file.read_bytes()).hexdigest()
    scores=[]
    for item in originals[3:]:
        name=item['name'];device=Device(name)
        try:
            known=set(x for x,y in item['transcript']['rows'])
            pts=[x for x in samples(name+'_HELDOUT',1024) if x not in known]
            while len(pts)<1024:
                x=samples(name+'_HELDOUT_EXTRA'+str(len(pts)),1)[0]
                if x not in pts and x not in known:pts.append(x)
            values=[device.ask(x) for x in pts]
            candidate=item['candidate']
            errors=None if candidate['status']!='QUADRATIC_FIVE_COORDINATE_CANDIDATE' else sum(
                canonical(x,candidate['coordinates'],candidate['output_flip'])!=y for x,y in zip(pts,values))
            scores.append(dict(name=name,n=len(pts),errors=errors,
                point_hash=hashlib.sha256(json.dumps(pts,separators=(',',':')).encode()).hexdigest()))
        finally:device.done()
    result=dict(verdict='XOR_RESEARCHER_COMPLETED_NEEDS_INDEPENDENT_AUDIT',
        models=len(originals),accepted=sum(r['candidate']['status']=='QUADRATIC_FIVE_COORDINATE_CANDIDATE' for r in originals),
        queries=sum(r['transcript']['count'] for r in originals),
        scores=scores,seal_sha256=seal_sha,
        global_claim='REFUSE_UNCONDITIONAL')
    (out/'xor_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print('XOR_RESEARCHER_EXECUTED',result['models'],result['accepted'],result['queries'],flush=True)
    return result
if __name__=='__main__':
    main(sys.argv[1])
