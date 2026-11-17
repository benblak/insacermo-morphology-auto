#!/usr/bin/env python3
"""Synthetic 24-bit hidden law oracle for integrated XOR lab.
Separate process for learner. NOT an unknown law of nature."""
import argparse,json,random,sys
N=24
CASES=['source_0','source_1','source_2','target_0','target_1','target_2','target_rare','target_cubic','target_rank2']
SEED=73913
def independent(masks):
    pivots={}
    for m in masks:
        q=m
        while q:
            b=q.bit_length()-1
            if b not in pivots:pivots[b]=q;break
            q^=pivots[b]
        else:return False
    return True
def secrets(name):
    rng=random.Random(SEED+sum((i+1)*ord(c) for i,c in enumerate(name)))
    masks=[]
    while len(masks)<(8 if name=='target_cubic' else 5):
        mask=sum(1<<i for i in rng.sample(range(N),rng.randint(3,6)))
        if independent(masks+[mask]):masks.append(mask)
    return masks,rng.getrandbits(1)
def needle():return random.Random(SEED+99117).randrange(1<<N)
def evaluate(name,x):
    m,flip=secrets(name)
    a,b,c,d,e=[(x&v).bit_count()%2 for v in m[:5]]
    z=a^b^c^d^e^(a&b)^(c&d)
    if name=='target_rank2':z^=(c&d)
    if name=='target_cubic':
        f,g,h=[(x&v).bit_count()%2 for v in m[5:]]
        z^=(f&g&h)
    if name=='target_rare':z^=int(x==needle())
    return z^flip
def main():
    p=argparse.ArgumentParser();p.add_argument('--case',choices=CASES,required=True)
    name=p.parse_args().case
    for line in sys.stdin:
        try:
            x=json.loads(line)['x']
            assert type(x) is int and 0<=x<1<<N
            print(json.dumps({'x':x,'y':evaluate(name,x)},separators=(',',':')),flush=True)
        except Exception as exc:print(json.dumps({'error':str(exc)}),flush=True)
if __name__=='__main__':main()
