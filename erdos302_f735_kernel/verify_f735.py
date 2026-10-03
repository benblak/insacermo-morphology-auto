#!/usr/bin/env python3
import json
from pathlib import Path

p=Path(__file__).with_name("erdos302_f735_certificate.json")
d=json.loads(p.read_text())
n=d["n"]
W=d["witness"]
S=set(W)

assert n==735
assert len(W)==609
assert len(S)==609
assert 735 in S
assert 294 not in S
assert len([x for x in S if x<=734])==608

triples=[]
viol=[]
new735=[]
for b in range(1,n+1):
    for c in range(b+1,n+1):
        den=b+c
        num=b*c
        q,r=divmod(num,den)
        if r==0 and 1<=q<b:
            t=(q,b,c)
            triples.append(t)
            if c==735:
                new735.append(t)
            if all(x in S for x in t):
                viol.append(t)

assert len(triples)==740, len(triples)
assert new735==[(210,294,735),(294,490,735)], new735
assert not viol, viol[:5]

print("WITNESS_OK")
print("size =",len(S))
print("restriction_to_734 =",len([x for x in S if x<=734]))
print("forbidden triples through 735 =",len(triples))
print("new triples at endpoint 735 =",new735)
print("violations =",len(viol))
print("blocking vertex 294 present? =",294 in S)
