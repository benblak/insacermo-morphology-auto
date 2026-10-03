#!/usr/bin/env python3
import json
from pathlib import Path
d=json.loads(Path(__file__).with_name("erdos302_f735_certificate.json").read_text())
S=set(d["witness"]); n=d["n"]
assert n==735 and len(S)==609 and 735 in S
viol=[]; triples=0
for b in range(1,n+1):
    for c in range(b+1,n+1):
        den=b+c; num=b*c
        if num%den: continue
        a=num//den
        if 1<=a<b:
            triples+=1
            if a in S and b in S and c in S: viol.append((a,b,c))
assert triples==740, triples
assert not viol, viol[:3]
assert len([x for x in S if x<=734])==608
print("WITNESS_OK")
print("size =",len(S))
print("forbidden triples =",triples)
print("restriction_to_734 =",len([x for x in S if x<=734]))
print("f(735) >= 609 verified exactly")
