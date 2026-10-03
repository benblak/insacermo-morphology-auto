#!/usr/bin/env python3
import json
from pathlib import Path
p = Path(__file__).with_name("erdos302_f735_certificate.json")
d = json.loads(p.read_text())
S = set(d["witness"])
n = d["n"]
assert n == 735
assert len(S) == d["lower_bound_witness_size"] == 609
assert all(1 <= x <= n for x in S)
viol = []
triples = 0
for b in range(1,n+1):
    for c in range(b+1,n+1):
        den=b+c
        num=b*c
        if num % den: continue
        a=num//den
        if 1 <= a < b:
            triples += 1
            if a in S and b in S and c in S:
                viol.append((a,b,c))
assert triples == 740, triples
assert not viol, viol[:1]
print("WITNESS_OK")
print("n =",n)
print("size =",len(S))
print("forbidden triples enumerated =",triples)
print("f(735) >= 609 verified exactly")
print("Combined with the external finite upper-bound premise f(734)<=608: f(735)=609.")
