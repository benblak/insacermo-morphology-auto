#!/usr/bin/env python3
"""Sealed-by-protocol hidden-structure oracle on a 24-bit Boolean domain.
Three modes share the same 4-clause monotone function:
  clean: monotone,
  obvious: a positive high-density input is changed to False,
  needle: one fixed 12+-bit positive input changed to False.
Only JSON-lines x->y is available to the learner. Program source is public:
procedural blindness, NOT independent cryptographic secrecy.
"""
import argparse,json,random,sys
N=24
FULL=(1<<N)-1
SEED=177

def clauses():
    rng=random.Random(SEED)
    bits=list(range(N));rng.shuffle(bits)
    result=[];j=0
    for k in (2,3,4,5):
        mask=0
        for b in bits[j:j+k]:mask|=1<<b
        result.append(mask);j+=k
    return tuple(result)

def hidden_needle():
    # fixed before the learner's execution; 12 bits plus first 2-bit clause
    rng=random.Random(SEED+999)
    chosen=rng.sample(range(N),12)
    mask=sum(1<<b for b in chosen)
    return mask|clauses()[0]

def truth(x):
    return int(any((x&c)==c for c in clauses()))

def evaluate(mode,x):
    y=truth(x)
    if mode=="obvious" and x==FULL^(1<<23):return 0
    if mode=="needle" and x==hidden_needle():return 0
    return y

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--mode",choices=("clean","obvious","needle"),required=True)
    a=parser.parse_args()
    assert truth(hidden_needle())==1
    assert truth(FULL^(1<<23))==1
    for line in sys.stdin:
        try:
            q=json.loads(line);x=q["x"]
            if type(x)!=int or not 0<=x<=FULL:raise ValueError("OUTSIDE_INPUT_DOMAIN")
            print(json.dumps({"x":x,"y":evaluate(a.mode,x)},separators=(",",":")),flush=True)
        except (ValueError,TypeError,KeyError,json.JSONDecodeError) as e:
            print(json.dumps({"error":str(e)}),flush=True)

if __name__=="__main__":main()
