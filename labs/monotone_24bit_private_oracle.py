#!/usr/bin/env python3
"""Separate query-only oracle: monotone 24-bit unknown Boolean law, or
one deliberately non-monotone physical-analogue adversary.

The discovery client sees only x in [0,2^24) -> {0,1}. The true generating
clauses are neither imported nor passed to the learner. This is a locally
constructed synthetic oracle, not independent experiment or real physics.
"""
import argparse,hashlib,json,random,sys
N=24; FULL=(1<<N)-1

def clauses(seed):
    rng=random.Random(seed)
    bits=list(range(N));rng.shuffle(bits)
    result=[];j=0
    for k in (2,3,4,5):
        mask=0
        for b in bits[j:j+k]:mask|=1<<b
        result.append(mask);j+=k
    return result

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--seed",type=int,required=True)
    p.add_argument("--adversarial",action="store_true")
    args=p.parse_args()
    secret=clauses(args.seed)
    # point near the top is a guaranteed positive superset of all clauses
    # except maybe one, and can be illegally reversed in adversarial mode.
    violation=FULL ^ (1 << 23)
    assert any((violation&c)==c for c in secret)
    for line in sys.stdin:
        try:
            obj=json.loads(line);x=obj["x"]
            if type(x)!=int or x<0 or x>FULL:raise ValueError("OUT_OF_DOMAIN")
            y=int(any((x&c)==c for c in secret))
            if args.adversarial and x==violation:y=0
            print(json.dumps({"x":x,"y":y},separators=(",",":")),flush=True)
        except (KeyError,ValueError,TypeError) as e:
            print(json.dumps({"error":str(e)}),flush=True)
if __name__=="__main__":main()
