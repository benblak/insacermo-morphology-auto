#!/usr/bin/env python3
"""Separate query-only oracle for four randomly generated 6-bit laws.

The oracle only exposes x -> bit. Its generated secret specification is not
imported by the learner. This is procedural blindness within an ordinary CI
runner, not cryptographic or external-party validation.

Degree-2/3/4 and a degree-6 point-spike are generated from a fresh CI secret.
The degree and coefficients are withheld from the synthesis code.
"""
from __future__ import annotations
import argparse,hashlib,itertools,json,secrets,sys
from pathlib import Path

N_BITS=6
DOMAIN=64
def weight(x):return x.bit_count()

def make_secret():
    rng=secrets.SystemRandom()
    masks_by_degree={
       d:[i for i in range(64) if weight(i)==d] for d in range(7)
    }
    cases={}
    for case,top in (("case_0",2),("case_1",3),("case_2",4),("case_3",6)):
        low=set(rng.sample(masks_by_degree[1]+masks_by_degree[2],6))
        # Force a quadratic term to be present.
        low.add(rng.choice(masks_by_degree[2]))
        if rng.randrange(2):low.add(0)
        if top==3:low.add(rng.choice(masks_by_degree[3]))
        if top==4:low.add(rng.choice(masks_by_degree[4]))
        if top==6:low.add(63)  # one-point, high-degree exception
        cases[case]=sorted(low)
    return cases

def evaluate(masks,x):
    return sum((x&m)==m for m in masks)&1

def serve(spec,case):
    masks=spec[case]
    for line in sys.stdin:
        try:
            req=json.loads(line)
            x=req["x"]
            if type(x) is not int or x not in range(DOMAIN):
                raise ValueError("INVALID_QUERY")
            reply={"x":x,"y":evaluate(masks,x)}
        except (ValueError,KeyError,TypeError,json.JSONDecodeError) as e:
            reply={"error":str(e)}
        print(json.dumps(reply,separators=(",",":")),flush=True)

def main():
    a=argparse.ArgumentParser()
    a.add_argument("--make-secret",type=Path)
    a.add_argument("--secret-file",type=Path)
    a.add_argument("--case",choices=("case_0","case_1","case_2","case_3"))
    args=a.parse_args()
    if args.make_secret:
        masks=make_secret()
        args.make_secret.write_text(json.dumps(masks,sort_keys=True))
        print("GENERATED_SECRET_COMMITMENT_SHA256",
          hashlib.sha256(args.make_secret.read_bytes()).hexdigest(),flush=True)
    elif args.secret_file and args.case:
        spec=json.loads(args.secret_file.read_text())
        serve(spec,args.case)
    else:
        a.error("Provide --make-secret or --secret-file with --case")

if __name__=="__main__":
    main()
