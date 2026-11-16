#!/usr/bin/env python3
"""Private-by-INTERFACE synthetic oracle for open-world tests.
The discovery client is deliberately restricted to JSON stdin/stdout queries.
This is procedural blindness, NOT cryptographic/third-party secrecy.
"""
import argparse,hashlib,json,sys

# Private implementation of case laws. NOT imported by discovery client.
_BASE_MONOMIALS=(13,18,56)
_FORBIDDEN_PROBES={55,10,2,15,13,14,22,20}
_DOMAIN=range(64)
# Seeded deterministic challenge. The candidate and learner never receive
# these exception locations from the query API.
_RANKED=sorted((i for i in _DOMAIN if i not in _FORBIDDEN_PROBES),
               key=lambda i:hashlib.sha256(("outside-catalogue-2026:"+str(i)).encode()).digest())
_CASE_SPIKES={"known":(),"one_spike":tuple(_RANKED[:1]),
              "two_spikes":tuple(_RANKED[:2]),"unstable":()}

def evaluate(case,x,calls):
    y=sum((x&k)==k for k in _BASE_MONOMIALS)%2
    if x in _CASE_SPIKES[case]:y^=1
    if case=="unstable" and x==0:y^=(calls[x]%2)
    return y

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--case",choices=tuple(_CASE_SPIKES),required=True)
    a=p.parse_args()
    calls={}
    for line in sys.stdin:
        try:
            obj=json.loads(line)
            x=obj["x"]
            if type(x)!=int or not 0<=x<64:raise ValueError("OUT_OF_DOMAIN")
            calls[x]=calls.get(x,0)+1
            print(json.dumps({"x":x,"y":evaluate(a.case,x,calls)},separators=(",",":")),flush=True)
        except (ValueError,TypeError,KeyError,json.JSONDecodeError) as e:
            print(json.dumps({"error":str(e)}),flush=True)

if __name__=="__main__":main()
