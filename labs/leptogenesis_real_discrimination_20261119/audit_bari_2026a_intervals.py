#!/usr/bin/env python3
"""INSACERMO laboratory: phase-only overlap with PRELIMINARY Bari 2026.a.
Source: https://home.ba.infn.it/~marrone/Results.html (as of 2026-11-19).
Normal ordering, global LBL+solar+reactor+atmosphere fit incl JUNO.
Only published rounded 1/2/3-sigma endpoints are transcribed.
No full chi2 curve downloaded; no new C3 verdict is claimed.
"""
from decimal import Decimal
from itertools import product

A=(1980,2250)
B=((50,400),(3200,3550))
INTERVALS={
    "1sigma":("1.05","1.34"),
    "2sigma":("0.92","1.65"),
    "3sigma":("0.79","1.95"),
}
def in_tenths(s):
    return int(Decimal(s)*1800)
def overlap(x,y):
    return max(x[0],y[0])<=min(x[1],y[1])
def intersection(x,y):
    return (max(x[0],y[0]),min(x[1],y[1])) if overlap(x,y) else None
def main():
    answers=[]
    for label, endpoints in INTERVALS.items():
        observed=tuple(map(in_tenths,endpoints))
        hit_a=intersection(observed,A)
        hit_b=[intersection(observed,b) for b in B]
        b_present=any(x is not None for x in hit_b)
        verdict="BOTH" if hit_a and b_present else "A_ONLY" if hit_a else "B_ONLY" if b_present else "NEITHER"
        answers.append(verdict)
        print(label, observed, verdict, "A:", hit_a, "B:", hit_b)
    assert answers==["A_ONLY","A_ONLY","BOTH"]
    assert intersection((1422,3510),B[1])==(3200,3510)
    assert not overlap((1656,2970),B[1])
    print("BARI_2026A_PUBLISHED_INTERVAL_AUDIT_SUCCESS")
if __name__=="__main__":
    main()
