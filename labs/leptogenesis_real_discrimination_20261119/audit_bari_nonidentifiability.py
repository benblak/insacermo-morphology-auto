#!/usr/bin/env python3
"""INSACERMO Bari 2026.a: underdetermination from published contours.
Two hypothetical continuous periodic piecewise-linear profiles reproduce all
three quoted normal-ordering phase intervals but differ on min chi2 in B high.
These are COUNTERMODELS, NOT published likelihood measurements.
"""
from fractions import Fraction
from hashlib import sha256
import json
KNOT_BASE=[(0,20),(1422,9),(1656,4),(1890,1),(2142,0),
           (2412,1),(2970,4)]
KNOT_TAIL=[(3510,9),(3600,20)]
CONTOURS={1:(1890,2412),4:(1656,2970),9:(1422,3510)}
A=range(1980,2251)
B_LOW=range(50,401)
B_HIGH=range(3200,3551)
def knots(t):
    assert 4<t<9
    return KNOT_BASE+[(3200,t)]+KNOT_TAIL
def evaluate(k,x):
    assert 0<=x<3600
    for (x0,y0),(x1,y1) in zip(k,k[1:]):
        if x0<=x<=x1:
            return Fraction(y0,1)+Fraction(y1-y0,x1-x0)*(x-x0)
    raise AssertionError(x)
def check(t):
    k=knots(t)
    assert k[0][1]==k[-1][1]
    values=[evaluate(k,x) for x in range(3600)]
    for level,interval in CONTOURS.items():
        region=[x for x,v in enumerate(values) if v<=level]
        assert region==list(range(interval[0],interval[1]+1))
    assert min(values[x] for x in A)==0
    assert min(values[x] for x in B_LOW)>9
    assert min(values[x] for x in B_HIGH)==t
    return dict(name=f'constructed_P{t}',min_chi2_B_high=t,
        common_contours={str(z):list(ends) for z,ends in CONTOURS.items()},
        checked_angles_tenth_degree=len(values),
        values_sha256=sha256(' '.join(str(v) for v in values).encode()).hexdigest())
def main():
    p5,p8=check(5),check(8)
    assert p5['common_contours']==p8['common_contours']
    assert p5['min_chi2_B_high']!=p8['min_chi2_B_high']
    print(json.dumps({'source':'Bari 2026.a preliminary NO rounded contours',
      'interpretation':'constructed counterexamples, not measured fits',
      'bracket':'4 < min_B_high(delta_chi2) <= 9',
      'hypothetical_profiles':[p5,p8]},indent=2))
    print('BARI_2026A_PROFILE_NONIDENTIFIABILITY_SUCCESS')
if __name__=='__main__':main()
