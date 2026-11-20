#!/usr/bin/env python3
"""Single exact independent arithmetic audit for Erdős #302 at N=737.

Equation: 1/a = 1/b + 1/c for pairwise distinct a,b,c in [1,N].
For N=737, any newly forbidden triple must include 737 as largest denominator.
For a<c<737, rearrangement yields c=737*a/(737-a) and
(737-a)*(c+737)=737**2. Hence the integer d=737-a must be
a divisor of 737**2 with 737/2<d<737.
The interval is empty of divisors, so the new vertex is isolated.
Consequently f(737)=f(736)+1 without assuming an exact value of f(736).
"""
from math import isqrt
import json
N=737
assert N==11*67
triples=[]
for a in range(1,N):
    den=N-a
    num=N*a
    if num%den!=0:continue
    c=num//den
    if a<c<N:triples.append((a,c,N))
assert triples==[]
gap=[d for d in range(N//2+1,N) if N*N%d==0]
assert gap==[]
factors=[d for d in range(1,isqrt(N*N)+1) if N*N%d==0]
divisors=sorted(set(factors+[N*N//d for d in factors]))
assert divisors==[1,11,67,121,737,4489,8107,49379,543169]
report={
 'problem':'Erdos 302; 1/a=1/b+1/c, a,b,c positive pairwise distinct',
 'N':N,
 'new_forbidden_triples_containing_N':triples,
 'square_divisors':divisors,
 'no_divisor_in_open_half_to_N_interval':gap,
 'theorem':'f(737) = f(736) + 1',
 'scope':'Exact recurrence, no claim of exact f(736), and no solution to asymptotic open problem',
}
print(json.dumps(report,indent=2))
print('ERDOS302_737_INDEPENDENT_EXACT_AUDIT_SUCCESS')
