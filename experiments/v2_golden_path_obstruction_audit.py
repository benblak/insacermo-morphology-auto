from fractions import Fraction
from math import sqrt

PHI = (1 + sqrt(5.0))/2.0
TARGET = 1.0/(PHI*PHI)

def fibonacci_counts(nmax):
    A=[0]*(nmax+1)
    A[0]=1
    if nmax>=1:
        A[1]=2
    for n in range(2,nmax+1):
        A[n]=A[n-1]+A[n-2]
    return A

def exact_endpoint_counts(nmax):
    A=fibonacci_counts(nmax)
    for n in range(2,nmax+1):
        total=A[n]
        include=A[n-2]
        omit=A[n-1]
        assert include+omit==total
    return A

def weighted_Z(nmax, lam):
    # exact rational lambda
    Z=[Fraction(0,1)]*(nmax+1)
    Z[0]=Fraction(1,1)
    if nmax>=1:
        Z[1]=Fraction(1,1)+lam
    for n in range(2,nmax+1):
        Z[n]=Z[n-1]+lam*Z[n-2]
    return Z

def weighted_endpoint_prob(n, lam, Z):
    if n==0:
        return Fraction(0,1)
    if n==1:
        return lam/(1+lam)
    return lam*Z[n-2]/Z[n]

print("INSACERMO_V2_GOLDEN_PATH_OBSTRUCTION_AUDIT")
print("STATUS","DERIVED_THEN_CONFIRMED")

A=exact_endpoint_counts(1000)
for n in [2,3,4,5,8,10,20,50,100,500,1000]:
    p=A[n-2]/A[n]
    q=A[n-1]/A[n]
    print("UNWEIGHTED","N",n,"TOTAL",A[n],"P_INCLUDE",f"{p:.15f}","P_OMIT",f"{q:.15f}",
          "P_MINUS_Q2",f"{p-q*q:.15e}","ERR_TO_GOLDEN",f"{p-TARGET:.15e}")

assert abs(A[1000-2]/A[1000] - TARGET) < 1e-14
print("UNWEIGHTED_LIMIT_MATCH_GOLDEN","YES")
print("TARGET",f"{TARGET:.15f}")

tests=[
    Fraction(1,4),
    Fraction(1,2),
    Fraction(1,1),
    Fraction(2,1),
    Fraction(4,1)
]
for lam in tests:
    Z=weighted_Z(400,lam)
    p=weighted_endpoint_prob(400,lam,Z)
    pf=float(p)
    residual=pf-float(lam)*(1-pf)**2
    print("WEIGHTED","LAMBDA",float(lam),"P400",f"{pf:.15f}","FIXED_POINT_RESIDUAL",f"{residual:.15e}")

# Exact finite recurrence identity for endpoint decomposition.
for lam in tests:
    Z=weighted_Z(80,lam)
    for n in range(2,81):
        assert Z[n] == Z[n-1] + lam*Z[n-2]
        p = weighted_endpoint_prob(n,lam,Z)
        assert p == lam*Z[n-2]/Z[n]
        assert (Fraction(1,1)-p) == Z[n-1]/Z[n]
print("WEIGHTED_RECURRENCE_EXACT","PASS")

# Closed-form fixed point for lambda>0:
# p = lambda (1-p)^2. We verify the positive root against long-n limit.
for lam in [0.25,0.5,1.0,2.0,4.0]:
    # lambda p^2 - (2lambda+1)p + lambda = 0
    root=((2*lam+1)-sqrt(4*lam+1))/(2*lam)
    Z=weighted_Z(1000,Fraction(str(lam)))
    p=float(weighted_endpoint_prob(1000,Fraction(str(lam)),Z))
    print("CLOSED_FORM","LAMBDA",lam,"ROOT",f"{root:.15f}","P1000",f"{p:.15f}","ERR",f"{p-root:.15e}")
    assert abs(p-root) < 1e-13

print("RESULT","COMPLETE")
