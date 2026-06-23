#!/usr/bin/env python3
"""Oracle for SpecRadiusReal.agda — specRadius M : ℝ IS the spectral radius (the cut brackets ρ(M)).
For symmetric M (n=1..5): every q in the lower cut L is < ρ(M); every q in the upper cut U is > ρ(M);
and the cut is located (the brackets close on ρ)."""
from fractions import Fraction as Q
import random
def matmul(A,B):
    n=len(A); return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def one_norm(A): return sum(abs(A[i][j]) for i in range(len(A)) for j in range(len(A)))
def qpow(t,L):
    x=t
    for _ in range(L): x=x*x
    return x
def pow2(M,L):
    A=M
    for _ in range(L): A=matmul(A,A)
    return A
def rho(A):
    import numpy as np; return max(abs(e) for e in np.linalg.eigvals([[float(x) for x in r] for r in A]))
def inL(M,q,n):   # q < 0, or some diagonal of some power exceeds q^{2^L}
    if q < 0: return True
    return any(qpow(q,L) < pow2(M,L)[i][i] for L in range(8) for i in range(n))
def inU(M,q,n):   # q > 0 and some power's ‖·‖₁ < q^{2^L}
    return q > 0 and any(one_norm(pow2(M,L)) < qpow(q,L) for L in range(8))
ok_L=ok_U=ok_loc=True
for n in range(1,6):
    for _ in range(3000):
        M=[[None]*n for _ in range(n)]
        for i in range(n):
            for j in range(i,n):
                v=Q(random.randint(-4,4),random.randint(1,3)); M[i][j]=v; M[j][i]=v
        r=rho(M)
        for _ in range(3):
            q=Q(random.randint(-5,12),random.randint(1,3))
            if inL(M,q,n) and not (float(q) < r+1e-7): ok_L=False     # L below ρ
            if inU(M,q,n) and not (float(q) > r-1e-7): ok_U=False     # U above ρ
        # located: for a<b straddling ρ, one of them is decided
        a=Q(int(r*100)-30,100); b=Q(int(r*100)+30,100)
        if a<b and not (inL(M,a,n) or inU(M,b,n)): ok_loc=False
print("L below ρ   q∈L ⟹ q<ρ(M)        (n=1..5):", "PASS" if ok_L else "FAIL")
print("U above ρ   q∈U ⟹ q>ρ(M)        (n=1..5):", "PASS" if ok_U else "FAIL")
print("located     a<b ⟹ a∈L or b∈U     (n=1..5):", "PASS" if ok_loc else "FAIL")
print("ALL", "PASS" if (ok_L and ok_U and ok_loc) else "FAIL")
