#!/usr/bin/env python3
"""Oracle for SpecLocated.agda — the located core: for symmetric M and 0<a<b, EITHER some diagonal of
some M^{2^L} exceeds a^{2^L} (a is below ρ) OR ‖M^{2^L}‖₁ < b^{2^L} for some L (b is above ρ). n=1..5."""
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
ok=True
for n in range(1,6):
    for _ in range(4000):
        M=[[None]*n for _ in range(n)]
        for i in range(n):
            for j in range(i,n):
                v=Q(random.randint(-4,4),random.randint(1,3)); M[i][j]=v; M[j][i]=v
        a=Q(random.randint(1,8),random.randint(1,3)); b=a+Q(random.randint(1,8),random.randint(1,3))
        low = any(qpow(a,L) < pow2(M,L)[i][i] for L in range(8) for i in range(n))
        upp = any(one_norm(pow2(M,L)) < qpow(b,L) for L in range(8))
        if not (low or upp): ok=False    # locatedness of the core
print("coreLoc  0<a<b ⟹ LowRaw a ⊎ UppRaw b  (n=1..5):", "PASS" if ok else "FAIL")
print("ALL", "PASS" if ok else "FAIL")
