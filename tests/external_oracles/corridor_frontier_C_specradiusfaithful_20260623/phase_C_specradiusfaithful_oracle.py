#!/usr/bin/env python3
"""Oracle for SpecRadiusFaithful.agda — U-sound: an upper-cut witness ‖M^{2^L}‖₁<q^{2^L} implies the
operator-norm bound normUp M q (= ‖Mx‖²<q²⟨x,x⟩ ∀x≠0, i.e. ‖M‖<q). Certifies specRadius's upper cut
agrees with the operator norm. Symmetric M, n=1..5."""
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
def opnorm(A):
    import numpy as np; return max(abs(e) for e in np.linalg.eigvals([[float(x) for x in r] for r in A]))
def mv(A,x): n=len(A); return [sum(A[i][j]*x[j] for j in range(n)) for i in range(n)]
def ip(u,v): return sum(a*b for a,b in zip(u,v))
ok=True
for n in range(1,6):
    for _ in range(20000):
        M=[[None]*n for _ in range(n)]
        for i in range(n):
            for j in range(i,n):
                v=Q(random.randint(-4,4),random.randint(1,3)); M[i][j]=v; M[j][i]=v
        q=Q(random.randint(1,15),random.randint(1,3))
        # if some upper-cut witness holds, normUp M q must hold (‖M‖<q)
        upp=any(one_norm(pow2(M,L)) < qpow(q,L) for L in range(7))
        if upp and not (opnorm(M) < float(q)+1e-7): ok=False
print("U-sound  UppRaw witness ⟹ normUp M q (‖M‖<q) (n=1..5):", "PASS" if ok else "FAIL")
print("ALL", "PASS" if ok else "FAIL")
