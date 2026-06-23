#!/usr/bin/env python3
"""Oracle for LowerBracket.agda — eᵢ realizes the diagonal: ⟨eᵢ,eᵢ⟩=1, ⟨A·eᵢ,eᵢ⟩=Aᵢᵢ,
hence maxDiag(A) ≤ ρ(A) for SYMMETRIC A (a rational lower bracket on the spectral radius). n=1..6."""
from fractions import Fraction as Q
import random
def e(n,i): return [Q(1) if k==i else Q(0) for k in range(n)]
def mv(A,x): n=len(A); return [sum(A[i][j]*x[j] for j in range(n)) for i in range(n)]
def ip(u,v): return sum(a*b for a,b in zip(u,v))
def rho(A):
    import numpy as np; return max(abs(ev) for ev in np.linalg.eigvals([[float(x) for x in r] for r in A]))
ok_e=ok_lb=True
for n in range(1,7):
    for _ in range(20000):
        # symmetric A (lower bracket maxDiag ≤ ρ holds for symmetric/normal)
        A=[[None]*n for _ in range(n)]
        for i in range(n):
            for j in range(i,n):
                v=Q(random.randint(-5,5),random.randint(1,3)); A[i][j]=v; A[j][i]=v
        for i in range(n):
            ei=e(n,i)
            if ip(ei,ei)!=1: ok_e=False                          # ⟨eᵢ,eᵢ⟩=1
            if ip(ei, mv(A,ei))!=A[i][i]: ok_e=False             # ⟨A·eᵢ,eᵢ⟩=Aᵢᵢ
        maxdiag=max(A[i][i] for i in range(n))
        if float(maxdiag) > rho(A)+1e-9: ok_lb=False             # maxDiag ≤ ρ(A)
print("eNorm/eRayleigh  ⟨eᵢ,eᵢ⟩=1, ⟨A·eᵢ,eᵢ⟩=Aᵢᵢ (n=1..6):", "PASS" if ok_e else "FAIL")
print("lower bracket    maxDiag(A) ≤ ρ(A)  symmetric  (n=1..6):", "PASS" if ok_lb else "FAIL")
print("ALL", "PASS" if (ok_e and ok_lb) else "FAIL")
