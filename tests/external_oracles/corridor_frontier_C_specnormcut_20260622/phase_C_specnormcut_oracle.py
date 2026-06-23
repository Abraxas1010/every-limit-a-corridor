#!/usr/bin/env python3
"""Oracle for SpecNormCut.agda — the LOCATED operator-norm cut for symmetric M (‖M‖=ρ(M)), n=1..6:
  normUp-up    : ‖M·M‖₁ < r²   ⟹  ‖M‖ < r     (r above the operator norm);
  notNormUp-low: r² < (M·M)ᵢᵢ  ⟹  ‖M‖ ≥ r     (r below the operator norm).
So ‖M‖ ∈ [√maxDiag(M·M), √‖M·M‖₁]. Confirms the located cut is sound for symmetric M."""
from fractions import Fraction as Q
import random
def matmul(A,B):
    n=len(A); return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def one_norm(A): return sum(abs(A[i][j]) for i in range(len(A)) for j in range(len(A)))
def opnorm(A):  # operator norm = spectral radius for symmetric A
    import numpy as np; return max(abs(ev) for ev in np.linalg.eigvals([[float(x) for x in r] for r in A]))
import math
ok_up=ok_lo=True
for n in range(1,7):
    for _ in range(20000):
        M=[[None]*n for _ in range(n)]
        for i in range(n):
            for j in range(i,n):
                v=Q(random.randint(-5,5),random.randint(1,3)); M[i][j]=v; M[j][i]=v
        M2=matmul(M,M); nm=opnorm(M)
        n1=float(one_norm(M2)); md=float(max(M2[i][i] for i in range(n)))
        # ‖M‖² ≤ ‖M·M‖₁  (so r²>‖M·M‖₁ ⟹ r>‖M‖)
        if not (nm*nm <= n1+1e-9): ok_up=False
        # maxDiag(M·M) ≤ ‖M‖²  (so r²<maxDiag ⟹ r<‖M‖)
        if not (md <= nm*nm+1e-9): ok_lo=False
print("normUp-up      ‖M‖² ≤ ‖M·M‖₁     (n=1..6):", "PASS" if ok_up else "FAIL")
print("notNormUp-low  maxDiag(M·M) ≤ ‖M‖² (n=1..6):", "PASS" if ok_lo else "FAIL")
print("ALL", "PASS" if (ok_up and ok_lo) else "FAIL")
