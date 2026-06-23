#!/usr/bin/env python3
"""Oracle for SpecBracket.agda — the located bracket on the spectral-radius cut, symmetric A, n=1..6:
  q > ‖A‖₁  ⟹  q above ρ(A)   (rayUp-oneNorm: q is a strict Rayleigh upper bound);
  q < maxDiag ⟹  q below ρ(A) (notRayUp-diag: q is NOT a Rayleigh upper bound).
Confirms the cut maxDiag ≤ ρ ≤ ‖A‖₁ separates rationals correctly."""
from fractions import Fraction as Q
import random
def one_norm(A): return sum(abs(A[i][j]) for i in range(len(A)) for j in range(len(A)))
def rho(A):
    import numpy as np; return max(abs(ev) for ev in np.linalg.eigvals([[float(x) for x in r] for r in A]))
ok_up=ok_lo=True
for n in range(1,7):
    for _ in range(20000):
        A=[[None]*n for _ in range(n)]
        for i in range(n):
            for j in range(i,n):
                v=Q(random.randint(-5,5),random.randint(1,3)); A[i][j]=v; A[j][i]=v
        r=rho(A); n1=float(one_norm(A)); md=float(max(A[i][i] for i in range(n)))
        # every q above ‖A‖₁ is above ρ
        if not (n1 >= r-1e-9): ok_up=False
        # every q below maxDiag is below ρ
        if not (md <= r+1e-9): ok_lo=False
print("rayUp-oneNorm  q>‖A‖₁ ⟹ q>ρ      (n=1..6):", "PASS" if ok_up else "FAIL")
print("notRayUp-diag  q<maxDiag ⟹ q<ρ   (n=1..6):", "PASS" if ok_lo else "FAIL")
print("ALL", "PASS" if (ok_up and ok_lo) else "FAIL")
