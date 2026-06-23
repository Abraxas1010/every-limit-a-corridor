#!/usr/bin/env python3
"""Oracle for SquareRefine.agda — for PSD A (symmetric), rayUp(A²)(s²) ⟹ rayUp A s, n=1..6.
rayUp B t = (∀x≠0, ⟨x,Bx⟩ < t⟨x,x⟩) = (λmax(B) < t). Check: λmax(A²)<s²  ⟹  λmax(A)<s  (PSD A)."""
from fractions import Fraction as Q
import random
def matmul(A,B):
    n=len(A); return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def lam_max(A):
    import numpy as np; return max(e.real for e in np.linalg.eigvals([[float(x) for x in r] for r in A]))
def lam_min(A):
    import numpy as np; return min(e.real for e in np.linalg.eigvals([[float(x) for x in r] for r in A]))
ok=True
for n in range(1,7):
    for _ in range(20000):
        # PSD symmetric A = BᵀB
        B=[[Q(random.randint(-4,4),random.randint(1,3)) for _ in range(n)] for _ in range(n)]
        A=[[sum(B[k][i]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
        if lam_min(A) < -1e-9: continue                 # ensure PSD numerically
        A2=matmul(A,A); s=Q(random.randint(1,40),random.randint(1,4))
        # rayUp(A²)(s²) ⟹ rayUp A s :  λmax(A²)<s²  ⟹  λmax(A)<s
        if lam_max(A2) < float(s*s)-1e-7:
            if not (lam_max(A) < float(s)+1e-7): ok=False
print("square-refine  λmax(A²)<s² ⟹ λmax(A)<s  (PSD A, n=1..6):", "PASS" if ok else "FAIL")
print("ALL", "PASS" if ok else "FAIL")
