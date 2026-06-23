#!/usr/bin/env python3
"""Oracle for QuadBound.agda — ⟨x,A·x⟩ ≤ ‖A‖₁·⟨x,x⟩ (ℓ¹ entry-sum bound), any matrix, n=1..6.
Also confirms ‖A‖₁ ≥ ρ(A): a valid computable UPPER bracket for the spectral radius."""
from fractions import Fraction as Q
import random
def mv(A,x): n=len(A); return [sum(A[i][j]*x[j] for j in range(n)) for i in range(n)]
def ip(u,v): return sum(a*b for a,b in zip(u,v))
def one_norm(A): return sum(abs(A[i][j]) for i in range(len(A)) for j in range(len(A)))
def rho(A):
    import numpy as np; return max(abs(e) for e in np.linalg.eigvals([[float(x) for x in r] for r in A]))
ok_q=ok_rho=True
for n in range(1,7):
    for _ in range(40000):
        A=[[Q(random.randint(-5,5),random.randint(1,3)) for _ in range(n)] for _ in range(n)]  # ARBITRARY
        x=[Q(random.randint(-5,5),random.randint(1,3)) for _ in range(n)]
        if ip(x, mv(A,x)) > one_norm(A)*ip(x,x): ok_q=False             # ⟨x,Ax⟩ ≤ ‖A‖₁·⟨x,x⟩
        if rho(A) > float(one_norm(A))+1e-9: ok_rho=False               # ρ(A) ≤ ‖A‖₁ (upper bracket)
print("quadBound  ⟨x,Ax⟩ ≤ ‖A‖₁·⟨x,x⟩  (n=1..6):", "PASS" if ok_q else "FAIL")
print("bracket    ρ(A) ≤ ‖A‖₁           (n=1..6):", "PASS" if ok_rho else "FAIL")
print("ALL", "PASS" if (ok_q and ok_rho) else "FAIL")
