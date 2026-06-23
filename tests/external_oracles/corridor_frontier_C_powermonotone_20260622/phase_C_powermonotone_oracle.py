#!/usr/bin/env python3
"""Oracle for PowerMonotone.agda — the persistence facts making the cut disjoint, symmetric A, n=1..6:
  diag-sq       : (Aᵢᵢ)² ≤ (A²)ᵢᵢ        (lower-cut persistence under squaring);
  entry≤oneNorm : Aᵢᵢ ≤ ‖A‖₁              (disjointness bound).
Also: the lower-cut condition q^{2^L}<(M^{2^L})ᵢᵢ PERSISTS to L+1 (the whole point)."""
from fractions import Fraction as Q
import random
def matmul(A,B):
    n=len(A); return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def one_norm(A): return sum(abs(A[i][j]) for i in range(len(A)) for j in range(len(A)))
ok_d=ok_e=ok_persist=True
for n in range(1,7):
    for _ in range(20000):
        A=[[None]*n for _ in range(n)]
        for i in range(n):
            for j in range(i,n):
                v=Q(random.randint(-5,5),random.randint(1,3)); A[i][j]=v; A[j][i]=v
        A2=matmul(A,A)
        for i in range(n):
            if A[i][i]*A[i][i] > A2[i][i]: ok_d=False        # (Aᵢᵢ)² ≤ (A²)ᵢᵢ
            if A[i][i] > one_norm(A): ok_e=False             # Aᵢᵢ ≤ ‖A‖₁
        # persistence: q^{2}<(A)ᵢᵢ ⟹ q^4<(A²)ᵢᵢ  (q below diagonal persists; uses 0≤q)
        q=Q(random.randint(0,4),random.randint(1,3))
        for i in range(n):
            if q*q < A[i][i]:
                if not (q*q*q*q < A2[i][i]): ok_persist=False
print("diag-sq        (Aᵢᵢ)² ≤ (A²)ᵢᵢ        (n=1..6):", "PASS" if ok_d else "FAIL")
print("entry≤oneNorm  Aᵢᵢ ≤ ‖A‖₁             (n=1..6):", "PASS" if ok_e else "FAIL")
print("persistence    q²<Aᵢᵢ ⟹ q⁴<(A²)ᵢᵢ    (n=1..6):", "PASS" if ok_persist else "FAIL")
print("ALL", "PASS" if (ok_d and ok_e and ok_persist) else "FAIL")
