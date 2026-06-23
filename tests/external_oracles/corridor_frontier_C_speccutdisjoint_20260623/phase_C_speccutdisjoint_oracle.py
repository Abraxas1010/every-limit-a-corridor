#!/usr/bin/env python3
"""Oracle for SpecCutDisjoint.agda — the spectral-radius cut is DISJOINT, symmetric M, 0≤q, n=1..5.
  lowAt L q := ∃i, q^{2^L}<(M^{2^L})ᵢᵢ ;  uppAt L q := ‖M^{2^L}‖₁<q^{2^L}.
Disjoint: never both lowAt L1 q AND uppAt L2 q (for any L1,L2) — they persist to a common level
where (M^{2^L})ᵢᵢ ≤ ‖M^{2^L}‖₁ forces a contradiction."""
from fractions import Fraction as Q
import random
def matmul(A,B):
    n=len(A); return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def one_norm(A): return sum(abs(A[i][j]) for i in range(len(A)) for j in range(len(A)))
def pow2(M,L):
    A=M
    for _ in range(L): A=matmul(A,A)
    return A
ok=True
for n in range(1,6):
    for _ in range(6000):
        M=[[None]*n for _ in range(n)]
        for i in range(n):
            for j in range(i,n):
                v=Q(random.randint(-4,4),random.randint(1,3)); M[i][j]=v; M[j][i]=v
        q=Q(random.randint(0,5),random.randint(1,3))
        for L1 in range(0,4):
            A1=pow2(M,L1); qp1=q**(2**L1)
            low = any(qp1 < A1[i][i] for i in range(n))
            for L2 in range(0,4):
                A2=pow2(M,L2); qp2=q**(2**L2)
                upp = one_norm(A2) < qp2
                if low and upp: ok=False     # disjointness violated
print("disjoint  ¬(lowAt L1 q ∧ uppAt L2 q), 0≤q (n=1..5):", "PASS" if ok else "FAIL")
print("ALL", "PASS" if ok else "FAIL")
