#!/usr/bin/env python3
"""Oracle for OffDiagBound.agda — for A=B·B (B symmetric): (Aᵢⱼ)² ≤ Aᵢᵢ·Aⱼⱼ, n=1..6.
This is the 2×2-minor / off-diagonal control: |Aᵢⱼ| ≤ √(Aᵢᵢ Aⱼⱼ) ≤ maxDiag, the basis of locatedness."""
from fractions import Fraction as Q
import random
def matmul(A,B):
    n=len(A); return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
ok=True
for n in range(1,7):
    for _ in range(30000):
        B=[[None]*n for _ in range(n)]
        for i in range(n):
            for j in range(i,n):
                v=Q(random.randint(-5,5),random.randint(1,3)); B[i][j]=v; B[j][i]=v
        A=matmul(B,B)
        for i in range(n):
            for j in range(n):
                if A[i][j]*A[i][j] > A[i][i]*A[j][j]: ok=False    # (Aᵢⱼ)² ≤ Aᵢᵢ·Aⱼⱼ
print("offdiag-sq  (Aᵢⱼ)² ≤ Aᵢᵢ·Aⱼⱼ  (A=B·B, B sym, n=1..6):", "PASS" if ok else "FAIL")
print("ALL", "PASS" if ok else "FAIL")
