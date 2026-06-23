#!/usr/bin/env python3
"""Oracle for OneNormDiagBound.agda — for A=B·B (B symmetric), all Aᵢᵢ≤c ⟹ ‖A‖₁ ≤ c·n², n=1..6.
(entry-bound: |Aᵢⱼ|≤c via off-diag; then ‖A‖₁ = Σᵢⱼ|Aᵢⱼ| ≤ n²·c.)"""
from fractions import Fraction as Q
import random
def matmul(A,B):
    n=len(A); return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def one_norm(A): return sum(abs(A[i][j]) for i in range(len(A)) for j in range(len(A)))
ok_e=ok_n=True
for n in range(1,7):
    for _ in range(20000):
        B=[[None]*n for _ in range(n)]
        for i in range(n):
            for j in range(i,n):
                v=Q(random.randint(-5,5),random.randint(1,3)); B[i][j]=v; B[j][i]=v
        A=matmul(B,B)
        c=max(A[i][i] for i in range(n))            # the tightest c with all Aᵢᵢ≤c
        for i in range(n):
            for j in range(n):
                if abs(A[i][j]) > c: ok_e=False       # |Aᵢⱼ| ≤ c
        if one_norm(A) > c*(n*n): ok_n=False           # ‖A‖₁ ≤ c·n²
print("entry-bound        |Aᵢⱼ| ≤ c (all Aᵢᵢ≤c)  (n=1..6):", "PASS" if ok_e else "FAIL")
print("oneNorm-diag-bound ‖A‖₁ ≤ c·n²            (n=1..6):", "PASS" if ok_n else "FAIL")
print("ALL", "PASS" if (ok_e and ok_n) else "FAIL")
