#!/usr/bin/env python3
"""Oracle for OneNormSubmult.agda — ‖A·B‖₁ ≤ ‖A‖₁·‖B‖₁ (ℓ¹ submultiplicativity), n=1..6, arbitrary A,B.
Also the upper-cut persistence consequence: ‖A²‖₁ ≤ ‖A‖₁²."""
from fractions import Fraction as Q
import random
def matmul(A,B):
    n=len(A); return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def one_norm(A): return sum(abs(A[i][j]) for i in range(len(A)) for j in range(len(A)))
ok_s=ok_sq=True
for n in range(1,7):
    for _ in range(40000):
        A=[[Q(random.randint(-5,5),random.randint(1,3)) for _ in range(n)] for _ in range(n)]
        B=[[Q(random.randint(-5,5),random.randint(1,3)) for _ in range(n)] for _ in range(n)]
        if one_norm(matmul(A,B)) > one_norm(A)*one_norm(B): ok_s=False     # ‖A·B‖₁ ≤ ‖A‖₁‖B‖₁
        if one_norm(matmul(A,A)) > one_norm(A)*one_norm(A): ok_sq=False    # ‖A²‖₁ ≤ ‖A‖₁²
print("oneNorm-submult  ‖A·B‖₁ ≤ ‖A‖₁·‖B‖₁  (n=1..6):", "PASS" if ok_s else "FAIL")
print("upper persistence ‖A²‖₁ ≤ ‖A‖₁²       (n=1..6):", "PASS" if ok_sq else "FAIL")
print("ALL", "PASS" if (ok_s and ok_sq) else "FAIL")
