#!/usr/bin/env python3
"""Oracle for SpecLocHelpers.agda — 1≤n² (n≥1); and beat-suc: s·a^{2^L}<b^{2^L} ⟹ s·a^{2^{L+1}}<b^{2^{L+1}}
(for 1≤s, 0≤a)."""
from fractions import Fraction as Q
import random
def qpow(t,L):
    x=t
    for _ in range(L): x=x*x
    return x
ok_n=ok_b=True
for n in range(1,30):
    if not (1 <= n*n): ok_n=False
for _ in range(40000):
    s=Q(random.randint(1,10),random.randint(1,3))
    if s<1: continue
    a=Q(random.randint(0,8),random.randint(1,4)); b=Q(random.randint(0,8),random.randint(1,4)); L=random.randint(0,4)
    if s*qpow(a,L) < qpow(b,L):
        if not (s*qpow(a,L+1) < qpow(b,L+1)): ok_b=False
print("1≤nSq     1 ≤ n²  (n≥1)                       :", "PASS" if ok_n else "FAIL")
print("beat-suc  s·a^{2^L}<b^{2^L} ⟹ s·a^{2^{L+1}}<… :", "PASS" if ok_b else "FAIL")
print("ALL", "PASS" if (ok_n and ok_b) else "FAIL")
