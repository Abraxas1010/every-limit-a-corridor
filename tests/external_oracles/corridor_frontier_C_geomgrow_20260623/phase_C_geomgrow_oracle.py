#!/usr/bin/env python3
"""Oracle for GeomGrow.agda — Bernoulli for repeated squaring: 1 + 2^L·(t-1) ≤ t^{2^L} for t≥1.
This linear-in-2^L lower bound is what makes t^{2^L} exceed any C (the growth driving locatedness)."""
from fractions import Fraction as Q
import random
def qpow(t,L):
    x=t
    for _ in range(L): x=x*x
    return x
ok=True
for _ in range(200000):
    t=Q(random.randint(1,9),random.randint(1,4))
    if t<1: continue
    L=random.randint(0,5)
    if 1 + (2**L)*(t-1) > qpow(t,L): ok=False
# growth: for t>1, ∃L with t^{2^L} > C (sanity)
grow=True
for _ in range(2000):
    t=Q(random.randint(5,20),random.randint(1,4))
    if t<=1: continue
    C=Q(random.randint(1,1000))
    if not any(qpow(t,L)>C for L in range(20)): grow=False
print("bern   1 + 2^L·(t-1) ≤ t^{2^L}  (t≥1):", "PASS" if ok else "FAIL")
print("growth ∃L, t^{2^L} > C          (t>1):", "PASS" if grow else "FAIL")
print("ALL", "PASS" if (ok and grow) else "FAIL")
