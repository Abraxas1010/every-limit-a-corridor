#!/usr/bin/env python3
"""Oracle for QpowMono.agda — 0≤a≤b ⟹ a^{2^L} ≤ b^{2^L}, and 0≤a ⟹ 0≤a^{2^L}."""
from fractions import Fraction as Q
import random
def qpow(t,L):
    x=t
    for _ in range(L): x=x*x
    return x
ok=True
for _ in range(200000):
    a=Q(random.randint(0,9),random.randint(1,4)); b=a+Q(random.randint(0,9),random.randint(1,4)); L=random.randint(0,5)
    if qpow(a,L) > qpow(b,L): ok=False
    if qpow(a,L) < 0: ok=False
print("qpow-mono  0≤a≤b ⟹ a^{2^L}≤b^{2^L}:", "PASS" if ok else "FAIL")
print("ALL", "PASS" if ok else "FAIL")
