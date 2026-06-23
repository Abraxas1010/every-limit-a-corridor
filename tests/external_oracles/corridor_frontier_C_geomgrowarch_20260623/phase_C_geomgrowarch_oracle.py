#!/usr/bin/env python3
"""Oracle for GeomGrowArch.agda — t>1 ⟹ ∃L, C < t^{2^L}, and the dyadic bound k+1 ≤ 2^k."""
from fractions import Fraction as Q
import random
def qpow(t,L):
    x=t
    for _ in range(L): x=x*x
    return x
ok_g=ok_d=True
for k in range(0,25):
    if k+1 > 2**k: ok_d=False                              # k+1 ≤ 2^k
for _ in range(3000):
    t=Q(random.randint(11,40),random.randint(1,10))
    if t<=1: continue
    C=Q(random.randint(1,5000),random.randint(1,3))
    if not any(C < qpow(t,L) for L in range(40)): ok_g=False   # ∃L, C < t^{2^L}
print("dyadic-ge  k+1 ≤ 2^k        :", "PASS" if ok_d else "FAIL")
print("qgrow      t>1 ⟹ ∃L, C<t^{2^L}:", "PASS" if ok_g else "FAIL")
print("ALL", "PASS" if (ok_g and ok_d) else "FAIL")
