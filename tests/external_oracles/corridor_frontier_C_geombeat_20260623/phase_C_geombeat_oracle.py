#!/usr/bin/env python3
"""Oracle for GeomBeat.agda — 0<q<r ⟹ ∃L, C·q^{2^L} < r^{2^L}; and qpow L(ab)=qpow L a·qpow L b."""
from fractions import Fraction as Q
import random
def qpow(t,L):
    x=t
    for _ in range(L): x=x*x
    return x
ok_m=ok_b=True
for _ in range(50000):
    a=Q(random.randint(-6,6),random.randint(1,3)); b=Q(random.randint(-6,6),random.randint(1,3)); L=random.randint(0,4)
    if qpow(a*b,L) != qpow(a,L)*qpow(b,L): ok_m=False
for _ in range(2000):
    q=Q(random.randint(1,8),random.randint(1,5)); r=q+Q(random.randint(1,8),random.randint(1,5))
    C=Q(random.randint(1,2000),random.randint(1,3))
    if not any(C*qpow(q,L) < qpow(r,L) for L in range(40)): ok_b=False
print("qpow-mult  qpow L(ab)=qpow L a·qpow L b :", "PASS" if ok_m else "FAIL")
print("geom-beat  0<q<r ⟹ ∃L, C·q^{2^L}<r^{2^L}:", "PASS" if ok_b else "FAIL")
print("ALL", "PASS" if (ok_m and ok_b) else "FAIL")
