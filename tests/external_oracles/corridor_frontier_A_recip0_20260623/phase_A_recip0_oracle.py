#!/usr/bin/env python3
"""Oracle for Cofinal.recip→0 — the Cassini gap 1/fibP(2n)² is driven below any ε>0 (n=suc m suffices
for ε=1/(m+1)): so f(lo n)=1−1/D² climbs to 1 (the convergents fill φ's cut)."""
from fractions import Fraction as Q
def fibP(m):
    a,b=1,1
    for _ in range(m): a,b=b,a+b
    return a
ok=True
for m in range(0,60):
    eps=Q(1,m+1)
    n=m+1                          # the witness recip→0 uses
    D=fibP(2*n)
    if not (Q(1, D*D) < eps): ok=False
# also: for arbitrary small ε some n works
for num,den in [(1,1000),(3,777),(1,10**6)]:
    eps=Q(num,den)
    if not any(Q(1, fibP(2*n)*fibP(2*n)) < eps for n in range(0,60)): ok=False
print("recip→0  ∃n, 1/fibP(2n)² < ε  (n=m+1 for ε=1/(m+1)):", "PASS" if ok else "FAIL")
print("ALL", "PASS" if ok else "FAIL")
