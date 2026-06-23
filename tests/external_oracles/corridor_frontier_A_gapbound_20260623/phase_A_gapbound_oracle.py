#!/usr/bin/env python3
"""Oracle for GapBound.agda — the EXACT Cassini gap: loPlus1 n − lo n² = 1/fibP(2n)², i.e.
loPlus1 n = lo n² + 1/D²  (D = fibP(2n) = F_{2n+1}).  And the gap → 0."""
from fractions import Fraction as Q
def fibP(m):  # F_{m+1}
    a,b=1,1
    for _ in range(m): a,b=b,a+b
    return a
def lo(n):    # F_{2n+2}/F_{2n+1}
    return Q(fibP(2*n+1), fibP(2*n))
def loPlus1(n):
    return Q(fibP(2*n+2), fibP(2*n))   # F_{2n+3}/F_{2n+1}
ok_eq=ok_gap=True
for n in range(0,40):
    D=fibP(2*n)
    if loPlus1(n) != lo(n)*lo(n) + Q(1, D*D): ok_eq=False
for n in range(0,40):
    D=fibP(2*n)
    if loPlus1(n) - lo(n)*lo(n) != Q(1,D*D): ok_gap=False
print("gapForm   loPlus1 n = lo n² + 1/D²  (D=F_{2n+1}):", "PASS" if ok_eq else "FAIL")
print("gap → 0   loPlus1 n − lo n² = 1/D² ↓ 0          :", "PASS" if ok_gap else "FAIL")
print("ALL", "PASS" if (ok_eq and ok_gap) else "FAIL")
