#!/usr/bin/env python3
"""Oracle for QuadSqueeze.agda — q²−q < r²−r and 1 < q+r ⟹ q < r (order-reflection through f(x)=x²−x,
the increasing branch).  Counterexample search over ℚ."""
from fractions import Fraction as Q
import random
ok=True
for _ in range(500000):
    q=Q(random.randint(-10,20),random.randint(1,5)); r=Q(random.randint(-10,20),random.randint(1,5))
    if (q*q-q) < (r*r-r) and 1 < (q+r):
        if not (q < r): ok=False
print("quad-squeeze  q²−q<r²−r ∧ 1<q+r ⟹ q<r:", "PASS" if ok else "FAIL")
print("ALL", "PASS" if ok else "FAIL")
