#!/usr/bin/env python3
"""Oracle for AbsLemmas.agda — |x·y|=|x||y|, |x+y|≤|x|+|y|, sqrt-inj, over ℚ."""
from fractions import Fraction as Q
import random
ok_m=ok_t=ok_s=True
for _ in range(400000):
    x=Q(random.randint(-9,9),random.randint(1,4)); y=Q(random.randint(-9,9),random.randint(1,4))
    if abs(x*y) != abs(x)*abs(y): ok_m=False
    if abs(x+y) > abs(x)+abs(y): ok_t=False
    a=abs(x); b=abs(y)            # nonneg
    if a*a==b*b and a!=b: ok_s=False
print("abs-mult      |x·y| = |x||y|      :", "PASS" if ok_m else "FAIL")
print("abs-triangle  |x+y| ≤ |x|+|y|     :", "PASS" if ok_t else "FAIL")
print("sqrt-inj      a²=b²,0≤a,0≤b ⟹ a=b :", "PASS" if ok_s else "FAIL")
print("ALL", "PASS" if (ok_m and ok_t and ok_s) else "FAIL")
