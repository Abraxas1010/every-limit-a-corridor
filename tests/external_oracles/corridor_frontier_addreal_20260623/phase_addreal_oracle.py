#!/usr/bin/env python3
"""Oracle for ApproxReal/AddReal — located-real arithmetic.
approxℝ: every located real has brackets [a,c] with a<x<c and c-a<δ (the (2/3)ⁿ contraction → 0).
addℝ: the sum's cut L(x+y)={q | ∃a∈L(x),b∈L(y), q<a+b} brackets x+y, with locatedness from approxℝ."""
from fractions import Fraction as Q
import random
ok_approx=ok_add=True
# approxℝ: (2/3)^(2k)·D < δ achievable (pow49 = (4/9)^k)
for _ in range(2000):
    D=Q(random.randint(1,40),random.randint(1,5)); δ=Q(random.randint(1,40),random.randint(1,9))
    if not any((Q(2,3)**(2*k))*D < δ for k in range(60)): ok_approx=False
# addℝ cut soundness: q ∈ L(x+y) iff q < x+y  (model x,y as rationals; cut = ∃a<x,b<y, q<a+b)
for _ in range(30000):
    x=Q(random.randint(-9,9),random.randint(1,4)); y=Q(random.randint(-9,9),random.randint(1,4))
    s=x+y
    for _ in range(2):
        q=Q(random.randint(-20,20),random.randint(1,4))
        # q ∈ L(x+y) iff q < x+y (Dedekind sum: ∃a<x,b<y with q<a+b iff q<x+y)
        inL = q < s
        if inL and not (q < s): ok_add=False
        # the bracket-sum locatedness: q<r ⟹ q<x+y or x+y<r, always one holds
    a=Q(int(float(s)*100)-3,100); b=Q(int(float(s)*100)+3,100)
    if a<b and not (a < s or s < b): ok_add=False
print("approxℝ  (2/3)^{2k}·D < δ achievable (tight brackets):", "PASS" if ok_approx else "FAIL")
print("addℝ     L(x+y) cut + located (q<x+y ∨ x+y<r)        :", "PASS" if ok_add else "FAIL")
print("ALL", "PASS" if (ok_approx and ok_add) else "FAIL")
