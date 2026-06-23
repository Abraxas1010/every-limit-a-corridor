#!/usr/bin/env python3
"""Oracle for SqrtReal.agda — sqrtReal x IS √x: the cut L={q|q<0∨q²<x}, U={q|q>0∧q²>x} brackets √x,
is sound on both sides, and is located (decidable). x ≥ 0 rational, n=1..; many x."""
from fractions import Fraction as Q
import random, math
def inL(x,q):  return (q<0) or (q*q < x)
def inU(x,q):  return (q>0) and (x < q*q)
ok_L=ok_U=ok_loc=ok_disj=True
for _ in range(40000):
    x=Q(random.randint(0,40),random.randint(1,7))
    s=math.sqrt(float(x))
    for _ in range(3):
        q=Q(random.randint(-8,12),random.randint(1,7))
        if inL(x,q) and not (float(q) < s+1e-9): ok_L=False        # L below √x
        if inU(x,q) and not (float(q) > s-1e-9): ok_U=False        # U above √x
        if inL(x,q) and inU(x,q): ok_disj=False                    # disjoint
    a=Q(int(s*100)-25,100); b=Q(int(s*100)+25,100)
    if a<b and not (inL(x,a) or inU(x,b)): ok_loc=False            # located
print("L below √x   q∈L ⟹ q<√x        :", "PASS" if ok_L else "FAIL")
print("U above √x   q∈U ⟹ q>√x        :", "PASS" if ok_U else "FAIL")
print("disjoint     ¬(q∈L ∧ q∈U)       :", "PASS" if ok_disj else "FAIL")
print("located      a<b ⟹ a∈L ∨ b∈U   :", "PASS" if ok_loc else "FAIL")
print("ALL", "PASS" if (ok_L and ok_U and ok_loc and ok_disj) else "FAIL")
