#!/usr/bin/env python3
"""Independent oracle for SpecRadiusCut.agda — the 2x2 spectral-radius cut from the PD test.
Re-derives (NOT transliterated): the cut isUpper q = isPD(qI-M), the upper-bound property
(isUpper q => <Mx,x> < q<x,x> for all x!=0), and the lower-cut witnesses (not isUpper => an
explicit vector with <(qI-M)x,x> <= 0). Validates each against the genuine largest eigenvalue."""
from fractions import Fraction as Q
import random, math

def quad(a,b,d,x,y):  return a*x*x + b*x*y + b*x*y + d*y*y      # <Mx,x>
def shiftQ(a,b,d,q,x,y): return quad(q-a,-b,q-d,x,y)            # <(qI-M)x,x>
def isUpper(a,b,d,q): return (q-a>0) and ((q-a)*(q-d)-(-b)*(-b)>0)
def lam_max(a,b,d):   # largest eigenvalue of symmetric [[a,b],[b,d]]
    tr=a+d; det=a*d-b*b; disc=tr*tr-4*det                       # >=0
    return (float(tr)+math.sqrt(float(disc)))/2.0

ok_cut=ok_ub=ok_w1=ok_w2=True
for _ in range(40000):
    a=Q(random.randint(-6,6),random.randint(1,4)); b=Q(random.randint(-6,6),random.randint(1,4)); d=Q(random.randint(-6,6),random.randint(1,4))
    q=Q(random.randint(-12,12),random.randint(1,3))
    lm=lam_max(a,b,d)
    # cut correct: isUpper q  <=>  q > lam_max  (use a tolerance band to avoid float ties)
    if abs(float(q)-lm) > 1e-6:
        if isUpper(a,b,d,q) != (float(q) > lm): ok_cut=False
    # upper-bound: isUpper q => shiftQ q x y > 0 for nonzero x
    if isUpper(a,b,d,q):
        x=Q(random.randint(-5,5),random.randint(1,3)); y=Q(random.randint(-5,5),random.randint(1,3))
        if not (x==0 and y==0):
            if not (shiftQ(a,b,d,q,x,y) > 0): ok_ub=False
    else:
        # witnesses: not isUpper => the failing-pivot vector has shiftQ q <= 0
        if not (q-a>0):
            if not (shiftQ(a,b,d,q,Q(1),Q(0)) <= 0): ok_w1=False
        else:
            wx=-(-b); wy=q-a
            if not (shiftQ(a,b,d,q,wx,wy) <= 0): ok_w2=False
print("cut  isUpper q <=> q > lam_max          :", "PASS" if ok_cut else "FAIL")
print("upper-bound isUpper q => <(qI-M)x,x>>0  :", "PASS" if ok_ub else "FAIL")
print("witness pivot1 (1,0)   <(qI-M)x,x><=0   :", "PASS" if ok_w1 else "FAIL")
print("witness pivot2 (b,q-a) <(qI-M)x,x><=0   :", "PASS" if ok_w2 else "FAIL")

# located: for p<q, either isUpper q OR an explicit witness with shiftQ p < 0 (strict, at p).
ok_loc=True
for _ in range(40000):
    a=Q(random.randint(-6,6),random.randint(1,4)); b=Q(random.randint(-6,6),random.randint(1,4)); d=Q(random.randint(-6,6),random.randint(1,4))
    p=Q(random.randint(-12,12),random.randint(1,3)); q=p+Q(random.randint(1,9),random.randint(1,3))  # p<q
    if isUpper(a,b,d,q): continue                  # left branch ok by the cut check above
    # right branch: the located witness must have shiftQ p < 0 (strict)
    if not (q-a>0):
        if not (shiftQ(a,b,d,p,Q(1),Q(0)) < 0): ok_loc=False     # pivot1 witness (1,0) at p
    else:
        wx=-(-b); wy=q-a
        if not (shiftQ(a,b,d,p,wx,wy) < 0): ok_loc=False         # pivot2 witness (b,q-a) at p
print("located p<q => isUpper q OR shiftQ p<0  :", "PASS" if ok_loc else "FAIL")

print("ALL", "PASS" if all([ok_cut,ok_ub,ok_w1,ok_w2,ok_loc]) else "FAIL")
