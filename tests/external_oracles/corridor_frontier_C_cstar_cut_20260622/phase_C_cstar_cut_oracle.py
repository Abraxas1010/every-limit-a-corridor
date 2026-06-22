#!/usr/bin/env python3
"""Independent oracle for CStarLocated.agda — the cut-level C* identity (2x2).
Re-derives (NOT transliterated): det-multiplicativity det(r^2 I - M^2)=det(rI-M)det(rI+M); the two
first-minor splits fm1/fm2; and the BACKWARD direction isPD(rI-M)&isPD(rI+M) => isPD(r^2 I - M^2)."""
from fractions import Fraction as Q
import random
def isPD2(A,B,D): return (A>0) and (A*D-B*B>0)
ok_det=ok_fm1=ok_fm2=ok_back=True
for _ in range(100000):
    a=Q(random.randint(-7,7),random.randint(1,4)); b=Q(random.randint(-7,7),random.randint(1,4)); d=Q(random.randint(-7,7),random.randint(1,4))
    r=Q(random.randint(1,14),random.randint(1,3))
    a2=a*a+b*b; b2=b*(a+d); d2=b*b+d*d                  # M^2 entries
    fm = r*r-(a*a+b*b)                                   # first minor of r^2 I - M^2
    DL = (r*r-a2)*(r*r-d2) - (-(b2))*(-(b2))             # det(r^2 I - M^2)
    DR1 = (r-a)*(r-d)-(-b)*(-b); DR2=(r+a)*(r+d)-b*b     # det(rI-M), det(rI+M)
    if DL != DR1*DR2: ok_det=False
    if fm != (a+d)*(r-a)+DR1: ok_fm1=False
    if fm != (-(a+d))*(r+a)+DR2: ok_fm2=False
    # backward: isPD(rI-M)=isPD2(r-a,-b,r-d) and isPD(rI+M)=isPD2(r+a,b,r+d) => isPD2(r^2I-M^2)
    if isPD2(r-a,-b,r-d) and isPD2(r+a,b,r+d):
        if not isPD2(r*r-a2, -(b2), r*r-d2): ok_back=False
print("det-multiplicativity det(r2I-M2)=det(rI-M)det(rI+M):", "PASS" if ok_det else "FAIL")
print("first-minor split fm1  r2-a2-b2=(a+d)(r-a)+det(rI-M):", "PASS" if ok_fm1 else "FAIL")
print("first-minor split fm2  r2-a2-b2=-(a+d)(r+a)+det(rI+M):", "PASS" if ok_fm2 else "FAIL")
print("BACKWARD  isPD(rI-M)&isPD(rI+M) => isPD(r2I-M2)     :", "PASS" if ok_back else "FAIL")

# forward + full iff: isPD(r2I-M2) <=> isPD(rI-M) & isPD(rI+M)  (r>0)
ok_fwd=ok_iff=True
for _ in range(100000):
    a=Q(random.randint(-7,7),random.randint(1,4)); b=Q(random.randint(-7,7),random.randint(1,4)); d=Q(random.randint(-7,7),random.randint(1,4))
    r=Q(random.randint(1,14),random.randint(1,3))
    a2=a*a+b*b; b2=b*(a+d); d2=b*b+d*d
    lhs = isPD2(r*r-a2, -(b2), r*r-d2)
    rhs = isPD2(r-a,-b,r-d) and isPD2(r+a,b,r+d)
    if lhs != rhs: ok_iff=False
    if lhs and not rhs: ok_fwd=False
print("FORWARD   isPD(r2I-M2) => isPD(rI-M)&isPD(rI+M) :", "PASS" if ok_fwd else "FAIL")
print("FULL IFF  isPD(r2I-M2) <=> isPD(rI-M)&isPD(rI+M):", "PASS" if ok_iff else "FAIL")

print("ALL", "PASS" if all([ok_det,ok_fm1,ok_fm2,ok_back,ok_fwd,ok_iff]) else "FAIL")
