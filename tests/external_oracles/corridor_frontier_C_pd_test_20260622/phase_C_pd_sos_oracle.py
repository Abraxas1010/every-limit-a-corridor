#!/usr/bin/env python3
"""Independent oracle for PDTest2.agda — the 2x2 square-root-free Cholesky (LDLT) PD test.
Re-derives (NOT transliterated) the SOS certificate + witnesses and checks consistency with
the genuine eigenvalue-based PD test. Validates: a*Q = (ax+by)^2 + (ad-b^2)y^2 (the LDLT/SOS
identity); Q(1,0)=a; a*Q(-b,a)=(ad-b^2)a^2; and that the witness vectors certify non-PD."""
from fractions import Fraction as Q
import random, math

def quad(a,b,d,x,y):  # <Mx,x> for symmetric [[a,b],[b,d]]
    return a*x*x + b*x*y + b*x*y + d*y*y

def eig_pd(a,b,d):  # genuine: PD iff both eigenvalues > 0
    tr=a+d; det=a*d-b*b; disc=tr*tr-4*det
    # disc>=0 for symmetric; eigenvalues (tr +- sqrt(disc))/2; PD iff min eig>0 iff tr>0 and det>0
    return (tr>0) and (det>0)

ok_sos=ok_w1=ok_w2=ok_syl=ok_witfail=True
for _ in range(20000):
    a=Q(random.randint(-6,6),random.randint(1,4)); b=Q(random.randint(-6,6),random.randint(1,4)); d=Q(random.randint(-6,6),random.randint(1,4))
    x=Q(random.randint(-5,5),random.randint(1,3)); y=Q(random.randint(-5,5),random.randint(1,3))
    disc=a*d-b*b
    # SOS identity
    if a*quad(a,b,d,x,y) != (a*x+b*y)**2 + disc*y*y: ok_sos=False
    # witness reductions
    if quad(a,b,d,Q(1),Q(0)) != a: ok_w1=False
    if a*quad(a,b,d,-b,a) != disc*a*a: ok_w2=False
    # Sylvester (0<a & 0<disc) == genuine eigenvalue PD
    if (a>0 and disc>0) != eig_pd(a,b,d): ok_syl=False
    # when not PD, the right witness has Q<=0
    if not (a>0):
        if not (quad(a,b,d,Q(1),Q(0)) <= 0): ok_witfail=False
    elif not (disc>0):
        if not (quad(a,b,d,-b,a) <= 0): ok_witfail=False
print("SOS identity a*Q=(ax+by)^2+(ad-b^2)y^2 :", "PASS" if ok_sos else "FAIL")
print("witness Q(1,0)=a                       :", "PASS" if ok_w1 else "FAIL")
print("witness a*Q(-b,a)=(ad-b^2)a^2          :", "PASS" if ok_w2 else "FAIL")
print("Sylvester(0<a & 0<ad-b^2) == eig-PD    :", "PASS" if ok_syl else "FAIL")
print("non-PD witness gives Q<=0              :", "PASS" if ok_witfail else "FAIL")

# forward: PD (0<a & 0<disc) => Q(x,y)>0 for every nonzero (x,y)
ok_fwd=True
import random as _r
for _ in range(20000):
    a=Q(_r.randint(1,6),_r.randint(1,4)); d=Q(_r.randint(-3,6),_r.randint(1,4)); b=Q(_r.randint(-6,6),_r.randint(1,4))
    if not (a>0 and a*d-b*b>0): continue
    x=Q(_r.randint(-5,5),_r.randint(1,3)); y=Q(_r.randint(-5,5),_r.randint(1,3))
    if x==0 and y==0: continue
    if not (quad(a,b,d,x,y) > 0): ok_fwd=False
print("forward PD => Q>0 for nonzero x          :", "PASS" if ok_fwd else "FAIL")

print("ALL", "PASS" if all([ok_sos,ok_w1,ok_w2,ok_syl,ok_witfail,ok_fwd]) else "FAIL")
