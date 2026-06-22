#!/usr/bin/env python3
"""Independent oracle for CStarRay.agda — the GENERAL-n C* identity at the Rayleigh-cut level.
Re-derives (NOT transliterated): the adjoint identity <Mx,Mx> = <x, M^2 x> for symmetric M in
each dimension, and that therefore the ‖M²‖ cut (∀x ⟨M²x,x⟩<r²⟨x,x⟩) and the ‖M‖² cut
(∀x ‖Mx‖²<r²‖x‖²) are the SAME condition, for n=2,3,4,5."""
from fractions import Fraction as Q
import random
def ip(u,v): return sum(u[i]*v[i] for i in range(len(u)))          # <u,v>
def mv(M,x): return [sum(M[i][j]*x[j] for j in range(len(x))) for i in range(len(M))]  # M x
ok_adj=ok_cut=True
for n in (2,3,4,5):
    for _ in range(20000):
        # symmetric M
        M=[[None]*n for _ in range(n)]
        for i in range(n):
            for j in range(i,n):
                v=Q(random.randint(-5,5),random.randint(1,3)); M[i][j]=v; M[j][i]=v
        x=[Q(random.randint(-5,5),random.randint(1,3)) for _ in range(n)]
        if all(t==0 for t in x): continue
        Mx=mv(M,x); M2x=mv(M,Mx)
        # adjoint: <Mx,Mx> == <x, M^2 x>
        if ip(Mx,Mx) != ip(x,M2x): ok_adj=False
        # cut coincidence at a random r: (<M2x,x> < r^2<x,x>) == (<Mx,Mx> < r^2<x,x>)
        r=Q(random.randint(1,9),random.randint(1,3)); xx=ip(x,x)
        if (ip(x,M2x) < r*r*xx) != (ip(Mx,Mx) < r*r*xx): ok_cut=False
print("adjoint  <Mx,Mx> = <x,M^2 x>  (n=2..5)      :", "PASS" if ok_adj else "FAIL")
print("cut coincidence  ‖M²‖-cut = ‖M‖²-cut        :", "PASS" if ok_cut else "FAIL")
print("ALL", "PASS" if (ok_adj and ok_cut) else "FAIL")
