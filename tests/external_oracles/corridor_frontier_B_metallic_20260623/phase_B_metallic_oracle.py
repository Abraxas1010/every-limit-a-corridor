#!/usr/bin/env python3
"""Oracle for MetallicReal.agda — metallic k = specEdge k 1 0 IS the larger root of x²=kx+1 = (k+√(k²+4))/2.
Golden=metallic 1=(1+√5)/2, silver=metallic 2=1+√2, bronze=metallic 3=(3+√13)/2.  The cut Lσ q =
L_{√(k²+4)}(2q-k) brackets it; and it solves x²=kx+1."""
from fractions import Fraction as Q
import random, math
def inLroot(p, Δ): return (p<0) or (p*p < Δ)
ok_cut=ok_root=True
for _ in range(20000):
    k=Q(random.randint(-8,8),random.randint(1,3))
    Δ=k*k+4; s=k
    val=(float(k)+math.sqrt(float(Δ)))/2            # metallic k
    if abs(val*val - (float(k)*val + 1)) > 1e-6: ok_root=False   # x²=kx+1
    for _ in range(3):
        q=Q(random.randint(-12,12),random.randint(1,3))
        Lsig = inLroot(2*q - s, Δ)
        if Lsig and not (float(q) < val+1e-7): ok_cut=False
        if (float(q) < val-1e-7) and not Lsig: ok_cut=False
# named members
g=(1+5**0.5)/2; si=1+2**0.5; br=(3+13**0.5)/2
ok_named = abs(g*g-(g+1))<1e-9 and abs(si*si-(2*si+1))<1e-9 and abs(br*br-(3*br+1))<1e-9
print("metallic k  cut brackets (k+√(k²+4))/2  :", "PASS" if ok_cut else "FAIL")
print("metallic k  solves x² = kx + 1          :", "PASS" if ok_root else "FAIL")
print("golden/silver/bronze solve x²=kx+1      :", "PASS" if ok_named else "FAIL")
print("ALL", "PASS" if (ok_cut and ok_root and ok_named) else "FAIL")
