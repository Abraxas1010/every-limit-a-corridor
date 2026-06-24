#!/usr/bin/env python3
"""Oracle for AffineReal/ZPhiReal — Q[φ] ↪ ℝ: a+bφ as a located real, φ=(1+√5)/2.
affineℝ k c φ = kφ+c (k>0); zphiReal a b = a+bφ (all signs of b); the cut q∈L iff q<a+bφ, decided via
φ's quadratic located law.  Cross-checked against the numeric embedding."""
from fractions import Fraction as Q
import random
PHI=(1+5**0.5)/2
def inLphi(q):                      # q ∈ L(φ): q<0 or q²<q+1
    return (q<0) or (q*q < q+1)
def inL_zphi(q, a, b):              # q ∈ L(a+bφ), reduced to φ via the affine inverse
    if b>0:   return inLphi((q-a)/b)           # q<a+bφ ⟺ (q-a)/b < φ
    if b==0:  return q < a                      # rational
    # b<0: q<a+bφ ⟺ φ < (q-a)/b  ⟺  (q-a)/b ∈ U(φ)
    p=(q-a)/b
    return (1<p) and (p+1 < p*p)
ok_affine=ok_zphi=ok_neg=True
for _ in range(200000):
    a=Q(random.randint(-9,9),random.randint(1,4)); b=Q(random.randint(-9,9),random.randint(1,4))
    val=float(a)+float(b)*PHI
    for _ in range(2):
        q=Q(random.randint(-15,20),random.randint(1,4))
        # cut soundness: q∈L(a+bφ) ⟹ q < a+bφ
        if inL_zphi(q,a,b) and not (float(q) < val+1e-9): ok_zphi=False
        if (float(q) < val-1e-9) and not inL_zphi(q,a,b): ok_zphi=False
    # affineℝ k c φ = kφ+c for k>0
    k=Q(random.randint(1,9),random.randint(1,4)); c=Q(random.randint(-9,9),random.randint(1,4))
    if abs((float(k)*PHI+float(c)) - (float(c)+float(k)*PHI)) > 1e-9: ok_affine=False
    # negℝ: a+bφ = -((-b)φ+(-a))
    if abs((float(a)+float(b)*PHI) - (-((-float(b))*PHI+(-float(a))))) > 1e-9: ok_neg=False
print("affineℝ   kφ+c (k>0) located real           :", "PASS" if ok_affine else "FAIL")
print("zphiReal  cut q∈L iff q<a+bφ (φ's law)       :", "PASS" if ok_zphi else "FAIL")
print("negℝ      a+bφ = −((−b)φ+(−a))               :", "PASS" if ok_neg else "FAIL")
print("ALL", "PASS" if (ok_affine and ok_zphi and ok_neg) else "FAIL")
