#!/usr/bin/env python3
"""Oracle for SpectralEdgeReal.agda — specEdge a b d IS the larger eigenvalue λ₊ of [[a,b],[b,d]]:
λ₊ = (a+d+√Δ)/2, Δ=(a-d)²+4b².  The reparam cut Lσ q = L_{√Δ}(2q-(a+d)) brackets λ₊, and λ₊ is the
true top eigenvalue (numpy)."""
from fractions import Fraction as Q
import random, numpy as np
def inLrootΔ(p, Δ): return (p<0) or (p*p < Δ)   # √Δ lower cut
ok_edge=ok_eig=True
for _ in range(20000):
    a=Q(random.randint(-6,6),random.randint(1,3)); b=Q(random.randint(-6,6),random.randint(1,3)); d=Q(random.randint(-6,6),random.randint(1,3))
    Δ=(a-d)*(a-d)+4*(b*b)
    s=a+d
    lam=max(np.linalg.eigvalsh([[float(a),float(b)],[float(b),float(d)]]))
    # specEdge lower cut: q ∈ Lσ iff (2q-s) ∈ L_{√Δ}
    for _ in range(3):
        q=Q(random.randint(-15,15),random.randint(1,3))
        Lsig = inLrootΔ(2*q - s, Δ)
        if Lsig and not (float(q) < lam+1e-7): ok_edge=False         # σ-cut below λ₊
        if (float(q) < lam-1e-7) and not Lsig: ok_edge=False         # complete below λ₊
    # λ₊ = (s+√Δ)/2 matches numpy top eigenvalue
    if abs((float(s)+float(Δ)**0.5)/2 - lam) > 1e-6: ok_eig=False
print("specEdge  cut Lσ q=L_{√Δ}(2q-s) brackets λ₊ :", "PASS" if ok_edge else "FAIL")
print("λ₊ = (a+d+√Δ)/2 = numpy top eigenvalue       :", "PASS" if ok_eig else "FAIL")
print("ALL", "PASS" if (ok_edge and ok_eig) else "FAIL")
