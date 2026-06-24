#!/usr/bin/env python3
"""Oracle for ZPhiSpectralEdge — the larger eigenvalue of a symmetric 2×2 Z[φ] matrix
   [[a+bφ, c+dφ],[c+dφ, e+fφ]] is λ₊=(tr+√Δ)/2, Δ=(A−E)²+4C²=Δa+Δb·φ.
   Verify the Δa,Δb coefficient formulas (φ²=φ+1) and λ₊ vs numpy eigenvalue."""
from fractions import Fraction as Q
import random, numpy as np
PHI=(1+5**0.5)/2
ok_disc=ok_eig=True
for _ in range(200000):
    a,b,c,d,e,f=[Q(random.randint(-6,6),random.randint(1,3)) for _ in range(6)]
    # discriminant coefficients (must match the Agda Δa, Δb)
    Δa = ((a-e)*(a-e) + (b-f)*(b-f)) + 4*((c*c)+(d*d))
    Δb = (2*((a-e)*(b-f)) + (b-f)*(b-f)) + 4*((2*(c*d))+(d*d))
    # check Δ = (A-E)²+4C² as a real equals Δa+Δb·φ
    A=float(a)+float(b)*PHI; E=float(e)+float(f)*PHI; C=float(c)+float(d)*PHI
    Δreal=(A-E)**2 + 4*C*C
    if abs(Δreal - (float(Δa)+float(Δb)*PHI)) > 1e-7: ok_disc=False
    # λ₊=(tr+√Δ)/2 vs numpy larger eigenvalue
    tr=A+E
    lam_formula=(tr + Δreal**0.5)/2
    M=np.array([[A,C],[C,E]]); lam_np=max(np.linalg.eigvalsh(M))
    if abs(lam_formula - lam_np) > 1e-6: ok_eig=False
print("Δ = (A−E)²+4C² = Δa+Δb·φ  (φ²=φ+1 reduction) :", "PASS" if ok_disc else "FAIL")
print("λ₊ = (tr+√Δ)/2 = larger eigenvalue (numpy)    :", "PASS" if ok_eig else "FAIL")
print("ALL", "PASS" if (ok_disc and ok_eig) else "FAIL")
