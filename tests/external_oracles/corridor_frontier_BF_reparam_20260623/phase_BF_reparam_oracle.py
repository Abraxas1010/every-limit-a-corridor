#!/usr/bin/env python3
"""Oracle for ReparamReal.agda — a monotone ℚ-bijection (φ,ψ) reparametrizes a located real ρ to ψ(ρ):
the cut Lσ q = Lρ(φ q) brackets ψ(value of ρ).  Concrete check: ρ=√x (cut q²<x), ψ(p)=(p+s)/2,
φ(q)=2q-s, so ψ(√x) = (√x+s)/2 — and Lσ q ⟺ q < (√x+s)/2."""
from fractions import Fraction as Q
import random, math
ok=True
for _ in range(30000):
    x=Q(random.randint(0,30),random.randint(1,5)); s=Q(random.randint(-10,10),random.randint(1,3))
    sx=math.sqrt(float(x)); target=(sx+float(s))/2
    phi=lambda q: 2*q - s
    # Lρ(p) = p<0 or p²<x  (the √x lower cut);  Lσ q = Lρ(φ q)
    inLrho=lambda p: (p<0) or (p*p<x)
    for _ in range(3):
        q=Q(random.randint(-15,15),random.randint(1,4))
        Lsig = inLrho(phi(q))
        if Lsig and not (float(q) < target+1e-9): ok=False     # σ-cut below ψ(√x)
        if (float(q) < target-1e-9) and not Lsig: ok=False     # and complete below it
print("reparamℝ  Lσ q = Lρ(φ q) brackets ψ(value) (ρ=√x, ψ=(·+s)/2):", "PASS" if ok else "FAIL")
print("ALL", "PASS" if ok else "FAIL")
