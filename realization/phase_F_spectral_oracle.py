#!/usr/bin/env python3
"""Phase-F external oracle — certified √ by bisection + 2×2 symmetric spectral edge.

Replicates the EXACT algorithm of CertifiedSqrt.bisect (init bracket [0,x+1],
midpoint (lo+hi)/2, decidable test x < mid²) and SpectralEdge.specEdgeBracket
(Δ=(a−d)²+4b², λ₊=(a+d+√Δ)/2), and checks the certified bounds hold and the
brackets genuinely contain the irrational targets (√2 and φ²=(3+√5)/2).

All arithmetic is exact (Fraction), mirroring the Agda's ℚ.  No floats in the cert.
"""
from fractions import Fraction as Q
import math, sys

def sqrt_bracket(x: Q, D: int):
    """exact mirror of CertifiedSqrt: D steps of bisection of [0, x+1]."""
    lo, hi = Q(0), x + 1
    assert lo * lo <= x <= hi * hi, "initial invariant"
    for _ in range(D):
        mid = (lo + hi) * Q(1, 2)
        if x < mid * mid:        # √x < mid  → keep lo, new hi = mid
            hi = mid
        else:                    # mid² ≤ x  → new lo = mid, keep hi
            lo = mid
    return lo, hi

def discriminant(a: Q, b: Q, d: Q) -> Q:
    return (a - d) * (a - d) + 4 * (b * b)

def spec_edge(a: Q, b: Q, d: Q, D: int):
    Δ = discriminant(a, b, d)
    assert Δ >= 0
    slo, shi = sqrt_bracket(Δ, D)
    half = Q(1, 2)
    return ((a + d) + slo) * half, ((a + d) + shi) * half, slo, shi

def main() -> int:
    ok = True
    # 1. certified √: lo² ≤ x ≤ hi², and the bracket contains the true √x.
    for x in (Q(2), Q(3), Q(5), Q(7), Q(10), Q(1, 4), Q(9, 4)):
        for D in (0, 1, 5, 10, 20):
            lo, hi = sqrt_bracket(x, D)
            if not (lo * lo <= x <= hi * hi):
                print(f"  [FAIL] √{x} D={D}: cert lo²≤x≤hi² broken"); ok = False
            r = math.sqrt(float(x))
            if not (float(lo) - 1e-9 <= r <= float(hi) + 1e-9):
                print(f"  [FAIL] √{x} D={D}: bracket [{lo},{hi}] misses {r}"); ok = False
        lo, hi = sqrt_bracket(x, 24)
        width = float(hi - lo)
        if width > 2 ** -10:
            print(f"  [WARN] √{x}: width {width:.2e} at D=24 (narrows but check rate)")
    # 2. √2 ≈ 1.41421356 — depth-20 bracket is tight and contains it.
    lo, hi = sqrt_bracket(Q(2), 20)
    assert lo * lo <= 2 <= hi * hi and float(lo) <= 1.41421356 <= float(hi), "√2"
    print(f"  [OK]   √2 ∈ [{float(lo):.8f}, {float(hi):.8f}]  (depth 20, lo²≤2≤hi²)")

    # 3. spectral edge of [[2,1],[1,1]]: Δ=5, λ₊=(3+√5)/2 = φ² ≈ 2.61803399.
    a, b, d = Q(2), Q(1), Q(1)
    assert discriminant(a, b, d) == 5, "Δ([[2,1],[1,1]]) = 5"
    loλ, hiλ, slo, shi = spec_edge(a, b, d, 20)
    phi2 = (3 + math.sqrt(5)) / 2
    if not (slo * slo <= 5 <= shi * shi):
        print("  [FAIL] spectral cert slo²≤Δ≤shi² broken"); ok = False
    if not (float(loλ) <= phi2 <= float(hiλ)):
        print(f"  [FAIL] edge bracket [{loλ},{hiλ}] misses φ²={phi2}"); ok = False
    # cross-check: φ² = φ+1, and the golden ratio φ = (1+√5)/2 = 1.6180339887
    phi = (1 + math.sqrt(5)) / 2
    assert abs(phi2 - (phi + 1)) < 1e-12, "φ² = φ+1"
    print(f"  [OK]   spectral edge [[2,1],[1,1]] λ₊ ∈ [{float(loλ):.8f}, {float(hiλ):.8f}]  ∋ φ²={phi2:.8f}")

    # 4. another edge with rational eigenvalues [[2,1],[1,2]]: Δ=1, λ=1,3 → λ₊=3.
    loλ, hiλ, slo, shi = spec_edge(Q(2), Q(1), Q(2), 20)
    if not (float(loλ) <= 3.0 <= float(hiλ)):
        print(f"  [FAIL] [[2,1],[1,2]] edge misses 3"); ok = False
    else:
        print(f"  [OK]   spectral edge [[2,1],[1,2]] λ₊ ∈ [{float(loλ):.6f}, {float(hiλ):.6f}]  ∋ 3 (exact)")

    print("Phase-F oracle:", "ALL CHECKS PASS" if ok else "FAILED")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
