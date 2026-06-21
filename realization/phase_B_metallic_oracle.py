#!/usr/bin/env python3
"""Phase-B external oracle — the metallic family of running corridors.

Independently re-derives the m-Fibonacci ladder kfib(m), checks the GENERAL
Cassini identity kfib(n+1)² = kfib(n)·kfib(n+2) + (−1)^n for every m (the
m-independent determinant), the metallic equation x²=m·x+1 satisfied by the
convergents up to (−1)^n/kfib(n)², and that metallic_m = (m+√(m²+4))/2 is the
spectral edge of [[m,1],[1,0]] (bracketed by the Phase-F bisection on Δ=m²+4).
"""
from fractions import Fraction as Q
import math, sys

def kfib(m: int, n: int) -> int:
    a, b = 0, 1
    if n == 0: return 0
    for _ in range(n - 1):
        a, b = b, m * b + a
    return b

def sqrt_bracket(x: Q, D: int):
    lo, hi = Q(0), x + 1
    for _ in range(D):
        mid = (lo + hi) * Q(1, 2)
        if x < mid * mid: hi = mid
        else: lo = mid
    return lo, hi

def main() -> int:
    ok = True
    # 1. ladders: m=1 Fibonacci 0,1,1,2,3,5,8 ; m=2 Pell 0,1,2,5,12,29 ; m=3 0,1,3,10,33,109
    assert [kfib(1, n) for n in range(7)] == [0, 1, 1, 2, 3, 5, 8], "Fibonacci (m=1)"
    assert [kfib(2, n) for n in range(6)] == [0, 1, 2, 5, 12, 29], "Pell (m=2)"
    assert [kfib(3, n) for n in range(6)] == [0, 1, 3, 10, 33, 109], "bronze (m=3)"
    print("  [OK]   ladders: m=1 Fibonacci, m=2 Pell, m=3 bronze")

    # 2. GENERAL Cassini  kfib(n+1)² = kfib(n)·kfib(n+2) + (−1)^n  for all m, n.
    for m in range(1, 8):
        for n in range(0, 30):
            lhs = kfib(m, n + 1) ** 2
            rhs = kfib(m, n) * kfib(m, n + 2) + (1 if n % 2 == 0 else -1)
            if lhs != rhs:
                print(f"  [FAIL] Cassini m={m} n={n}: {lhs} != {rhs}"); ok = False
    print("  [OK]   general Cassini (m-independent ±1) for m∈1..7, n∈0..29")

    # 3. metallic equation x²=m·x+1: kfib(n+1)² = m·kfib(n+1)·kfib(n) + kfib(n)² + (−1)^n
    for m in range(1, 8):
        for n in range(1, 30):
            lhs = kfib(m, n + 1) ** 2
            rhs = m * kfib(m, n + 1) * kfib(m, n) + kfib(m, n) ** 2 + (1 if n % 2 == 0 else -1)
            if lhs != rhs:
                print(f"  [FAIL] metallicℤ m={m} n={n}"); ok = False
    print("  [OK]   metallic equation x²=m·x+1 (exact up to (−1)^n) for m∈1..7")

    # 4. convergents → metallic_m, and metallic_m = spectral edge of [[m,1],[1,0]].
    for m, name in ((1, "golden φ"), (2, "silver 1+√2"), (3, "bronze (3+√13)/2")):
        metallic = (m + math.sqrt(m * m + 4)) / 2
        conv = kfib(m, 30) / kfib(m, 29)        # a high convergent
        if abs(conv - metallic) > 1e-6:
            print(f"  [FAIL] {name}: convergent {conv} ≠ {metallic}"); ok = False
        # spectral edge of [[m,1],[1,0]]: Δ = m²+4, λ₊ = (m+√Δ)/2
        Δ = Q(m) * Q(m) + 4
        assert Δ == m * m + 4
        slo, shi = sqrt_bracket(Δ, 24)
        loλ, hiλ = (Q(m) + slo) * Q(1, 2), (Q(m) + shi) * Q(1, 2)
        if not (float(loλ) <= metallic <= float(hiλ)):
            print(f"  [FAIL] {name}: spectral edge bracket misses {metallic}"); ok = False
        else:
            print(f"  [OK]   {name} = metallic {m} = spectral edge[[{m},1],[1,0]] (Δ={m*m+4}) ∈ [{float(loλ):.6f},{float(hiλ):.6f}] ∋ {metallic:.6f}")

    print("Phase-B oracle:", "ALL CHECKS PASS" if ok else "FAILED")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
