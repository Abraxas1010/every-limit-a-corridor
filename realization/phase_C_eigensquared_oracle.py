#!/usr/bin/env python3
"""Phase-C external oracle — the algebraic core of the C*-identity ‖M²‖=‖M‖².

Checks `eigenSquared`: for a symmetric 2×2 matrix M=[[a,b],[b,d]], if λ satisfies
the characteristic equation  λ² = (a+d)λ − (ad−b²),  then μ=λ² satisfies M²'s
characteristic equation  μ² = tr(M²)·μ − det(M²),  with tr(M²)=a²+2b²+d² and
det(M²)=(ad−b²)².  This is "λ eigenvalue of M ⟹ λ² eigenvalue of M²".

Verified symbolically (sympy if available) AND on concrete rational matrices,
including the spectral-edge eigenvalues from Phases A/F (φ, the [[2,1],[1,2]] case).
"""
from fractions import Fraction as Q
import math, sys

def charM(a, b, d, l):   # λ² − ((a+d)λ − (ad−b²))
    return l * l - ((a + d) * l - (a * d - b * b))

def traceSq(a, b, d): return a * a + 2 * (b * b) + d * d
def detSq(a, b, d):   return (a * d - b * b) ** 2
def charM2(a, b, d, mu):  # μ² − (tr(M²)μ − det(M²))
    return mu * mu - (traceSq(a, b, d) * mu - detSq(a, b, d))

def main() -> int:
    ok = True
    # 1. symbolic identity (if sympy present): charM(λ)=0 ⟹ charM2(λ²)=0, via factorisation.
    try:
        import sympy as sp
        a, b, d, l = sp.symbols("a b d l")
        quartic = (l*l)*(l*l) - (traceSq(a, b, d) * (l*l) - detSq(a, b, d))
        f1 = (l*l) - (a + d) * l + (a * d - b * b)      # charpoly_M(λ)
        f2 = (l*l) + (a + d) * l + (a * d - b * b)
        if sp.expand(quartic - f1 * f2) != 0:
            print("  [FAIL] quartic factorisation charM·cofactor is wrong"); ok = False
        else:
            print("  [OK]   symbolic: λ⁴ − tr(M²)λ² + det(M²) = charpoly_M(λ)·(λ²+trλ+det)")
    except ImportError:
        print("  [note] sympy absent; symbolic factorisation check skipped")

    # 2. concrete rational matrices with rational eigenvalues.
    cases = [
        # (a, b, d, eigenvalues)
        (Q(2), Q(1), Q(2), [Q(3), Q(1)]),     # M²=[[5,4],[4,5]], eig 9,1
        (Q(3), Q(2), Q(3), [Q(5), Q(1)]),     # eig (6±√(0+16))/2 = 5,1
        (Q(5), Q(0), Q(2), [Q(5), Q(2)]),     # diagonal-ish, eig 5,2
        (Q(1), Q(2), Q(1), [Q(3), Q(-1)]),    # eig (2±4)/2 = 3,−1
    ]
    for a, b, d, eigs in cases:
        for l in eigs:
            if charM(a, b, d, l) != 0:
                print(f"  [FAIL] {l} not an eigenvalue of [[{a},{b}],[{b},{d}]]"); ok = False
            if charM2(a, b, d, l * l) != 0:   # eigenSquared: λ² is an eigenvalue of M²
                print(f"  [FAIL] eigenSquared: {l}²={l*l} not eigenvalue of M²"); ok = False
        print(f"  [OK]   [[{a},{b}],[{b},{d}]]: eigenvalues {[str(e) for e in eigs]} → squares {[str(e*e) for e in eigs]} are eigenvalues of M²")

    # 3. tie to Phase A/F: φ is an eigenvalue of [[1,1],[1,0]] (the Fibonacci matrix);
    #    φ² is an eigenvalue of its square [[2,1],[1,1]] (the φ² spectral demo).
    phi = (1 + math.sqrt(5)) / 2
    a, b, d = 1.0, 1.0, 0.0
    assert abs(charM(a, b, d, phi)) < 1e-9, "φ eigenvalue of [[1,1],[1,0]]"
    assert abs(charM2(a, b, d, phi * phi)) < 1e-9, "φ² eigenvalue of [[1,1],[1,0]]²"
    print(f"  [OK]   φ={phi:.6f} eigenvalue of [[1,1],[1,0]]; φ²={phi*phi:.6f} eigenvalue of its square (ties A/F)")

    # 4. C3 — the operator-norm C*-identity ‖M²‖=‖M‖² for the spectral edge.
    #    disc(M²)=(a+d)²·disc(M), and the spectral-edge bracket scales by (a+d).
    def disc(a, b, d): return (a - d) ** 2 + 4 * b * b
    def specedge(a, b, d): return ((a + d) + math.sqrt(disc(a, b, d))) / 2
    for a, b, d in ((Q(2), Q(1), Q(1)), (Q(3), Q(2), Q(1)), (Q(1), Q(1), Q(0)), (Q(5), Q(2), Q(3))):
        a2, b2, d2 = a * a + b * b, b * (a + d), b * b + d * d   # M² entries
        # (i) discriminant identity (exact, rational)
        if disc(a2, b2, d2) != (a + d) ** 2 * disc(a, b, d):
            print(f"  [FAIL] disc(M²) ≠ (a+d)²·disc(M) for [[{a},{b}],[{b},{d}]]"); ok = False
        # (ii) the C*-identity at the value level: specEdge(M²) = specEdge(M)²
        lhs, rhs = specedge(float(a2), float(b2), float(d2)), specedge(float(a), float(b), float(d)) ** 2
        if abs(lhs - rhs) > 1e-9:
            print(f"  [FAIL] specEdge(M²)={lhs} ≠ specEdge(M)²={rhs}"); ok = False
        else:
            print(f"  [OK]   C*-identity [[{a},{b}],[{b},{d}]]: disc(M²)=(a+d)²disc(M); ‖M²‖={lhs:.5f}=‖M‖²")

    # 5. C beyond the principal case — the NON-PSD magnitude norm ‖M‖=max(|λ₊|,|λ₋|)
    #    = (|a+d|+√Δ)/2.  The C*-identity ‖M²‖=‖M‖² holds for indefinite M too,
    #    because disc(M²)=(a+d)²·disc(M) is sign-agnostic ((a+d)²=|a+d|²).
    def specradius(a, b, d): return (abs(a + d) + math.sqrt(disc(a, b, d))) / 2
    indefinite = [(Q(1), Q(2), Q(1)),    # eig 3,−1 (indefinite): ‖M‖=3
                  (Q(0), Q(1), Q(0)),    # eig 1,−1: ‖M‖=1
                  (Q(-2), Q(1), Q(-3)),  # tr<0: ‖M‖=|λ₋|
                  (Q(-5), Q(0), Q(1))]   # diagonal indefinite
    for a, b, d in indefinite:
        a2, b2, d2 = a * a + b * b, b * (a + d), b * b + d * d
        # |a+d| scaling of the √Δ bracket is the certified content (cstarBracketAbs):
        if disc(a2, b2, d2) != (a + d) ** 2 * disc(a, b, d):     # sign-agnostic
            print(f"  [FAIL] non-PSD disc(M²)≠(a+d)²disc(M) [[{a},{b}],[{b},{d}]]"); ok = False
        lhs, rhs = specradius(float(a2), float(b2), float(d2)), specradius(float(a), float(b), float(d)) ** 2
        if abs(lhs - rhs) > 1e-9:
            print(f"  [FAIL] non-PSD ‖M²‖={lhs} ≠ ‖M‖²={rhs} for [[{a},{b}],[{b},{d}]]"); ok = False
        else:
            print(f"  [OK]   non-PSD [[{a},{b}],[{b},{d}]] (tr={a+d}): spectral radius ‖M²‖={lhs:.5f}=‖M‖² (|a+d| scaling)")

    # 6. the adjoint C*-bridge ‖Mx‖²=⟨M*Mx,x⟩ (any 2×2 M, any x) — toward general n×n.
    def normMx_sq(a, b, c, d, x0, x1):
        return (a * x0 + b * x1) ** 2 + (c * x0 + d * x1) ** 2
    def adjForm(a, b, c, d, x0, x1):   # ⟨MᵀM x, x⟩
        return (x0 * ((a * a + c * c) * x0 + (a * b + c * d) * x1)
                + x1 * ((a * b + c * d) * x0 + (b * b + d * d) * x1))
    adj_ok = True
    for (a, b, c, d) in ((Q(1), Q(2), Q(3), Q(4)), (Q(2), Q(-1), Q(0), Q(5)), (Q(1), Q(1), Q(1), Q(0))):
        for (x0, x1) in ((Q(1), Q(0)), (Q(1), Q(1)), (Q(2), Q(-3)), (Q(-1), Q(4))):
            if normMx_sq(a, b, c, d, x0, x1) != adjForm(a, b, c, d, x0, x1):
                print(f"  [FAIL] ‖Mx‖²≠⟨M*Mx,x⟩ M=[[{a},{b}],[{c},{d}]] x=({x0},{x1})"); adj_ok = ok = False
    if adj_ok:
        print("  [OK]   adjoint C*-bridge ‖Mx‖²=⟨M*Mx,x⟩ for arbitrary 2×2 M and x (any M, toward n×n)")

    # 7. the GENERAL-n adjoint bridge ⟨Mx,Mx⟩=⟨MᵀM·x,x⟩ (AdjointFormN, all dimensions).
    def matvec(M, x): return [sum(M[i][j] * x[j] for j in range(len(x))) for i in range(len(M))]
    def dot(u, v): return sum(a * b for a, b in zip(u, v))
    def transp(M): return [[M[j][i] for j in range(len(M))] for i in range(len(M[0]))]
    def matmul(A, B): return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
    nd_ok = True
    mats = [
        [[Q(1), Q(2), Q(0)], [Q(2), Q(3), Q(1)], [Q(0), Q(1), Q(4)]],          # 3×3
        [[Q(2), Q(-1), Q(0), Q(1)], [Q(-1), Q(3), Q(2), Q(0)],
         [Q(0), Q(2), Q(1), Q(-2)], [Q(1), Q(0), Q(-2), Q(5)]],                # 4×4 symmetric
        [[Q(1), Q(2), Q(3)], [Q(0), Q(1), Q(4)], [Q(5), Q(0), Q(1)]],          # 3×3 NON-symmetric
    ]
    vecs3 = [[Q(1), Q(0), Q(0)], [Q(1), Q(1), Q(1)], [Q(2), Q(-1), Q(3)]]
    vecs4 = [[Q(1), Q(1), Q(1), Q(1)], [Q(2), Q(0), Q(-1), Q(3)]]
    for M in mats:
        vs = vecs4 if len(M) == 4 else vecs3
        MtM = matmul(transp(M), M)
        for x in vs:
            Mx = matvec(M, x)
            if dot(Mx, Mx) != dot(matvec(MtM, x), x):     # ‖Mx‖² = ⟨MᵀM x, x⟩
                print(f"  [FAIL] n={len(M)} adjoint bridge ⟨Mx,Mx⟩≠⟨MᵀMx,x⟩"); nd_ok = ok = False
    if nd_ok:
        print("  [OK]   general-n adjoint bridge ⟨Mx,Mx⟩=⟨MᵀM·x,x⟩ for n=3,4 (incl. non-symmetric)")

    print("Phase-C oracle:", "ALL CHECKS PASS" if ok else "FAILED")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
