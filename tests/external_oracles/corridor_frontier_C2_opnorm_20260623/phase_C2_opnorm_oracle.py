#!/usr/bin/env python3
"""Oracle for OperatorNormReal/SqrtRealR — the ℝ-completed operator norm of ANY (non-symmetric) rational
matrix: ‖M‖ = √ρ(MᵀM) = largest singular value.  The cut L = {q | q<0 ∨ q² ∈ L(ρ(MᵀM))} brackets ‖M‖,
which equals numpy's spectral 2-norm.  Genuinely non-symmetric M tested, n=1..5."""
from fractions import Fraction as Q
import random, numpy as np
ok_eq=ok_cut=ok_sqrt=True
for n in range(1,6):
    for _ in range(8000):
        M=[[Q(random.randint(-6,6),random.randint(1,3)) for _ in range(n)] for _ in range(n)]
        Mf=np.array([[float(x) for x in r] for r in M])
        opnorm=np.linalg.norm(Mf,2)                    # largest singular value
        MtM=[[sum(M[k][i]*M[k][j] for k in range(n)) for j in range(n)] for i in range(n)]   # MᵀM
        rho=max(abs(e) for e in np.linalg.eigvalsh([[float(x) for x in r] for r in MtM]))    # ρ(MᵀM)
        if abs(opnorm**2 - rho) > 1e-6: ok_eq=False     # ‖M‖² = ρ(MᵀM)
        if abs(opnorm - rho**0.5) > 1e-6: ok_sqrt=False # ‖M‖ = √ρ(MᵀM)
        # sqrtRealℝ cut: q ∈ L(‖M‖) iff q<0 or q² < ρ(MᵀM)
        for _ in range(2):
            q=Q(random.randint(-8,12),random.randint(1,3))
            inL = (q<0) or (float(q*q) < rho)
            if inL and not (float(q) < opnorm+1e-7): ok_cut=False
print("‖M‖² = ρ(MᵀM)              (non-symmetric M, n=1..5):", "PASS" if ok_eq else "FAIL")
print("‖M‖ = √ρ(MᵀM) = numpy 2-norm                       :", "PASS" if ok_sqrt else "FAIL")
print("sqrtRealℝ cut q∈L iff q²<ρ brackets ‖M‖            :", "PASS" if ok_cut else "FAIL")
print("ALL", "PASS" if (ok_eq and ok_sqrt and ok_cut) else "FAIL")
