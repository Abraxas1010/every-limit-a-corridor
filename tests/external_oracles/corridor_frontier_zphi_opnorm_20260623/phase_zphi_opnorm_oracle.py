#!/usr/bin/env python3
"""Oracle for ZPhiOperatorNorm — the n×n Z[φ] operator norm via the regular representation.
M=(A,B) for A+Bφ ↦ M̃=[[A,B],[B,A+B]] (2n×2n rational; φ↦[[0,1],[1,1]]).  zphiHouseNorm M = ‖M̃‖ = √ρ(M̃ᵀM̃).
Verify: (1) M̃ is the regular rep (block structure), (2) ‖M̃‖ = max(‖A+Bφ⁺‖, ‖A+Bφ⁻‖) — the house norm,
(3) the rep is a ring hom so M̃ᵀM̃ block structure = (MᵀM)~."""
import numpy as np, random
PHIp=(1+5**0.5)/2; PHIm=(1-5**0.5)/2
def regrep(A,B):
    n=A.shape[0]
    return np.block([[A, B],[B, A+B]])
ok_house=ok_hom=True
for _ in range(100000):
    n=random.randint(1,5)
    A=np.random.randint(-4,5,(n,n)).astype(float); B=np.random.randint(-4,5,(n,n)).astype(float)
    Mt=regrep(A,B)
    norm_reg = np.linalg.norm(Mt, 2)                       # ‖M̃‖ = largest singular value = √ρ(M̃ᵀM̃)
    norm_house = max(np.linalg.norm(A+PHIp*B, 2), np.linalg.norm(A+PHIm*B, 2))
    if abs(norm_reg - norm_house) > 1e-6: ok_house=False
    # ring hom: M̃ᵀM̃ should equal regrep of MᵀM (Z[φ]).  MᵀM = (AᵀA+BᵀB)+(AᵀB+BᵀA+BᵀB)φ
    P = A.T@A + B.T@B ; Q = A.T@B + B.T@A + B.T@B
    if not np.allclose(Mt.T@Mt, regrep(P,Q), atol=1e-7): ok_hom=False
print("‖M̃‖ = max(‖A+Bφ⁺‖,‖A+Bφ⁻‖)  (house norm = both real places):", "PASS" if ok_house else "FAIL")
print("M̃ᵀM̃ = (MᵀM)~  (regular rep is a ring homomorphism)         :", "PASS" if ok_hom else "FAIL")
print("ALL", "PASS" if (ok_house and ok_hom) else "FAIL")
