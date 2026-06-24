#!/usr/bin/env python3
"""Oracle for ZPhiMatrix — the Z[φ] matrix pair arithmetic, faithful to Z[φ] multiplication.
A Z[φ]-matrix is (A,B) for A+Bφ.  zφMul (A,B)(C,D) = (AC+BD, AD+BC+BD) [φ²=φ+1].  The Agda `prodExpand`
proves the entrywise golden reduction; this verifies the full ∑-lift (eval(zφMul s s')=eval s · eval s')
on random matrices at BOTH golden embeddings φ⁺=(1+√5)/2 and φ⁻=(1−√5)/2, and that zφSq = repeated square."""
import numpy as np, random
PHIp=(1+5**0.5)/2; PHIm=(1-5**0.5)/2
def zfMul(A,B,C,D):                       # (A+Bφ)(C+Dφ) = (AC+BD)+(AD+BC+BD)φ
    return (A@C + B@D, A@D + B@C + B@D)
def ev(A,B,t): return A + t*B
ok_mul=ok_sq=True
for _ in range(200000):
    n=random.randint(1,5)
    A,B,C,D=[np.random.randint(-4,5,(n,n)).astype(float) for _ in range(4)]
    P,Q=zfMul(A,B,C,D)
    for t in (PHIp,PHIm):                 # faithful at BOTH real embeddings (t²=t+1)
        if not np.allclose(ev(P,Q,t), ev(A,B,t)@ev(C,D,t), atol=1e-7): ok_mul=False
    # zφSq = zφMul s s = repeated squaring (what specRadius runs on)
    Ps,Qs=zfMul(A,B,A,B)
    for t in (PHIp,PHIm):
        if not np.allclose(ev(Ps,Qs,t), ev(A,B,t)@ev(A,B,t), atol=1e-7): ok_sq=False
print("zφMul faithful: eval(zφMul s s') = eval s · eval s' (φ⁺,φ⁻):", "PASS" if ok_mul else "FAIL")
print("zφSq  faithful: eval(zφSq s) = eval s · eval s   (squaring)  :", "PASS" if ok_sq else "FAIL")
print("ALL", "PASS" if (ok_mul and ok_sq) else "FAIL")
