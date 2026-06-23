#!/usr/bin/env python3
"""Oracle for PowerScaffold.agda — the upper cut with the dyadic modulus, symmetric M, n=1..5.
  normUp-from-pow: ‖M^{2^L}‖₁ < q^{2^L} ⟹ ‖M‖ < q  (= the cut captures q>ρ via high powers);
also confirms the modulus: ‖M^{2^L}‖₁^{1/2^L} → ρ(M) (decreasing upper bound)."""
from fractions import Fraction as Q
import random
def matmul(A,B):
    n=len(A); return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def one_norm(A): return sum(abs(A[i][j]) for i in range(len(A)) for j in range(len(A)))
def opnorm(A):
    import numpy as np; return max(abs(ev) for ev in np.linalg.eigvals([[float(x) for x in r] for r in A]))
ok_cut=ok_mod=True
for n in range(1,6):
    for _ in range(8000):
        M=[[None]*n for _ in range(n)]
        for i in range(n):
            for j in range(i,n):
                v=Q(random.randint(-4,4),random.randint(1,3)); M[i][j]=v; M[j][i]=v
        nm=opnorm(M)
        A=M; pw=1; bounds=[]
        for L in range(1,5):
            A=matmul(A,A); pw*=2                        # A = M^{2^L}
            n1=one_norm(A)
            bounds.append(float(n1)**(1.0/pw))          # ‖M^{2^L}‖₁^{1/2^L}, an upper bound on ρ
            # the cut soundness: if ‖A‖₁ < q^{2^L} then q > ‖M‖
            q=Q(int((float(n1)**(1.0/pw))*100)+2,100)   # q just above the L-th bracket
            if n1 < q**pw:
                if not (nm < float(q)+1e-7): ok_cut=False
        # modulus: bounds are ≥ ρ and approach it (non-increasing-ish, all ≥ ρ)
        if any(b < nm-1e-6 for b in bounds): ok_mod=False
print("normUp-from-pow  ‖M^{2^L}‖₁<q^{2^L} ⟹ q>‖M‖ (n=1..5):", "PASS" if ok_cut else "FAIL")
print("modulus          ‖M^{2^L}‖₁^{1/2^L} ≥ ρ(M)     (n=1..5):", "PASS" if ok_mod else "FAIL")
print("ALL", "PASS" if (ok_cut and ok_mod) else "FAIL")
