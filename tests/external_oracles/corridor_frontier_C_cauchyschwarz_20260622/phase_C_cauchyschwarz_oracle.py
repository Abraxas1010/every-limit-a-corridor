#!/usr/bin/env python3
"""Oracle for CauchySchwarz.agda — ⟨u,v⟩² ≤ ⟨u,u⟩·⟨v,v⟩ (vector Cauchy–Schwarz), n=1..7,
plus the auxiliary identity Q = Σ(⟨v,v⟩uᵢ−⟨u,v⟩vᵢ)² = ⟨v,v⟩(⟨u,u⟩⟨v,v⟩−⟨u,v⟩²)."""
from fractions import Fraction as Q
import random
def ip(u,v): return sum(a*b for a,b in zip(u,v))
ok_cs=ok_q=True
for n in range(1,8):
    for _ in range(40000):
        u=[Q(random.randint(-6,6),random.randint(1,3)) for _ in range(n)]
        v=[Q(random.randint(-6,6),random.randint(1,3)) for _ in range(n)]
        uu,uv,vv=ip(u,u),ip(u,v),ip(v,v)
        if uv*uv > uu*vv: ok_cs=False                       # ⟨u,v⟩² ≤ ⟨u,u⟩⟨v,v⟩
        Qs=sum((vv*u[i]-uv*v[i])**2 for i in range(n))      # auxiliary sum of squares
        if Qs != vv*(uu*vv - uv*uv): ok_q=False             # the expansion identity
print("cauchy-schwarz  ⟨u,v⟩² ≤ ⟨u,u⟩·⟨v,v⟩       (n=1..7):", "PASS" if ok_cs else "FAIL")
print("cs-form         Q = ⟨v,v⟩(⟨u,u⟩⟨v,v⟩−⟨u,v⟩²) (n=1..7):", "PASS" if ok_q else "FAIL")
print("ALL", "PASS" if (ok_cs and ok_q) else "FAIL")
