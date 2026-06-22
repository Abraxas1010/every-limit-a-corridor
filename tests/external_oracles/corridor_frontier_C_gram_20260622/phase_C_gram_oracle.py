#!/usr/bin/env python3
"""Oracle for GramPosDef.agda — the inner product ⟨v,v⟩=Σvⱼ² is positive definite (n=1..6)."""
from fractions import Fraction as Q
import random
def gram(v): return sum(x*x for x in v)
ok_nn=ok_def=True
for n in range(1,7):
    for _ in range(50000):
        v=[Q(random.randint(-6,6),random.randint(1,3)) for _ in range(n)]
        if gram(v) < 0: ok_nn=False                              # ⟨v,v⟩ ≥ 0
        if (gram(v)==0) != all(x==0 for x in v): ok_def=False    # ⟨v,v⟩=0 ⟺ v=0
print("gram-nonneg  ⟨v,v⟩ ≥ 0          (n=1..6):", "PASS" if ok_nn else "FAIL")
print("gram-def     ⟨v,v⟩=0 ⟺ v=0      (n=1..6):", "PASS" if ok_def else "FAIL")
print("ALL", "PASS" if (ok_nn and ok_def) else "FAIL")
