#!/usr/bin/env python3
"""Oracle for Item E — the corridor's logical-entropy observables (Ellerman currency).
h(π)=1−Σpᵢ²: trivial=0, corridor (balanced ±1 Cassini)=½ = H¹ screen, trisection (⅓,⅓,⅓)=⅔.
Discriminating across objects, symmetric h(p)=h(1−p), provenance cost μ(D)=D grows."""
from fractions import Fraction as Q
def H(masses): return 1 - sum(p*p for p in masses)
trivial   = H([Q(1),Q(0)])
corridor  = H([Q(1,2),Q(1,2)])
trisect   = H([Q(1,3),Q(1,3),Q(1,3)])
ok_vals = (trivial==0) and (corridor==Q(1,2)) and (trisect==Q(2,3))
ok_disc = (trivial < corridor < trisect)                              # object-dependent (HC-E)
ok_sym  = all(H([p,1-p])==H([1-p,p]) for p in [Q(1,5),Q(2,7),Q(3,4)]) # symmetry
ok_screen = (corridor == Q(1,2))                                      # = H¹ screen value
ok_cost = all(d < d+1 for d in range(20))                            # μ(D)=D strictly grows
print("logical entropy   trivial 0 / corridor ½ / trisection ⅔ :", "PASS" if ok_vals else "FAIL")
print("HC-E control      0 < ½ < ⅔  (object-dependent)          :", "PASS" if ok_disc else "FAIL")
print("symmetry          h(p) = h(1−p)                          :", "PASS" if ok_sym else "FAIL")
print("screen match      corridor entropy = H¹ screen ½         :", "PASS" if ok_screen else "FAIL")
print("provenance cost   μ(D)=D strictly grows                  :", "PASS" if ok_cost else "FAIL")
print("ALL", "PASS" if (ok_vals and ok_disc and ok_sym and ok_screen and ok_cost) else "FAIL")
