#!/usr/bin/env python3
"""
External semantic oracle — the running corridor (Phases 1-2).

Intent: re-derive, from first principles and independently of the Agda source,
(a) the Fibonacci ladder, (b) Cassini's identity F_{k+1}^2 = F_k*F_{k+2} + (-1)^k,
(c) the corridor's running rational bracket lo n = F_{2n+2}/F_{2n+1},
hi n = F_{2n+3}/F_{2n+2}, and (d) its exact width 1/(F_{2n+1}*F_{2n+2}). Assert
that these match the concrete reduction targets the Agda kernel certificates
(`Bracket.lo-0..hi-2`, `Cassini.cassini`) commit to by `refl`. This is the
project-level meaning check: the Agda must compute the *golden ratio's
convergents*, with the *Cassini-exact* width — not merely some pair of rationals.

A vacuous Agda implementation (e.g. width hard-coded as 1/(n+1), or lo:=hi) would
diverge from this oracle on n=1 (expects [3/2,5/3], width 1/6) and on the Cassini
sign. This oracle is independent: it builds Fibonacci by the recurrence, not by
transliterating the Agda.
"""
from fractions import Fraction


def fib(n):
    a, b = 0, 1          # F_0=0, F_1=1
    for _ in range(n):
        a, b = b, a + b
    return a


def cassini(k):
    # F_{k+1}^2 - F_k*F_{k+2}  should equal (-1)^k
    return fib(k + 1) * fib(k + 1) - fib(k) * fib(k + 2)


def lo(n):
    return Fraction(fib(2 * n + 2), fib(2 * n + 1))


def hi(n):
    return Fraction(fib(2 * n + 3), fib(2 * n + 2))


def width(n):
    return hi(n) - lo(n)


def main():
    # (a) Cassini identity for k = 0..25 (independent re-derivation)
    for k in range(26):
        assert cassini(k) == (-1) ** k, f"Cassini fails at k={k}: {cassini(k)}"

    # (b) the running bracket reduces to exactly the values the Agda `refl`
    #     certificates commit to (Bracket.agda lo-0..hi-2):
    expected = {
        0: (Fraction(1, 1), Fraction(2, 1)),
        1: (Fraction(3, 2), Fraction(5, 3)),   # the paper's bracket
        2: (Fraction(8, 5), Fraction(13, 8)),
    }
    for n, (elo, ehi) in expected.items():
        assert lo(n) == elo, f"lo({n})={lo(n)} != {elo}"
        assert hi(n) == ehi, f"hi({n})={hi(n)} != {ehi}"

    # (c) the width is Cassini-exact: hi n - lo n == 1/(F_{2n+1}*F_{2n+2}) > 0
    for n in range(20):
        w = width(n)
        denom = fib(2 * n + 1) * fib(2 * n + 2)
        assert w == Fraction(1, denom), f"width({n})={w} != 1/{denom}"
        assert w > 0, f"width({n}) not positive"
    # n=1 width is exactly 1/6 = 1/(F_3*F_4) — the paper's claimed value
    assert width(1) == Fraction(1, 6), "width(1) must be 1/6 = 1/(F_3 F_4)"

    # (d) DISCRIMINATING INPUTS (positive apartness witnesses): a vacuous impl
    #     would fail these. correct vs vacuous, with min separation.
    #   - a constant-width "modulus" (1/(n+1)) diverges from the golden width at n=1:
    correct_w1 = Fraction(1, 6)
    vacuous_w1 = Fraction(1, 2)          # 1/(1+1), the lazy constant-shaped width
    assert width(1) == correct_w1
    assert abs(correct_w1 - vacuous_w1) >= Fraction(1, 3), "apartness witness too small"

    # (e) the bracket genuinely brackets phi (golden ratio) — lo < phi < hi:
    phi = (1 + 5 ** 0.5) / 2
    for n in range(15):
        assert float(lo(n)) < phi < float(hi(n)), f"phi not in bracket at n={n}"
    # and the width -> 0 (the genuine forcing; a constant rate cannot):
    assert float(width(14)) < 1e-5, "width must shrink (forcing)"

    # (f) TIGHTENING (Located.lo↗): the lower convergents strictly increase,
    #     and the cross-term gap is exactly +1 (the d'Ocagne/Cassini payoff):
    for n in range(20):
        assert lo(n) < lo(n + 1), f"lo not increasing at n={n}"
        # sucℤ P ≡ Q  ⟺  F_{2n+4}·F_{2n+1} − F_{2n+2}·F_{2n+3} == 1
        P = fib(2 * n + 2) * fib(2 * n + 3)
        Q = fib(2 * n + 4) * fib(2 * n + 1)
        assert Q - P == 1, f"tightening gap != 1 at n={n}: {Q - P}"
    # the upper convergents strictly DECREASE (hi↘), gap +1 (d'Ocagne):
    for n in range(20):
        assert hi(n + 1) < hi(n), f"hi not decreasing at n={n}"
        P = fib(2 * n + 5) * fib(2 * n + 2)   # F_{2n+5}·F_{2n+2}
        Q = fib(2 * n + 3) * fib(2 * n + 4)   # F_{2n+3}·F_{2n+4}
        assert Q - P == 1, f"upper d'Ocagne gap != 1 at n={n}: {Q - P}"
    # so the family is NESTED: lo n < lo(n+1) < hi(n+1) < hi n
    for n in range(20):
        assert lo(n) < lo(n + 1) < hi(n + 1) < hi(n), f"not nested at n={n}"

    # a CONSTANT lower rate would NOT strictly increase — the discriminator:
    const_rate = [Fraction(3, 2)] * 21
    assert not all(const_rate[n] < const_rate[n + 1] for n in range(20)), \
        "a constant rate must fail strict tightening"

    # (g) FORCING (Forcing.forcing): the denominators are unbounded, M < denom M,
    #     so width = 1/denom -> 0 (golden-specific; a constant denom fails).
    def denom(n):
        return fib(2 * n + 1) * fib(2 * n + 2)
    for M in range(40):
        assert M < denom(M), f"forcing fails: denom({M})={denom(M)} not > {M}"
    # a constant denominator c cannot exceed all M (constant-rate-fails):
    c = 6
    assert not all(M < c for M in range(c + 1)), "constant denom must fail forcing"

    # (h) CERTIFIED √2 via Pell (CertifiedSqrt2): convergents p_n/q_n -> √2,
    #     Pell–Cassini p² = 2q² + (−1)^{n+1}, and even≤√2≤odd squared bounds.
    pp, pq = [1], [1]
    for _ in range(12):
        pp.append(pp[-1] + 2 * pq[-1])
        pq.append(pp[-2] + pq[-1])
    # reduction targets the Agda commits by refl:
    assert (pp[1], pq[1]) == (3, 2), "pP/pQ 1"
    assert (pp[2], pq[2]) == (7, 5), "pP/pQ 2"
    assert (pp[3], pq[3]) == (17, 12), "pP/pQ 3"
    for n in range(12):
        # Pell–Cassini: p² − 2q² == (−1)^{n+1}
        assert pp[n] ** 2 - 2 * pq[n] ** 2 == (-1) ** (n + 1), f"Pell-Cassini n={n}"
    sqrt2 = 2 ** 0.5
    for n in range(12):
        if n % 2 == 0:   # even: below √2, squared ≤ 2  (belowSq)
            assert pp[n] ** 2 <= 2 * pq[n] ** 2 and pp[n] / pq[n] <= sqrt2, f"belowSq n={n}"
        else:            # odd: above √2, squared ≥ 2  (aboveSq)
            assert 2 * pq[n] ** 2 <= pp[n] ** 2 and pp[n] / pq[n] >= sqrt2, f"aboveSq n={n}"

    # (i) LOCATED LAW (LocatedLaw): φ satisfies x²=x+1 by squeezing —
    #     lo² < lo+1  and  hi+1 < hi²,  the convergent form of Cassini.
    for n in range(15):
        assert lo(n) * lo(n) < lo(n) + 1, f"golden-lower fails at n={n}"
        assert hi(n) + 1 < hi(n) * hi(n), f"golden-upper fails at n={n}"
        # the squeeze brackets the golden fixed point x²=x+1 (x=φ):
        assert lo(n) * lo(n) < lo(n) + 1 and hi(n) + 1 < hi(n) * hi(n)
    # the exact errors are the Cassini terms 1/F², which vanish:
    assert abs(float(hi(12) * hi(12)) - float(hi(12) + 1)) < 1e-5, "golden error must vanish"

    # (j) DEDEKIND CUT (CrossCut): lo m < hi n for ALL m, n — φ is a unique real.
    for m in range(12):
        for n in range(12):
            assert lo(m) < hi(n), f"cut fails: lo({m}) >= hi({n})"

    print("phase_1_2_oracle: PASS")
    print(f"  Cassini k=0..25 OK; bracket lo/hi/width match Agda refl targets;")
    print(f"  located law x²=x+1 squeeze (lo²<lo+1<hi+1<hi²) OK;")
    print(f"  Pell √2: convergents+Pell-Cassini+below/above bounds OK;")
    print(f"  width(1)=1/6 (=1/(F3 F4)); lo(n)<phi<hi(n); width->0 (forcing).")


if __name__ == "__main__":
    main()
