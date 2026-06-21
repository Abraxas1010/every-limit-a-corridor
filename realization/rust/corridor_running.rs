// corridor_running.rs — a Rust realization of the running-convergent construction.
//
// A second substrate (besides the cubical-Agda kernel) that EXECUTES the same
// brackets and checks the same theorems the Agda proves, from first principles:
//   - the golden convergent brackets lo n = F_{2n+2}/F_{2n+1}, hi n = F_{2n+3}/F_{2n+2}
//   - Cassini  F_{k+1}^2 - F_k F_{k+2} = (-1)^k       (Cassini.agda)
//   - width = 1/(F_{2n+1} F_{2n+2})                   (Bracket.width)
//   - non-degeneracy, nesting, forcing                (Ordered/Located/Forcing)
//   - the golden equation lo^2 < lo+1 < hi+1 < hi^2   (LocatedLaw)
//   - the Dedekind cut  lo m < hi n  for all m,n      (CrossCut)
//   - sqrt2 via Pell  p^2 - 2q^2 = (-1)^{n+1}         (CertifiedSqrt2)
//
// All comparisons are exact (cross-multiplied i128), never floating point —
// matching the Agda's integer-level proofs.  Build:  rustc -O corridor_running.rs
//
// Aligned with heyting-imm corpus/cubical_agda/Corridor/Running/ (cubical pin d684d7d8).

type Z = i128;

// Fibonacci: F_0=0, F_1=1, ...
fn fib(n: u32) -> Z {
    let (mut a, mut b): (Z, Z) = (0, 1);
    for _ in 0..n { let t = a + b; a = b; b = t; }
    a
}

// a rational as (num, den) with den > 0
#[derive(Clone, Copy)]
struct Q { n: Z, d: Z }

impl Q {
    fn lt(self, o: Q) -> bool { self.n * o.d < o.n * self.d } // exact cross-mult
    fn sq(self) -> Q { Q { n: self.n * self.n, d: self.d * self.d } }
    fn add_one(self) -> Q { Q { n: self.n + self.d, d: self.d } } // a/b + 1 = (a+b)/b
}

fn lo(n: u32) -> Q { Q { n: fib(2 * n + 2), d: fib(2 * n + 1) } }
fn hi(n: u32) -> Q { Q { n: fib(2 * n + 3), d: fib(2 * n + 2) } }
fn width(n: u32) -> Q { Q { n: 1, d: fib(2 * n + 1) * fib(2 * n + 2) } }

// Pell convergents to sqrt2: (p,q) -> (p+2q, p+q), from 1/1
fn pell(n: u32) -> (Z, Z) {
    let (mut p, mut q): (Z, Z) = (1, 1);
    for _ in 0..n { let (pp, qq) = (p + 2 * q, p + q); p = pp; q = qq; }
    (p, q)
}

fn main() {
    // 1. the bracket REDUCES to the stated rationals (the Agda refl certs)
    assert!(lo(1).n == 3 && lo(1).d == 2, "lo 1 = 3/2");
    assert!(hi(1).n == 5 && hi(1).d == 3, "hi 1 = 5/3");
    assert!(width(1).n == 1 && width(1).d == 6, "width 1 = 1/6 = 1/(F3 F4)");

    let nmax: u32 = 24; // i128-safe (squares of F_~50 stay below 1.7e38)

    // 2. Cassini  F_{k+1}^2 - F_k F_{k+2} = (-1)^k
    for k in 0..40u32 {
        let lhs = fib(k + 1) * fib(k + 1) - fib(k) * fib(k + 2);
        assert!(lhs == if k % 2 == 0 { 1 } else { -1 }, "Cassini k={}", k);
    }

    // 3. width is Cassini-exact, and the family closes (forcing): denom unbounded
    for n in 0..nmax {
        let w = width(n);
        assert!(w.n == 1 && w.d == fib(2 * n + 1) * fib(2 * n + 2), "exact width n={}", n);
        assert!((n as Z) < w.d, "forcing: denom > n at n={}", n); // M < denom M
    }

    // 4. non-degeneracy + nesting:  lo n < lo(n+1) < hi(n+1) < hi n
    for n in 0..nmax {
        assert!(lo(n).lt(hi(n)), "lo<hi n={}", n);
        assert!(lo(n).lt(lo(n + 1)), "lo increasing n={}", n);
        assert!(hi(n + 1).lt(hi(n)), "hi decreasing n={}", n);
        assert!(lo(n + 1).lt(hi(n + 1)), "nested n={}", n);
    }

    // 5. the golden equation x^2 = x + 1, by squeezing:  lo^2 < lo+1 < hi+1 < hi^2
    for n in 0..nmax {
        assert!(lo(n).sq().lt(lo(n).add_one()), "golden-lower n={}", n);
        assert!(hi(n).add_one().lt(hi(n).sq()), "golden-upper n={}", n);
        // exact integer golden identity F_{n+1}^2 = F_{n+1}F_n + F_n^2 + (-1)^n
        // (the convergent F_{n+1}/F_n satisfies x^2 = x+1 up to (-1)^n / F_n^2)
        let s = if n % 2 == 0 { 1 } else { -1 };
        assert!(fib(n + 1) * fib(n + 1) == fib(n + 1) * fib(n) + fib(n) * fib(n) + s,
                "goldenZ n={}", n);
    }

    // 6. the Dedekind cut:  lo m < hi n  for ALL m, n
    for m in 0..nmax { for n in 0..nmax {
        assert!(lo(m).lt(hi(n)), "cut lo({}) < hi({})", m, n);
    }}

    // 7. sqrt2 via Pell:  p/q bracket sqrt2, Pell-Cassini, even<=sqrt2<=odd
    let (mut pp, mut pq): (Z, Z) = (1, 1);
    for n in 0..28u32 {
        let (p, q) = pell(n);
        assert!((p, q) == (pp, pq), "pell recurrence n={}", n);
        assert!(p * p - 2 * q * q == if (n + 1) % 2 == 0 { 1 } else { -1 }, "Pell-Cassini n={}", n);
        if n % 2 == 0 { assert!(p * p <= 2 * q * q, "below sqrt2 n={}", n); }   // belowSq
        else          { assert!(2 * q * q <= p * p, "above sqrt2 n={}", n); }   // aboveSq
        let (np, nq) = (pp + 2 * pq, pp + pq); pp = np; pq = nq;
    }
    assert!(pell(1) == (3, 2) && pell(3) == (17, 12), "pell 3/2, 17/12");

    println!("corridor_running (Rust realization): ALL CHECKS PASS");
    println!("  golden phi: lo 1 = {}/{}, hi 1 = {}/{}, width = 1/{}",
             lo(1).n, lo(1).d, hi(1).n, hi(1).d, width(1).d);
    println!("  Cassini exact; non-degenerate + nested + forced for n<{}; golden x^2=x+1 squeeze;", nmax);
    println!("  Dedekind cut lo m < hi n for all m,n<{}; sqrt2 Pell bracket certified.", nmax);
}
