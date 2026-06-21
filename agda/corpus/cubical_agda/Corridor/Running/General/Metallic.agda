{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE METALLIC FAMILY — every quadratic x² = m·x + 1 is a running corridor.
--
-- The golden ratio (m=1) is one member of a family: the metallic ratios
--   metallic m = (m + √(m²+4))/2,   the positive root of  x² = m·x + 1.
-- m=1 → golden φ, m=2 → silver 1+√2, m=3 → bronze (3+√13)/2, …  Each is the
-- limit of the m-Fibonacci convergents  kfib(n+1)/kfib(n)  with recurrence
-- kfib(n+2) = m·kfib(n+1) + kfib(n).  The KEY INSIGHT — the one reusable lego —
-- is that the Cassini ±1 is m-INDEPENDENT: it is det[[m,1],[1,0]] = −1, the same
-- for every m.  So a SINGLE induction proves Cassini for the whole family, and
-- the metallic equation x²=mx+1 holds for the convergents up to (−1)^n / kfib(n)².
-- This generalises the Fibonacci `Cassini`/`LocatedLaw` from one root to all of
-- the metallic ratios — the general theory the φ-construction was a seed for.
--
module corpus.cubical_agda.Corridor.Running.General.Metallic where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int using (ℤ; pos; _+_; _·_; -_)
open import Cubical.Data.Int.Properties using (·IdL)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Tactics.CommRingSolver using (solve!)
open import corpus.cubical_agda.Corridor.Running.Cassini using (fibℤ; altSign)

-- ── the m-Fibonacci ladder (m = the metallic parameter) ─────────────────────
kfib : (m : ℤ) → ℕ → ℤ
kfib m zero          = pos 0
kfib m (suc zero)    = pos 1
kfib m (suc (suc n)) = (m · kfib m (suc n)) + kfib m n

-- ── CASSINI FOR THE WHOLE FAMILY:  kfib(n+1)² = kfib(n)·kfib(n+2) + (−1)^n ──
-- The proof is the Fibonacci induction with `b+a` replaced by `m·b+a`; the ±1
-- survives unchanged because the determinant is m-independent.
kCassini : (m : ℤ) (n : ℕ)
         → kfib m (suc n) · kfib m (suc n)
         ≡ kfib m n · kfib m (suc (suc n)) + altSign n
kCassini m zero    = refl
kCassini m (suc n) = ringId ∙ cong (λ z → b · ((m · (m · b + a)) + b) + z) widthNum
  where
    a b s : ℤ
    a = kfib m n
    b = kfib m (suc n)
    s = altSign n
    ih : b · b ≡ a · (m · b + a) + s
    ih = kCassini m n
    ringId : (m · b + a) · (m · b + a)
           ≡ b · ((m · (m · b + a)) + b) + (a · (m · b + a) + (- (b · b)))
    ringId = solve! ℤCommRing
    widthNum : (a · (m · b + a) + (- (b · b))) ≡ - s
    widthNum = cong (λ z → a · (m · b + a) + (- z)) ih ∙ solve! ℤCommRing

-- ── THE METALLIC EQUATION x²=m·x+1, exact up to (−1)^n ───────────────────────
-- kfib(n+1)² = m·(kfib(n+1)·kfib(n)) + kfib(n)² + (−1)^n  — i.e. the convergent
-- c = kfib(n+1)/kfib(n) satisfies  c² = m·c + 1 + (−1)^n / kfib(n)².
metallicℤ : (m : ℤ) (n : ℕ)
          → kfib m (suc n) · kfib m (suc n)
          ≡ ((m · (kfib m (suc n) · kfib m n)) + (kfib m n · kfib m n)) + altSign n
metallicℤ m n = kCassini m n ∙ cong (_+ altSign n) lemma
  where
    lemma : kfib m n · kfib m (suc (suc n))
          ≡ (m · (kfib m (suc n) · kfib m n)) + (kfib m n · kfib m n)
    lemma = solve! ℤCommRing

-- ── m = 1 RECOVERS the golden Fibonacci ladder (ties to φ / LocatedLaw) ──────
kfib-one : (n : ℕ) → kfib (pos 1) n ≡ fibℤ n
kfib-one zero          = refl
kfib-one (suc zero)    = refl
kfib-one (suc (suc n)) =
  cong (λ z → (pos 1 · z) + kfib (pos 1) n) (kfib-one (suc n))
  ∙ cong (λ z → (pos 1 · fibℤ (suc n)) + z) (kfib-one n)
  ∙ cong (_+ fibℤ n) (·IdL (fibℤ (suc n)))

-- ── named instances: φ (m=1), silver (m=2), bronze (m=3) ────────────────────
goldenCassini : (n : ℕ) → kfib (pos 1) (suc n) · kfib (pos 1) (suc n)
                        ≡ kfib (pos 1) n · kfib (pos 1) (suc (suc n)) + altSign n
goldenCassini = kCassini (pos 1)

silverCassini : (n : ℕ) → kfib (pos 2) (suc n) · kfib (pos 2) (suc n)
                        ≡ kfib (pos 2) n · kfib (pos 2) (suc (suc n)) + altSign n
silverCassini = kCassini (pos 2)

bronzeCassini : (n : ℕ) → kfib (pos 3) (suc n) · kfib (pos 3) (suc n)
                        ≡ kfib (pos 3) n · kfib (pos 3) (suc (suc n)) + altSign n
bronzeCassini = kCassini (pos 3)

-- reduction sanity: silver ladder = Pell numbers 0,1,2,5,12,29 (m=2);
-- bronze ladder 0,1,3,10,33,109 (m=3, OEIS A006190).  The convergents
-- kfib(n+1)/kfib(n) → silver 1+√2 = 2.414…, bronze (3+√13)/2 = 3.302….
_ : kfib (pos 2) 2 ≡ pos 2
_ = refl
_ : kfib (pos 2) 3 ≡ pos 5
_ = refl
_ : kfib (pos 2) 4 ≡ pos 12
_ = refl
_ : kfib (pos 3) 3 ≡ pos 10
_ = refl
_ : kfib (pos 3) 4 ≡ pos 33
_ = refl
