{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE CORRIDOR GENERALIZES — a certified √2 that EXECUTES.
--
-- The golden corridor's whole engine (convergents + a Cassini identity + the
-- ℚ-order unfolding) is not special to φ.  Here we run it for √2, using the
-- Pell numbers (p,q) ↦ (p+2q, p+q) in place of Fibonacci.  The Pell–Cassini
-- identity p² = 2q² + (−1)^{n+1} is the direct analogue of Cassini, and it makes
-- the convergents p_n/q_n bracket √2 with certified, kernel-reducing squared
-- bounds: at even n, (p_n/q_n)² ≤ 2; at odd n, (p_n/q_n)² ≥ 2.  This is the
-- corridor as a reusable certified-numerics primitive: a different algebraic
-- number, the same machine, still running.
--
module corpus.cubical_agda.Corridor.Running.CertifiedSqrt2 where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int using (ℤ; pos; negsuc; sucℤ) renaming (_+_ to _+ℤ_; _·_ to _·ℤ_; -_ to -ℤ_)
open import Cubical.Data.Int.Properties using (-Involutive)
open import Cubical.Data.Int.Order using (_≤_; ≤-predℤ; ≤-sucℤ)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Tactics.CommRingSolver using (solve!)

open import corpus.cubical_agda.Corridor.Running.Bracket using (dbl)

-- ────────────────────────────────────────────────────────────────────────────
-- Pell convergents p_n/q_n → √2:  (p,q) ↦ (p+2q, p+q), from 1/1.
--   1/1, 3/2, 7/5, 17/12, 41/29, …
-- ────────────────────────────────────────────────────────────────────────────

pP : ℕ → ℤ
pQ : ℕ → ℤ
pP zero    = pos 1
pP (suc n) = pP n +ℤ pos 2 ·ℤ pQ n
pQ zero    = pos 1
pQ (suc n) = pP n +ℤ pQ n

altSign : ℕ → ℤ
altSign zero    = pos 1
altSign (suc n) = -ℤ altSign n

-- ────────────────────────────────────────────────────────────────────────────
-- Pell–Cassini:  p_n² = 2·q_n² + (−1)^{n+1}.
-- Proved by induction; the sign is kept abstract so the ring solver applies.
-- ────────────────────────────────────────────────────────────────────────────

pellCassini : (n : ℕ) → pP n ·ℤ pP n ≡ pos 2 ·ℤ (pQ n ·ℤ pQ n) +ℤ altSign (suc n)
pellCassini zero    = refl
pellCassini (suc n) = ringId ∙ cong (pos 2 ·ℤ ((a +ℤ b) ·ℤ (a +ℤ b)) +ℤ_) signEq
  where
    a b s : ℤ
    a = pP n
    b = pQ n
    s = altSign (suc n)

    ih : a ·ℤ a ≡ pos 2 ·ℤ (b ·ℤ b) +ℤ s
    ih = pellCassini n

    -- pure ring:  (a+2b)² = 2(a+b)² + (−a² + 2b²)
    ringId : (a +ℤ pos 2 ·ℤ b) ·ℤ (a +ℤ pos 2 ·ℤ b)
           ≡ pos 2 ·ℤ ((a +ℤ b) ·ℤ (a +ℤ b)) +ℤ ((-ℤ (a ·ℤ a)) +ℤ pos 2 ·ℤ (b ·ℤ b))
    ringId = solve! ℤCommRing

    -- eliminate the sign:  −a² + 2b² = −(2b² + s) + 2b² = −s
    signEq : (-ℤ (a ·ℤ a)) +ℤ pos 2 ·ℤ (b ·ℤ b) ≡ -ℤ s
    signEq = cong (λ z → (-ℤ z) +ℤ pos 2 ·ℤ (b ·ℤ b)) ih ∙ solve! ℤCommRing

-- ────────────────────────────────────────────────────────────────────────────
-- Reduction certificates: the Pell convergents EXECUTE.
-- ────────────────────────────────────────────────────────────────────────────

pP-1 : pP 1 ≡ pos 3
pP-1 = refl
pQ-1 : pQ 1 ≡ pos 2          -- 3/2
pQ-1 = refl
pP-2 : pP 2 ≡ pos 7
pP-2 = refl
pQ-2 : pQ 2 ≡ pos 5          -- 7/5
pQ-2 = refl
pP-3 : pP 3 ≡ pos 17
pP-3 = refl
pQ-3 : pQ 3 ≡ pos 12         -- 17/12
pQ-3 = refl

-- ────────────────────────────────────────────────────────────────────────────
-- The certified squared bounds: the convergents BRACKET √2.
--   even n:  (p_n/q_n)² ≤ 2   (below √2)
--   odd  n:  (p_n/q_n)² ≥ 2   (above √2)
-- ────────────────────────────────────────────────────────────────────────────

altSignEven : (n : ℕ) → altSign (dbl n) ≡ pos 1
altSignEven zero    = refl
altSignEven (suc n) = -Involutive (altSign (dbl n)) ∙ altSignEven n

altSignOdd : (n : ℕ) → altSign (suc (dbl n)) ≡ negsuc 0
altSignOdd n = cong -ℤ_ (altSignEven n)

-- even convergent is below √2: p² ≤ 2q²  (Pell–Cassini sign −1; p² = predℤ(2q²))
belowSq : (n : ℕ)
        → pP (dbl n) ·ℤ pP (dbl n) ≤ pos 2 ·ℤ (pQ (dbl n) ·ℤ pQ (dbl n))
belowSq n = subst (_≤ pos 2 ·ℤ (pQ (dbl n) ·ℤ pQ (dbl n))) (sym pellEq) ≤-predℤ
  where
    pellEq : pP (dbl n) ·ℤ pP (dbl n) ≡ pos 2 ·ℤ (pQ (dbl n) ·ℤ pQ (dbl n)) +ℤ negsuc 0
    pellEq = pellCassini (dbl n)
           ∙ cong (pos 2 ·ℤ (pQ (dbl n) ·ℤ pQ (dbl n)) +ℤ_) (altSignOdd n)

-- odd convergent is above √2: 2q² ≤ p²  (Pell–Cassini sign +1; p² = sucℤ(2q²))
aboveSq : (n : ℕ)
        → pos 2 ·ℤ (pQ (suc (dbl n)) ·ℤ pQ (suc (dbl n))) ≤ pP (suc (dbl n)) ·ℤ pP (suc (dbl n))
aboveSq n = subst (pos 2 ·ℤ (pQ (suc (dbl n)) ·ℤ pQ (suc (dbl n))) ≤_) (sym pellEq) ≤-sucℤ
  where
    pellEq : pP (suc (dbl n)) ·ℤ pP (suc (dbl n))
           ≡ pos 2 ·ℤ (pQ (suc (dbl n)) ·ℤ pQ (suc (dbl n))) +ℤ pos 1
    pellEq = pellCassini (suc (dbl n))
           ∙ cong (pos 2 ·ℤ (pQ (suc (dbl n)) ·ℤ pQ (suc (dbl n))) +ℤ_) (altSignEven (suc n))
