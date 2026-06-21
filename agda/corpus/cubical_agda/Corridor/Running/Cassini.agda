{-# OPTIONS --cubical --safe --guardedness #-}
--
-- CASSINI'S IDENTITY — the lego block that makes the corridor's width exact.
--
-- For the golden Fibonacci ladder, consecutive convergents F_{n+1}/F_n bracket
-- φ, and the *exact* width of the bracket is governed by Cassini's identity
--      F_{n+1}² = F_n · F_{n+2} + (−1)^n .
-- Specialised to an even index this gives the corridor's bracket width
-- 1/(F_{2n+1}·F_{2n+2}) (e.g. 1/(F₃·F₄) = 1/6), with no parity branching.  This
-- module proves the identity over ℤ by induction, using the commutative-ring
-- solver for the polynomial rearrangement in the inductive step.
--
module corpus.cubical_agda.Corridor.Running.Cassini where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int using (ℤ; pos; _+_; _·_; -_)
open import Cubical.Algebra.CommRing.Instances.Int using (ℤCommRing)
open import Cubical.Tactics.CommRingSolver using (solve!)

-- ────────────────────────────────────────────────────────────────────────────
-- The ladder over ℤ (clean recurrence) and the alternating sign (−1)^k.
-- ────────────────────────────────────────────────────────────────────────────

fibℤ : ℕ → ℤ
fibℤ zero          = pos 0
fibℤ (suc zero)    = pos 1
fibℤ (suc (suc n)) = fibℤ (suc n) + fibℤ n

altSign : ℕ → ℤ
altSign zero    = pos 1
altSign (suc n) = - altSign n

-- ────────────────────────────────────────────────────────────────────────────
-- Cassini:  F_{k+1}² = F_k · F_{k+2} + (−1)^k.
-- The recurrence F_{k+2} = F_{k+1} + F_k holds definitionally, so the inductive
-- step is a pure ring rearrangement once the hypothesis eliminates the sign.
-- ────────────────────────────────────────────────────────────────────────────

cassini : (k : ℕ)
        → fibℤ (suc k) · fibℤ (suc k) ≡ fibℤ k · fibℤ (suc (suc k)) + altSign k
cassini zero    = refl
cassini (suc k) = ringId ∙ cong (λ z → b · ((b + a) + b) + z) widthNum
  where
    a b s : ℤ
    a = fibℤ k
    b = fibℤ (suc k)
    s = altSign k

    ih : b · b ≡ a · (b + a) + s
    ih = cassini k

    -- pure commutative-ring identity (true for all a, b):
    --   (b+a)² = b·((b+a)+b) + (a·(b+a) + (−(b·b)))
    ringId : (b + a) · (b + a) ≡ b · ((b + a) + b) + (a · (b + a) + (- (b · b)))
    ringId = solve! ℤCommRing

    -- eliminate the sign using the hypothesis:
    --   a·(b+a) + (−(b·b)) = a·(b+a) + (−(a·(b+a)+s)) = − s
    widthNum : (a · (b + a) + (- (b · b))) ≡ - s
    widthNum = cong (λ z → a · (b + a) + (- z)) ih ∙ solve! ℤCommRing

-- ────────────────────────────────────────────────────────────────────────────
-- Sanity checks (the identity reduces on concrete indices).
-- ────────────────────────────────────────────────────────────────────────────

_ : fibℤ (suc 0) · fibℤ (suc 0) ≡ fibℤ 0 · fibℤ (suc (suc 0)) + altSign 0
_ = cassini 0

_ : fibℤ (suc 1) · fibℤ (suc 1) ≡ fibℤ 1 · fibℤ (suc (suc 1)) + altSign 1
_ = cassini 1
