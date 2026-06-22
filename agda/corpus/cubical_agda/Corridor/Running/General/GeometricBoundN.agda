{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE GEOMETRIC BOUND, INTEGER LEVEL — 4ᵏ·(k+1) ≤ 9ᵏ.
--
-- This is the cross-multiplied form of (4/9)ᵏ ≤ 1/(k+1), the explicit-modulus convergence
-- that drives trisect-n's geometric width (2/3)²ᵏ·D = (4/9)ᵏ·D toward 0.  Proved as a pure
-- ℕ induction (no ℚ/ℕ₊₁ machinery): the step is 4·(k+2) ≤ 9·(k+1), i.e. 4 ≤ 5·(k+1), times
-- 4ᵏ.  This is the mathematical heart of the geometric convergence; the ℚ-level statement
-- pow49 k ≤ 1/(k+1) follows by cross-multiplication.
--
module corpus.cubical_agda.Corridor.Running.General.GeometricBoundN where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-trans; ≤-·k; ≤-k+; ≤SumLeft; suc-≤-suc; zero-≤)

-- 4ᵏ and 9ᵏ.
p4 p9 : ℕ → ℕ
p4 zero    = 1
p4 (suc k) = 4 · p4 k
p9 zero    = 1
p9 (suc k) = 9 · p9 k

-- the step inequality:  4·(k+2) ≤ 9·(k+1).   ( = 4 ≤ 5·(k+1), shifted by 4·(k+1) )
lin : (k : ℕ) → 4 · (suc (suc k)) ≤ 9 · (suc k)
lin k = subst2 _≤_ e4 e9 4≤part
  where
    -- 4·(k+2) = 4·(k+1) + 4 ;  9·(k+1) = 4·(k+1) + 5·(k+1).
    e4 : 4 · (suc k) + 4 ≡ 4 · (suc (suc k))
    e4 = +-comm (4 · suc k) 4 ∙ sym (·-suc 4 (suc k))
    e9 : 4 · (suc k) + 5 · (suc k) ≡ 9 · (suc k)
    e9 = ·-distribʳ 4 5 (suc k)
    -- 4 ≤ 5·(k+1):  5·(k+1) = 5 + 5·k ≥ 5 ≥ 4.
    4≤5sk : 4 ≤ 5 · (suc k)
    4≤5sk = ≤-trans (≤SumLeft {n = 4} {k = 1})
              (subst (5 ≤_) (sym (·-suc 5 k)) (≤SumLeft {n = 5} {k = 5 · k}))
    4≤part : 4 · (suc k) + 4 ≤ 4 · (suc k) + 5 · (suc k)
    4≤part = ≤-k+ {k = 4 · suc k} 4≤5sk

-- THE GEOMETRIC BOUND:  4ᵏ·(k+1) ≤ 9ᵏ.
geomBoundℕ : (k : ℕ) → p4 k · suc k ≤ p9 k
geomBoundℕ zero    = ≤-refl
geomBoundℕ (suc k) = ≤-trans step1 step2
  where
    -- 4ᵏ⁺¹·(k+2) = 4ᵏ·(4·(k+2)) ≤ 4ᵏ·(9·(k+1)) = 9·(4ᵏ·(k+1)) ≤ 9·9ᵏ = 9ᵏ⁺¹.
    r1 : p4 (suc k) · suc (suc k) ≡ p4 k · (4 · suc (suc k))
    r1 = cong (_· suc (suc k)) (·-comm 4 (p4 k)) ∙ sym (·-assoc (p4 k) 4 (suc (suc k)))
    step1 : p4 (suc k) · suc (suc k) ≤ p4 k · (9 · suc k)
    step1 = subst (_≤ p4 k · (9 · suc k)) (sym r1)
              (subst2 _≤_ (·-comm (4 · suc (suc k)) (p4 k)) (·-comm (9 · suc k) (p4 k))
                (≤-·k {k = p4 k} (lin k)))
    r2 : p4 k · (9 · suc k) ≡ 9 · (p4 k · suc k)
    r2 = ·-assoc (p4 k) 9 (suc k) ∙ cong (_· suc k) (·-comm (p4 k) 9) ∙ sym (·-assoc 9 (p4 k) (suc k))
    step2 : p4 k · (9 · suc k) ≤ p9 (suc k)
    step2 = subst (_≤ 9 · p9 k) (sym r2)
              (subst2 _≤_ (·-comm (p4 k · suc k) 9) (·-comm (p9 k) 9)
                (≤-·k {k = 9} (geomBoundℕ k)))
