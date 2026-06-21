{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE RATE IS FORCED — the genuine, golden-specific forcing.
--
-- The landed corridor's `modulus-forced : Σ D, width c < D` holds for ANY
-- ℕ→ℕ function (it is just unboundedness of ℕ); it does not use the golden
-- growth, and the substitution test passes a constant.  This module proves the
-- content the audit demanded instead: the bracket DENOMINATORS are unbounded,
-- `∀ M, M < denom M`, where `denom n = F_{2n+1}·F_{2n+2}` is the reciprocal of
-- the width.  This uses the golden growth (Fibonacci dominates linear) and a
-- CONSTANT rate provably fails it (`constant-rate-fails`).  Since
-- `width n = 1/denom n` (proved by reduction in `Bracket.width-*`), denom→∞ is
-- exactly width→0: the corridor genuinely closes, and no constant rate can.
--
module corpus.cubical_agda.Corridor.Running.Forcing where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; +-comm) renaming (_+_ to _+ℕ_; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Properties using (·-identityˡ)
open import Cubical.Data.Nat.Order
  using (_≤_; _<_; ≤-refl; ≤-suc; ≤-trans; ≤-+k; ≤-k+; ≤-·k; suc-≤-suc; zero-≤; ≤SumLeft; ¬m<m)
open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_; ℕ₊₁→ℕ)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import corpus.cubical_agda.Corridor.Running.Bracket using (fibP; dbl)
open import corpus.cubical_agda.Corridor.Running.Ordered using (n→ℕ+₁)

-- ────────────────────────────────────────────────────────────────────────────
-- The Fibonacci ladder, ℕ-valued (the bracket denominators).  fpN m = F_{m+1}.
-- ────────────────────────────────────────────────────────────────────────────

fpN : ℕ → ℕ
fpN m = ℕ₊₁→ℕ (fibP m)

fpN-rec : (m : ℕ) → fpN (suc (suc m)) ≡ fpN (suc m) +ℕ fpN m
fpN-rec m = n→ℕ+₁ (fibP (suc m)) (fibP m)

fpN-pos : (m : ℕ) → 1 ≤ fpN m
fpN-pos m = n₊pos (fibP m)
  where
    n₊pos : (z : ℕ₊₁) → 1 ≤ ℕ₊₁→ℕ z
    n₊pos (1+ k) = suc-≤-suc zero-≤

+-mono-≤ : {a b c d : ℕ} → a ≤ b → c ≤ d → a +ℕ c ≤ b +ℕ d
+-mono-≤ {b = b} {c = c} p q = ≤-trans (≤-+k {k = c} p) (≤-k+ {k = b} q)

-- the golden growth dominates linear: F_{n+2} ≥ n+1 (mirror of the landed lemma)
fpN-lower : (n : ℕ) → suc n ≤ fpN (suc n)
fpN-lower zero    = ≤-refl
fpN-lower (suc m) =
  subst (λ z → z ≤ fpN (suc (suc m))) (+-comm (suc m) 1)
    (subst (λ w → (suc m +ℕ 1) ≤ w) (sym (fpN-rec m))
      (+-mono-≤ (fpN-lower m) (fpN-pos m)))

-- b ≤ a·b whenever a ≥ 1   (1·b ≤ a·b by ≤-·k, and 1·b ≡ b)
le-mult : (a b : ℕ) → 1 ≤ a → b ≤ a ·ℕ b
le-mult a b 1≤a = subst (_≤ a ·ℕ b) (·-identityˡ b) (≤-·k {k = b} 1≤a)

-- ────────────────────────────────────────────────────────────────────────────
-- The bracket denominator and the forcing theorem.
-- ────────────────────────────────────────────────────────────────────────────

denom : ℕ → ℕ
denom n = fpN (dbl n) ·ℕ fpN (suc (dbl n))

M≤dbl : (M : ℕ) → M ≤ dbl M
M≤dbl zero    = ≤-refl
M≤dbl (suc M) = ≤-suc (suc-≤-suc (M≤dbl M))

denom-lower : (M : ℕ) → suc (dbl M) ≤ denom M
denom-lower M =
  ≤-trans (fpN-lower (dbl M))
          (le-mult (fpN (dbl M)) (fpN (suc (dbl M))) (fpN-pos (dbl M)))

-- THE FORCING: the denominators are unbounded — width n = 1/denom n → 0.
forcing : (M : ℕ) → M < denom M
forcing M = ≤-trans (suc-≤-suc (M≤dbl M)) (denom-lower M)

-- and a CONSTANT rate cannot: its fixed denominator c fails to exceed M = c.
constant-rate-fails : (c : ℕ) → ¬ ((M : ℕ) → M < c)
constant-rate-fails c h = ¬m<m (h c)
