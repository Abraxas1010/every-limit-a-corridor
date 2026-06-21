{-# OPTIONS --cubical --safe --guardedness #-}
--
-- φ IS A UNIQUE REAL — the Dedekind-cut property:  lo m < hi n  for ALL m, n.
--
-- The nesting (`lo↗`, `hi↘`) says each bracket sits inside the previous.  This
-- module proves the global separation: EVERY lower convergent is below EVERY
-- upper convergent, regardless of the rungs.  That is the Dedekind-cut property
-- — the lower convergents and the upper convergents form a genuine cut, so the
-- located real φ they pin is UNIQUE.  The proof: monotone-close `lo↗`/`hi↘` and
-- split on m ≤ n vs n < m, using the library's mixed transitivity.
--
module corpus.cubical_agda.Corridor.Running.CrossCut where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order as ℕ using (splitℕ-≤)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Rationals.Order
  using (isRefl≤; isTrans≤; isTrans≤<; isTrans<≤; <Weaken≤)
  renaming (_≤_ to _≤ℚ_; _<_ to _<ℚ_)

open import corpus.cubical_agda.Corridor.Running.Bracket using (lo; hi)
open import corpus.cubical_agda.Corridor.Running.Ordered using (lo<hi)
open import corpus.cubical_agda.Corridor.Running.Located using (lo↗; hi↘)

-- ────────────────────────────────────────────────────────────────────────────
-- Monotone closures of the strict step relations.
-- ────────────────────────────────────────────────────────────────────────────

lo-mono+ : (m k : ℕ) → lo m ≤ℚ lo (k +ℕ m)
lo-mono+ m zero    = isRefl≤ (lo m)
lo-mono+ m (suc k) =
  isTrans≤ (lo m) (lo (k +ℕ m)) (lo (suc k +ℕ m))
    (lo-mono+ m k)
    (<Weaken≤ (lo (k +ℕ m)) (lo (suc (k +ℕ m))) (lo↗ (k +ℕ m)))

lo-mono : (m n : ℕ) → m ℕ.≤ n → lo m ≤ℚ lo n
lo-mono m n (k , p) = subst (lo m ≤ℚ_) (cong lo p) (lo-mono+ m k)

hi-mono+ : (m k : ℕ) → hi (k +ℕ m) ≤ℚ hi m
hi-mono+ m zero    = isRefl≤ (hi m)
hi-mono+ m (suc k) =
  isTrans≤ (hi (suc k +ℕ m)) (hi (k +ℕ m)) (hi m)
    (<Weaken≤ (hi (suc (k +ℕ m))) (hi (k +ℕ m)) (hi↘ (k +ℕ m)))
    (hi-mono+ m k)

hi-mono : (m n : ℕ) → m ℕ.≤ n → hi n ≤ℚ hi m
hi-mono m n (k , p) = subst (_≤ℚ hi m) (cong hi p) (hi-mono+ m k)

-- ────────────────────────────────────────────────────────────────────────────
-- The Dedekind-cut property:  lo m < hi n  for all m, n.
-- ────────────────────────────────────────────────────────────────────────────

lo<hi-cut : (m n : ℕ) → lo m <ℚ hi n
lo<hi-cut m n with splitℕ-≤ m n
... | inl m≤n = isTrans≤< (lo m) (lo n) (hi n) (lo-mono m n m≤n) (lo<hi n)
... | inr n<m = isTrans<≤ (lo m) (hi m) (hi n) (lo<hi m) (hi-mono n m (ℕ.<-weaken n<m))
