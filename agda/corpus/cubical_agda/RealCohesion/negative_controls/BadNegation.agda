{-# OPTIONS --cubical --safe --guardedness #-}

-- NEGATIVE CONTROL for real negation. The kernel MUST reject this.
-- It claims -ℝ 1ℝ ≡ 1ℝ (that negation fixes 1). This is false (−1 ≠ 1); the
-- kernel rejects the refl because the swapped/flipped cuts of -ℝ 1ℝ differ from
-- 1ℝ's cuts -- so negation genuinely changes the real (it is not the identity).

module corpus.cubical_agda.RealCohesion.negative_controls.BadNegation where

open import Cubical.Foundations.Prelude
open import corpus.cubical_agda.RealCohesion.DedekindReal using (ℝ; 1ℝ)
open import corpus.cubical_agda.RealCohesion.RealNegation using (-ℝ_)

bad-neg-fixes-1 : -ℝ 1ℝ ≡ 1ℝ
bad-neg-fixes-1 = refl
