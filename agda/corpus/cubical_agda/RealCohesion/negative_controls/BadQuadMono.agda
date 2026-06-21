{-# OPTIONS --cubical --safe --guardedness #-}

-- NEGATIVE CONTROL for quad-mono. The kernel MUST reject this. It asserts the
-- quadratic monotonicity x²−x WITHOUT the hypothesis q+r>1, at q=0, r=1/2 (where
-- q+r = 1/2 < 1). There x²−x DECREASES: 0²−0 = 0 but (1/2)²−1/2 = −1/4, so the
-- claimed (0²−0) < ((1/2)²−1/2) is 0 < −1/4, FALSE. The kernel rejects it -- so
-- the q+r>1 hypothesis of quad-mono is genuinely load-bearing.

module corpus.cubical_agda.RealCohesion.negative_controls.BadQuadMono where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Int using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; <Dec)
open import Cubical.Relation.Nullary using (Dec; yes; no)

private
  IsYes : {A : Type₀} → Dec A → Type₀
  IsYes (yes _) = Unit
  IsYes (no  _) = ⊥
  getYes : {A : Type₀} (d : Dec A) → IsYes d → A
  getYes (yes a) _  = a
  getYes (no  _) ()

½ : ℚ
½ = [ pos 1 / 1+ 1 ]

bad-quad-without-hypothesis : ((0 · 0) + (- 0)) < ((½ · ½) + (- ½))
bad-quad-without-hypothesis =
  getYes (<Dec ((0 · 0) + (- 0)) ((½ · ½) + (- ½))) tt
