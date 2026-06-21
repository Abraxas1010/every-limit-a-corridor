{-# OPTIONS --cubical --safe --guardedness #-}

-- NEGATIVE CONTROL for the diagonal C*-identity. The kernel MUST reject this.
-- maxℚ-sq (max commutes with squaring) GENUINELY needs nonnegativity: at x=−3,
-- y=1 it claims maxℚ(9,1) = (maxℚ(−3,1))², i.e. 9 = 1², FALSE. The kernel rejects
-- it, so the 0≤x,0≤y hypotheses of maxℚ-sq are load-bearing (squaring is NOT
-- monotone across sign -- the C*-norm needs the absolute value).

module corpus.cubical_agda.RealCohesion.negative_controls.BadCStarNonneg where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Rationals
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (maxℚ)

private
  IsYes : {A : Type₀} → Dec A → Type₀
  IsYes (yes _) = Unit
  IsYes (no  _) = ⊥
  getYes : {A : Type₀} (d : Dec A) → IsYes d → A
  getYes (yes a) _  = a
  getYes (no  _) ()

bad-cstar-needs-nonneg :
  maxℚ ((- 3) · (- 3)) (1 · 1) ≡ (maxℚ (- 3) 1) · (maxℚ (- 3) 1)
bad-cstar-needs-nonneg =
  getYes (discreteℚ (maxℚ ((- 3) · (- 3)) (1 · 1)) ((maxℚ (- 3) 1) · (maxℚ (- 3) 1))) tt
