{-# OPTIONS --cubical --safe --guardedness #-}

-- NEGATIVE CONTROL for the trisection engine. The kernel MUST reject this.
-- It claims (1−⅓) < ⅓, i.e. 2/3 < 1/3 -- FALSE. The trisection's two interior
-- points need ⅓ < 1−⅓ (m₁ < m₂) for the located call to split a genuine gap;
-- the kernel rejects this reversed inequality, so the split is non-degenerate.

module corpus.cubical_agda.RealCohesion.negative_controls.BadTrisection where

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

bad-split-reversed : (1 + (- [ pos 1 / 1+ 2 ])) < [ pos 1 / 1+ 2 ]
bad-split-reversed = getYes (<Dec (1 + (- [ pos 1 / 1+ 2 ])) [ pos 1 / 1+ 2 ]) tt
