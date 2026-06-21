{-# OPTIONS --cubical --safe --guardedness #-}

-- NEGATIVE CONTROL for Sprint 1 (DedekindReal). The kernel MUST reject this.
-- It asserts a FALSE rational inequality 2 < 1 via the same `getYes (<Dec ..) tt`
-- idiom the real module uses for TRUE ones. Because <Dec 2 1 computes to `no`,
-- `IsYes (no _)` reduces to ⊥, so the `tt : ⊥` is ill-typed: the discriminator
-- has content (a degenerate "ordering" cannot manufacture a cut witness).

module corpus.cubical_agda.RealCohesion.negative_controls.BadCutOrder where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
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

-- 2 < 1 is FALSE; this line is the degenerate move the kernel rejects.
bad-2<1 : [ pos 2 / 1+ 0 ] < [ pos 1 / 1+ 0 ]
bad-2<1 = getYes (<Dec [ pos 2 / 1+ 0 ] [ pos 1 / 1+ 0 ]) tt
