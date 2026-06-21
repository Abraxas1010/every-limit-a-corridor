{-# OPTIONS --cubical --safe --guardedness #-}
-- The Ellerman 2-block logical-entropy symmetry h(p)=h(1−p), as a ring identity
-- over an arbitrary commutative ring (kept apart from ℚ to avoid a `_-_` clash).
module corpus.cubical_agda.Corridor.Running.General.EntropyRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr)
open import Cubical.Tactics.CommRingSolver

module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  H2 : ⟨ R ⟩ → ⟨ R ⟩
  H2 p = 1r - ((p · p) + ((1r - p) · (1r - p)))
  H2-sym : (p : ⟨ R ⟩) → H2 p ≡ H2 (1r - p)
  H2-sym p = solve! R
