{-# OPTIONS --cubical --safe --guardedness #-}

-- NEGATIVE CONTROL for Sprint 5 (GoldenSpectrum). The kernel MUST reject this.
-- It claims the golden modulus COLLAPSES (the bracket-width sign is 0 at n=0).
-- modulus-never-collapses proves this impossible; the kernel rejects the refl
-- because negsign 0 = -1 ≠ 0, so the non-collapse certificate is non-vacuous.

module corpus.cubical_agda.RealCohesion.negative_controls.BadModulusCollapse where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (pos)
open import corpus.cubical_agda.RealCohesion.GoldenSpectrum using (negsign)

bad-collapse : negsign 0 ≡ pos 0
bad-collapse = refl
