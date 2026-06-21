{-# OPTIONS --cubical --safe --guardedness #-}

-- NEGATIVE CONTROL for Sprint 3. The kernel MUST reject this.
-- It claims 0G ≡ 1G by refl in ℤ[φ]. This is the fact underlying ιB's
-- non-surjectivity (the corner unit E₀₀ has a 1G where every ιB-image has 0G).
-- The kernel rejects it (gφ 0 0 vs gφ 1 0), so the non-surjectivity is non-vacuous.

module corpus.cubical_agda.RealCohesion.negative_controls.BadGoldenUnit where

open import Cubical.Foundations.Prelude
open import corpus.cubical_agda.Theory.GoldenRing using (Gφ; 0G; 1G)

bad-0G≡1G : 0G ≡ 1G
bad-0G≡1G = refl
