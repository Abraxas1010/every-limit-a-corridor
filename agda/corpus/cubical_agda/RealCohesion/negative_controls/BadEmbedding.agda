{-# OPTIONS --cubical --safe --guardedness #-}

-- NEGATIVE CONTROL for the rational order-embedding. The kernel MUST reject this.
-- It claims ι 0 ≡ ι 1 (the embedding collapses distinct rationals). False: ι is
-- injective (order-faithful), so the kernel rejects the refl -- the embedding
-- genuinely distinguishes rationals, making ι-monotone/ι-reflects non-vacuous.

module corpus.cubical_agda.RealCohesion.negative_controls.BadEmbedding where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals
open import corpus.cubical_agda.RealCohesion.DedekindReal using (ℝ; ι)

bad-ι-collapses : ι 0 ≡ ι 1
bad-ι-collapses = refl
