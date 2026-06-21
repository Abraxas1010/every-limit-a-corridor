{-# OPTIONS --cubical --safe --guardedness #-}

-- NEGATIVE CONTROL for Sprint 2. The kernel MUST reject this.
-- It claims 0ℝ ≡ 1ℝ by refl in the FLAT (set) level. If this were accepted the
-- whole separation would be vacuous (flat would already collapse 0 and 1). The
-- kernel rejects it because ι 0 and ι 1 are genuinely distinct cuts -- so flat
-- really does keep them apart, and the shape≠flat separation has content.

module corpus.cubical_agda.RealCohesion.negative_controls.BadShapeCollapse where

open import Cubical.Foundations.Prelude
open import corpus.cubical_agda.RealCohesion.DedekindReal using (ℝ; 0ℝ; 1ℝ)

bad-0≡1 : 0ℝ ≡ 1ℝ
bad-0≡1 = refl
