{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

------------------------------------------------------------------------------
-- Theory/CohesionMetricSeparationNegativeControl.agda — kernel-REJECTED control for
-- `CohesionMetricSeparation`.
--
-- The discriminator's force is that ∫ and ♭ GENUINELY differ on the cohesive line.
-- This control asserts they agree there (the separation collapses); it MUST fail,
-- since ∫(line 2) has 1 point and ♭(line 2) has 2.  Its rejection witnesses that the
-- cohesion separation is real, not an artifact.
------------------------------------------------------------------------------

module corpus.cubical_agda.Theory.CohesionMetricSeparationNegativeControl where

open import Cubical.Foundations.Prelude using (_≡_; refl)
open import Cubical.Data.Nat.Order using (≤-refl)
open import corpus.cubical_agda.Theory.CohesiveTower using (Space; shape; flat; line)
open Space

-- FALSE: on the cohesive line, ∫ and ♭ have the same number of points.
-- (∫(line 2) has 1 point, ♭(line 2) has 2, so the kernel rejects this.)
bad-line-no-separation : points (shape (line 2 ≤-refl)) ≡ points (flat (line 2 ≤-refl))
bad-line-no-separation = refl
