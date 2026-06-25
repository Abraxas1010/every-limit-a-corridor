{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------------
-- Theory/CStarInductiveLimitNegativeControl.agda — kernel-REJECTED control for
-- `CStarInductiveLimit`.
--
-- The C*-identity on the limit is content only if the descended square genuinely squares
-- the norm.  For the example tower (ν = id, sq = squaring) the limit norm of a*a at the
-- value 3 is 9, not 3.  This control asserts it is 3; it MUST fail (9 ≠ 3), witnessing
-- that the C*-identity at the limit is the quadratic relation, not a triviality.
------------------------------------------------------------------------------

module corpus.cubical_agda.Theory.CStarInductiveLimitNegativeControl where

open import Cubical.Foundations.Prelude using (_≡_; refl)
open import Cubical.HITs.SequentialColimit.Base using (incl)
open import corpus.cubical_agda.Theory.CStarInductiveLimit using (exampleTower; normLimit; sqLimit)

-- FALSE: ‖a*a‖ = ‖a‖ (not ‖a‖²) on the limit, at the value 3.
bad-cstar-is-identity : normLimit exampleTower (sqLimit exampleTower (incl {n = 0} 3)) ≡ 3
bad-cstar-is-identity = refl
