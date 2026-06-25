{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------------
-- Theory/CStarCompletionNegativeControl.agda — kernel-REJECTED control for
-- `CStarCompletion`.
--
-- The isometric embedding η must SEPARATE distinct points: η 0 and η 1 cannot be within
-- tolerance 2⁰ in the discrete gauge (that would force 0 ≡ 1).  This control asserts they
-- are; it MUST fail, witnessing that the completion's gauge is a genuine separation, not a
-- collapse that would make completeness vacuous.
------------------------------------------------------------------------------

module corpus.cubical_agda.Theory.CStarCompletionNegativeControl where

open import Cubical.Foundations.Prelude using (_≡_; refl)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import corpus.cubical_agda.Theory.CStarCompletion using (discreteGauge; η; _∼[_]_)

private
  G0 : _
  G0 = discreteGauge ℕ

-- FALSE: the embeddings of 0 and 1 are within tolerance 2⁰ (would force 0 ≡ 1).
bad-eta-collapse : _∼[_]_ G0 (η G0 0) 0 (η G0 1)
bad-eta-collapse = refl
