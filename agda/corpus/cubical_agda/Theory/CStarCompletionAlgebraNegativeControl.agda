{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------------
-- Theory/CStarCompletionAlgebraNegativeControl.agda — kernel-REJECTED control for
-- `CStarCompletionAlgebra`.
--
-- The extended operation must genuinely COMPUTE, not collapse to the identity.  Extending
-- `suc` and applying it to the embedded 0 gives the embedded 1, not the embedded 0.  This
-- control asserts it gives 0 (would force suc 0 ≡ 0); it MUST fail, witnessing that the
-- operation extension is the real operation, not a vacuous map.
------------------------------------------------------------------------------

module corpus.cubical_agda.Theory.CStarCompletionAlgebraNegativeControl where

open import Cubical.Foundations.Prelude using (_≡_; refl; cong)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import corpus.cubical_agda.Theory.CStarCompletion using (discreteGauge; η)
open import corpus.cubical_agda.Theory.CStarCompletionAlgebra using (extendF; _≈CH[_]_)

private
  G0 : _
  G0 = discreteGauge ℕ

-- FALSE: extending `suc` and applying to η 0 yields η 0 (would force suc 0 ≡ 0).
bad-extend-is-identity :
  _≈CH[_]_ G0 G0
    (extendF G0 G0 suc (λ k → k) (λ m n le → le) (λ k x y p → cong suc p) (η G0 0))
    0
    (η G0 0)
bad-extend-is-identity = refl
