{-# OPTIONS --cubical --safe --no-import-sorts --guardedness #-}

------------------------------------------------------------------------------
-- Theory/LogicalEntropyTEEBridgeNegativeControl.agda — kernel-REJECTED control for
-- `LogicalEntropyTEEBridge`.
--
-- The bridge's force is the EXACT value h = 2/5 for the Fibonacci quantum-dimension
-- distribution.  This control asserts h = 3/5 instead (5·distinctions = 3·D⁴); it MUST
-- fail (10+10φ ≠ 15+15φ in ℤ[φ]), witnessing that the logical-entropy value is the genuine
-- 2/5 and not an artifact — the φ-parts really do cancel to a specific rational.
------------------------------------------------------------------------------

module corpus.cubical_agda.Theory.LogicalEntropyTEEBridgeNegativeControl where

open import Cubical.Foundations.Prelude using (_≡_; refl)
open import Cubical.Data.Int using (pos)
open import corpus.cubical_agda.Theory.GoldenRing using (_·G_; fromℤ)
open import corpus.cubical_agda.Theory.LogicalEntropyTEEBridge using (distinctions; Dsq)

-- FALSE: the Fibonacci quantum-dimension logical entropy is 3/5 (5·distinctions = 3·D⁴).
bad-three-fifths :
  (fromℤ (pos 5) ·G distinctions) ≡ (fromℤ (pos 3) ·G (Dsq ·G Dsq))
bad-three-fifths = refl
