{-# OPTIONS --cubical --safe --guardedness #-}
--
-- LOGICAL-ENTROPY PROVENANCE OF THE CORRIDOR (Ellerman's currency).
--
-- Ellerman's logical entropy of a partition π = {B₁,…,Bₖ} of masses pᵢ is
--   h(π) = 1 − Σ pᵢ²   (the probability two random draws are DISTINGUISHED).
-- The running corridor's exactness mechanism is the alternating Cassini sign
-- (−1)^n (Cassini.altSign): a BALANCED two-symbol process {+,−}, masses (½,½).
-- Its logical entropy is therefore  h = 1 − (¼+¼) = ½ — exactly the value of the
-- organism's H¹ cohomological screen (Corridor.EntropyScreen): the corridor's
-- distinction-content equals the screen's.  This module gives the Ellerman
-- 2-block entropy as a genuine FUNCTION (discriminating — 0 at the trivial
-- partition, ½ at the balanced one — and symmetric h(p)=h(1−p)), not a constant,
-- and pins the corridor's balanced value at ½.
--
module corpus.cubical_agda.Corridor.Running.General.EntropyProvenance where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import corpus.cubical_agda.Corridor.Running.General.EntropyRing using (H2-sym)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Tactics.CommRingSolver
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)

private
  IsYes : {A : Type₀} → Dec A → Type₀
  IsYes (yes _) = Unit
  IsYes (no  _) = ⊥
  getYes : {A : Type₀} (d : Dec A) → IsYes d → A
  getYes (yes a) _ = a

-- Ellerman logical entropy of a 2-block partition with masses (p, 1−p).
logicalEntropy2 : ℚ → ℚ
logicalEntropy2 p = 1 - ((p · p) + ((1 - p) · (1 - p)))

-- DISCRIMINATING values (the function is not constant):
--   trivial partition (p=0): no distinctions, h = 0.
entropy2-zero : logicalEntropy2 0 ≡ 0
entropy2-zero = getYes (discreteℚ (logicalEntropy2 0) 0) tt

--   BALANCED partition (p=½): the corridor's Cassini-sign screen, h = ½ = H¹ screen.
entropy2-half : logicalEntropy2 [ pos 1 / 1+ 1 ] ≡ [ pos 1 / 1+ 1 ]
entropy2-half = getYes (discreteℚ (logicalEntropy2 [ pos 1 / 1+ 1 ]) [ pos 1 / 1+ 1 ]) tt

-- SYMMETRY h(p) = h(1−p): a partition and its complement carry the same logical
-- entropy.  Proved as a ring identity (EntropyRing.H2-sym), instantiated to ℚ.
entropy2-sym : (p : ℚ) → logicalEntropy2 p ≡ logicalEntropy2 (1 - p)
entropy2-sym = H2-sym ℚCommRing
