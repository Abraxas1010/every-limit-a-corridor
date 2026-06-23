{-# OPTIONS --cubical --safe --guardedness #-}
--
-- ABSOLUTE-VALUE LEMMAS — multiplicativity and the triangle inequality on ℚ.
--
-- Needed for the ℓ¹ submultiplicativity ‖A·B‖₁ ≤ ‖A‖₁·‖B‖₁ (the upper-cut persistence).  Both are
-- proved SQUARED, via the landed sqrt-mono-≤ — no case analysis on signs:
--   abs-mult      — |x·y| = |x|·|y|        (since |x·y|² = (x·x)(y·y) = (|x||y|)²);
--   abs-triangle  — |x+y| ≤ |x|+|y|        (since (x+y)² ≤ (|x|+|y|)², as x·y ≤ |x·y| = |x||y|).
-- sqrt-inj (a²=b² ⟹ a=b on the nonnegatives) is the antisymmetric companion of sqrt-mono-≤.
--
module corpus.cubical_agda.Corridor.Running.General.AbsLemmas where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr; CommRing→Ring)
open import Cubical.Tactics.CommRingSolver using (solve!)

-- ring identities (before the ℚ open: the abstract ring's `_·_`/`_+_`).
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  prodSqR : (x y : ⟨ R ⟩) → ((x · y) · (x · y)) ≡ ((x · x) · (y · y))
  prodSqR x y = solve! R
  sumSqR : (a b : ⟨ R ⟩) → ((a + b) · (a + b)) ≡ (((a · a) + ((a · b) + (a · b))) + (b · b))
  sumSqR a b = solve! R

open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_≤_; isRefl≤; isAntisym≤; ≤Monotone+; ≤-·o)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (absℚ; absℚ-sq; 0≤absℚ)
open import corpus.cubical_agda.Corridor.Running.General.QuadLemmas using (sqrt-mono-≤)
open import corpus.cubical_agda.Corridor.Running.General.QuadBound using (val≤abs)

private
  0≤·0≤ : (a b : ℚ) → 0 ≤ a → 0 ≤ b → 0 ≤ (a · b)
  0≤·0≤ a b 0≤a 0≤b = subst (_≤ (a · b)) (·AnnihilL b) (≤-·o 0 a b 0≤b 0≤a)
  0≤sum : (a b : ℚ) → 0 ≤ a → 0 ≤ b → 0 ≤ (a + b)
  0≤sum a b 0≤a 0≤b = subst (_≤ (a + b)) (+IdL 0) (≤Monotone+ 0 a 0 b 0≤a 0≤b)

-- squares are injective on the nonnegatives:  a² = b²  ⟹  a = b.
sqrt-inj : (a b : ℚ) → 0 ≤ a → 0 ≤ b → (a · a) ≡ (b · b) → a ≡ b
sqrt-inj a b 0≤a 0≤b aa≡bb =
  isAntisym≤ a b
    (sqrt-mono-≤ a b 0≤a 0≤b (subst ((a · a) ≤_) aa≡bb (isRefl≤ (a · a))))
    (sqrt-mono-≤ b a 0≤b 0≤a (subst (_≤ (a · a)) aa≡bb (isRefl≤ (a · a))))

-- |x·y| = |x|·|y|.
abs-mult : (x y : ℚ) → absℚ (x · y) ≡ (absℚ x · absℚ y)
abs-mult x y = sqrt-inj (absℚ (x · y)) (absℚ x · absℚ y)
  (0≤absℚ (x · y)) (0≤·0≤ (absℚ x) (absℚ y) (0≤absℚ x) (0≤absℚ y)) sqEq
  where
    sqEq : (absℚ (x · y) · absℚ (x · y)) ≡ ((absℚ x · absℚ y) · (absℚ x · absℚ y))
    sqEq = absℚ-sq (x · y) ∙ prodSqR ℚCommRing x y
         ∙ sym (cong₂ _·_ (absℚ-sq x) (absℚ-sq y))
         ∙ sym (prodSqR ℚCommRing (absℚ x) (absℚ y))

-- |x+y| ≤ |x|+|y|.
abs-triangle : (x y : ℚ) → absℚ (x + y) ≤ (absℚ x + absℚ y)
abs-triangle x y = sqrt-mono-≤ (absℚ (x + y)) (absℚ x + absℚ y)
  (0≤absℚ (x + y)) (0≤sum (absℚ x) (absℚ y) (0≤absℚ x) (0≤absℚ y)) sq≤
  where
    sq≤ : (absℚ (x + y) · absℚ (x + y)) ≤ ((absℚ x + absℚ y) · (absℚ x + absℚ y))
    sq≤ = subst2 _≤_ (sym lhs) (sym rhs) mono
      where
        lhs : (absℚ (x + y) · absℚ (x + y)) ≡ (((x · x) + ((x · y) + (x · y))) + (y · y))
        lhs = absℚ-sq (x + y) ∙ sumSqR ℚCommRing x y
        rhs : ((absℚ x + absℚ y) · (absℚ x + absℚ y))
            ≡ (((x · x) + ((absℚ x · absℚ y) + (absℚ x · absℚ y))) + (y · y))
        rhs = sumSqR ℚCommRing (absℚ x) (absℚ y)
            ∙ cong (λ z → ((z + ((absℚ x · absℚ y) + (absℚ x · absℚ y))) + (absℚ y · absℚ y))) (absℚ-sq x)
            ∙ cong (λ z → (((x · x) + ((absℚ x · absℚ y) + (absℚ x · absℚ y))) + z)) (absℚ-sq y)
        xy≤ : (x · y) ≤ (absℚ x · absℚ y)
        xy≤ = subst ((x · y) ≤_) (abs-mult x y) (val≤abs (x · y))
        mono : (((x · x) + ((x · y) + (x · y))) + (y · y))
             ≤ (((x · x) + ((absℚ x · absℚ y) + (absℚ x · absℚ y))) + (y · y))
        mono = ≤Monotone+ ((x · x) + ((x · y) + (x · y)))
                          ((x · x) + ((absℚ x · absℚ y) + (absℚ x · absℚ y))) (y · y) (y · y)
                 (≤Monotone+ (x · x) (x · x) ((x · y) + (x · y)) ((absℚ x · absℚ y) + (absℚ x · absℚ y))
                    (isRefl≤ (x · x)) (≤Monotone+ (x · y) (absℚ x · absℚ y) (x · y) (absℚ x · absℚ y) xy≤ xy≤))
                 (isRefl≤ (y · y))
