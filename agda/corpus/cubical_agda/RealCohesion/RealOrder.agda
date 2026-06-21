{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 5 support: the strict order on the analytic real line is a genuine
-- strict partial order (irreflexive + transitive).  This is the order structure
-- the located spectrum lives in -- a spectral value is pinned by where it sits
-- in <ℝ.  Built on Sprint-1's Dedekind ℝ; pure cut algebra, no postulates.

module corpus.cubical_agda.RealCohesion.RealOrder where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Data.Rationals.Order using (_<_; _≟_; lt; eq; gt; isAsym<)
open import corpus.cubical_agda.RealCohesion.DedekindReal

-- the cut-law projections (IsCut is the right-nested 8-tuple; cut = x .snd .snd)
private
  cutOf : (x : ℝ) → IsCut (lowerCut x) (upperCut x)
  cutOf x = x .snd .snd

  UupOf : (x : ℝ) (q r : ℚ) → q < r → ⟦ upperCut x ⟧ q → ⟦ upperCut x ⟧ r
  UupOf x = cutOf x .snd .snd .snd .snd .snd .fst

  LdownOf : (x : ℝ) (q r : ℚ) → q < r → ⟦ lowerCut x ⟧ r → ⟦ lowerCut x ⟧ q
  LdownOf x = cutOf x .snd .snd .snd .snd .fst

  disjOf : (x : ℝ) (q : ℚ) → ⟦ lowerCut x ⟧ q → ⟦ upperCut x ⟧ q → ⊥
  disjOf x = cutOf x .snd .snd .snd .snd .snd .snd .fst

-- a rational in y's lower cut is strictly below one in y's upper cut.
private
  cut-sep : (y : ℝ) (q r : ℚ) → ⟦ lowerCut y ⟧ q → ⟦ upperCut y ⟧ r → q < r
  cut-sep y q r yLq yUr with q ≟ r
  ... | lt q<r = q<r
  ... | eq q≡r = ⊥.rec (disjOf y r (subst (λ z → ⟦ lowerCut y ⟧ z) q≡r yLq) yUr)
  ... | gt r<q = ⊥.rec (disjOf y q yLq (UupOf y r q r<q yUr))

-- the strict real order is TRANSITIVE.
<ℝ-trans : (x y z : ℝ) → x <ℝ y → y <ℝ z → x <ℝ z
<ℝ-trans x y z = PT.rec2 squash₁ λ { (q , xUq , yLq) (r , yUr , zLr) →
  ∣ q , xUq , LdownOf z q r (cut-sep y q r yLq yUr) zLr ∣₁ }

-- irreflexive (a rational cannot be in both cuts) and asymmetric.
<ℝ-irrefl : (x : ℝ) → ¬ (x <ℝ x)
<ℝ-irrefl x = PT.rec (λ p q i → ⊥.isProp⊥ p q i)
                     (λ { (s , xUs , xLs) → disjOf x s xLs xUs })

<ℝ-asym : (x y : ℝ) → x <ℝ y → ¬ (y <ℝ x)
<ℝ-asym x y x<y y<x = <ℝ-irrefl x (<ℝ-trans x y x x<y y<x)
