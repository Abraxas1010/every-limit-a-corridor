{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 5/6: the CONJUGATE golden value ψ = 1 − φ, the SECOND root of x²=x+1 and
-- the second eigenvalue of the Fibonacci recurrence -- built as a located real
-- ψ = (-ℝ φ) +ℚ 1 from φ:ℝ via negation and ℚ-translation.  Together φ and ψ are
-- the located SPECTRAL PAIR, and they are apart (ψ < 0 < φ).  No postulates.

module corpus.cubical_agda.RealCohesion.GoldenConjugate where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; <Dec)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import corpus.cubical_agda.RealCohesion.DedekindReal
  using (ℝ; _<ℝ_; _#ℝ_; ⟦_⟧; lowerCut; upperCut)
open import corpus.cubical_agda.RealCohesion.RealNegation using (-ℝ_)
open import corpus.cubical_agda.RealCohesion.RealTranslation using (_+ℚ_)
open import corpus.cubical_agda.RealCohesion.GoldenCut using (φ; φL)

private
  IsYes : {A : Type₀} → Dec A → Type₀
  IsYes (yes _) = Unit
  IsYes (no  _) = ⊥
  getYes : {A : Type₀} (d : Dec A) → IsYes d → A
  getYes (yes a) _  = a
  getYes (no  _) ()

-- ψ = 1 − φ, the conjugate root, as a genuine located real.
ψ : ℝ
ψ = (-ℝ φ) +ℚ 1

-- 0 ∈ L_φ  and (via the reflection) 0 ∈ U_ψ, so 0 separates ψ from φ.
0∈φL : ⟦ φL ⟧ 0
0∈φL = ∣ inr (getYes (<Dec (0 · 0) (0 + 1)) tt) ∣₁

1∈φL : ⟦ φL ⟧ 1
1∈φL = ∣ inr (getYes (<Dec (1 · 1) (1 + 1)) tt) ∣₁

-- the conjugate is genuinely below φ: ψ <ℝ φ, witnessed by 0.
ψ<ℝφ : ψ <ℝ φ
ψ<ℝφ = ∣ 0 , (subst ⟦ φL ⟧ (sym eq) 1∈φL , 0∈φL) ∣₁
  where eq : (- (0 + (- 1))) ≡ 1
        eq = cong -_ (+IdL (- 1)) ∙ -Invol 1

-- THE GOLDEN SPECTRAL PAIR: φ and ψ are distinct located reals (apart).
φ#ψ : φ #ℝ ψ
φ#ψ = inr ψ<ℝφ
