{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE APPROXIMATION LEMMA — every located real has arbitrarily tight rational brackets.
--
-- RealApprox built the trisection contraction (trisect-n: a bracket of width EXACTLY (2/3)ⁿ·(c−a));
-- this assembles it into the keystone the module named: for any δ>0, a bracket [a,c] of x with a∈L(x),
-- c∈U(x) and c−a < δ.  Proof = iterate the contraction the right number of times: on the even
-- subsequence W^{2k} = (2/3)^{2k} = (4/9)ᵏ = pow49 k, which the landed pow49-vanish drives below any δ.
-- This is the missing piece for Dedekind addition (located-real arithmetic) and the Z[φ] matrix layer.
--
module corpus.cubical_agda.Corridor.Running.General.ApproxReal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; _×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Int using (pos; pos·pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import corpus.cubical_agda.Corridor.Running.General.GeometricBoundN using (p4)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; _≤_; isTrans<; isTrans<≤; <Weaken≤; ≮→≥; isAntisym≤; <Dec)
open import corpus.cubical_agda.RealCohesion.DedekindReal using (ℝ; ⟦_⟧; lowerCut; upperCut; IsCut)
open import corpus.cubical_agda.RealCohesion.RealApprox using (W; _^ℚ_; trisect-n)
open import corpus.cubical_agda.Corridor.Running.Bracket using (dbl)
open import corpus.cubical_agda.Corridor.Running.General.GeometricBoundQ using (pow49)
open import corpus.cubical_agda.Corridor.Running.General.GeometricVanish using (pow49-vanish)

private
  IsYes : {A : Type₀} → Dec A → Type₀
  IsYes (yes _) = Unit
  IsYes (no  _) = ⊥
  getYes : {A : Type₀} (d : Dec A) → IsYes d → A
  getYes (yes a) _ = a

  twothirds : ℚ
  twothirds = [ pos 2 / 1+ 2 ]
  W≡⅔ : W ≡ twothirds
  W≡⅔ = getYes (discreteℚ W twothirds) tt
  ⅔² : (twothirds · twothirds) ≡ [ pos 4 / 1+ 8 ]
  ⅔² = getYes (discreteℚ (twothirds · twothirds) [ pos 4 / 1+ 8 ]) tt
  W·W≡49 : (W · W) ≡ [ pos 4 / 1+ 8 ]
  W·W≡49 = cong₂ _·_ W≡⅔ W≡⅔ ∙ ⅔²
  pow49-rec : (k : ℕ) → pow49 (suc k) ≡ ([ pos 4 / 1+ 8 ] · pow49 k)
  pow49-rec k = cong₂ [_/_] (pos·pos 4 (p4 k)) refl

-- W^{2k} = (4/9)ᵏ = pow49 k.
W2k : (k : ℕ) → (W ^ℚ (dbl k)) ≡ pow49 k
W2k zero    = refl
W2k (suc k) =
    ·Assoc W W (W ^ℚ (dbl k))
  ∙ cong₂ _·_ W·W≡49 (W2k k)
  ∙ sym (pow49-rec k)

-- a rational below x is below a rational above x.
lt-LU : (x : ℝ) (a c : ℚ) → ⟦ lowerCut x ⟧ a → ⟦ upperCut x ⟧ c → a < c
lt-LU x a c xLa xUc with <Dec a c
... | yes a<c = a<c
... | no ¬a<c = ⊥-rec (x-disj c (x-down c a (c≤a→c<a) xLa) xUc)
  where
    cut : IsCut (lowerCut x) (upperCut x)
    cut = snd (snd x)
    x-down : (q r : ℚ) → q < r → ⟦ lowerCut x ⟧ r → ⟦ lowerCut x ⟧ q
    x-down = fst (snd (snd (snd (snd cut))))
    x-disj : (q : ℚ) → ⟦ lowerCut x ⟧ q → ⟦ upperCut x ⟧ q → ⊥
    x-disj = fst (snd (snd (snd (snd (snd (snd cut))))))
    -- ¬(a<c) gives c≤a; we only need c<a OR a≡c — but x-down needs c<a strictly.
    -- ≮→≥ gives c ≤ a; refine to c < a by excluding a≡c (which disjoint forbids at a).
    c≤a : c ≤ a
    c≤a = ≮→≥ a c ¬a<c
    c≤a→c<a : c < a
    c≤a→c<a with <Dec c a
    ... | yes c<a = c<a
    ... | no ¬c<a = ⊥-rec (x-disj a xLa (subst ⟦ upperCut x ⟧ (sym a≡c) xUc))
      where a≡c : a ≡ c
            a≡c = isAntisym≤ a c (≮→≥ c a ¬c<a) c≤a

-- THE APPROXIMATION LEMMA:  arbitrarily tight rational brackets of x.
approxℝ : (x : ℝ) (δ : ℚ) → 0 < δ
        → ∥ Σ[ a ∈ ℚ ] Σ[ c ∈ ℚ ] ⟦ lowerCut x ⟧ a × ⟦ upperCut x ⟧ c × ((c + (- a)) < δ) ∥₁
approxℝ x δ 0<δ = PT.rec squash₁
  (λ { (a₀ , xLa₀) → PT.rec squash₁
    (λ { (c₀ , xUc₀) →
      let a₀<c₀ = lt-LU x a₀ c₀ xLa₀ xUc₀
          0≤d₀ = <Weaken≤ 0 (c₀ + (- a₀)) (0<width a₀ c₀ a₀<c₀)
      in PT.rec squash₁
         (λ { (k , small) →
           PT.map
             (λ { (a , c , xLa , xUc , a<c , wEq) →
               a , c , xLa , xUc ,
                 subst (_< δ) (sym (wEq ∙ cong (_· (c₀ + (- a₀))) (W2k k))) small })
             (trisect-n (dbl k) x a₀ c₀ xLa₀ xUc₀ a₀<c₀) })
         (pow49-vanish (c₀ + (- a₀)) 0≤d₀ δ 0<δ) })
    (inhU x) }) (inhL x)
  where
    inhL : (x : ℝ) → ∥ Σ[ q ∈ ℚ ] ⟦ lowerCut x ⟧ q ∥₁
    inhL x = fst (snd (snd x))
    inhU : (x : ℝ) → ∥ Σ[ q ∈ ℚ ] ⟦ upperCut x ⟧ q ∥₁
    inhU x = fst (snd (snd (snd x)))
    0<width : (a c : ℚ) → a < c → 0 < (c + (- a))
    0<width a c a<c = subst (_< (c + (- a))) (+InvR a)
      (Cubical.Data.Rationals.Order.<-+o a c (- a) a<c)
      where import Cubical.Data.Rationals.Order
