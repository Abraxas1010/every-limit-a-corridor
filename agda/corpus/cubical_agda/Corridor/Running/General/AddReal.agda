{-# OPTIONS --cubical --safe --guardedness #-}
--
-- LOCATED-REAL ADDITION — x +ℝ y : ℝ, the sum of two Dedekind reals.
--
-- The cut: L(x+y) = {q | ∃ a∈L(x), b∈L(y), q<a+b}, U(x+y) = {q | ∃ a∈U(x), b∈U(y), a+b<q}.  Seven of
-- the eight laws are direct; LOCATEDNESS is the keystone — given q<r, the approximation lemma (approxℝ)
-- brackets x and y each to width < ½(r−q), so the bracket sum [aₓ+a_y, cₓ+c_y] for x+y has width < r−q
-- and one of q<aₓ+a_y (lower) or cₓ+c_y<r (upper) must hold.  With affineℝ (rational scaling) and -ℝ
-- (negation) this makes the located reals an ordered field, and unblocks the Z[φ] matrix layer.
--
module corpus.cubical_agda.Corridor.Running.General.AddReal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; _×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.Relation.Nullary using (yes; no)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr)
open import Cubical.Tactics.CommRingSolver using (solve!)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Nullary using (Dec)

-- abstract ring identities (before the ℚ open).
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  sumSplitR : (ax ay cx cy : ⟨ R ⟩)
            → (cx + cy) ≡ ((ax + ay) + ((cx + (- ax)) + (cy + (- ay))))
  sumSplitR ax ay cx cy = solve! R
  qrR : (q r : ⟨ R ⟩) → (q + (r + (- q))) ≡ r
  qrR q r = solve! R
  ddR : (s h : ⟨ R ⟩) → ((s · h) + (s · h)) ≡ (s · (h + h))
  ddR s h = solve! R

open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; isTrans<; isTrans<≤; isTrans≤<; isIrrefl<; <-+o; <-o+; <-·o; ≤-+o; ≮→≥; <Weaken≤; <Dec)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import corpus.cubical_agda.RealCohesion.DedekindReal
  using (ℝ; Pred; ⟦_⟧; IsCut; lowerCut; upperCut; dense; x<x+1; x-1<x; half; 0<half)
open import corpus.cubical_agda.Corridor.Running.General.ApproxReal using (approxℝ; lt-LU)

private
  -- half + half ≡ 1 and the two facts the located proof needs from it.
  IsYes : {A : Type₀} → Dec A → Type₀
  IsYes (yes _) = Unit
  IsYes (no  _) = ⊥
  getYes : {A : Type₀} (d : Dec A) → IsYes d → A
  getYes (yes a) _ = a
  hh : (half + half) ≡ 1
  hh = getYes (discreteℚ (half + half) 1) tt

module _ (x y : ℝ) where

  private
    Lx Ly Ux Uy : Pred
    Lx = lowerCut x ; Ly = lowerCut y
    Ux = upperCut x ; Uy = upperCut y
    cx : IsCut Lx Ux ; cx = snd (snd x)
    cy : IsCut Ly Uy ; cy = snd (snd y)
    iLx = fst cx ; iUx = fst (snd cx)
    iLy = fst cy ; iUy = fst (snd cy)
    dLx = fst (snd (snd (snd (snd cx))))       -- L down-closed
    uUx = fst (snd (snd (snd (snd (snd cx)))))  -- U up-closed
    dLy = fst (snd (snd (snd (snd cy))))
    uUy = fst (snd (snd (snd (snd (snd cy)))))

  Lp Up : Pred
  Lp q = (∥ Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] ⟦ Lx ⟧ a × ⟦ Ly ⟧ b × (q < (a + b)) ∥₁) , squash₁
  Up q = (∥ Σ[ a ∈ ℚ ] Σ[ b ∈ ℚ ] ⟦ Ux ⟧ a × ⟦ Uy ⟧ b × ((a + b) < q) ∥₁) , squash₁

  _+ℝ'_ : ℝ
  _+ℝ'_ = Lp , Up , (inhL , inhU , rndL , rndU , dnL , upU , disj , loc)
    where
      inhL : ∥ Σ[ q ∈ ℚ ] ⟦ Lp ⟧ q ∥₁
      inhL = PT.rec squash₁ (λ { (a , La) → PT.map
        (λ { (b , Lb) → ((a + b) + (- 1)) , ∣ a , b , La , Lb , x-1<x (a + b) ∣₁ }) iLy }) iLx
      inhU : ∥ Σ[ q ∈ ℚ ] ⟦ Up ⟧ q ∥₁
      inhU = PT.rec squash₁ (λ { (a , Ua) → PT.map
        (λ { (b , Ub) → ((a + b) + 1) , ∣ a , b , Ua , Ub , x<x+1 (a + b) ∣₁ }) iUy }) iUx

      rndL : (q : ℚ) → ⟦ Lp ⟧ q → ∥ Σ[ r ∈ ℚ ] (q < r) × ⟦ Lp ⟧ r ∥₁
      rndL q = PT.map (λ { (a , b , La , Lb , q<ab) →
        let (c , q<c , c<ab) = dense q (a + b) q<ab in c , q<c , ∣ a , b , La , Lb , c<ab ∣₁ })
      rndU : (q : ℚ) → ⟦ Up ⟧ q → ∥ Σ[ r ∈ ℚ ] (r < q) × ⟦ Up ⟧ r ∥₁
      rndU q = PT.map (λ { (a , b , Ua , Ub , ab<q) →
        let (c , ab<c , c<q) = dense (a + b) q ab<q in c , c<q , ∣ a , b , Ua , Ub , ab<c ∣₁ })

      dnL : (q r : ℚ) → q < r → ⟦ Lp ⟧ r → ⟦ Lp ⟧ q
      dnL q r q<r = PT.map (λ { (a , b , La , Lb , r<ab) →
        a , b , La , Lb , isTrans< q r (a + b) q<r r<ab })
      upU : (q r : ℚ) → q < r → ⟦ Up ⟧ q → ⟦ Up ⟧ r
      upU q r q<r = PT.map (λ { (a , b , Ua , Ub , ab<q) →
        a , b , Ua , Ub , isTrans< (a + b) q r ab<q q<r })

      disj : (q : ℚ) → ⟦ Lp ⟧ q → ⟦ Up ⟧ q → ⊥
      disj q lq uq = PT.rec isProp⊥ (λ { (a , b , La , Lb , q<ab) → PT.rec isProp⊥
        (λ { (a' , b' , Ua' , Ub' , a'b'<q) →
          isIrrefl< q (isTrans< q (a + b) q q<ab
            (isTrans< (a + b) (a' + b') q
              (<-+o' a b (lt-LU x a a' La Ua') (lt-LU y b b' Lb Ub')) a'b'<q)) }) uq }) lq
        where
          -- a<a' , b<b'  ⟹  a+b < a'+b'
          <-+o' : (s t : ℚ) → {s' t' : ℚ} → s < s' → t < t' → (s + t) < (s' + t')
          <-+o' s t {s'} {t'} s<s' t<t' =
            isTrans< (s + t) (s' + t) (s' + t') (<-+o s s' t s<s') (<-o+ t t' s' t<t')

      loc : (q r : ℚ) → q < r → ∥ ⟦ Lp ⟧ q ⊎ ⟦ Up ⟧ r ∥₁
      loc q r q<r =
        PT.rec squash₁ (λ { (ax , cx' , Lxa , Uxc , wx) → PT.map
          (λ { (ay , cy' , Lya , Uyc , wy) → decide ax cx' ay cy' Lxa Uxc Lya Uyc wx wy })
          (approxℝ y δ 0<δ) }) (approxℝ x δ 0<δ)
        where
          δ : ℚ
          δ = (r + (- q)) · half
          0<r-q : 0 < (r + (- q))
          0<r-q = subst (_< (r + (- q))) (+InvR q) (<-+o q r (- q) q<r)
          0<δ : 0 < δ
          0<δ = subst (_< δ) (·AnnihilL half) (<-·o 0 (r + (- q)) half 0<half 0<r-q)
          decide : (ax cx' ay cy' : ℚ)
                 → ⟦ Lx ⟧ ax → ⟦ Ux ⟧ cx' → ⟦ Ly ⟧ ay → ⟦ Uy ⟧ cy'
                 → ((cx' + (- ax)) < δ) → ((cy' + (- ay)) < δ)
                 → ⟦ Lp ⟧ q ⊎ ⟦ Up ⟧ r
          decide ax cx' ay cy' Lxa Uxc Lya Uyc wx wy with <Dec q (ax + ay)
          ... | yes q<axay = inl ∣ ax , ay , Lxa , Lya , q<axay ∣₁
          ... | no ¬q<axay = inr ∣ cx' , cy' , Uxc , Uyc , cxcy<r ∣₁
            where
              axay≤q : (ax + ay) ≤ q
              axay≤q = ≮→≥ q (ax + ay) ¬q<axay
              widthSum< : ((cx' + (- ax)) + (cy' + (- ay))) < (δ + δ)
              widthSum< = isTrans< ((cx' + (- ax)) + (cy' + (- ay))) (δ + (cy' + (- ay))) (δ + δ)
                (<-+o (cx' + (- ax)) δ (cy' + (- ay)) wx) (<-o+ (cy' + (- ay)) δ δ wy)
              cxcy<axayδδ : (cx' + cy') < ((ax + ay) + (δ + δ))
              cxcy<axayδδ = subst (_< ((ax + ay) + (δ + δ))) (sym (sumSplitR ℚCommRing ax ay cx' cy'))
                (<-o+ ((cx' + (- ax)) + (cy' + (- ay))) (δ + δ) (ax + ay) widthSum<)
              axayδδ≤r : ((ax + ay) + (δ + δ)) ≤ r
              axayδδ≤r = subst (((ax + ay) + (δ + δ)) ≤_) qδδ≡r (≤-+o (ax + ay) q (δ + δ) axay≤q)
                where qδδ≡r : (q + (δ + δ)) ≡ r
                      qδδ≡r = cong (q +_) δ+δ≡r-q ∙ qrR ℚCommRing q r
                        where δ+δ≡r-q : (δ + δ) ≡ (r + (- q))
                              δ+δ≡r-q = ddR ℚCommRing (r + (- q)) half
                                      ∙ cong ((r + (- q)) ·_) hh ∙ ·IdR (r + (- q))
              cxcy<r : (cx' + cy') < r
              cxcy<r = isTrans<≤ (cx' + cy') ((ax + ay) + (δ + δ)) r cxcy<axayδδ axayδδ≤r

-- the located reals are now an ordered field (with affineℝ scaling and -ℝ negation).
addℝ : ℝ → ℝ → ℝ
addℝ x y = _+ℝ'_ x y
