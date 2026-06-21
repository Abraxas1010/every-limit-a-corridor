{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 5/6: the ℚ-TRANSLATION action on ℝ.  (x +ℚ r) shifts every cut of x by
-- r -- a pure shift, so all eight Dedekind-cut laws follow from x's by the
-- order-preserving bijection q ↦ q−r (no convergence needed, unlike full +ℝ).
-- This is the rational-translation group action ℚ ↷ ℝ, and it yields the
-- conjugate golden value ψ = 1−φ -- the SECOND located eigenvalue.  No postulates.

module corpus.cubical_agda.RealCohesion.RealTranslation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; <-+o)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁)
open import corpus.cubical_agda.RealCohesion.DedekindReal

-- shift identities for the bijection q ↦ q + (- r) and its inverse.
private
  cancelR : (q r : ℚ) → (q + r) + (- r) ≡ q
  cancelR q r = sym (+Assoc q r (- r)) ∙ cong (q +_) (+InvR r) ∙ +IdR q
  cancelL : (q r : ℚ) → (q + (- r)) + r ≡ q
  cancelL q r = sym (+Assoc q (- r) r) ∙ cong (q +_) (+InvL r) ∙ +IdR q

-- TRANSLATION: (x +ℚ r).L q = x.L (q − r).
_+ℚ_ : ℝ → ℚ → ℝ
x +ℚ r = L' , U' , (m1 , m2 , m3 , m4 , m5 , m6 , m7 , m8)
  where
    Lx Ux : Pred
    Lx = lowerCut x ;  Ux = upperCut x
    cx = x .snd .snd
    xLinhab = cx .fst
    xUinhab = cx .snd .fst
    xLopen  = cx .snd .snd .fst
    xUopen  = cx .snd .snd .snd .fst
    xLdown  = cx .snd .snd .snd .snd .fst
    xUup    = cx .snd .snd .snd .snd .snd .fst
    xdisj   = cx .snd .snd .snd .snd .snd .snd .fst
    xloc    = cx .snd .snd .snd .snd .snd .snd .snd

    L' U' : Pred
    L' q = Lx (q + (- r))
    U' q = Ux (q + (- r))

    -- inhabitation: shift the witness by +r.
    m1 = PT.map (λ { (p , h) → (p + r) , subst ⟦ Lx ⟧ (sym (cancelR p r)) h }) xLinhab
    m2 = PT.map (λ { (p , h) → (p + r) , subst ⟦ Ux ⟧ (sym (cancelR p r)) h }) xUinhab
    -- roundedness: shift the rounding witness.
    m3 : (q : ℚ) → ⟦ L' ⟧ q → ∥ Σ[ s ∈ ℚ ] (q < s) × ⟦ L' ⟧ s ∥₁
    m3 q h = PT.map (λ { (s , q-r<s , xLs) →
               (s + r) , (subst (_< (s + r)) (cancelL q r) (<-+o (q + (- r)) s r q-r<s)
                         , subst ⟦ Lx ⟧ (sym (cancelR s r)) xLs) }) (xLopen (q + (- r)) h)
    m4 : (q : ℚ) → ⟦ U' ⟧ q → ∥ Σ[ s ∈ ℚ ] (s < q) × ⟦ U' ⟧ s ∥₁
    m4 q h = PT.map (λ { (s , s<q-r , xUs) →
               (s + r) , (subst ((s + r) <_) (cancelL q r) (<-+o s (q + (- r)) r s<q-r)
                         , subst ⟦ Ux ⟧ (sym (cancelR s r)) xUs) }) (xUopen (q + (- r)) h)
    -- closure: translation preserves order.
    m5 : (q s : ℚ) → q < s → ⟦ L' ⟧ s → ⟦ L' ⟧ q
    m5 q s q<s h = xLdown (q + (- r)) (s + (- r)) (<-+o q s (- r) q<s) h
    m6 : (q s : ℚ) → q < s → ⟦ U' ⟧ q → ⟦ U' ⟧ s
    m6 q s q<s h = xUup (q + (- r)) (s + (- r)) (<-+o q s (- r) q<s) h
    -- disjointness (same shifted point).
    m7 : (q : ℚ) → ⟦ L' ⟧ q → ⟦ U' ⟧ q → ⊥
    m7 q hL hU = xdisj (q + (- r)) hL hU
    -- locatedness: shift both bounds.
    m8 : (q s : ℚ) → q < s → ∥ ⟦ L' ⟧ q ⊎ ⟦ U' ⟧ s ∥₁
    m8 q s q<s = xloc (q + (- r)) (s + (- r)) (<-+o q s (- r) q<s)
