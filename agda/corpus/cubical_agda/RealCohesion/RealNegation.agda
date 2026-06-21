{-# OPTIONS --cubical --safe --guardedness #-}

-- Sprint 5 / real arithmetic: NEGATION on the analytic real line.  The first
-- real-arithmetic operation -- (-ℝ x) just swaps and flips x's two cuts, so each
-- Dedekind-cut law follows from x's own law by symmetry.  This is the on-ramp to
-- Dedekind addition and, ultimately, φ as a located real.  No postulates.

module corpus.cubical_agda.RealCohesion.RealNegation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; <-+o-cancel)

-- the order-flip:  q < r  ⟹  - r < - q.
neg-flip : (q r : ℚ) → q < r → (- r) < (- q)
neg-flip q r q<r = <-+o-cancel (- r) (- q) (q + r) (subst2 _<_ (sym lemr) (sym lemq) q<r)
  where
    lemr : (- r) + (q + r) ≡ q
    lemr = (- r) + (q + r)   ≡⟨ +Comm (- r) (q + r) ⟩
           (q + r) + (- r)   ≡⟨ sym (+Assoc q r (- r)) ⟩
           q + (r + (- r))   ≡⟨ cong (q +_) (+InvR r) ⟩
           q + 0             ≡⟨ +IdR q ⟩
           q ∎
    lemq : (- q) + (q + r) ≡ r
    lemq = (- q) + (q + r)   ≡⟨ +Assoc (- q) q r ⟩
           ((- q) + q) + r   ≡⟨ cong (_+ r) (+InvL q) ⟩
           0 + r             ≡⟨ +IdL r ⟩
           r ∎

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁)
open import corpus.cubical_agda.RealCohesion.DedekindReal

-- NEGATION on the reals: swap and flip the two cuts.  (-ℝ x).L q = x.U(−q).
-ℝ_ : ℝ → ℝ
-ℝ x = Lneg , Uneg , (l1 , l2 , l3 , l4 , l5 , l6 , l7 , l8)
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

    Lneg Uneg : Pred
    Lneg q = Ux (- q)
    Uneg q = Lx (- q)

    -- inhabitation
    l1 = PT.map (λ { (p , h) → (- p) , subst ⟦ Ux ⟧ (sym (-Invol p)) h }) xUinhab
    l2 = PT.map (λ { (p , h) → (- p) , subst ⟦ Lx ⟧ (sym (-Invol p)) h }) xLinhab
    -- roundedness (open above / below), via U-open / L-open of x
    l3 : (q : ℚ) → ⟦ Lneg ⟧ q → ∥ Σ[ r ∈ ℚ ] (q < r) × ⟦ Lneg ⟧ r ∥₁
    l3 q h = PT.map (λ { (s , s<-q , xUs) →
               (- s) , (subst (_< (- s)) (-Invol q) (neg-flip s (- q) s<-q)
                       , subst ⟦ Ux ⟧ (sym (-Invol s)) xUs) }) (xUopen (- q) h)
    l4 : (q : ℚ) → ⟦ Uneg ⟧ q → ∥ Σ[ r ∈ ℚ ] (r < q) × ⟦ Uneg ⟧ r ∥₁
    l4 q h = PT.map (λ { (s , -q<s , xLs) →
               (- s) , (subst ((- s) <_) (-Invol q) (neg-flip (- q) s -q<s)
                       , subst ⟦ Lx ⟧ (sym (-Invol s)) xLs) }) (xLopen (- q) h)
    -- closure
    l5 : (q r : ℚ) → q < r → ⟦ Lneg ⟧ r → ⟦ Lneg ⟧ q
    l5 q r q<r h = xUup (- r) (- q) (neg-flip q r q<r) h
    l6 : (q r : ℚ) → q < r → ⟦ Uneg ⟧ q → ⟦ Uneg ⟧ r
    l6 q r q<r h = xLdown (- r) (- q) (neg-flip q r q<r) h
    -- disjointness
    l7 : (q : ℚ) → ⟦ Lneg ⟧ q → ⟦ Uneg ⟧ q → ⊥
    l7 q hL hU = xdisj (- q) hU hL
    -- locatedness (reorder the disjuncts of x.located)
    l8 : (q r : ℚ) → q < r → ∥ ⟦ Lneg ⟧ q ⊎ ⟦ Uneg ⟧ r ∥₁
    l8 q r q<r = PT.map (λ { (inl xLr) → inr xLr ; (inr xUq) → inl xUq })
                        (xloc (- r) (- q) (neg-flip q r q<r))

-- the defining property: negation REVERSES the strict order.
-ℝ-reverses : (x y : ℝ) → x <ℝ y → (-ℝ y) <ℝ (-ℝ x)
-ℝ-reverses x y = PT.map λ { (q , xUq , yLq) →
  (- q) , ( subst ⟦ lowerCut y ⟧ (sym (-Invol q)) yLq
          , subst ⟦ upperCut x ⟧ (sym (-Invol q)) xUq ) }

-- negation is involutive: -ℝ(-ℝ x) ≡ x (both cuts collapse via -Invol).
-ℝ-involutive : (x : ℝ) → -ℝ (-ℝ x) ≡ x
-ℝ-involutive x = ΣPathP (pL , ΣPathP (pU ,
                    isProp→PathP (λ i → isPropIsCut (pL i) (pU i)) _ _))
  where
    pL : (λ q → lowerCut x (- (- q))) ≡ lowerCut x
    pL = funExt λ q → cong (lowerCut x) (-Invol q)
    pU : (λ q → upperCut x (- (- q))) ≡ upperCut x
    pU = funExt λ q → cong (upperCut x) (-Invol q)
