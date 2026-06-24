{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE GOLDEN FIELD AS LOCATED REALS — zphiReal a b : ℝ realises every a+bφ ∈ Q[φ]  (Item: Z[φ] frontier).
--
-- The remaining operator-norm frontier is the coefficient ring Z[φ] (entries a+bφ).  Its foundation is
-- the embedding Q[φ] ↪ ℝ as located reals: a+bφ is a located Dedekind real for all a,b.  For b>0 it is
-- the affine image affineℝ b a φ = b·φ+a of the golden value; for b=0 the rational embedding ι a; for
-- b<0 the negation negℝ of the b>0 case.  Hence the cut condition the Z[φ] spectral radius needs ---
-- "rational q below a+bφ" --- is membership in this located real's lower cut, decidable through φ's own
-- quadratic located law.  negℝ (the negation of a located real, L↔U swapped under q↦−q) completes the
-- field structure on the located reals.
--
module corpus.cubical_agda.Corridor.Running.General.ZPhiReal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; _×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr)
open import Cubical.Tactics.CommRingSolver using (solve!)

-- abstract ring identities for neg-reverses-order (before the ℚ open).
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  n1 : (x y : ⟨ R ⟩) → (((- x) + (- y)) + x) ≡ (- y)
  n1 x y = solve! R
  n2 : (x y : ⟨ R ⟩) → (((- x) + (- y)) + y) ≡ (- x)
  n2 x y = solve! R

open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; <-o+; _≟_; lt; eq; gt)
open import corpus.cubical_agda.RealCohesion.DedekindReal
  using (ℝ; Pred; ⟦_⟧; lowerCut; upperCut; ι)
open import corpus.cubical_agda.RealCohesion.GoldenCut using (φ)
open import corpus.cubical_agda.Corridor.Running.General.AffineReal using (affineℝ)

-- negation reverses the strict order:  q < r ⟹ −r < −q.
neg-rev : (q r : ℚ) → q < r → (- r) < (- q)
neg-rev q r q<r = subst2 _<_ (n1 ℚCommRing q r) (n2 ℚCommRing q r)
                    (<-o+ q r ((- q) + (- r)) q<r)
  where open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)

-- NEGATION of a located real:  −x has lower cut U(x)∘(−·), upper cut L(x)∘(−·).
negℝ : ℝ → ℝ
negℝ (Lx , Ux , (iL , iU , rL , rU , dL , uU , dj , lc)) =
  Ln , Un , (inhLn , inhUn , rndLn , rndUn , dnLn , upUn , disjn , locn)
  where
    Ln Un : Pred
    Ln q = Ux (- q)
    Un q = Lx (- q)

    inhLn : ∥ Σ[ q ∈ ℚ ] ⟦ Ln ⟧ q ∥₁
    inhLn = PT.map (λ { (s , Us) → (- s) , subst ⟦ Ux ⟧ (sym (-Invol s)) Us }) iU
    inhUn : ∥ Σ[ q ∈ ℚ ] ⟦ Un ⟧ q ∥₁
    inhUn = PT.map (λ { (s , Ls) → (- s) , subst ⟦ Lx ⟧ (sym (-Invol s)) Ls }) iL

    rndLn : (q : ℚ) → ⟦ Ln ⟧ q → ∥ Σ[ r ∈ ℚ ] (q < r) × ⟦ Ln ⟧ r ∥₁
    rndLn q Lnq = PT.map
      (λ { (s , s<-q , Us) →
            (- s) , subst (_< (- s)) (-Invol q) (neg-rev s (- q) s<-q)
                  , subst ⟦ Ux ⟧ (sym (-Invol s)) Us })
      (rU (- q) Lnq)
    rndUn : (q : ℚ) → ⟦ Un ⟧ q → ∥ Σ[ r ∈ ℚ ] (r < q) × ⟦ Un ⟧ r ∥₁
    rndUn q Unq = PT.map
      (λ { (s , -q<s , Ls) →
            (- s) , subst ((- s) <_) (-Invol q) (neg-rev (- q) s -q<s)
                  , subst ⟦ Lx ⟧ (sym (-Invol s)) Ls })
      (rL (- q) Unq)

    dnLn : (q r : ℚ) → q < r → ⟦ Ln ⟧ r → ⟦ Ln ⟧ q
    dnLn q r q<r Lnr = uU (- r) (- q) (neg-rev q r q<r) Lnr
    upUn : (q r : ℚ) → q < r → ⟦ Un ⟧ q → ⟦ Un ⟧ r
    upUn q r q<r Unq = dL (- r) (- q) (neg-rev q r q<r) Unq

    disjn : (q : ℚ) → ⟦ Ln ⟧ q → ⟦ Un ⟧ q → ⊥
    disjn q Lnq Unq = dj (- q) Unq Lnq

    locn : (q r : ℚ) → q < r → ∥ ⟦ Ln ⟧ q ⊎ ⟦ Un ⟧ r ∥₁
    locn q r q<r = PT.map
      (λ { (inl L-r) → inr L-r ; (inr U-q) → inl U-q })
      (lc (- r) (- q) (neg-rev q r q<r))

-- THE GOLDEN INTEGERS/RATIONALS as located reals:  a + bφ : ℝ for all a, b : ℚ.
zphiReal : (a b : ℚ) → ℝ
zphiReal a b with b ≟ 0
... | gt 0<b = affineℝ b a 0<b φ                                   -- b·φ + a
... | eq b≡0 = ι a                                                 -- the rational a
... | lt b<0 = negℝ (affineℝ (- b) (- a) 0<-b φ)                   -- −((−b)·φ + (−a)) = a + bφ
  where 0<-b : 0 < (- b)
        0<-b = subst2 _<_ (+InvL b) (+IdR (- b)) (<-o+ b 0 (- b) b<0)
