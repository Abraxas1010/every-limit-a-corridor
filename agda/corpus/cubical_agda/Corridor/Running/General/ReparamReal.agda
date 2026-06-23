{-# OPTIONS --cubical --safe --guardedness #-}
--
-- MONOTONE REPARAMETRIZATION OF A LOCATED REAL — reparamℝ φ ψ ρ : ℝ.
--
-- Given a strictly-increasing ℚ-bijection (φ, ψ inverse), reparamℝ sends a located real ρ to the real
-- ψ(value of ρ): its cut is just ρ's cut precomposed with φ (Lσ q = Lρ (φ q)).  All eight Dedekind-cut
-- laws transfer mechanically — φ-monotone moves the order side, ψ-monotone + the inverse equations move
-- the witness side.  This is the affine machinery for the corridor: the metallic ratios
-- (k+√(k²+4))/2 and the spectral edges (a+d+√Δ)/2 are reparametrizations of sqrtReal.
--
module corpus.cubical_agda.Corridor.Running.General.ReparamReal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (Σ-syntax; _,_; _×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁)
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Data.Rationals.Order using (_<_)
open import corpus.cubical_agda.RealCohesion.DedekindReal using (ℝ; Pred; ⟦_⟧; IsCut)

module _ (φ ψ : ℚ → ℚ)
         (φ-mono : (q r : ℚ) → q < r → φ q < φ r)
         (ψ-mono : (q r : ℚ) → q < r → ψ q < ψ r)
         (φ∘ψ : (p : ℚ) → φ (ψ p) ≡ p)
         (ψ∘φ : (q : ℚ) → ψ (φ q) ≡ q) where

  reparamℝ : ℝ → ℝ
  reparamℝ (Lρ , Uρ , (iL , iU , rL , rU , dL , uU , dj , lc)) =
    Lσ , Uσ , (inhL , inhU , rndL , rndU , dnL , upU , disj , loc)
    where
      Lσ Uσ : Pred
      Lσ q = Lρ (φ q)
      Uσ q = Uρ (φ q)

      inhL : ∥ Σ[ q ∈ ℚ ] ⟦ Lσ ⟧ q ∥₁
      inhL = PT.map (λ { (s , Ls) → ψ s , subst ⟦ Lρ ⟧ (sym (φ∘ψ s)) Ls }) iL

      inhU : ∥ Σ[ q ∈ ℚ ] ⟦ Uσ ⟧ q ∥₁
      inhU = PT.map (λ { (s , Us) → ψ s , subst ⟦ Uρ ⟧ (sym (φ∘ψ s)) Us }) iU

      rndL : (q : ℚ) → ⟦ Lσ ⟧ q → ∥ Σ[ r ∈ ℚ ] (q < r) × ⟦ Lσ ⟧ r ∥₁
      rndL q Lσq = PT.map
        (λ { (s , φq<s , Ls) →
              ψ s , subst (_< ψ s) (ψ∘φ q) (ψ-mono (φ q) s φq<s)
                  , subst ⟦ Lρ ⟧ (sym (φ∘ψ s)) Ls })
        (rL (φ q) Lσq)

      rndU : (q : ℚ) → ⟦ Uσ ⟧ q → ∥ Σ[ r ∈ ℚ ] (r < q) × ⟦ Uσ ⟧ r ∥₁
      rndU q Uσq = PT.map
        (λ { (s , s<φq , Us) →
              ψ s , subst (ψ s <_) (ψ∘φ q) (ψ-mono s (φ q) s<φq)
                  , subst ⟦ Uρ ⟧ (sym (φ∘ψ s)) Us })
        (rU (φ q) Uσq)

      dnL : (q r : ℚ) → q < r → ⟦ Lσ ⟧ r → ⟦ Lσ ⟧ q
      dnL q r q<r Lσr = dL (φ q) (φ r) (φ-mono q r q<r) Lσr

      upU : (q r : ℚ) → q < r → ⟦ Uσ ⟧ q → ⟦ Uσ ⟧ r
      upU q r q<r Uσq = uU (φ q) (φ r) (φ-mono q r q<r) Uσq

      disj : (q : ℚ) → ⟦ Lσ ⟧ q → ⟦ Uσ ⟧ q → ⊥
      disj q Lσq Uσq = dj (φ q) Lσq Uσq

      loc : (q r : ℚ) → q < r → ∥ ⟦ Lσ ⟧ q ⊎ ⟦ Uσ ⟧ r ∥₁
      loc q r q<r = lc (φ q) (φ r) (φ-mono q r q<r)
