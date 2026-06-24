{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE AFFINE GROUP ACTING ON THE LOCATED REALS — affineℝ k c (k>0) : ℝ → ℝ sends x ↦ k·x + c.
--
-- reparamℝ transports a located real along ANY strictly-increasing ℚ-bijection.  The affine map
-- ψ(p)=k·p+c (k>0) is one, with inverse φ(q)=(q−c)·k⁻¹ (ℚ is a field — hasInverseℚ).  So affineℝ k c
-- is reparamℝ φ ψ: positive-scale-and-shift of any located real, with all eight cut laws transferred.
-- This is the general affine machinery (the SpectralEdge half-shift was the special case k=½), and the
-- lego block that realises every golden integer a+bφ as a located real (ZPhiReal).
--
module corpus.cubical_agda.Corridor.Running.General.AffineReal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Sigma using (_,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr)
open import Cubical.Tactics.CommRingSolver using (solve!)

-- abstract ring rearrangements for the inverse equations (before the ℚ open, to avoid op-clash).
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  a1 : (k p c : ⟨ R ⟩) → (((k · p) + c) + (- c)) ≡ (k · p)
  a1 k p c = solve! R
  a2 : (k p i : ⟨ R ⟩) → ((k · p) · i) ≡ (p · (k · i))
  a2 k p i = solve! R
  a3 : (k q c i : ⟨ R ⟩) → ((k · ((q + (- c)) · i)) + c) ≡ ((((q + (- c)) · (k · i)) + c))
  a3 k q c i = solve! R
  a4 : (q c : ⟨ R ⟩) → (((q + (- c)) · 1r) + c) ≡ q
  a4 q c = solve! R

open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; isTrans<; isIrrefl<; <-+o; <-o+; <-·o; _≟_; lt; eq; gt)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Algebra.Field.Instances.Rationals using (hasInverseℚ)
open import corpus.cubical_agda.RealCohesion.DedekindReal using (ℝ; 0<1ℚ)
open import corpus.cubical_agda.Corridor.Running.General.ReparamReal using (reparamℝ)

private
  -- inverse of a positive is positive (k·i = 1 > 0).
  0<inv : (k i : ℚ) → 0 < k → (k · i) ≡ 1 → 0 < i
  0<inv k i 0<k ki≡1 with i ≟ 0
  ... | gt 0<i = 0<i
  ... | eq i≡0 = ⊥-rec (isIrrefl< 0 (subst (0 <_) (sym ki≡1 ∙ cong (k ·_) i≡0 ∙ ·AnnihilR k) 0<1ℚ))
  ... | lt i<0 = ⊥-rec (isIrrefl< 0 (isTrans< 0 (k · i) 0
        (subst (0 <_) (sym ki≡1) 0<1ℚ)
        (subst2 _<_ (·Comm i k) (·AnnihilL k) (<-·o i 0 k 0<k i<0))))

module _ (k c : ℚ) (0<k : 0 < k) where

  private
    k≢0 : ¬ (k ≡ 0)
    k≢0 k≡0 = isIrrefl< 0 (subst (0 <_) k≡0 0<k)
    i : ℚ
    i = fst (hasInverseℚ k k≢0)
    k·i≡1 : (k · i) ≡ 1
    k·i≡1 = snd (hasInverseℚ k k≢0)
    0<i : 0 < i
    0<i = 0<inv k i 0<k k·i≡1

    φ ψ : ℚ → ℚ
    φ q = (q + (- c)) · i
    ψ p = (k · p) + c

    φ-mono : (q r : ℚ) → q < r → φ q < φ r
    φ-mono q r q<r = <-·o (q + (- c)) (r + (- c)) i 0<i (<-+o q r (- c) q<r)
    ψ-mono : (p p' : ℚ) → p < p' → ψ p < ψ p'
    ψ-mono p p' p<p' = <-+o (k · p) (k · p') c
      (subst2 _<_ (·Comm p k) (·Comm p' k) (<-·o p p' k 0<k p<p'))
    φ∘ψ : (p : ℚ) → φ (ψ p) ≡ p
    φ∘ψ p = cong (_· i) (a1 ℚCommRing k p c)
          ∙ a2 ℚCommRing k p i
          ∙ cong (p ·_) k·i≡1
          ∙ ·IdR p
    ψ∘φ : (q : ℚ) → ψ (φ q) ≡ q
    ψ∘φ q = a3 ℚCommRing k q c i
          ∙ cong (λ z → ((q + (- c)) · z) + c) k·i≡1
          ∙ a4 ℚCommRing q c

  -- x ↦ k·x + c, on any located real.
  affineℝ : ℝ → ℝ
  affineℝ = reparamℝ φ ψ φ-mono ψ-mono φ∘ψ ψ∘φ
