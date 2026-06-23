{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE SPECTRAL EDGE AS A LOCATED REAL — specEdge a b d : ℝ, the larger eigenvalue of [[a,b],[b,d]].
--
-- λ₊ = (a + d + √Δ)/2,  Δ = (a−d)² + 4b² ≥ 0 (the discriminant).  This is the affine reparametrization
-- ψ(p) = (p + (a+d))·½ of sqrtReal Δ (value √Δ), with inverse φ(q) = 2q − (a+d).  reparamℝ transfers
-- all the cut laws, so λ₊ is a genuine located Dedekind real — Item F, certified spectral edges, with
-- NO eigenvector computation: the edge is the √ of the discriminant, shifted and halved.
--
module corpus.cubical_agda.Corridor.Running.General.SpectralEdgeReal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Algebra.CommRing using (CommRing; CommRingStr)
open import Cubical.Tactics.CommRingSolver using (solve!)

-- abstract ring rearrangements for the φ/ψ inverse equations (before the ℚ open).
module _ (R : CommRing ℓ-zero) where
  open CommRingStr (snd R)
  e1 : (p s h : ⟨ R ⟩) → ((((p + s) · h) + ((p + s) · h)) + (- s)) ≡ ((((p + s) · (h + h)) + (- s)))
  e1 p s h = solve! R
  e2 : (p s : ⟨ R ⟩) → ((((p + s) · 1r) + (- s))) ≡ p
  e2 p s = solve! R
  e3 : (q s h : ⟨ R ⟩) → (((((q + q) + (- s)) + s) · h)) ≡ (((q + q) · h))
  e3 q s h = solve! R
  e4 : (q h : ⟨ R ⟩) → (((q + q) · h)) ≡ ((q · (h + h)))
  e4 q h = solve! R
  e5 : (q : ⟨ R ⟩) → ((q · 1r)) ≡ q
  e5 q = solve! R

open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order
  using (_<_; _≤_; isTrans<; isTrans≤; <-+o; <-o+; <-·o; ≤-·o; <Weaken≤; <Dec)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import corpus.cubical_agda.RealCohesion.DedekindReal using (ℝ; half; 0<half)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (0≤sq-all)
open import corpus.cubical_agda.Corridor.Running.General.SqrtReal using (sqrtReal)
open import corpus.cubical_agda.Corridor.Running.General.ReparamReal using (reparamℝ)

private
  IsYes : {A : Type₀} → Dec A → Type₀
  IsYes (yes _) = Unit
  IsYes (no  _) = ⊥
  getYes : {A : Type₀} (d : Dec A) → IsYes d → A
  getYes (yes a) _ = a

  hh : (half + half) ≡ 1
  hh = getYes (discreteℚ (half + half) 1) tt

  0≤4·sq : (b : ℚ) → 0 ≤ (4 · (b · b))
  0≤4·sq b = subst (_≤ (4 · (b · b))) (·AnnihilL (b · b))
               (≤-·o 0 4 (b · b) (0≤sq-all b) (<Weaken≤ 0 4 (getYes (<Dec 0 4) tt)))

module _ (a b d : ℚ) where

  Δ : ℚ
  Δ = ((a - d) · (a - d)) + (4 · (b · b))

  0≤Δ : 0 ≤ Δ
  0≤Δ = subst (_≤ Δ) (+IdR 0)
          (≤Monotone+ 0 ((a - d) · (a - d)) 0 (4 · (b · b)) (0≤sq-all (a - d)) (0≤4·sq b))
    where open import Cubical.Data.Rationals.Order using (≤Monotone+)

  s : ℚ
  s = a + d

  φ ψ : ℚ → ℚ
  φ q = (q + q) + (- s)
  ψ p = (p + s) · half

  φ-mono : (q r : ℚ) → q < r → φ q < φ r
  φ-mono q r q<r =
    <-+o (q + q) (r + r) (- s)
      (isTrans< (q + q) (r + q) (r + r) (<-+o q r q q<r) (<-o+ q r r q<r))

  ψ-mono : (p p' : ℚ) → p < p' → ψ p < ψ p'
  ψ-mono p p' p<p' = <-·o (p + s) (p' + s) half 0<half (<-+o p p' s p<p')

  φ∘ψ : (p : ℚ) → φ (ψ p) ≡ p
  φ∘ψ p = e1 ℚCommRing p s half
        ∙ cong (λ z → ((p + s) · z) + (- s)) hh
        ∙ e2 ℚCommRing p s

  ψ∘φ : (q : ℚ) → ψ (φ q) ≡ q
  ψ∘φ q = e3 ℚCommRing q s half
        ∙ e4 ℚCommRing q half
        ∙ cong (q ·_) hh
        ∙ e5 ℚCommRing q

  -- λ₊ = (a + d + √Δ)/2 as a located Dedekind real.
  specEdge : ℝ
  specEdge = reparamℝ φ ψ φ-mono ψ-mono φ∘ψ ψ∘φ (sqrtReal Δ 0≤Δ)
