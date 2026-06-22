{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE SPECTRAL ROUTE — reducing the n×n operator-norm C*-identity to EXISTING work.
--
-- A search of the corpus shows the post-diagonalisation C*-identity is ALREADY built:
-- the organism's `DiagonalCStar` provides the finite spectral-radius / ℓ∞ norm ‖·‖ on
-- an eigenvalue vector together with its C*-identity `cstar-identity : ‖λ²‖ ≡ ‖λ‖²`,
-- sup-of-squares (`maxℚ-sq`), submultiplicativity, and the LUB laws.  So the general
-- symmetric operator-norm C*-identity ‖M²‖=‖M‖² needs NO variational supremum or
-- Cauchy–Schwarz: with the spectral radius ‖M‖ := ‖λ‖ (λ = the eigenvalues),
--      ‖M²‖ = ‖λ²‖ = ‖λ‖² = ‖M‖²    is exactly `DiagonalCStar.cstar-identity`,
-- and M²'s spectrum IS λ² by `eigenSquared` (λ eigenvalue of M ⟹ λ² eigenvalue of M²).
-- This module assembles those two existing results into the C*-identity, leaving the
-- SOLE remaining obligation the eigendecomposition itself (the constructive spectral
-- theorem M ↦ λ + orthogonal invariance) — the one genuinely deep piece.
--
module corpus.cubical_agda.Corridor.Running.General.SpectralCStar where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Rationals using (ℚ; _·_)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import corpus.cubical_agda.RealCohesion.DiagonalCStar using (‖_‖; cstar-identity)
open import corpus.cubical_agda.Corridor.Running.General.OperatorNorm using (charEq; charEqSq; eigenSquared)

-- the spectral-radius operator norm of a symmetric matrix presented by its eigenvalue
-- vector λ (= the existing DiagonalCStar ℓ∞ norm of the spectrum).
specRadius : {n : ℕ} → (Fin (suc n) → ℚ) → ℚ
specRadius vs = ‖ vs ‖

-- THE C*-IDENTITY FOR THE SPECTRAL RADIUS — directly the existing DiagonalCStar result.
-- ‖M²‖ = ‖M‖²  (M² presented by the squared spectrum λ²).
specRadius-cstar : {n : ℕ} (vs : Fin (suc n) → ℚ)
                 → specRadius (λ i → vs i · vs i) ≡ specRadius vs · specRadius vs
specRadius-cstar vs = cstar-identity vs

-- THE 2-EIGENVALUE ASSEMBLY: combining DiagonalCStar.cstar-identity with eigenSquared.
-- Given a symmetric 2×2 M=[[a,b],[b,d]] with eigenvalues λ₀,λ₁ (charEq), we get BOTH
--   (i) the C*-identity ‖(λ₀²,λ₁²)‖ = ‖(λ₀,λ₁)‖²        [DiagonalCStar.cstar-identity]
--   (ii) λ₀², λ₁² are eigenvalues of M²                  [eigenSquared, ours]
-- i.e. the squared spectrum is M²'s spectrum AND it satisfies the C*-identity.
twoEig : (λ₀ λ₁ : ℚ) → Fin 2 → ℚ
twoEig λ₀ λ₁ zero    = λ₀
twoEig λ₀ λ₁ (suc _) = λ₁

spectral2-cstar : (a b d λ₀ λ₁ : ℚ)
  → charEq ℚCommRing a b d λ₀ → charEq ℚCommRing a b d λ₁
  → (‖ (λ i → twoEig λ₀ λ₁ i · twoEig λ₀ λ₁ i) ‖ ≡ ‖ twoEig λ₀ λ₁ ‖ · ‖ twoEig λ₀ λ₁ ‖)
  × charEqSq ℚCommRing a b d (λ₀ · λ₀)
  × charEqSq ℚCommRing a b d (λ₁ · λ₁)
spectral2-cstar a b d λ₀ λ₁ h₀ h₁ =
    cstar-identity (twoEig λ₀ λ₁)
  , eigenSquared ℚCommRing a b d λ₀ h₀
  , eigenSquared ℚCommRing a b d λ₁ h₁
