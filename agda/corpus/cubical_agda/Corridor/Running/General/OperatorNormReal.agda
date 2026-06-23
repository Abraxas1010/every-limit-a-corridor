{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE ℝ-COMPLETED OPERATOR NORM — operatorNorm M : ℝ, for ANY rational matrix (non-symmetric included).
--
-- This closes the C2/C3 frontier that OperatorNorm (the algebraic eigenSquared core) flagged open: the
-- passage to the ℝ-completed operator norm.  The largest singular value of any M is
--      ‖M‖ = √ρ(MᵀM),
-- and MᵀM is symmetric (Mᵀ⋆M, with (Mᵀ⋆M)ᵀ ≡ Mᵀ⋆M by ⋆ᵀ), so its spectral radius is the located real
-- specRadius (MᵀM), and the operator norm is its constructive square root sqrtRealℝ.  Hence the full
-- operator norm of every rational matrix in every finite dimension is a located Dedekind real --- the
-- irrational singular numbers the analytic line makes reachable --- with no eigenvectors, no SVD, no
-- spectral theorem.  Its positive upper bound is ‖MᵀM‖₁ + 2 (the ℓ¹ bound on the spectral radius).
--
module corpus.cubical_agda.Corridor.Running.General.OperatorNormReal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc; zero)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; _≤_; isTrans<; isTrans≤<)
open import corpus.cubical_agda.RealCohesion.DedekindReal using (ℝ; x<x+1)
open import corpus.cubical_agda.Corridor.Running.General.AdjointFormN
open import corpus.cubical_agda.Corridor.Running.General.QuadBound using (oneNorm)
open import corpus.cubical_agda.Corridor.Running.General.SpecCutDisjoint using (0≤oneNorm)
open import corpus.cubical_agda.Corridor.Running.General.SpecRadiusReal using (specRadius)
open import corpus.cubical_agda.Corridor.Running.General.SqrtRealR using (sqrtRealℝ; PosUpper)

open Coefficient ℚCommRing using (Mat; _⋆_)
open Adjoint ℚCommRing using (_ᵀ; ⋆ᵀ)

-- transpose is an involution:  (Mᵀ)ᵀ ≡ M  (entrywise refl).
ᵀᵀ : {m n : ℕ} (M : Mat m n) → (M ᵀ) ᵀ ≡ M
ᵀᵀ M = refl

module _ {n' : ℕ} (M : Mat (suc n') (suc n')) where

  -- MᵀM is symmetric:  (Mᵀ⋆M)ᵀ ≡ Mᵀ⋆(Mᵀ)ᵀ ≡ Mᵀ⋆M.
  symMtM : (M ᵀ ⋆ M) ᵀ ≡ (M ᵀ ⋆ M)
  symMtM = ⋆ᵀ (M ᵀ) M ∙ cong ((M ᵀ) ⋆_) (ᵀᵀ M)

  private
    MtM : Mat (suc n') (suc n')
    MtM = M ᵀ ⋆ M
    ρ : ℝ
    ρ = specRadius MtM symMtM                 -- ρ(MᵀM) = ‖M‖², a located real
    0≤‖MtM‖ : 0 ≤ oneNorm MtM
    0≤‖MtM‖ = 0≤oneNorm MtM symMtM MtM
    0<‖MtM‖+1 : 0 < (oneNorm MtM + 1)
    0<‖MtM‖+1 = isTrans≤< 0 (oneNorm MtM) (oneNorm MtM + 1) 0≤‖MtM‖ (x<x+1 (oneNorm MtM))
    -- ‖M‖² < ‖MᵀM‖₁ + 2  is a positive upper bound for the square root.
    posUpper : PosUpper ρ
    posUpper = (oneNorm MtM + 1) + 1
             , isTrans< 0 (oneNorm MtM + 1) ((oneNorm MtM + 1) + 1)
                 0<‖MtM‖+1 (x<x+1 (oneNorm MtM + 1))
             , ∣ (oneNorm MtM + 1)
               , x<x+1 (oneNorm MtM + 1)
               , (0<‖MtM‖+1 , (0 , x<x+1 (oneNorm MtM))) ∣₁

  -- THE OPERATOR NORM:  ‖M‖ = √ρ(MᵀM), a located real for any rational matrix.
  operatorNorm : ℝ
  operatorNorm = sqrtRealℝ ρ posUpper
