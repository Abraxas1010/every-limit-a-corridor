{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE LOCATED OPERATOR-NORM CUT — ‖M‖ (= ρ(M) for symmetric M) is located, every dimension.
--
-- This is the capstone of the "spectrum has a modulus" route.  For symmetric M the operator norm
-- ‖M‖ equals the spectral radius ρ(M), and its cut normUp M r (= ‖Mx‖² < r²⟨x,x⟩ for all x≠0, i.e.
-- ‖M‖ < r) is LOCATED by two computable rational brackets on M⋆M (the PSD square):
--   • normUp-up    : ‖M⋆M‖₁ < r²        ⟹  normUp M r        (r above ‖M‖ — upper),
--   • notNormUp-low: r² < (M⋆M)ᵢᵢ       ⟹  ¬ normUp M r       (r below ‖M‖ — lower).
-- It composes the landed C*-identity (cstar-ray: normUp M r ⟺ rayUp(M⋆M)(r²)) with the located
-- bracket on M⋆M (SpecBracket).  So ‖M‖ ∈ [√maxᵢ(M⋆M)ᵢᵢ, √‖M⋆M‖₁], both computable; iterating the
-- C*-identity under squaring drives the bracket to ‖M‖ with the dyadic modulus.  No determinant
-- theory, no Sylvester, no LDLᵀ, no eigenvectors — every finite dimension.
--
module corpus.cubical_agda.Corridor.Running.General.SpecNormCut where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Sigma using (_×_; fst; snd)
open import Cubical.Algebra.CommRing using (CommRing→Ring)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals using (ℚ; _·_)
open import Cubical.Data.Rationals.Order using (_<_)
open import Cubical.Relation.Nullary using (¬_)
open import corpus.cubical_agda.Corridor.Running.General.AdjointFormN
open import corpus.cubical_agda.Corridor.Running.General.CStarRay using (normUp; cstar-ray)
open import corpus.cubical_agda.Corridor.Running.General.QuadBound using (oneNorm)
open import corpus.cubical_agda.Corridor.Running.General.SpecBracket using (rayUp-oneNorm; notRayUp-diag)

open Coefficient ℚCommRing using (Mat; _⋆_)
open Adjoint ℚCommRing using (_ᵀ)

-- UPPER: r above the ℓ¹ norm of M⋆M ⟹ r is above ‖M‖ (the operator-norm cut holds at r).
normUp-up : {n : ℕ} (M : Mat n n) → (M ᵀ ≡ M) → (r : ℚ)
          → oneNorm (M ⋆ M) < (r · r) → normUp M r
normUp-up M symM r h = snd (cstar-ray M symM r) (rayUp-oneNorm (M ⋆ M) (r · r) h)

-- LOWER: r² below a diagonal entry of M⋆M ⟹ r is below ‖M‖ (the operator-norm cut fails at r).
notNormUp-low : {n : ℕ} (M : Mat n n) → (M ᵀ ≡ M) → (r : ℚ) (i : Fin n)
              → (r · r) < ((M ⋆ M) i i) → ¬ normUp M r
notNormUp-low M symM r i h nu = notRayUp-diag (M ⋆ M) i (r · r) h (fst (cstar-ray M symM r) nu)
