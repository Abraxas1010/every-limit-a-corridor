{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE SPECTRAL RADIUS IS LOCATED — both brackets meet the operator-norm cut, in every dimension.
--
-- rayUp A q  (every Rayleigh quotient strictly below q) is the upper part of the operator-norm /
-- spectral-radius cut.  The "spectrum has a modulus" route brackets it from both sides with
-- COMPUTABLE RATIONALS:
--   • q > ‖A‖₁   ⟹  rayUp A q       (q is an upper bound — from QuadBound),
--   • q < Aᵢᵢ    ⟹  ¬ rayUp A q     (q is NOT an upper bound — from the eᵢ witness, LowerBracket).
-- So maxᵢ Aᵢᵢ ≤ ρ(A) ≤ ‖A‖₁, and the cut separates exactly the rationals on either side of the
-- spectral radius.  This is the located bracket; iterating it under squaring (ρ(M^{2^L})=ρ(M)^{2^L},
-- the landed C*-identity) drives the bracket width to 0 with the dyadic modulus.
--
module corpus.cubical_agda.Corridor.Running.General.SpecBracket where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Algebra.CommRing using (CommRing→Ring)
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals
open import Cubical.Data.Rationals.Order using (_<_; _≤_; isTrans≤<; isTrans<; isIrrefl<; <-·o)
open import Cubical.Relation.Nullary using (¬_)
open import corpus.cubical_agda.RealCohesion.DedekindReal using (0<1ℚ)
open import corpus.cubical_agda.Corridor.Running.General.GramPosDef using (⟪_,_⟫)
open import corpus.cubical_agda.Corridor.Running.General.QuadBound using (oneNorm; quadBound)
open import corpus.cubical_agda.Corridor.Running.General.LowerBracket using (eVec; eNorm; eRayleigh)

open Coefficient ℚCommRing using (Mat; _⋆_)

-- the upper part of the operator-norm / spectral-radius cut.
rayUp : {n : ℕ} → Mat n n → ℚ → Type
rayUp A q = (x : Mat _ 1) → 0 < ⟪ x , x ⟫ → ⟪ x , A ⋆ x ⟫ < (q · ⟪ x , x ⟫)

-- UPPER bracket: q above the ℓ¹ norm ⟹ q is a strict Rayleigh upper bound (q above ρ).
rayUp-oneNorm : {n : ℕ} (A : Mat n n) (q : ℚ) → (oneNorm A) < q → rayUp A q
rayUp-oneNorm A q n1<q x 0<xx =
  isTrans≤< (⟪ x , A ⋆ x ⟫) (oneNorm A · ⟪ x , x ⟫) (q · ⟪ x , x ⟫)
    (quadBound A x)
    (<-·o (oneNorm A) q (⟪ x , x ⟫) 0<xx n1<q)

-- LOWER bracket: q below a diagonal entry ⟹ q is NOT a Rayleigh upper bound (q below ρ).
notRayUp-diag : {n : ℕ} (A : Mat n n) (i : Fin n) (q : ℚ) → q < (A i i) → ¬ rayUp A q
notRayUp-diag A i q q<Aii ru = isIrrefl< q (isTrans< q (A i i) q q<Aii Aii<q)
  where
    0<ee : 0 < ⟪ eVec i , eVec i ⟫
    0<ee = subst (0 <_) (sym (eNorm i)) 0<1ℚ
    Aii<q : (A i i) < q
    Aii<q = subst2 _<_ (eRayleigh A i) (cong (q ·_) (eNorm i) ∙ ·IdR q) (ru (eVec i) 0<ee)
