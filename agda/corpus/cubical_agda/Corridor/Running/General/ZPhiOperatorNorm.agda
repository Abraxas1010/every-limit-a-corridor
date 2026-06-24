{-# OPTIONS --cubical --safe --guardedness #-}
--
-- THE n×n Z[φ] OPERATOR NORM — zphiHouseNorm M : ℝ, a located real, for ANY dimension and ANY n×n matrix.
--
-- This closes the n×n operator norm without re-deriving the spectral radius over Z[φ].  The lego is the
-- REGULAR REPRESENTATION of the golden ring: multiplication by φ acts on the basis (1,φ) as [[0,1],[1,1]]
-- (φ·1=φ, φ·φ=φ+1), so a golden integer a+bφ becomes the 2×2 rational matrix [[a,b],[b,a+b]], and an n×n
-- Z[φ]-matrix M=(A,B) becomes the 2n×2n RATIONAL matrix  M̃ = [[A,B],[B,A+B]]  (`regRep`).  The rep is a
-- ring homomorphism and every scalar block is symmetric, so M̃ᵀM̃ = (MᵀM)~ is rational symmetric — and the
-- EXISTING operator norm (operatorNorm = √ρ of the Gram matrix, the full located-real spectral radius) just
-- applies to M̃.  Hence ‖M‖ := ‖M̃‖ = √ρ(M̃ᵀM̃) is a located Dedekind real for every n×n Z[φ]-matrix.
--
-- Because the rep's eigenvalues are the eigenvalues of M under BOTH real embeddings φ⁺=(1+√5)/2 and
-- φ⁻=(1−√5)/2 (and both Gram matrices are PSD), this norm is max(‖M‖_{φ⁺}, ‖M‖_{φ⁻}) — the "house" norm,
-- the operator norm of M over all real places, the natural size of a Z[φ]-matrix.  No new spectral radius,
-- no Q[φ] C*-convergence: the analytic layer is supplied entirely by the rational operatorNorm.
--
module corpus.cubical_agda.Corridor.Running.General.ZPhiOperatorNorm where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Algebra.Matrix.CommRingCoefficient using (module Coefficient)
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals using (ℚ) renaming (_+_ to _+ℚ_)
open import corpus.cubical_agda.RealCohesion.DedekindReal using (ℝ)
open import corpus.cubical_agda.Corridor.Running.General.OperatorNormReal using (operatorNorm)

open Coefficient ℚCommRing using (Mat)

-- a golden-integer matrix:  the pair (A,B) standing for A + Bφ.
ZφMat : ℕ → Type₀
ZφMat n = Mat n n × Mat n n

-- split a Fin (n+n) index into its two halves (the ⊗1 part and the ⊗φ part).
splitFin : {m n : ℕ} → Fin (m + n) → Fin m ⊎ Fin n
splitFin {zero}  i       = inr i
splitFin {suc m} zero    = inl zero
splitFin {suc m} (suc i) with splitFin {m} i
... | inl j = inl (suc j)
... | inr j = inr j

-- THE REGULAR REPRESENTATION:  M = (A,B) ↦ the 2n×2n rational matrix [[A,B],[B,A+B]].
regRep : {n : ℕ} → ZφMat n → Mat (n + n) (n + n)
regRep {n} (A , B) i j = entry (splitFin {n} {n} i) (splitFin {n} {n} j)
  where
    entry : Fin n ⊎ Fin n → Fin n ⊎ Fin n → ℚ
    entry (inl i') (inl j') = A i' j'            -- ⊗1 → ⊗1 : A
    entry (inl i') (inr j') = B i' j'            -- ⊗φ → ⊗1 : B
    entry (inr i') (inl j') = B i' j'            -- ⊗1 → ⊗φ : B
    entry (inr i') (inr j') = (A i' j') +ℚ (B i' j')   -- ⊗φ → ⊗φ : A+B

-- THE n×n Z[φ] OPERATOR NORM:  ‖M‖ = ‖M̃‖ = √ρ(M̃ᵀM̃), a located real for every Z[φ]-matrix.
-- (suc m + suc m = suc (m + suc m) definitionally, so the regular rep is square of size suc _.)
zphiHouseNorm : {m : ℕ} → ZφMat (suc m) → ℝ
zphiHouseNorm {m} M = operatorNorm (regRep M)
